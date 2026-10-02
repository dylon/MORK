//! Bounded decoding of a serialized SharedMapping from one owned byte image.
//! The historical path decoder is retained for trusted inputs; ACT migration
//! uses this entry point after capturing exact `.sm` bytes once.

use crate::{MAX_WRITER_THREADS, PEARSON_BOUND, SharedMapping, SharedMappingHandle, Slab, Symbol, ThinBytes, bounded_pearson_hash};
use pathmap::PathMap;
use std::collections::HashSet;
use std::io::{self, Cursor, Read};
use zip::ZipArchive;

const META_NAME: &str = "FileSizes.meta";
const DATA_PREFIX: &str = "SharedMapping_0x";
const DATA_SUFFIX: &str = ".binary_data";
const META_RECORD_BYTES: usize = 16;
const STORED_SYMBOL_BYTES: usize = 6;

/// Resource ceilings for loading one historical MORK `.sm` image.
#[derive(Clone, Copy, Debug)]
pub struct SharedMappingReadLimits {
  pub max_archive_bytes: usize,
  pub max_total_uncompressed_bytes: usize,
  pub max_lane_bytes: usize,
  pub max_symbol_bytes: usize,
  pub max_symbols: usize,
}

impl Default for SharedMappingReadLimits {
  fn default() -> Self {
    Self {
      max_archive_bytes: 128 * 1024 * 1024,
      max_total_uncompressed_bytes: 256 * 1024 * 1024,
      max_lane_bytes: 64 * 1024 * 1024,
      max_symbol_bytes: 16 * 1024 * 1024,
      max_symbols: 1_000_000,
    }
  }
}

fn invalid(message: impl Into<String>) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn limit(message: &'static str) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn lane_from_name(name: &str) -> io::Result<usize> {
  let digits = name
    .strip_prefix(DATA_PREFIX)
    .and_then(|rest| rest.strip_suffix(DATA_SUFFIX))
    .ok_or_else(|| invalid("unknown SharedMapping ZIP entry"))?;
  let bytes = digits.as_bytes();
  if bytes.len() != 2 || !bytes.iter().all(|byte| byte.is_ascii_digit() || (b'A'..=b'F').contains(byte)) {
    return Err(invalid("malformed SharedMapping lane filename"));
  }
  let lane = usize::from_str_radix(digits, 16).map_err(|_| invalid("invalid SharedMapping lane index"))?;
  if lane >= MAX_WRITER_THREADS {
    return Err(invalid("SharedMapping lane index exceeds writer limit"));
  }
  Ok(lane)
}

// ZipArchive reserves space for the declared file count while opening. Check
// the bounded EOCD count first, so a tiny malicious ZIP64 footer cannot make
// that constructor reserve an unbounded amount of memory.
fn check_zip_entry_count(bytes: &[u8]) -> io::Result<()> {
  const EOCD_BYTES: usize = 22;
  if bytes.len() < EOCD_BYTES {
    return Err(invalid("truncated SharedMapping ZIP footer"));
  }
  let first = bytes.len().saturating_sub(EOCD_BYTES + usize::from(u16::MAX));
  let mut saw_exact_footer = false;
  for offset in (first..=bytes.len() - EOCD_BYTES).rev() {
    let footer = &bytes[offset..offset + EOCD_BYTES];
    if &footer[..4] != b"PK\x05\x06" {
      continue;
    }
    let comment_len = usize::from(u16::from_le_bytes(footer[20..22].try_into().expect("two comment bytes")));
    let Some(footer_end) = offset.checked_add(EOCD_BYTES).and_then(|end| end.checked_add(comment_len)) else {
      continue;
    };
    if footer_end > bytes.len() {
      continue;
    }
    let disk = u16::from_le_bytes(footer[4..6].try_into().expect("two disk bytes"));
    let central_disk = u16::from_le_bytes(footer[6..8].try_into().expect("two central disk bytes"));
    let on_disk = u16::from_le_bytes(footer[8..10].try_into().expect("two disk count bytes"));
    let total = u16::from_le_bytes(footer[10..12].try_into().expect("two total count bytes"));
    let central_size = u32::from_le_bytes(footer[12..16].try_into().expect("four central size bytes"));
    let central_offset = u32::from_le_bytes(footer[16..20].try_into().expect("four central offset bytes"));
    if disk != 0 || central_disk != 0 || on_disk != total || usize::from(total) > MAX_WRITER_THREADS + 1 || central_size == u32::MAX || central_offset == u32::MAX {
      return Err(limit("SharedMapping ZIP file count or disk is outside cap"));
    }
    saw_exact_footer |= footer_end == bytes.len();
  }
  if saw_exact_footer { Ok(()) } else { Err(invalid("SharedMapping ZIP footer is missing")) }
}

// zip::ZipArchive indexes entries by filename, so duplicate central-directory
// names disappear from its len()/by_index() view. Count and check the bounded
// central-directory records directly before trusting that view.
fn check_central_directory_names(bytes: &[u8], start: u64, visible_entries: usize) -> io::Result<()> {
  let mut cursor = usize::try_from(start).map_err(|_| invalid("SharedMapping central directory offset exceeds usize"))?;
  let mut names: HashSet<&[u8]> = HashSet::new();
  let mut count = 0usize;
  while bytes.get(cursor..cursor.saturating_add(4)) == Some(b"PK\x01\x02".as_slice()) {
    let header = bytes
      .get(cursor..cursor.checked_add(46).ok_or_else(|| invalid("SharedMapping central header offset overflow"))?)
      .ok_or_else(|| invalid("truncated SharedMapping central header"))?;
    let name_len = usize::from(u16::from_le_bytes(header[28..30].try_into().expect("two name bytes")));
    let extra_len = usize::from(u16::from_le_bytes(header[30..32].try_into().expect("two extra bytes")));
    let comment_len = usize::from(u16::from_le_bytes(header[32..34].try_into().expect("two comment bytes")));
    let record_end = cursor
      .checked_add(46)
      .and_then(|end| end.checked_add(name_len))
      .and_then(|end| end.checked_add(extra_len))
      .and_then(|end| end.checked_add(comment_len))
      .ok_or_else(|| invalid("SharedMapping central record offset overflow"))?;
    let record = bytes.get(cursor..record_end).ok_or_else(|| invalid("truncated SharedMapping central record"))?;
    if !names.insert(&record[46..46 + name_len]) {
      return Err(invalid("duplicate SharedMapping ZIP central-directory name"));
    }
    count += 1;
    if count > MAX_WRITER_THREADS + 1 {
      return Err(limit("SharedMapping ZIP has too many central-directory entries"));
    }
    cursor = record_end;
  }
  if count != visible_entries {
    return Err(invalid("SharedMapping ZIP central-directory count differs from ZIP index"));
  }
  Ok(())
}

struct Record {
  symbol: Symbol,
  tag_at: usize,
  bytes_at: usize,
  bytes_end: usize,
}

impl SharedMapping {
  /// Decode a single bounded ZIP image without reopening a pathname or
  /// allocating slabs from untrusted metadata. Every record is checked before
  /// a pointer into a slab or PathMap is constructed.
  pub fn deserialize_bytes_checked(bytes: &[u8], limits: &SharedMappingReadLimits) -> io::Result<SharedMappingHandle> {
    if bytes.len() > limits.max_archive_bytes {
      return Err(limit("SharedMapping archive exceeds byte cap"));
    }
    check_zip_entry_count(bytes)?;
    let mut archive = ZipArchive::new(Cursor::new(bytes)).map_err(|error| invalid(format!("invalid SharedMapping ZIP: {error}")))?;
    if archive.len() > MAX_WRITER_THREADS + 1 {
      return Err(limit("SharedMapping ZIP has too many entries"));
    }
    check_central_directory_names(bytes, archive.central_directory_start(), archive.len())?;

    let mut metadata: Option<Vec<u8>> = None;
    let mut lanes: [Option<Vec<u8>>; MAX_WRITER_THREADS] = std::array::from_fn(|_| None);
    let mut total_uncompressed = 0usize;
    for entry_index in 0..archive.len() {
      let mut entry = archive.by_index(entry_index).map_err(|error| invalid(format!("invalid SharedMapping ZIP entry: {error}")))?;
      let name = entry.name().to_owned();
      let lane = if name == META_NAME { None } else { Some(lane_from_name(&name)?) };
      if (lane.is_none() && metadata.is_some()) || lane.is_some_and(|index| lanes[index].is_some()) {
        return Err(invalid("duplicate SharedMapping ZIP entry"));
      }
      let declared = usize::try_from(entry.size()).map_err(|_| limit("SharedMapping ZIP entry size exceeds usize"))?;
      let entry_cap = if lane.is_none() { MAX_WRITER_THREADS * META_RECORD_BYTES } else { limits.max_lane_bytes };
      if declared > entry_cap {
        return Err(limit("SharedMapping ZIP entry exceeds byte cap"));
      }
      total_uncompressed = total_uncompressed.checked_add(declared).ok_or_else(|| limit("SharedMapping uncompressed length overflow"))?;
      if total_uncompressed > limits.max_total_uncompressed_bytes {
        return Err(limit("SharedMapping uncompressed data exceeds byte cap"));
      }
      let mut data = Vec::new();
      data.try_reserve_exact(declared).map_err(|_| limit("SharedMapping allocation exceeds available memory"))?;
      (&mut entry).take(u64::try_from(declared).unwrap_or(u64::MAX).saturating_add(1)).read_to_end(&mut data)?;
      if data.len() != declared {
        return Err(invalid("SharedMapping ZIP entry differs from declared size"));
      }
      if let Some(index) = lane {
        lanes[index] = Some(data);
      } else {
        metadata = Some(data);
      }
    }

    let metadata = metadata.ok_or_else(|| invalid("SharedMapping metadata is missing"))?;
    if metadata.len() % META_RECORD_BYTES != 0 {
      return Err(invalid("SharedMapping metadata has a partial record"));
    }
    let mut declared_sizes: [Option<usize>; MAX_WRITER_THREADS] = [None; MAX_WRITER_THREADS];
    for record in metadata.chunks_exact(META_RECORD_BYTES) {
      let index = usize::try_from(u64::from_be_bytes(record[..8].try_into().expect("eight index bytes"))).map_err(|_| invalid("SharedMapping metadata lane exceeds usize"))?;
      if index >= MAX_WRITER_THREADS || declared_sizes[index].is_some() {
        return Err(invalid("duplicate or out-of-range SharedMapping metadata lane"));
      }
      let size = usize::try_from(u64::from_be_bytes(record[8..].try_into().expect("eight size bytes"))).map_err(|_| limit("SharedMapping metadata size exceeds usize"))?;
      if size == 0 || size > limits.max_lane_bytes {
        return Err(limit("SharedMapping metadata size outside lane cap"));
      }
      declared_sizes[index] = Some(size);
    }
    for index in 0..MAX_WRITER_THREADS {
      match (&lanes[index], declared_sizes[index]) {
        (None, None) => (),
        (Some(data), Some(size)) if data.len() == size => (),
        _ => return Err(invalid("SharedMapping metadata does not match lane data")),
      }
    }

    let mut records: [Vec<Record>; MAX_WRITER_THREADS] = std::array::from_fn(|_| Vec::new());
    let mut seen_symbols: HashSet<Symbol> = HashSet::new();
    let mut seen_bytes: HashSet<&[u8]> = HashSet::new();
    let mut symbol_count = 0usize;
    for (lane_index, lane) in lanes.iter().enumerate() {
      let Some(data) = lane else {
        continue;
      };
      let mut cursor = 0usize;
      while cursor < data.len() {
        let symbol_end = cursor.checked_add(STORED_SYMBOL_BYTES).ok_or_else(|| invalid("SharedMapping symbol offset overflow"))?;
        let stored_symbol = data.get(cursor..symbol_end).ok_or_else(|| invalid("truncated SharedMapping symbol ID"))?;
        let mut symbol = [0u8; 8];
        symbol[2..].copy_from_slice(stored_symbol);
        if symbol[2] as usize != lane_index || symbol == [0; 8] || symbol[3..].iter().all(|byte| *byte == 0xff) || !seen_symbols.insert(symbol) {
          return Err(invalid("wrong-lane, zero, exhausted, or duplicate SharedMapping symbol ID"));
        }
        let tag_at = symbol_end;
        let tag = *data.get(tag_at).ok_or_else(|| invalid("truncated SharedMapping length tag"))?;
        let (length, bytes_at) = if tag & 0x80 != 0 {
          (usize::from(!tag), tag_at + 1)
        } else {
          let prefix = data.get(tag_at..tag_at + 8).ok_or_else(|| invalid("truncated SharedMapping long length"))?;
          let length = usize::try_from(u64::from_be_bytes(prefix.try_into().expect("eight length bytes"))).map_err(|_| limit("SharedMapping symbol length exceeds usize"))?;
          if length <= 127 {
            return Err(invalid("noncanonical SharedMapping long length"));
          }
          (length, tag_at + 8)
        };
        if length > limits.max_symbol_bytes {
          return Err(limit("SharedMapping symbol exceeds byte cap"));
        }
        let bytes_end = bytes_at.checked_add(length).ok_or_else(|| invalid("SharedMapping symbol length overflow"))?;
        let symbol_bytes = data.get(bytes_at..bytes_end).ok_or_else(|| invalid("truncated SharedMapping symbol bytes"))?;
        if !seen_bytes.insert(symbol_bytes) {
          return Err(invalid("duplicate SharedMapping symbol bytes"));
        }
        symbol_count = symbol_count.checked_add(1).ok_or_else(|| limit("SharedMapping symbol count overflow"))?;
        if symbol_count > limits.max_symbols {
          return Err(limit("SharedMapping symbol count exceeds cap"));
        }
        records[lane_index].push(Record { symbol, tag_at, bytes_at, bytes_end });
        cursor = bytes_end;
      }
      if records[lane_index].is_empty() {
        return Err(invalid("empty SharedMapping lane data"));
      }
    }

    let mapping = SharedMapping::new();
    let mapping_ptr = mapping.0.as_ptr();
    let mut to_symbol = [(); MAX_WRITER_THREADS].map(|()| PathMap::<Symbol>::new());
    let mut to_bytes = [(); MAX_WRITER_THREADS].map(|()| PathMap::<ThinBytes>::new());
    for (lane_index, lane) in lanes.iter().enumerate() {
      let Some(data) = lane else {
        continue;
      };
      let slab = unsafe { Slab::allocate(data.len() as u64) };
      unsafe {
        let slab_data = (*slab).slab_data;
        core::ptr::copy_nonoverlapping(data.as_ptr(), slab_data, data.len());
        (*slab).write_pos = data.len();
        (*mapping_ptr).permissions[lane_index].0.symbol_table_start.store(slab, core::sync::atomic::Ordering::Relaxed);
        (*mapping_ptr).permissions[lane_index].0.symbol_table_last.store(slab, core::sync::atomic::Ordering::Relaxed);
        let mut max_symbol = 0u64;
        for record in &records[lane_index] {
          let value = &data[record.bytes_at..record.bytes_end];
          max_symbol = max_symbol.max(u64::from_be_bytes(record.symbol));
          let bucket = bounded_pearson_hash::<PEARSON_BOUND>(value) as usize % MAX_WRITER_THREADS;
          to_symbol[bucket].insert(value, record.symbol);
          to_bytes[lane_index].insert(&record.symbol, ThinBytes(slab_data.add(record.tag_at)));
        }
        (*mapping_ptr).permissions[lane_index].0.next_symbol.store(max_symbol + 1, core::sync::atomic::Ordering::Relaxed);
      }
    }
    for (index, (symbols, bytes)) in to_symbol.into_iter().zip(to_bytes).enumerate() {
      *mapping.to_symbol[index].0.write().expect("new SharedMapping symbol lock") = symbols;
      *mapping.to_bytes[index].0.write().expect("new SharedMapping byte lock") = bytes;
    }
    Ok(mapping)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::io::Write;
  use std::sync::atomic::{AtomicU64, Ordering};
  use zip::write::FileOptions;

  static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

  fn zip_image(entries: &[(&str, Vec<u8>)]) -> Vec<u8> {
    let mut writer = zip::ZipWriter::new(Cursor::new(Vec::new()));
    for (name, data) in entries {
      writer.start_file::<&str, _>(*name, FileOptions::<()>::default()).expect("start ZIP entry");
      writer.write_all(data).expect("write ZIP entry");
    }
    writer.finish().expect("finish ZIP image").into_inner()
  }

  fn record(lane: u8, id: u8, bytes: &[u8]) -> Vec<u8> {
    assert!(bytes.len() <= 127);
    let mut out = vec![lane, 0, 0, 0, 0, id, !(bytes.len() as u8)];
    out.extend_from_slice(bytes);
    out
  }

  fn meta(lane: u64, size: usize) -> Vec<u8> {
    let mut out = lane.to_be_bytes().to_vec();
    out.extend_from_slice(&(size as u64).to_be_bytes());
    out
  }

  fn single_image() -> Vec<u8> {
    let data = record(0, 1, b"alpha");
    zip_image(&[("SharedMapping_0x00.binary_data", data.clone()), (META_NAME, meta(0, data.len()))])
  }

  fn rejects(entries: &[(&str, Vec<u8>)]) {
    SharedMapping::deserialize_bytes_checked(&zip_image(entries), &SharedMappingReadLimits::default())
      .err()
      .expect("malformed symbol map must be rejected");
  }

  #[test]
  fn checked_bytes_round_trip_the_original_writer() {
    let mapping = SharedMapping::new();
    let permit = mapping.try_aquire_permission().expect("single writer permit");
    let alpha = permit.get_sym_or_insert(b"alpha");
    let empty = permit.get_sym_or_insert(b"");
    let long_bytes = vec![b'x'; 200];
    let long = permit.get_sym_or_insert(&long_bytes);
    drop(permit);
    let serial = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("mork-checked-sm-{}-{serial}.zip", std::process::id()));
    mapping.serialize(&path).expect("serialize original mapping");
    let bytes = std::fs::read(&path).expect("read original symbol-map image");
    std::fs::remove_file(&path).expect("remove original symbol-map image");

    let loaded = SharedMapping::deserialize_bytes_checked(&bytes, &SharedMappingReadLimits::default()).expect("checked loader accepts original serializer output");
    assert_eq!(loaded.get_sym(b"alpha"), Some(alpha));
    assert_eq!(loaded.get_sym(b""), Some(empty));
    assert_eq!(loaded.get_sym(&long_bytes), Some(long));
    assert_eq!(loaded.get_bytes(alpha), Some(b"alpha".as_slice()));
    assert_eq!(loaded.get_bytes(empty), Some(b"".as_slice()));
    assert_eq!(loaded.get_bytes(long), Some(long_bytes.as_slice()));
    assert_eq!(loaded.get_bytes([0, 0, 128, 0, 0, 0, 0, 1]), None);
  }

  #[test]
  fn rejects_bad_zip_metadata_and_names_without_panicking() {
    let data = record(0, 1, b"alpha");
    rejects(&[("x", data.clone()), (META_NAME, meta(0, data.len()))]);
    rejects(&[("SharedMapping_0x00.binary_data", data.clone())]);
    rejects(&[(META_NAME, vec![0; 15])]);
    rejects(&[(META_NAME, meta(128, data.len()))]);
    let mut duplicate_meta = meta(0, data.len());
    duplicate_meta.extend(meta(0, data.len()));
    rejects(&[("SharedMapping_0x00.binary_data", data.clone()), (META_NAME, duplicate_meta)]);
    rejects(&[(META_NAME, meta(0, data.len()))]);
    rejects(&[("SharedMapping_0x00.binary_data", data.clone()), (META_NAME, meta(0, data.len() + 1))]);
    // ZipWriter rejects duplicate names itself. Change both copies of the
    // second name in a valid ZIP image to exercise the decoder's check.
    let mut duplicate_zip = zip_image(&[
      ("SharedMapping_0x00.binary_data", data.clone()),
      ("SharedMapping_0x01.binary_data", data.clone()),
      (META_NAME, meta(0, data.len())),
    ]);
    let old_name = b"SharedMapping_0x01.binary_data";
    let new_name = b"SharedMapping_0x00.binary_data";
    let offsets: Vec<_> = duplicate_zip
      .windows(old_name.len())
      .enumerate()
      .filter_map(|(offset, bytes)| (bytes == old_name).then_some(offset))
      .collect();
    assert_eq!(offsets.len(), 2, "local and central ZIP names");
    for offset in offsets {
      duplicate_zip[offset..offset + old_name.len()].copy_from_slice(new_name);
    }
    assert!(SharedMapping::deserialize_bytes_checked(&duplicate_zip, &SharedMappingReadLimits::default()).is_err());

    let mut declared_zip64_count = single_image();
    let footer = declared_zip64_count.len() - 22;
    assert_eq!(&declared_zip64_count[footer..footer + 4], b"PK\x05\x06");
    declared_zip64_count[footer + 8..footer + 12].fill(0xff);
    assert!(SharedMapping::deserialize_bytes_checked(&declared_zip64_count, &SharedMappingReadLimits::default()).is_err());

    // A later forged footer must not hide the dangerous count in an earlier
    // candidate: ZipArchive can fall back when the later one is invalid.
    let mut fallback_zip = declared_zip64_count;
    let mut forged_footer = single_image();
    forged_footer = forged_footer.split_off(forged_footer.len() - 22);
    fallback_zip.extend(forged_footer);
    assert!(SharedMapping::deserialize_bytes_checked(&fallback_zip, &SharedMappingReadLimits::default()).is_err());
  }

  #[test]
  fn rejects_truncated_wrong_lane_and_duplicate_symbol_records() {
    let truncated = vec![0, 0, 0, 0, 0, 1, !5, b'a'];
    rejects(&[("SharedMapping_0x00.binary_data", truncated.clone()), (META_NAME, meta(0, truncated.len()))]);

    let wrong_lane = record(1, 1, b"alpha");
    rejects(&[("SharedMapping_0x00.binary_data", wrong_lane.clone()), (META_NAME, meta(0, wrong_lane.len()))]);

    // A decoded maximum suffix would make the next insert borrow into the
    // following lane's ID range, even though the archive itself is bounded.
    let exhausted_id = vec![0, 0xff, 0xff, 0xff, 0xff, 0xff, !5, b'a', b'l', b'p', b'h', b'a'];
    rejects(&[("SharedMapping_0x00.binary_data", exhausted_id.clone()), (META_NAME, meta(0, exhausted_id.len()))]);

    let mut duplicate_ids = record(0, 1, b"alpha");
    duplicate_ids.extend(record(0, 1, b"beta"));
    rejects(&[("SharedMapping_0x00.binary_data", duplicate_ids.clone()), (META_NAME, meta(0, duplicate_ids.len()))]);

    let first = record(0, 1, b"alpha");
    let second = record(1, 1, b"alpha");
    let mut metadata = meta(0, first.len());
    metadata.extend(meta(1, second.len()));
    rejects(&[("SharedMapping_0x00.binary_data", first), ("SharedMapping_0x01.binary_data", second), (META_NAME, metadata)]);
  }

  #[test]
  fn writer_refuses_to_cross_a_restored_symbol_lane() {
    let mapping = SharedMapping::new();
    mapping.permissions[0].0.next_symbol.store((1u64 << 40) - 2, Ordering::Relaxed);
    let permit = mapping.try_aquire_permission().expect("single writer permit");
    let last_safe = permit.get_sym_or_insert(b"last safe symbol");
    assert_eq!(u64::from_be_bytes(last_safe), (1u64 << 40) - 2);
    let blocked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| permit.get_sym_or_insert(b"blocked symbol")));
    assert!(blocked.is_err());
    assert_eq!(permit.get_sym(b"blocked symbol"), None);
  }

  #[test]
  fn bounded_decoder_rejects_over_cap_images_and_corruptions() {
    let good = single_image();
    let small_archive = SharedMappingReadLimits {
      max_archive_bytes: good.len() - 1,
      ..SharedMappingReadLimits::default()
    };
    assert!(SharedMapping::deserialize_bytes_checked(&good, &small_archive).is_err());
    let small_output = SharedMappingReadLimits {
      max_total_uncompressed_bytes: 1,
      ..SharedMappingReadLimits::default()
    };
    assert!(SharedMapping::deserialize_bytes_checked(&good, &small_output).is_err());
    let no_symbols = SharedMappingReadLimits {
      max_symbols: 0,
      ..SharedMappingReadLimits::default()
    };
    assert!(SharedMapping::deserialize_bytes_checked(&good, &no_symbols).is_err());

    for len in 0..good.len() {
      let result = std::panic::catch_unwind(|| SharedMapping::deserialize_bytes_checked(&good[..len], &SharedMappingReadLimits::default()));
      assert!(result.is_ok(), "truncated ZIP panicked at {len}");
    }
    for index in 0..good.len() {
      let mut bad = good.clone();
      bad[index] ^= 0xff;
      let result = std::panic::catch_unwind(|| SharedMapping::deserialize_bytes_checked(&bad, &SharedMappingReadLimits::default()));
      assert!(result.is_ok(), "mutated ZIP panicked at {index}");
    }
  }
}
