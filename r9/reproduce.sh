#!/bin/sh

set -eu
export PYTHONDONTWRITEBYTECODE=1

usage() {
  printf '%s\n' \
    "Usage: ./reproduce.sh --mode release|proof|audit --geng PATH" \
    "       --lrat-check PATH --assets-dir DIRECTORY [--workers N]" \
    "" \
    "release checks manifests, endpoint catalogues, all 50 LRAT proofs," \
    "and the final implication chain. proof adds every solver-free" \
    "order-26 search. audit also adds the independent solver checks."
}

mode=""
geng=""
lrat_check=""
assets_dir=""
workers=8

while [ "$#" -gt 0 ]; do
  case "$1" in
    --mode)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      mode=$2
      shift 2
      ;;
    --geng)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      geng=$2
      shift 2
      ;;
    --lrat-check)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      lrat_check=$2
      shift 2
      ;;
    --assets-dir)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      assets_dir=$2
      shift 2
      ;;
    --workers)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      workers=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      printf 'Unknown argument: %s\n' "$1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

case "$mode" in
  release|proof|audit) ;;
  *) usage >&2; exit 2 ;;
esac

[ -x "$geng" ] || { printf 'geng is not executable: %s\n' "$geng" >&2; exit 2; }
[ -x "$lrat_check" ] || {
  printf 'LRAT checker is not executable: %s\n' "$lrat_check" >&2
  exit 2
}
[ -d "$assets_dir" ] || {
  printf 'Asset directory does not exist: %s\n' "$assets_dir" >&2
  exit 2
}
case "$workers" in
  ''|*[!0-9]*|0) printf 'workers must be a positive integer\n' >&2; exit 2 ;;
esac

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
package_root="$script_dir/package"
proof_dir="$package_root/research/erdos-617-r6"
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/erdos617-r9-public.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

check_hashes() {
  checksum_file=$1
  checksum_root=$2
  if command -v shasum >/dev/null 2>&1; then
    (cd "$checksum_root" && shasum -a 256 -c "$checksum_file")
  elif command -v sha256sum >/dev/null 2>&1; then
    (cd "$checksum_root" && sha256sum -c "$checksum_file")
  else
    printf '%s\n' 'Neither shasum nor sha256sum is available.' >&2
    exit 2
  fi
}

run_py() {
  python3 "$@"
}

cd "$package_root"

check_hashes "$script_dir/SHA256SUMS" "$script_dir"
check_hashes "$script_dir/RELEASE_ASSET_SHA256SUMS" "$assets_dir"

for archive in \
  erdos-617-r9-p93-d10-reduced-shard-0-of-4-20260721.tar.zst \
  erdos-617-r9-p93-d10-reduced-shard-1-of-4-20260721.tar.zst \
  erdos-617-r9-p93-d10-reduced-shard-2-of-4-20260721.tar.zst \
  erdos-617-r9-p93-d10-reduced-shard-3-of-4-20260721.tar.zst
do
  zstd -dc "$assets_dir/$archive" | tar -xf - -C "$tmp_dir"
done

set -- \
  "$tmp_dir/erdos-617-r9-p93-d10-reduced-shard-0-of-4-20260721" \
  "$tmp_dir/erdos-617-r9-p93-d10-reduced-shard-1-of-4-20260721" \
  "$tmp_dir/erdos-617-r9-p93-d10-reduced-shard-2-of-4-20260721" \
  "$tmp_dir/erdos-617-r9-p93-d10-reduced-shard-3-of-4-20260721"

run_py "$proof_dir/verify_r9_p93_order26_m64_manifest.py"
run_py "$proof_dir/verify_r9_p93_order26_uniform_m58_m64_core.py"
run_py "$proof_dir/verify_r9_p93_order26_d8_two_row.py" \
  --geng "$geng" --allow-unpinned
run_py "$proof_dir/verify_r9_p93_d10_core_degree_sum.py" \
  --geng "$geng" --allow-unpinned

if command -v shasum >/dev/null 2>&1; then
  geng_sha=$(shasum -a 256 "$geng" | awk '{print $1}')
else
  geng_sha=$(sha256sum "$geng" | awk '{print $1}')
fi
if [ "$geng_sha" = "3ca950af2145c546f9f586cf960eaf98f88fc3920564338f8306b6f58d018af5" ]; then
  d10_verifier="$proof_dir/verify_r9_p93_d10_certificate.py"
  printf '%s\n' 'order27_geng_identity=PINNED_BINARY'
else
  d10_verifier="$proof_dir/verify_r9_p93_d10_certificate_portable.py"
  printf '%s\n' 'order27_geng_identity=PORTABLE_CATALOG_RECONSTRUCTION'
fi

run_py "$d10_verifier" \
  --geng "$geng" \
  --package "$1" --package "$2" --package "$3" --package "$4" \
  --lrat-check "$lrat_check" \
  --require-degree-sum-survivors \
  --require-lrat
run_py "$proof_dir/test_r9_p93_d10_certificate_corruptions.py" \
  --package "$1" --package "$2" --package "$3" --package "$4" \
  --lrat-check "$lrat_check"

run_py -m pytest -q -p no:cacheprovider \
  "$proof_dir/test_r9_p93_order26_m62_package.py" \
  "$proof_dir/test_r9_p93_order26_m63_package.py" \
  "$proof_dir/test_r9_p93_order26_m64_package.py"

if [ "$mode" = "proof" ] || [ "$mode" = "audit" ]; then
  run_py "$proof_dir/verify_r9_p93_order26_m56_m57_shells.py" --geng "$geng"
  run_py "$proof_dir/verify_r9_p93_order26_m57_k2k.py" --geng "$geng"

  for level in 58 59 60 61 62 63 64
  do
    run_py "$proof_dir/verify_r9_p93_order26_m${level}_duals.py" \
      --geng "$geng" \
      --certificates "$proof_dir/r9_p93_order26_m${level}_duals.jsonl"
  done

  run_py "$proof_dir/verify_r9_p93_order26_m58_qstates.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m59_p1_qstate_verifier.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m60_p1_exceptional_shell_verifier.py" \
    --geng "$geng"
  run_py "$proof_dir/r9_p93_order26_m60_p1_qstate_verifier.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m61_scalar_side_verifier.py" --geng "$geng"
  run_py "$proof_dir/r9_p93_order26_m61_p1_qstate_verifier.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m62_scalar_side_verifier.py" --geng "$geng"
  run_py "$proof_dir/r9_p93_order26_m62_p1_orbit_verifier.py" --self-test
  run_py "$proof_dir/r9_p93_order26_m62_p1_orbit_verifier.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m63_scalar_side_verifier.py" \
    --geng "$geng"
  run_py "$proof_dir/r9_p93_order26_m63_p1_orbit_verifier.py" --self-test
  run_py "$proof_dir/r9_p93_order26_m63_p1_orbit_verifier.py" \
    --geng "$geng" --workers "$workers"
  run_py "$proof_dir/r9_p93_order26_m64_scalar_side_verifier.py" \
    --geng "$geng"
  run_py "$proof_dir/r9_p93_order26_m64_tau3_verifier.py"
  run_py "$proof_dir/r9_p93_order26_m64_p1_orbit_verifier.py" --self-test
  run_py "$proof_dir/r9_p93_order26_m64_p1_orbit_verifier.py" \
    --geng "$geng" --workers "$workers"
fi

if [ "$mode" = "audit" ]; then
  run_py "$proof_dir/audit_r9_p93_order26_m58_qstates_z3.py" \
    --geng "$geng" --workers "$workers"
  for level in 59 60 61 62 63
  do
    run_py "$proof_dir/r9_p93_order26_m${level}_p1_qstate_z3_audit.py" \
      --geng "$geng" --workers "$workers"
  done
  run_py "$proof_dir/r9_p93_order26_m64_cadical_audit.py" \
    --geng "$geng" --workers "$workers"
fi

run_py "$proof_dir/verify_r9_d8_full_color_bridge.py"
run_py "$proof_dir/verify_colored_core_ladder.py"

printf '%s\n' "fixed_r9_${mode}_replay=VERIFIED"
