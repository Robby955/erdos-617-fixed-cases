#!/bin/sh

set -eu

usage() {
  printf '%s\n' \
    "Usage: ./reproduce.sh --lrat-check PATH [--skip-sage]" \
    "" \
    "Runs the r=7 enumeration and arithmetic checks, the r=8 human" \
    "arithmetic checks, the endpoint semantic reconstruction, and all" \
    "862 LRAT replays. Sage is required unless --skip-sage is supplied."
}

lrat_check=""
skip_sage=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --lrat-check)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      lrat_check=$2
      shift 2
      ;;
    --skip-sage)
      skip_sage=1
      shift
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

[ -n "$lrat_check" ] || { usage >&2; exit 2; }
[ -x "$lrat_check" ] || {
  printf 'LRAT checker is not executable: %s\n' "$lrat_check" >&2
  exit 2
}

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/erdos617-r78.XXXXXX")
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$script_dir"

if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c SHA256SUMS
elif command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c SHA256SUMS
else
  printf '%s\n' 'Neither shasum nor sha256sum is available.' >&2
  exit 2
fi

python3 code/verify_r7_weighted_light_edge.py
if [ "$skip_sage" -eq 0 ]; then
  command -v sage >/dev/null 2>&1 || {
    printf '%s\n' 'Sage is required for the independent r=7 reconstruction.' >&2
    exit 2
  }
  sage code/verify_r7_weighted_light_edge_sage.py
else
  printf '%s\n' 'r7_sage_reconstruction=SKIPPED'
fi
python3 code/verify_r7_fixed_outer_closure.py
python3 code/verify_colored_core_ladder.py

python3 code/verify_r8_d7_full_color_bridge.py
python3 code/verify_endpoint18_certificate.py \
  --artifacts artifacts/endpoint18 \
  --lrat-check "$lrat_check"

tar -xzf \
  artifacts/r8-fixed-outer/p83-d8-cross-certificate-portable.tar.gz \
  -C "$tmp_dir"
d8_dir="$tmp_dir/p83-d8-cross-certificate-portable"
if command -v shasum >/dev/null 2>&1; then
  (cd "$d8_dir" && shasum -a 256 -c SHA256SUMS)
else
  (cd "$d8_dir" && sha256sum -c SHA256SUMS)
fi
python3 "$d8_dir/verify_p83_d8_direct_semantics.py" \
  --artifacts "$d8_dir" \
  --lrat-check "$lrat_check"

printf '%s\n' 'fixed_r7_r8_release_replay=VERIFIED'
