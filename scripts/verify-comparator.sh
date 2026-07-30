#!/bin/sh
set -eu

cd "$(dirname "$0")/.."

if [ "$(uname -s)" != Linux ]; then
    printf '%s\n' "Comparator verification requires Linux and Landlock." >&2
    exit 1
fi

if [ "$(id -u)" -eq 0 ]; then
    printf '%s\n' "Comparator must run as an unprivileged user." >&2
    exit 1
fi

kernel_version=$(uname -r | sed 's/-.*//')
kernel_major=${kernel_version%%.*}
kernel_rest=${kernel_version#*.}
kernel_minor=${kernel_rest%%.*}
if [ "${kernel_major}" -lt 6 ] ||
   { [ "${kernel_major}" -eq 6 ] && [ "${kernel_minor}" -lt 7 ]; }; then
    printf '%s\n' \
      "Comparator requires Linux 6.7 or newer for Landlock network rules." >&2
    exit 1
fi

: "${COMPARATOR_BIN:?set COMPARATOR_BIN to the Comparator executable}"
: "${COMPARATOR_LANDRUN:?set COMPARATOR_LANDRUN to the landrun executable}"
: "${COMPARATOR_LEAN4EXPORT:?set COMPARATOR_LEAN4EXPORT to lean4export}"
: "${COMPARATOR_NANODA:?set COMPARATOR_NANODA to nanoda_bin}"
: "${ELAN_HOME:?set ELAN_HOME to the Lean toolchain directory}"

for executable in \
    "${COMPARATOR_BIN}" \
    "${COMPARATOR_LANDRUN}" \
    "${COMPARATOR_LEAN4EXPORT}" \
    "${COMPARATOR_NANODA}"
do
    if [ ! -x "${executable}" ]; then
        printf '%s\n' "${executable} is not executable." >&2
        exit 1
    fi
done

if [ "$(lake env lean --short-version)" != "4.32.1" ]; then
    printf '%s\n' "Comparator tools and proof must use Lean 4.32.1." >&2
    exit 1
fi

# `COMPARATOR_BIN` is expanded inside the restricted service.
# shellcheck disable=SC2016
exec systemd-run \
    --user \
    --wait \
    --pipe \
    --collect \
    --property=NoNewPrivileges=yes \
    --property=RestrictSUIDSGID=yes \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --working-directory="$(pwd)" \
    -E PATH="${PATH}" \
    -E HOME="${HOME}" \
    -E ELAN_HOME="${ELAN_HOME}" \
    -E LEAN_ABORT_ON_PANIC=1 \
    -E COMPARATOR_BIN="${COMPARATOR_BIN}" \
    -E COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN}" \
    -E COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT}" \
    -E COMPARATOR_NANODA="${COMPARATOR_NANODA}" \
    /bin/sh -c 'exec lake env "$COMPARATOR_BIN" comparator.json'
