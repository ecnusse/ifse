#!/bin/sh
# Validate cksum --algorithm operation

# Copyright (C) 2021-2023 Free Software Foundation, Inc.

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

. "${srcdir=.}/tests/init.sh"; path_prepend_ ./src
print_ver_ cksum

cat > input_options <<\EOF || framework_failure_
bsd     sum -r
sysv    sum -s
crc     cksum
md5     md5sum MODE
sha1    sha1sum MODE
sha224  sha224sum MODE
sha256  sha256sum MODE
sha384  sha384sum MODE
sha512  sha512sum MODE
blake2b b2sum MODE
EOF

while read algo prog mode; do
  for cmode in '-b' '-t'; do
    pmode="$mode"
    case $pmode in MODE) pmode=$cmode;; esac

    $prog $pmode /dev/null >> out || continue
    cksum --untagged $cmode --algorithm=$algo /dev/null > out-c || fail=1

    case "$algo" in
      bsd) ;;
      sysv) ;;
      crc) ;;
      *) cksum --check --algorithm=$algo out-c || fail=1 ;;
    esac

    cat out-c >> out-a || framework_failure_
  done
done < input_options
compare out out-a || fail=1

# Ensure --check not allowed with older (non tagged) algorithms
returns_ 1 cksum -a bsd --check </dev/null || fail=1

# Ensure abbreviations not supported for algorithm selection
returns_ 1 cksum -a sha22 </dev/null || fail=1

Exit $fail
