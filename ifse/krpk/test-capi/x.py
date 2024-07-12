#!/usr/bin/env python3

from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import logging
import sys
import os

class colors:
    OKGREEN = '\033[92m'
    ENDC = '\033[0m'

current_dir = Path(__file__).resolve().parent
project_dir = current_dir.parent

USE_ASAN = False

subprocess.run(
    ['cargo', 'build'], 
    cwd=project_dir, 
    check=True,
    env= os.environ | ({
        'RUSTFLAGS': '-Zsanitizer=address',
    }  if USE_ASAN else {})
)

artifact_dir = project_dir / 'target' / 'debug'

cpp_file = current_dir / 'driver.cpp'

with TemporaryDirectory() as test_working_dir:
    subprocess.run(
        ['make'],
        cwd=str(current_dir),
        env=os.environ | {
            'TEST_WORKING_DIR': test_working_dir.removesuffix('/'),
            'CXX': '/usr/bin/clang++',
            'CXXFLAGS': '-g' + ' -std=c++17 -I' + str(project_dir / 'include') + ' -I' + str(current_dir) + (' -fsanitize=address' if USE_ASAN else ''),
            'LDFLAGS': '-L' + str(artifact_dir) + ' -lkrpk' + (' -fsanitize=address' if USE_ASAN else ''),
            'SRC_DIR': str(current_dir).removesuffix('/'),
            'SRC_FILES': ' '.join([
                'driver.cpp',
                'KRPKBuilder.cpp',  
            ]),
        },
        check=True,
        shell=True
    )

    subprocess.run(
        [str(Path(test_working_dir) / 'test')], 
        check=True,
        env= os.environ | {
            'LD_LIBRARY_PATH': str(artifact_dir),
        },
    )

    logging.critical(f'{colors.OKGREEN}[capi_test] All tests passed!{colors.ENDC}')

sys.exit(0)
