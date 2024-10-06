import subprocess
import csv
program_list = """ base64 basename cat chcon chgrp chmod chown chroot comm cp csplit cut
date dd df dirname du echo env expand expr factor false fmt fold ginstall head hostid
id join kill link ln logname ls md5sum mkdir mkfifo mknod mktemp mv nice nl nohup od paste pathchk
pinky pr printenv printf ptx pwd readlink rm rmdir runcon seq shuf split stat stty
sum sync tac tail tee touch tr tsort tty uname unexpand uniq unlink uptime users who whoami pwd tr
""".split()
output_dict = {}
for program in program_list:
    print(f"====> {program}")
    command = f"./collect_cov.sh {program}"
    try:
        result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output_lines = result.stdout.decode('utf-8').split('\n')
        print(output_lines)
        output_dict[program] = output_lines[1:3]
    except subprocess.CalledProcessError as e:
        output_dict[program] = ["Error occurred", str(e)]
    except Exception as e:
        output_dict[program] = ["Exception occurred", str(e)]
# Write the collected data to a CSV file
with open('program_output.csv', 'w', newline='') as csvfile:
    fieldnames = ['program', 'line_cov', 'branch_cov']
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()
    for program, lines in output_dict.items():
        # Ensure there are at least three elements in lines
        while len(lines) < 3:
            lines.append("")
        writer.writerow({'program': program, 'line_cov': lines[0], 'branch_cov': lines[1] if len(lines) > 1 else ''})
