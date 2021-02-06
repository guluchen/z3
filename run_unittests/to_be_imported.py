import subprocess

def from_file_to_data_row(file):
    print(file); result_list = [file]; ans_key = {} # since the file suffix can be .smt2 or .smt25, we don't set the filter here.
    # Note: since neither str.replaceall nor str.replace_all is supported by trau, we leave it as an error (no replacement) when solved by cvc4-1.8 and z3-4.8.9.
    ########################################
    # Section 1: ~/z3-4.8.9 (whether latest function name or not is allowed) (whether unicode representation or not is allowed)
    t = res = ''
    # p = subprocess.run(f"cat {file} | cat - <(echo ''; echo '(get-model)') |" + r"sed 's/(set-logic[^)]*)/(set-logic ALL)/g; s/(set-option[^)]*:strings-exp[^)]*)//g' |" \
    #     "time -p timeout 10 ~/z3-4.8.9 -in", shell=True, capture_output=True, executable='/bin/bash')
    # t = p.stderr.splitlines()[-3].decode('utf-8'); assert t.startswith('real '); t = t.split(' ')[1]
    # try:
    #     res = p.stdout.splitlines()[0].decode('utf-8')
    #     if not ans_key and res == 'sat':
    #         varname = ''; read_model = False
    #         for line in p.stdout.splitlines():
    #             line = line.decode('utf-8').strip()
    #             if read_model:
    #                 if line == ')': break
    #                 if not varname:
    #                     varname = line.strip().split(' ')[1]
    #                 else:
    #                     ans_key[varname] = line[:-1].strip()
    #                     varname = ''
    #             else:
    #                 if line == '(model': read_model = True
    # except: res = 'timeout' if float(t) >= 10 else 'error'
    result_list += [t, res]
    ########################################
    # Section 2: ~/cvc4-1.8-x86_64-linux-opt (only latest function name is allowed) (only unicode representation is allowed)
    t = res = ''
    # p = subprocess.run(f"cat {file} | cat - <(echo ''; echo '(get-model)') |" \
    #     r"sed 's/(set-logic[^)]*)/(set-logic ALL)/g; s/(set-option[^)]*:strings-exp[^)]*)//g; s/str\.to\.int/str.to_int/g; s/int\.to\.str/str.from_int/g; s/str\.in\.re/str.in_re/g; s/str\.to\.re/str.to_re/g; s/\\\\/\\z/g;" \
    #     r"s/\\\([[:digit:]]\)/\\u{\1}/g; s/\\x\([[:xdigit:]][[:xdigit:]]\)/\\u{\1}/g; s/\\a/\\u{7}/g; s/\\b/\\u{8}/g; s/\\f/\\u{c}/g; s/\\n/\\u{a}/g; s/\\r/\\u{d}/g; s/\\t/\\u{9}/g; s/\\v/\\u{b}/g; s/\\z/\\/g' |" \
    #     "time -p timeout 10 ~/cvc4-1.8-x86_64-linux-opt --lang=smt --strings-exp -m", shell=True, capture_output=True, executable='/bin/bash')
    # t = p.stderr.splitlines()[-3].decode('utf-8'); assert t.startswith('real '); t = t.split(' ')[1]
    # try:
    #     res = p.stdout.splitlines()[0].decode('utf-8')
    #     if not ans_key and res == 'sat':
    #         read_model = False
    #         for line in p.stdout.splitlines():
    #             line = line.decode('utf-8').strip()
    #             if read_model:
    #                 if line == ')': break
    #                 ans_key[line.strip().split(' ')[1]] = line[:-1].strip().split(' ')[-1]
    #             else:
    #                 if line == '(model': read_model = True
    # except: res = 'timeout' if float(t) >= 10 else 'error'
    result_list += [t, res]
    ########################################
    # Section 3: ~/z3/trau-not-contains-modify/z3 (latest function name is not allowed) (unicode representation is not allowed)
    # But please note that we currently don't convert unicode representation into the old one.
    # Also note that trau allows (set-logic ALL_SUPPORTED) instead of (set-logic ALL).
    t = res1 = res2 = varname = ''; read_model = False
    p = subprocess.run(f"cat {file} | cat - <(echo ''; echo '(get-model)') |" \
        r"sed 's/(set-logic[^)]*)//g; s/(set-option[^)]*:strings-exp[^)]*)//g; s/str\.to_int/str.to.int/g; s/str\.from_int/int.to.str/g; s/str\.in_re/str.in.re/g; s/str\.to_re/str.to.re/g' |" \
        "time -p timeout 10 ~/z3/trau-build/z3 smt.string_solver=trau -in", shell=True, capture_output=True, executable='/bin/bash')
        # f"time -p timeout 10 ~/z3/trau-build/z3 smt.string_solver=trau {file}", shell=True, capture_output=True, executable='/bin/bash')
    t = p.stderr.splitlines()[-3].decode('utf-8'); assert t.startswith('real '); t = t.split(' ')[1]
    try:
        for line in p.stdout.splitlines():
            line = line.decode('utf-8').strip()
            if read_model:
                if line == ')': break
                if not varname:
                    varname = line.strip().split(' ')[1]
                else:
                    ans_key[varname] = line[:-1].strip()
                    varname = ''
            elif line == 'complete-search':
                res1 = line
            elif line == 'imcomplete-search':
                res1 = line
            elif line == 'sat':
                res2 = line
            elif line == 'unsat':
                res2 = line
            elif line == 'unknown':
                res2 = line
            elif not ans_key and res2 == 'sat' and line == '(model':
                read_model = True
    except: pass
    if res2 not in ('sat', 'unsat', 'unknown') and float(t) >= 10:
        res2 = 'timeout'
    result_list += [t, res2, res1]
    ########################################
    # Section 4: If the results conflict with each other, we pick one available model and recompute it again.
    # if any(item not in ('sat', 'unsat', 'timeout', 'unknown') for item in (result_list[2], result_list[4], result_list[6])):
    #     result_list.append('error')
    # elif all(item in (result_list[2], result_list[4], result_list[6]) for item in ('sat', 'unsat')):
    #     p = subprocess.run(f"grep -Fn '(check-sat)' {file}", shell=True, capture_output=True, executable='/bin/bash')
    #     lineno = int(p.stdout.splitlines()[0].decode('utf-8').strip().split(':')[0]) # find the location to insert our model
    #     new_asserts = "".join(f"(assert (= {key} {value}))" for (key, value) in ans_key.items()) # our model in assertion form
    #     ###############################################
    #     # Section 4-1: ~/z3-4.8.9
    #     p = subprocess.run(f"cat <(cat {file} | head -{lineno-1}) <(echo '{new_asserts}') <(cat {file} | tail -n +{lineno}) |" \
    #         r"sed 's/(set-logic[^)]*)/(set-logic ALL)/g; s/(set-option[^)]*:strings-exp[^)]*)//g' | timeout 10 ~/z3-4.8.9 -in", shell=True, capture_output=True, executable='/bin/bash')
    #     try: res1 = p.stdout.splitlines()[0].decode('utf-8').strip()
    #     except: res1 = 'error'
    #     ###############################################
    #     # Section 4-2: ~/cvc4-1.8-x86_64-linux-opt
    #     p = subprocess.run(f"cat <(cat {file} | head -{lineno-1}) <(echo '{new_asserts}') <(cat {file} | tail -n +{lineno}) |" \
    #         r"sed 's/(set-logic[^)]*)/(set-logic ALL)/g; s/(set-option[^)]*:strings-exp[^)]*)//g; s/str\.to\.int/str.to_int/g; s/int\.to\.str/str.from_int/g; s/str\.in\.re/str.in_re/g; s/str\.to\.re/str.to_re/g; s/\\\\/\\z/g;" \
    #         r"s/\\\([[:digit:]]\)/\\u{\1}/g; s/\\x\([[:xdigit:]][[:xdigit:]]\)/\\u{\1}/g; s/\\a/\\u{7}/g; s/\\b/\\u{8}/g; s/\\f/\\u{c}/g; s/\\n/\\u{a}/g; s/\\r/\\u{d}/g; s/\\t/\\u{9}/g; s/\\v/\\u{b}/g; s/\\z/\\/g' |" \
    #         "timeout 10 ~/cvc4-1.8-x86_64-linux-opt --lang=smt --strings-exp", shell=True, capture_output=True, executable='/bin/bash')
    #     try: res2 = p.stdout.splitlines()[0].decode('utf-8').strip()
    #     except: res2 = 'error'
    #     ###############################################
    #     # Section 4-3: ~/z3/trau-not-contains-modify/z3
    #     p = subprocess.run(f"cat <(cat {file} | head -{lineno-1}) <(echo '{new_asserts}') <(cat {file} | tail -n +{lineno}) |" \
    #         r"sed 's/(set-logic[^)]*)//g; s/(set-option[^)]*:strings-exp[^)]*)//g; s/str\.to_int/str.to.int/g; s/str\.from_int/int.to.str/g; s/str\.in_re/str.in.re/g; s/str\.to_re/str.to.re/g' |" \
    #         "timeout 10 ~/z3/trau-build/z3 smt.string_solver=trau -in", shell=True, capture_output=True, executable='/bin/bash')
    #         # f"time -p timeout 10 ~/z3/trau-build/z3 smt.string_solver=trau {file}", shell=True, capture_output=True, executable='/bin/bash')
    #     try:
    #         res3 = p.stdout.splitlines()[0].decode('utf-8').strip(); i = 1
    #         while res3 not in ('sat', 'unsat', 'unknown'): # should not print 'timeout' here...
    #             res3 = p.stdout.splitlines()[i].decode('utf-8').strip()
    #             i += 1
    #     except: res3 = 'error'
    #     ###############################################
    #     # Section 4-4: refresh our result!
    #     if any(item not in ('sat', 'unsat', 'timeout', 'unknown') for item in (result_list[2], result_list[4], result_list[6])): result_list.append('error')
    #     elif 'sat' in (res1, res2, res3) and 'unsat' in (res1, res2, res3): result_list.append('conflict')
    #     elif 'sat' in (res1, res2, res3) and 'unsat' not in (res1, res2, res3): result_list.append('sat')
    #     elif 'unsat' in (res1, res2, res3) and 'sat' not in (res1, res2, res3): result_list.append('unsat')
    #     else: result_list.append('')
    # else:
    result_list.append('')
    return result_list
