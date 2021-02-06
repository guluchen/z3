import csv, os, sys

if len(sys.argv) > 1:
    statsdir = sys.argv[1]
else:
    statsdir = './statistics'
print('BENCHMARK, SAT: z3, cvc4, trau, UNSAT: z3, cvc4, trau, UNSOL: z3, cvc4, trau, WA: z3, cvc4, trau, TIME: z3, cvc4, trau, ERROR, CONFLICT, *')
os.system(f'rm -r {statsdir}/answer_sat_trau_unsat/'); os.system(f'mkdir {statsdir}/answer_sat_trau_unsat/')
os.system(f'rm -r {statsdir}/answer_unsat_trau_sat/'); os.system(f'mkdir {statsdir}/answer_unsat_trau_sat/')

with open(f'{statsdir}/collect_conflicts_and_errors.txt', 'w') as ferr:
    hold = ''
    for file in sorted(os.listdir(f'{statsdir}')):
        # print(file)
        if not ((file.startswith('trauc_') or file.startswith('project_') or file.startswith('unittests_')) and file.endswith('.csv')): continue
        if hold and not file.startswith(hold):
            print(f"{hold.replace('_', '-')} ({linecnt}), {sat[0]}, {sat[1]}, {sat[2]}, {unsat[0]}, {unsat[1]}, {unsat[2]}, " \
                    #f"{linecnt-sat[0]-unsat[0]}, {linecnt-sat[1]-unsat[1]}, {linecnt-sat[2]-unsat[2]}, " \
                    f"{unknown[0]}|{timeout[0]}|{linecnt-sat[0]-unsat[0]-unknown[0]-timeout[0]}, {unknown[1]}|{timeout[1]}|{linecnt-sat[1]-unsat[1]-unknown[1]-timeout[1]}, {unknown[2]}|{timeout[2]}|{linecnt-sat[2]-unsat[2]-unknown[2]-timeout[2]}, " \
                    f"{wa[0]}, {wa[1]}, {wa[2]}, {round(time[0]/linecnt, 2)}, {round(time[1]/linecnt, 2)}, {round(time[2]/linecnt, 2)}, " \
                    f"{error}, {conflict}, {trau_special}")
            hold = ''
        if not hold:
            linecnt = 0; conflict = 0; error = 0; sat = [0, 0, 0]; unsat = [0, 0, 0]; unknown = [0, 0, 0]; timeout = [0, 0, 0]; wa = [0, 0, 0]; time = [0, 0, 0]; trau_special = 0
        readdata = csv.reader(open(os.path.join(f'{statsdir}', file), 'r'))
        start = False
        for row in readdata:
            if not start: start = True; continue
            linecnt += 1 # source csv: f.write('filename,z3-time,z3-res,cvc4-time,cvc4-res,trau-time,trau-res,trau-msg,final\n')
            for i in (1, 3, 5):
                try: float(row[i]) if row[i] != '' else 0
                except: # special handling if a -time column contains error messages from the previous column
                    row[i-1] += '|' + row[i]
                    j = i + 1
                    while True:
                        try: row[j-1] = row[j]; j += 1
                        except: break
            #if row[8] == 'conflict': row[8] = 'sat' # another way to interpret the conflict
            for i in range(3):
                myans = row[2*(i+1)]
                sat[i] += int(myans == 'sat')
                unsat[i] += int(myans == 'unsat')
                ###
                unknown[i] += int(myans == 'unknown')
                timeout[i] += int(myans == 'timeout')
                ###
                time[i] += 0 if row[2*i+1] == '' else float(row[2*i+1]) 
                this_is_wrong_answer = 0
                if '_sat' in file: this_is_wrong_answer = int(myans == 'unsat')
                elif '_unsat' in file: this_is_wrong_answer = int(myans == 'sat')
                else: this_is_wrong_answer = int(row[8] == 'sat' and myans == 'unsat' or row[8] == 'unsat' and myans == 'sat')
                wa[i] += this_is_wrong_answer
                # if this_is_wrong_answer:
                    # print(row[0])
                if i == 2 and (this_is_wrong_answer > 0 and myans == 'unsat'):
                    os.system(f'cp {row[0].replace("=","")} {statsdir}/answer_sat_trau_unsat/{row[0].replace("/","")}')
                if i == 2 and (this_is_wrong_answer > 0 and myans == 'sat'):
                    os.system(f'cp {row[0].replace("=","")} {statsdir}/answer_unsat_trau_sat/{row[0].replace("/","")}')
            if row[6] == 'unsat' and row[7] == 'imcomplete-search': trau_special += 1 # I know "imcomplete" is a spelling mistake...
            if row[8] in ('conflict', 'error'):
                if row[8] == 'conflict':
                    conflict += 1
                elif row[8] == 'error':
                    error += 1
                print(row, file=ferr)
        if not hold and (file[-6] == '_' and file[-5].isdigit() and file.endswith('.csv')): hold = file[:-6]
        if not hold:
            print(f"{file[:-4].replace('_', '-')} ({linecnt}), {sat[0]}, {sat[1]}, {sat[2]}, {unsat[0]}, {unsat[1]}, {unsat[2]}, " \
                    #f"{linecnt-sat[0]-unsat[0]}, {linecnt-sat[1]-unsat[1]}, {linecnt-sat[2]-unsat[2]}, " \
                    f"{unknown[0]}|{timeout[0]}|{linecnt-sat[0]-unsat[0]-unknown[0]-timeout[0]}, {unknown[1]}|{timeout[1]}|{linecnt-sat[1]-unsat[1]-unknown[1]-timeout[1]}, {unknown[2]}|{timeout[2]}|{linecnt-sat[2]-unsat[2]-unknown[2]-timeout[2]}, " \
                    f"{wa[0]}, {wa[1]}, {wa[2]}, {round(time[0]/linecnt, 2)}, {round(time[1]/linecnt, 2)}, {round(time[2]/linecnt, 2)}, " \
                    f"{error}, {conflict}, {trau_special}")
