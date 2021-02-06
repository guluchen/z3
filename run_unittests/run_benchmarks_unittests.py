import os, sys
from to_be_imported import from_file_to_data_row
os.system('mkdir statistics')

for dirPath, dirNames, fileNames in os.walk('./benchmarks_unittests'):
    if dirPath.startswith('./benchmarks_unittests/'):
        with open(f"statistics/unittests_{dirPath.split('/')[-1]}.csv", 'w', buffering=1) as f:
            f.write('filename,z3-time,z3-res,cvc4-time,cvc4-res,trau-time,trau-res,trau-msg,final\n')
            for file in fileNames:
                file = os.path.join(dirPath, file)
                result_list = from_file_to_data_row(file)
                f.write(','.join(result_list) + '\n')

