file1 = open(r"C:\\iverilog\out_test.txt", "r")
Lines = file1.readlines()

file2 = open(r"C:\\rtlContest\RTL-CFG\testcase.txt", "r")
cases = file2.readlines()

variables = []
values = []
for line in Lines:
    if line != '\n':
        line = line.replace('\n','').replace('\t','')
        values.append(line)
    else:
        variables.append(values)
        values = []

printvals = []
variables.append(values)
checkcase = False
caseTrue = True
verified = False
for line in cases:
    verified = False
    checkcase = False
    caseTrue = True
    testcases = line.replace('\n','').replace('\t','').replace('[','').replace(']','').split(',')
    for index, val in enumerate(variables):
        if val == []:
            continue
        for x in val:
            if testcases[0] == x:
                checkcase = True
                caseTrue = False
                break
        if checkcase == True:
            for y in val:
                if testcases[1]==y:
                    caseTrue = True
                    break
        
        if(caseTrue == True and checkcase == True):
            if ("verified " + str(testcases) + " at runtime: " + val[0].split()[2]) not in printvals:
                printvals.append("verified " + str(testcases) + " at runtime: " + val[0].split()[2])
            verified = True
            break
        
    if checkcase == False:
        if ("condition not met" + str(testcases)) not in printvals:
            printvals.append("condition not met" + str(testcases))
        
    elif verified == False:
        if ("not correct" + str(testcases)) not in printvals:
            printvals.append("not correct" + str(testcases))

for i in printvals:
    print(i)
        
        
