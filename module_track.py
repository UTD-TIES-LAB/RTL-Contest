from os import listdir
#from os import join
from pdb import set_trace as breakpoint
import re
import os, glob
import sys
import random
import shutil
from shutil import copyfile


def copyfiles(mypath, newpath, justpath, filelist, filelist1):
    for folder in justpath:
        anotherpath = newpath + folder + '/'
        onlyfiles1 = [f for f in listdir(anotherpath) if os.path.isfile(''.join([anotherpath,f]))]
        justpath1 = [f for f in listdir(anotherpath) if not os.path.isfile(''.join([anotherpath,f]))]
        print(onlyfiles1)
        print(justpath1)
        #breakpoint()
        for files in onlyfiles1:
            source = anotherpath + files
            destination = mypath + Newdir + files
            if '.v' in files or '.sv' in files:
                filelist.append(files + '\n')
                filelist1.append(files)
                shutil.copyfile(source, destination)
        copyfiles(mypath, anotherpath, justpath1, filelist, filelist1)

 


mypath = 'RTL/'
f = listdir(mypath)
print(f)


onlyfiles = [f for f in listdir(mypath) if os.path.isfile(''.join([mypath,f]))]
justpath = [f for f in listdir(mypath) if not os.path.isfile(''.join([mypath,f]))]
print(onlyfiles)
print(justpath)

#def Module_Track():
#onlyfiles1 = []
#for f in listdir(mypath):
#    if os.path.isfile(''.join([mypath,f])):
#        onlyfiles1.append(f)

#print(onlyfiles1)
#breakpoint()
Newdir = 'All_RTL/'
Newpath = os.path.join(mypath, Newdir)
os.mkdir(Newpath) 



filelist = []
filelist1 = []
copyfiles(mypath, mypath, justpath, filelist, filelist1)

#breakpoint()
fileobject = open("RTL/All_RTL/RTLFiles.txt","w+") 
fileobject.writelines(filelist)
fileobject.close()

modulelist = []
modulelist1 = []
#breakpoint()
for i, items in enumerate(filelist1):
    itempath = "RTL/All_RTL/RTLFiles_" + str(i) + ".txt"
    fileobject = open(itempath,"w+")
    fileobject.write(items)
    fileobject.close()


    with open(mypath + Newdir + items) as fl:
        #breakpoint()
        lines = fl.readlines()
        fl.close()                
    for index4,line in enumerate(lines):
        if 'module' in line and 'endmodule' not in line and 'module' == line.split()[0]:
            themodule = line.split()[1]
            themodule1 = themodule.split('(')[0]
            modulelist.append(themodule1)
            modulelist1.append(items + ' ' + themodule1)

#breakpoint()
#moduleconnection = []

fileobject = open("RTL/All_RTL/moduleconnection.txt","w+")
for i, items in enumerate(filelist1):
    modulelist2 = []
    modulelist3 = modulelist
    modulelist4 = modulelist1
    check = 0
    comment = 0
    itempath = "RTL/All_RTL/RTLFiles_" + str(i) + ".txt"
    #fileobject = open(itempath,"w")
    with open(mypath + Newdir + items) as fl:
        #breakpoint()
        lines = fl.readlines()
        fl.close()
    #fileobject.write(items + '\n')      
    for index4,line in enumerate(lines):
        linevalue = line.split()
        if 'module' in line and 'endmodule' not in line and 'module' == line.split()[0]:
            modulelist2 = []
            Assignment = []
            check = 1
            themodule = line.split()[1]
            themodule1 = themodule.split('(')[0]
            modulelist2.append(themodule1 + ' ')
            print(modulelist2)
            continue
        if 'endmodule' in line:
            check = 0
            print(modulelist2)
            moduleconnection = ''.join(modulelist2)
            ConnectionAssignment = ''.join(Assignment)
            fileobject.write(moduleconnection + '/' + ConnectionAssignment + '\n')
            #fileobject.write()
        if check == 1:
            if linevalue != []:
                if '//' in linevalue[0]:
                    continue
                if '/*' in linevalue[0]: 
                    comment = 1
                    continue
                elif '*/' in linevalue[len(linevalue)-1]:
                    comment = 0
                    continue
                if comment == 1:
                    continue
                if '.' in linevalue[0]:
                    if len(linevalue) > 1:
                        if 'rst' in linevalue[1] or 'reset' in linevalue[1]:
                            Assignment1 = linevalue[0].replace('.','') + "=" + linevalue[1].replace(',','').replace('(','').replace(')','').replace(';','') + " "
                            Assignment.append(Assignment1)
                            #breakpoint()
                    elif '*' in linevalue[0]:
                        continue
                    else:
                        linevalue1 = linevalue[0].split('(')
                        if 'rst' in linevalue1[1] or 'reset' in linevalue1[1]:
                            Assignment1 = linevalue1[0].replace('.','') + "=" + linevalue1[1].replace(',','').replace('(','').replace(')','').replace(';','') + " "
                            Assignment.append(Assignment1)
                            #breakpoint()

            for index, modules in enumerate(modulelist3):
                if modules in linevalue:
                    #breakpoint()
                    if (modules + '(') in linevalue or '(' in lines[index4 + 1] or (modules in linevalue and '(' in linevalue):
                        #breakpoint()
                        #fileobject.write(modulelist4[index].split()[0] + '\n')
                        modulelist2.append(modules + ' ')
                        #modulelist3.pop(index)
                        #modulelist4.pop(index)
                        break
#breakpoint()
#fileobject.writelines(moduleconnection)
fileobject.close()



