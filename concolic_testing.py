import os
import subprocess
from subprocess import Popen, PIPE, STDOUT
from pdb import set_trace as breakpoint
import re
import os, glob
import sys
import random
import shutil
from shutil import copyfile

linevalue=[]
parameterLines=[]
modulevariables=[]
modulevariable = ''
modulevariablebracs = ''
submodulevar = ''
submodulevars=[]
wiremodules=[]
wiremodules1=[]
parameterVariables = []
parameterValues = []
addParameter = False
outputvars = []
regvars = []
regvarsnobracks = []
regvarsvalbracs = []
outputvarsnobracks = []
linestoadd = []
filestoadd = []
index = 0

flpath1 = 'RTL/All_RTL/'
with open(flpath1 + "RTLFiles.txt") as fl:
        
        moduleline = fl.readlines()
        fl.close()

for index, i in enumerate(moduleline):
    modulenumber = index+ 1

for i in range(modulenumber):
    file2 = "RTLFiles_" + str(i) + ".txt"

with open(flpath1 + file2) as fl:
    for block in fl:
        if '.v' in block or '.sv' in block:
            Connection = 0
            with open(flpath1 + block.replace('\n','')) as fl1: 
                Lines = fl1.readlines()


for index4, line in enumerate(Lines):

    line = line.replace('`','')

    if '//' in line:

        line1 = line.split('//')
        line = line1[0]
        
    
    if '/*' in line and '*/' not in line:
        nexline = Lines[index4]
        

        while '*/' not in nexline:
            
            index = index + 1
            nexline = Lines[index]
        

        if '*/' in nexline:
            
            index = index + 1

    
    
    if index4<index :
        continue
    nex=0
    if ';' not in line and '`define' not in line and 'end ' not in line and 'end\n' not in line and 'begin ' not in line and 'always' not in line and 'initial ' not in line and '\n'!=line and ''!=line and (((nex+index4)<=(len(Lines)-2)) or (('assign' in line and '=' in line) or '<=' in line)):
        if '//' in line:
            line1 = line.split('//')
            line = line1[0]
        nex = 1
        nexline = Lines[index4+nex]
        if nexline=='\n':
            nexline.replace('\n','')
        
        
        if '\n'==nexline or ' '==nexline:
            nexline.replace('\n','').replace(' ','')

        while ';' not in nexline and 'end' not in nexline and '\n'!=nexline and ((nex+index4)<=(len(Lines)-2)) and ('output ' not in nexline and 'wire ' not in nexline and 'input ' not in nexline and 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')): 
            
            
            if '//' in nexline:
                line1 = nexline.split('//')
                nexline = line1[0]
            else:
                
                nexline = nexline.replace('\n','')
            line = line + nexline.replace('\n','')
            ()
            nex = nex + 1
            
            nexline = Lines[index4+nex]
            
            if '//' in nexline:
                nexline = nexline.split('//')[0]
        if ';' in nexline and 'end' not in nexline and '\n'!=nexline and ((nex+index4)<=(len(Lines)-2)) and ('output ' not in nexline or 'wire ' not in nexline or 'input ' not in nexline or 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')):  
            if '//' in nexline:
                line1 = nexline.split('//')
                line = line+line1[0]
            else:
                line = line+nexline.replace('\n','')
        
        index = nex+index4

    
    if 'end' not in line or '`define' not in line:
        if 'parameter' in line:
            line.replace('\n','').replace('\t',' ').replace(';','')
        else:
            line = (line.replace('\n','').replace('\t','').replace(';',''))
     

    if 'wire' in line and 'input' not in line and 'output' not in line and '[' in line and ']' in line:
        
        start = line.find("[") + len("[")
        end = line.find("]")
        substring = line[start-1:end+1]
        
        start = line.find("]") + len("]")
        substringvals = line[start:]
        substringvals = substringvals.replace(',','')
        linevalue = substringvals.split()
        
        modulevariable = ''
        modulevariablebracs = ''
        for n,variable in enumerate(linevalue):
            
            if(len(variable)>0):
                modulevariable = substring + ' ' + variable.replace(',','')
                wiremodules1.append(variable.replace(',',''))
            wiremodules.append(modulevariable)
                        

    if 'wire ' in line and '[' not in line and ']' not in line and 'input' not in line and 'output' not in line:
        
        linevalue = line.split()
        addWire = True
        if linevalue[0] != 'wire':
            addWire = False
        for n,variable in enumerate(linevalue):
            if addWire:
                if n==0:
                    pass
                else:
                    if '[' not in variable and ']' not in variable:
                        if(len(variable)>0) and variable not in modulevariables:
                            wiremodules.append(variable.replace(',',''))
                            wiremodules1.append(variable.replace(',',''))
    
    if 'reg ' in line and '=' not in line and '<=' not in line and '||' not in line and '&&' not in line and '^' not in line and 'output ' not in line and 'input ' not in line:
        
        if '//' in line:
            line = line.split('//')[0]
        
        if '[' not in line and ']' not in line and 'output ' not in line and 'input ' not in line:
            
            linevalue = line.split()
            for n,variable in enumerate(linevalue):
                if n==0:
                    pass
                else:
                    if '[' not in variable and ']' not in variable and variable not in regvars:
                        
                        if(len(variable)>0):
                            
                            regvars.append(variable.replace(',',''))
                    
                            regvarsvalbracs.append('out_' + variable.replace(',',''))
                            regvarsnobracks.append('out_'+ variable.replace(',',''))

        if '[' in line and ']' in line and 'output ' not in line and 'input ' not in line:
            
            start = line.find("[") + len("[")
            end = line.find("]")
            substring = line[start-1:end+1]
            
            start = line.find("]") + len("]")
            substringvals = line[start:]
            substringvals = substringvals.replace(',','')
            linevalue = substringvals.split()
            modulevariable = ''
            modulevariablebracs = ''
            for n,variable in enumerate(linevalue):
        
                if(len(variable)>0):
                    
                    modulevariablebracs = substring + ' out_'+ variable.replace(',','')
                    
                    modulevariable = substring + ' ' + variable.replace(',','')
                    
                    regvarsnobracks.append('out_'+variable.replace(',',''))
                    
                regvars.append(modulevariable)
                regvarsvalbracs.append(modulevariablebracs)

    if '//' in line:
        temp1 = line.split('//')
        line=temp1[0]

    if 'parameter' in line or '`define' in line:
        
        addParameter = True
        parameterLines.append(line.replace('\n',''))
   
    if 'input ' in line and '[' in line and ']' in line:
        
        start = line.find("[") + len("[")
        end = line.find("]")
        substring = line[start-1:end+1]
        start = line.find("]") + len("]")
        substringvals = line[start:]
        substringvals = substringvals.replace(',','')
        linevalue = substringvals.split()
        
        modulevariable = ''
        modulevariablebracs = ''
        for n,variable in enumerate(linevalue):

            if(len(variable)>0):
                modulevariable = substring + ' ' + variable.replace(',','')
                submodulevars.append(variable.replace(',',''))
                
            modulevariables.append(modulevariable)
    
    if 'input ' in line and '[' not in line and ']' not in line and ('wire' not in line and 'reg' not in line):
        
        linevalue = line.split()
        for n,variable in enumerate(linevalue):
            if n==0:
                pass
            else:
                if '[' not in variable and ']' not in variable:
                    if(len(variable)>0) and variable not in modulevariables:
                        modulevariables.append(variable.replace(',',''))
                        submodulevars.append(variable.replace(',',''))

    if ('wire ' in line or 'reg ' in line) and '[' not in line and ']' not in line and 'input' in line:
        
        linevalue = line.split()
        for n,variable in enumerate(linevalue):
            if n==0 or n==1:
                pass
            else:
                if '[' not in variable and ']' not in variable:
                    
                    if(len(variable)>0) and variable not in modulevariables:
                        modulevariables.append(variable.replace(',',''))
                        submodulevars.append(variable.replace(',',''))
        

    if '' == line:
        
        pass

    if ('wire ' in line or 'reg ' in line) and '[' not in line and ']' not in line and 'output' in line:
        
        linevalue = line.split()
        for n,variable in enumerate(linevalue):
            if n==0 or n==1:
                pass
            else:
                if '[' not in variable and ']' not in variable:
                    if(len(variable)>0):
                        outputvars.append(variable.replace(',',''))
        
        outputvarsnobracks.append(linevalue[len(linevalue)-1].replace(',',''))

    if ('wire ' not in line and 'reg ' not in line) and '[' not in line and ']' not in line and 'output' in line:
        
        linevalue = line.split()
        for n,variable in enumerate(linevalue):
            if n==0:
                pass
            else:
                if '[' not in variable and ']' not in variable:
                    if(len(variable)>0):
                        outputvars.append(variable.replace(',',''))
        
        outputvarsnobracks.append(linevalue[len(linevalue)-1].replace(',',''))

    if '[' in line and ']' in line and 'output' in line:
        
        start = line.find("[") + len("[")
        end = line.find("]")
        substring = line[start-1:end+1]
        
        start = line.find("]") + len("]")
        substringvals = line[start:]
        substringvals = substringvals.replace(',','')
        linevalue = substringvals.split()
        
        modulevariable = ''
        modulevariablebracs = ''
        for n,variable in enumerate(linevalue):

            if(len(variable)>0):
                modulevariable = substring + ' ' + variable.replace(',','')
                outputvarsnobracks.append(variable.replace(',',''))
                
            outputvars.append(modulevariable)
 
for line in parameterLines:
    parameterLine = line.split()
    
    parameterVariables.append(parameterLine[1])
    parameterValues.append(parameterLine[3].replace(';',''))


index4 = 0

for index, line in enumerate(Lines):
    
    if index != (len(Lines)-1):
        nextLine = Lines[index + 1]
    
    if '//' in line:
        temp1 = line.split('//')
        line=temp1[0]
    
    if index4>index :
        
        continue
    
    nex=0

    if ';' not in line and 'end ' not in line and 'begin ' not in line and 'always' not in line and 'initial ' not in line and '\n'!=line and ''!=line and (((nex+index)<=(len(Lines)-2)) or (('assign' in line and '=' in line) or '<=' in line)):
        if '//' in line:
            line1 = line.split('//')
            line = line1[0]
        nex = 1
        nexline = Lines[index+nex]
        if nexline=='\n':
            nexline.replace('\n','')
        
        if '\n'==nexline or ' '==nexline:
            nexline.replace('\n','').replace(' ','')
        
        while ';' not in nexline and 'end' not in nexline and '\n'!=nexline and ((nex+index)<=(len(Lines)-2)) and ('output ' not in nexline and 'wire ' not in nexline and 'input ' not in nexline and 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')): 
            
            if '//' in nexline:
                line1 = nexline.split('//')
                line = line1[0]
            else:
                
                nexline = nexline.replace('\n','')
            line = line + nexline.replace('\n','')
            
            nex = nex + 1
            
            nexline = Lines[index+nex].replace('\n','')
            if '\n'==nexline or ' '==nexline:
                
                nexline.replace('\n','').replace(' ','')
                
            if '//' in line:
                nexline = nexline.split('//')[0]
        if ';' in nexline and 'end' not in nexline and '\n'!=nexline and ((nex+index)<=(len(Lines)-2)) and ('output ' not in nexline or 'wire ' not in nexline or 'input ' not in nexline or 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')):  
            if '//' in nexline:
                line1 = nexline.split('//')
                line = line+line1[0]
            else:
                line = line+nexline.replace('\n','')
        
        index4 = nex+index
    
    if '.' in line and '(' in line and ',' in line and ');' not in line :
        
        if ');' in Lines[index4]:
            line = line+Lines[index4].replace('\n','')
            index4 = index4+1
            

    if '(' in line and '.' in line and ',' in line and ');' in line:

        
        temp = line.replace(';','').replace('.','').replace('(','',1)
        temp1 = temp.split(',')
        for i in temp1:
            start = i.find("(") + len("(")
            end = i.find(")")
            substring = i[start:end]

            
            if(len(substring)>0) and substring not in modulevariables and substring not in submodulevars and substring not in regvars:
                if substring in wiremodules1:
                    
                    submodulevars.append(substring)
                    modulevariables.append(wiremodules[wiremodules1.index(substring)])
                

    if 'endmodule' in line:
        break
    
linevalue=[]
index4 = 0
for index, line in enumerate(Lines):
    
    if '//' in line:
        line = line.split('//')[0] + '\n'

    if index4>index:
        continue
    
    n = 1

    if line=='\n':
        line = line.replace('\n','')

    while (line=='' and Lines[index-1]=='' and Lines[index+1]=='') or (line=='\n' and Lines[index-1]=='\n' and Lines[index+1]=='\n'):
        
        line = line,replace('','') + Lines[index+n]
        n = n+1
        index4 = n+index+1
        

    if '//' in line:

        line1 = line.split('//')
        line = line1[0]
        
    
    
    nex=0

    if '/*' in line and '*/' not in line:
        
        nex = 1
        nexline = Lines[index+nex]
        if nexline=='\n':
            nexline.replace('\n','')
        
        
        while '*/' not in nexline: 
            
            
            
                
            nexline = nexline.replace('\n','')
            line = line + nexline.replace('\n','')
            ()
            nex = nex + 1
            
            nexline = Lines[index+nex]
            
            
        
        if '*/' in nexline:  
            line = line+nexline.replace('\n','')
        
        index4 = nex+index+1
        

    if index4>index :
            
        continue

    
    nex=0

    

    if 'include ' in line and '.' in line:
        
        filestoadd.append(line)

    if ';' not in line and 'end ' not in line and 'begin ' not in line and 'begin\n' not in line and 'if ' not in line and 'if(' not in line and 'case ' not in line and 'case(' not in line and 'else ' not in line and 'always' not in line and 'initial ' not in line and '\n'!=line and ''!=line and (((nex+index)<=(len(Lines)-2)) or (('assign' in line or '=' in line) or '<=' in line)):
        
        if '//' in line:
            line1 = line.split('//')
            line = line1[0]
        nex = 1
        nexline = Lines[index+nex]
        whiletrue = False
        
        
        while ';' not in nexline and 'end' not in nexline and 'begin' not in nexline and 'if' not in nexline and 'else' not in nexline and 'always' not in nexline and 'initial' not in nexline and '\n'!=nexline and ((nex+index)<=(len(Lines)-2)) and ('output ' not in nexline and 'wire ' not in nexline and 'input ' not in nexline and 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')): 
            
            
            if '//' in nexline:
                line1 = nexline.split('//')
                nexline = line1[0]
            else:
                
                nexline = nexline.replace('\n','')
            line = line + nexline.replace('\n','')
            ()
            nex = nex + 1
            
            nexline = Lines[index+nex].replace('\n','')
            if '\n'==nexline or ' '==nexline:
                
                nexline.replace('\n','').replace(' ','')
            
            if '//' in line:
                nexline = nexline.split('//')[0]
            whiletrue = True
        
        if ';' in nexline and 'end' not in nexline and 'begin' not in nexline and 'if' not in nexline and 'else' not in nexline and 'always' not in nexline and 'initial' not in nexline and '\n'!=nexline and ((nex+index)<=(len(Lines)-2)) and ('output ' not in nexline or 'wire ' not in nexline or 'input ' not in nexline or 'reg ' not in nexline) and (');'!=nexline.replace(' ','').replace('\n','').replace('\t','')) and whiletrue==True:  
            if '//' in nexline:
                line1 = nexline.split('//')
                line = line+line1[0]
            else:
                line = line+nexline.replace('\n','')
            
            nex = nex + 1
        line = line+'\n'
        
        index4 = nex+index
    
    if '.' in line and '(' in line and ',' in line and ');' not in line :
        
        if ');' in Lines[index4]:
            line = line+Lines[index4].replace('\n','')
            index4 = index4+1
            
    
    if '.' in line and '(' in line and ',' in line and ');' in line :
        
        continue
    
    if 'end\n' in line:
        line = line.replace('end\n','end\n\n')
        

    if 'include ' not in line and '`define' not in line:
        
        line = (line.replace('`',''))

    for index,i in enumerate(parameterVariables):
        if i in line and 'parameter' not in line and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

            
            line = line.replace(i,parameterValues[index])
    

    if ('reg ' in line or 'input' in line or 'output ' in line or 'wire ' in line) and ('=' not in line and '<=' not in line and '==' not in line) :
        pass
    
    elif 'parameter ' in line or '`define' in line or 'endmodule' in line or '`include' in line:
        pass
    
    elif 'module ' in line and 'endmodule' not in line:
        
        index4 = index
        while ');' not in Lines[index4]:
            
            index4 = index4 + 1
            pass
        if ');' in Lines[index4]:
            
            index4 = index4 + 1
            
            pass

        if(index4 < len(Lines)-1):
            index = index4
        

    

    else:
        linestoadd.append(line)

inputvals = []
inputvariables = []
index4 = 0
inputnode = ''


with open(r"C:\\rtlContest\RTL-CFG\inputvals.txt", "r") as f:
        
        for line in f:
            
            line = line.replace('\n','')
            inputvals.append(line)
            inputvariables.append(line.split()[0])

with open(r"C:\\rtlContest\RTL-CFG\inputnode.txt", "r") as f:
        
        for line in f:
            line = line.replace('\n','')
            if 'out_'+line.split()[0] in regvarsnobracks:
                inputnode = inputnode + 'out_' + line.split()[0] + '!=' + line.split()[1]
            else:
                inputnode = inputnode + line.split()[0] + '!=' + line.split()[1]

with open('C://iverilog/template_module.v', 'w') as f:
    
    f.write("module template_module(\n")
    
    for n,item in enumerate(submodulevars):
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
    
        if(n!=len(submodulevars)-1):
            f.write('\t%s, \n' % item)
        if(n==len(submodulevars)-1):
            f.write('\t%s, \n' % item)
    for index,reg in enumerate(regvarsnobracks):
        
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
    
        if(n!=len(regvarsnobracks)-1):
            f.write('\t'+reg+', \n')
        if(n==len(regvarsnobracks)-1):
            f.write('\t'+reg+',\n')
    for index,reg in enumerate(outputvarsnobracks):
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
        if(n!=len(outputvarsnobracks)-1):
            f.write('\t'+reg+', \n')
        if(n==(len(outputvarsnobracks)-1)):
            f.write('\t'+reg+'\n')
    f.write(');\n')
    
    
    if addParameter == True:
        
        for n,item in enumerate(parameterLines):
            
            f.write('\t%s; \n' % item)
    
    
    for item in modulevariables:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        f.write("\n\tinput %s;\n" % item)
    for item in outputvars:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        
        f.write("\toutput %s;\n" %item)
    for item in regvarsvalbracs:
        
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        
        f.write("\toutput %s;\n" %item)
    for item in regvars:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        
        f.write("\treg %s;\n" %item)
    for item in wiremodules:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        if item not in modulevariables:
        
            f.write("\twire %s;\n" %item)
    f.write('\tinteger fd;\n\tinitial begin\n\t\tfd = $fopen("out_test.txt", "w");\n\tend\n')
    f.write('\talways @(*) begin\n\t\t$fwrite(fd, "\\ntime = %t\\n", $time);\n')
    
    for reg in submodulevars:
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
        f.write('\n\t\t$fwrite(fd, \"'+reg+' = %h\\n\",'+ reg + ');\n')
    for reg in outputvarsnobracks:
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
        f.write('\n\t\t$fwrite(fd, \"'+reg+' = %h\\n\",'+ reg + ');\n')
    for reg in regvarsnobracks:
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
        f.write('\n\t\t$fwrite(fd, \"'+reg+' = %h\\n\",'+ reg + ');\n')
    f.write('\tend\n')

    for index, line in enumerate(linestoadd):
        f.write(line)

    for reg in regvarsnobracks:
        for index,i in enumerate(parameterVariables):
            if i in reg and 'parameter' not in reg and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                reg = reg.replace(i,parameterValues[index])
        regnoout = reg.replace('out_','')
        
        f.write('\n\tassign '+reg+ ' = '+regnoout+';')
    f.write('\nendmodule')    

reverselistkeys = []
reverselistvals = []
reverseinputkeys = []
reverseinputvals = []
reverseinputvalslist = []
reverseinputkeyslist = []

# Append the clock signals to the list togglevariables

togglevariables = ['clk']

with open('C://iverilog/template_testbench.v', 'w') as f:
    
    f.write("module template_testbench;\n")
    
    for item in modulevariables:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        f.write("\treg %s;\n" % item)
    
    for item in outputvars:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        f.write("\twire %s;\n" %item)
    
    for item in regvarsvalbracs:
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        f.write("\twire %s;\n" %item)
    
    f.write("\treg [4:0] i;\n")

    if addParameter == True:
        
        for n,item in enumerate(parameterLines):
            
            f.write('\t%s; \n' % item)
    

    f.write("\ttemplate_module uut (\n")
    
    for ind,item in enumerate(submodulevars):
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        if ind == len(submodulevars)-1:
            f.write("\t\t.%s(%s),\n" % (item,item))
        else:
            f.write("\t\t.%s(%s),\n" % (item,item))
    
    for ind,item in enumerate(regvarsnobracks):
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        if ind == len(regvarsnobracks)-1:
            f.write("\t\t.%s(%s),\n" % (item,item))
        else:
            f.write("\t\t.%s(%s),\n" % (item,item))
    
    for ind,item in enumerate(outputvarsnobracks):
        for index,i in enumerate(parameterVariables):
            if i in item and 'parameter' not in item and "'h" not in parameterValues[index] and "'b" not in parameterValues[index]:

                
                item = item.replace(i,parameterValues[index])
        if ind == len(outputvarsnobracks)-1:
            f.write("\t\t.%s(%s)\n" % (item,item))
        else:
            f.write("\t\t.%s(%s),\n" % (item,item))
    
    f.write("\t);\n")
    f.write('\tinitial\n\t\tbegin\n\t\t\t$dumpfile("iremodule.vcd");\n\t\t\t$dumpvars ;')
     
    
    
    for line in inputvals:
        
        linelist = line.split()
        reverselistkeys.append(linelist[0])
        reverselistvals.append(linelist[1])
    

    for i in reversed(reverselistkeys):
        reverseinputkeys.append(i)
    
    for i in reversed(reverselistvals):
        reverseinputvals.append(i)
    for index,i in enumerate(reverseinputvals):
        if i=='0!':
            reverseinputvals[index] = '1'
            
        elif i=='1!':
            reverseinputvals[index] = '0'
            
    reverseinputkeyslist = list(set(reverseinputkeys))
    
    reverselistkeys = []
    reverselistvals = []
    for i in reverseinputkeyslist:
        if i in submodulevars :
            reverselistkeys.append(i)
            
    for i in reverselistkeys:
        
        reverselistvals.append(reverseinputvals[reverseinputkeys.index(i)])

    for index,i in enumerate(reverselistvals):
        
        if i=='0!':
            reverselistvals[index] = '1'
            
        elif i=='1!':
            reverselistvals[index] = '0'
            
    
    for index, i in enumerate(reverselistkeys):
        f.write("\n\t\t\t%s = %s;" % (reverselistkeys[index], reverselistvals[index]))
    
    for line in modulevariables:
        
        if '[' in line and ']' in line and ':' in line:
            
            multipleline = line.split(']')
            line = multipleline[1].replace(' ','')
                
            linevals = multipleline[0].split(':')
            lineval = int(linevals[0].replace('[','').replace(']','').replace(':','')) - int(linevals[1].replace('[','').replace(']','').replace(':','')) + 1
                
            val = ''
            val = val+'0' 
             
            if line not in inputvariables:
                f.write("\n\t\t\t%s = %d'b%s;" % (line, lineval, val))
            
        else:
            if line not in inputvariables:
                    
                f.write("\n\t\t\t%s = 1'b0;" % line)

    f.write("\n\t\t\t#10;\n\t\t\twhile("+ inputnode +") begin\n")

    for line in modulevariables:

        if '[' in line and ']' in line and ':' in line:
            
            multipleline = line.split(']')
            line = multipleline[1].replace(' ','')
            linevals = multipleline[0].split(':')
            lineval = int(linevals[0].replace('[','').replace(']','').replace(':','')) - int(linevals[1].replace('[','').replace(']','').replace(':','')) + 1
            
            val = ''
            val = val+'0' 
             
            if line not in inputvariables:
                f.write("\n\t\t\t\t%s = %d'b%s;" % (line, lineval, val))
            
        elif line not in inputvariables or line in togglevariables :
                    
            pass

        elif line in inputvariables and line not in togglevariables:
            
            if line in reverseinputkeys:
                
                ind = reverseinputkeys.index(line, reverseinputkeys.index(line)+1)
                
                
                f.write("\n\t\t\t\t%s = %s;" % (line, reverseinputvals[ind]))
        
    f.write("\n\t\t\t\t#10;")
  
    f.write("\n\t\t\tend\n\t\t\t$finish; \n")
    f.write("\n\t\tend \n")
    f.write("\n\talways \n\t\tbegin ")
    for line in togglevariables:
        f.write("\n\t\t\t#5 %s = !%s;" %(line, line))
    f.write("\n\t\tend")
    f.write('\nendmodule')

proc = subprocess.Popen(['cmd', '/k', 'cd', 'C://iverilog', '&&', 'iverilog', '-o', 'dsn', 'template_testbench.v', 'template_module.v', '&&', 'vvp', 'dsn'])
