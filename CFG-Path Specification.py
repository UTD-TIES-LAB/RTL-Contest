from pdb import set_trace as breakpoint
from math import *
import re
import os, glob
import sys
import random
from collections import defaultdict
from wsgiref.util import guess_scheme

def EdgeRealignment(firstnode, Nodeflowx, inputnode, nestednodes):
    inputvals = []
    inputkeys = []
    nestedpath = []
    nodeavail = []
    targetnode = ''
    predecessors = []
    predecessors3 = []
    targetnode_list=[]
    targetnodes = []
    guard_condition = ''
    for node in Nodeflowx:
        if(node.split()[0].replace('n','')==firstnode and node.split()[len(node.split())-1] == '0'):
            targetnode_list.append(node)
        
    if(len(firstnode.split(','))>2):
        nextnode = firstnode.split(',')
        nestednode = '' 
        for index, values in enumerate(nextnode):
            if (index == len(nextnode)-1):
                nextnode.pop(index)
                nestednode = nestednode[:-1]
            else:
                nestednode = nestednode + str(values) + ','
        if nestednode not in nestednodes:
            nestednodes.append(nestednode)
    
    if inputnode == 1:
        if firstnode not in predecessors:
            predecessors.append(firstnode)
    targetnodesvalues = []
    if(targetnode_list != []):
        guard_condition = targetnode_list[0]
        guard_variables, guard_values, guard_cond, or1_and2_condition = ExpandGuardCondition(guard_condition)
        targetnodesval = SetofStrictValues(guard_variables, guard_values, guard_cond, Nodeflowx, or1_and2_condition)
        for targetnode in targetnodesval:
            if targetnode!=[]:
                predecessors3, nestednodes, inputvals, inputkeys = update_edge(targetnode, predecessors3, Nodeflowx, nestednodes, inputvals, inputkeys, predecessors)
                for i in predecessors3:
                    if i not in predecessors:
                        predecessors.append(i)
                    predecessors3 = []
            
            if(targetnode == []):
                vars = []
                guard_variables = []
                guard_variable = ''
                guard_values = []
                guard_cond = []
                or1_and2_condition = 0
                node = guard_condition.split()[0]
                vars = guard_condition.split()
                
                for index,i in enumerate(vars):
                    if index==0 or index==(len(vars)-1) or i=='always':
                        continue
                    else:
                        
                        guard_variable = guard_variable + ' ' + i
                if 'or' in vars or 'and'  in vars:
                    if 'or' in vars:
                        variables = guard_variable.split('or')
                        or1_and2_condition = 1
                    if 'and' in vars:
                        variables = guard_variable.split('and')
                        or1_and2_condition = 2
                    if or1_and2_condition!=1 or or1_and2_condition!=2:
                        or1_and2_condition = 0
                    
                    for i in variables:
                        
                        guard_variables.append(i.split()[0])
                        guard_cond.append(i.split()[len(i.split())-2])
                        guard_values.append(i.split()[len(i.split())-1])
                    
                else:
                    guard_variables.append(vars[1])
                    guard_values.append(vars[len(vars)-2])
                    guard_cond.append(vars[len(vars)-3])
                
                for i in range(len(guard_variables)):
                    
                    inputvals.append(guard_variables[i])
                    inputkeys.append(guard_values[i])
            
    while nestednodes != []:
        
        targetnodes = []
        targetnodes.append(nestednodes.pop(0))
        predecessors3, nestednodes, inputvals, inputkeys = update_edge(targetnodes, predecessors3, Nodeflowx, nestednodes, inputvals, inputkeys, predecessors)
        
        for i in predecessors3:
            if i not in predecessors and i!='10,0,1,2':
                predecessors.append(i)
        predecessors3 = [] 
    
    return predecessors, inputvals, inputkeys
        
def ExpandGuardCondition(guardCondition):
    vars = []
    guard_variables = []
    guard_variable = ''
    guard_values = []
    guard_cond = []
    node = guardCondition.split()[0]
    vars = guardCondition.split()
    
    for index,i in enumerate(vars):
        if index==0 or index==(len(vars)-1) or i=='always':
            continue
        else:
            guard_variable = guard_variable + ' ' + i
    variables = []
    if 'or' in vars or 'and'  in vars:
        if 'or' in vars:
            if 'always' in vars:
                variables.append(guard_variable.split('or')[0])
            else:
                variables = guard_variable.split('or')
            or1_and2_condition = 1
        if 'and' in vars:
            if 'always' in vars:
                variables.appendguard_variable.split('and')[0]
            else:
                variables = guard_variable.split('and')
            or1_and2_condition = 2
        if or1_and2_condition!=1 or or1_and2_condition!=2:
            or1_and2_condition = 0
        
        for i in variables:
            
            guard_variables.append(i.split()[0])
            guard_cond.append(i.split()[len(i.split())-2])
            guard_values.append(i.split()[len(i.split())-1])
    else:
        guard_variables.append(vars[1])
        guard_values.append(vars[len(vars)-2])
        guard_cond.append(vars[len(vars)-3])
        or1_and2_condition = 0
    return guard_variables, guard_values, guard_cond, or1_and2_condition

def SetofStrictValues(guard_variable, guard_value, guard_cond, Nodeflowx, or1_and2_condition):
    
    targetnode = []
    targetnodes = []
    fullvalue = ''
    bracketvalue = ''
    intermediate_variable1 = []
    intermediate_variable2 = []
    intermediate_node1 = []
    intermediate_node2 = []
    for ind, i in enumerate(guard_value):
        
        if i=='0!':
            guard_value[ind] = '1'
        elif i=='1!':
            guard_value[ind] = '0'
            
    for x in range(len(guard_variable)):
        targetnode = []
        fullvalue = ''
        bracketvalue = ''
        intermediate_variable1 = []
        intermediate_variable2 = []
        intermediate_node1 = []
        intermediate_node2 = []
        if '[' in guard_value[x] and ']' in guard_value[x]:
            
            start = guard_value[x].find("[") + len("[")
            end = guard_value[x].find("]")
            bracketvalue = guard_value[x][start:end]
            end = guard_value[x].find("[")
            fullvalue = guard_value[x][:end]
        for node in Nodeflowx:
            longvars = []
            longval = ''
            
            vars = node.split()
            if (len(vars))>5:
                for index, val in enumerate(vars):
                    
                    if(index == 0 or index == 1 or index == 2):
                        longvars.append(val)
                    elif index == (len(vars)-1):
                        longvars.append(longval)
                        longvars.append(val)
                    else:
                        if longval == '':
                            longval = longval + val 
                        else:
                            longval = longval + ' ' + val 
                if (isinstance(guard_value[x],int) or "'b" in guard_value[x] or "'h" in guard_value[x]) and ('!' not in guard_value[x] or '!=' not in guard_cond[x]) and '==' in vars:
                    if(guard_variable[x]==longvars[1] and guard_value[x]==longvars[3] and longvars[4] != '0'):
                        
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                elif (isinstance(guard_value[x],int) or "'b" in guard_value[x] or "'h" in guard_value[x]) and ('!' in guard_value[x] or '!=' in guard_cond[x]):
                    guard_value[x] = guard_value[x].replace('!','')
                    if(guard_variable[x]==longvars[1] and guard_value[x]!=longvars[3] and longvars[4] != '0'):
                        
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                elif isinstance(guard_value[x],str) and ('!' not in guard_value[x] or '!=' not in guard_cond[x]):
                    
                    if(guard_variable[x]==longvars[1] and longvars[4] != '0'):
                        intermediate_variable1.append(longvars[3])
                        intermediate_node1.append(node)
                        
                    if(guard_value[x]==longvars[3] and longvars[4] != '0' and '[' not in guard_value[x] and ']' not in guard_value[x])  and not(guard_value[x].isnumeric()):
                        intermediate_variable2.append(longvars[1])
                        intermediate_node2.append(node)
                        
                    if(fullvalue==longvars[1] and longvars[4] != '0' and '[' in guard_value[x] and ']' in guard_value[x]) and not(guard_value[x].isnumeric()):
                        
                        intermediate_variable2.append(longvars[1])
                        intermediate_node2.append(node)
                        
                    if(bracketvalue==longvars[1] and longvars[4] != '0' and '[' in guard_value[x] and ']' in guard_value[x]) and not(guard_value[x].isnumeric()):
                        
                        intermediate_variable2.append(longvars[1])
                        intermediate_node2.append(node)
                        
                    if(guard_value[x]==longvars[3] and vars[4] != '0' and guard_variable[x]==longvars[1]):
                            
                        targetnode.append(node.split()[0].replace('n',''))
                        break

                    if(guard_value[x]==longvars[3] and vars[4] == '0' and guard_variable[x]==longvars[1]):
                        if len(intermediate_variable2) == 0 or len(intermediate_variable1) == 0:
                            continue
                        else:
                            break
                    
                elif isinstance(guard_value[x],str) and ('!' in guard_value[x] or '!=' in guard_cond[x]):
                    guard_value[x] = guard_value[x].replace('!','')
                    if(guard_variable[x]==longvars[1] and longvars[4] != '0'):
                        intermediate_variable1.append(longvars[3])
                        intermediate_node1.append(node)
                        
                    if(guard_value[x]!=longvars[3] and longvars[4] != '0'):
                        intermediate_variable2.append(longvars[1])
                        intermediate_node2.append(node)
                        
                    if(guard_value[x]!=longvars[3] and vars[4] != '0' and guard_variable[x]==longvars[1]):
                            
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                    if((guard_value[x]+'!')==longvars[3] or (guard_value[x])==longvars[3] and '!=' in guard_cond[x]) and vars[4] == '0' and guard_variable[x]==longvars[1]:
                        break

            elif len(vars)==5:
                
                if (isinstance(guard_value[x],int) or "'b" in guard_value[x] or "'h" in guard_value[x]) and ('!' not in guard_value[x] or '!=' not in guard_cond[x]):
                    if(guard_variable[x]==vars[1] and guard_value[x]==vars[3] and vars[4] != '0'):
                            
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                
                if (isinstance(guard_value[x],int) or "'b" in guard_value[x] or "'h" in guard_value[x]) and ('!' in guard_value[x] or '!=' in guard_cond[x]):                    
                    
                    guard_value[x] = guard_value[x].replace('!','')
                    if(guard_variable[x]==vars[1] and guard_value[x]!=vars[3] and vars[4] != '0'):
                            
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                elif (isinstance(guard_value[x],str)) and ('!' not in guard_value[x] or '!=' not in guard_cond[x]):
                    
                    if(guard_variable[x]==vars[1] and vars[4] != '0'):
                        intermediate_variable1.append(vars[3])
                        intermediate_node1.append(node)
                        
                    if(guard_value[x]==vars[3] and vars[4] != '0' and '[' not in guard_value[x] and ']' not in guard_value[x]) and not(guard_value[x].isnumeric()):
                        intermediate_variable2.append(vars[1])
                        intermediate_node2.append(node)
                        
                    if(fullvalue==vars[1] and vars[4] != '0' and '[' in guard_value[x] and ']' in guard_value[x]):

                        intermediate_variable2.append(vars[1])
                        intermediate_node2.append(node)
                        

                    if(bracketvalue==vars[1] and vars[4] != '0' and '[' in guard_value[x] and ']' in guard_value[x]):
                        
                        intermediate_variable2.append(vars[1])
                        intermediate_node2.append(node)
                        
                    if(guard_value[x]==vars[3] and vars[4] != '0' and guard_variable[x]==vars[1]):
                        
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                    if(guard_value[x]==vars[3] and vars[4] == '0' and guard_variable[x]==vars[1]):
                        
                        if len(intermediate_variable2) == 0 or len(intermediate_variable1) == 0:
                            continue
                        else:
                            break
                    
                elif (isinstance(guard_value[x],str)) and ('!' in guard_value[x] or '!=' in guard_cond[x]):
                    guard_value[x] = guard_value[x].replace('!','')
                    if(guard_variable[x]==vars[1] and vars[4] != '0'):
                        intermediate_variable1.append(vars[3])
                        intermediate_node1.append(node)
                    if(guard_value[x]!=vars[3] and vars[4] != '0'):
                        intermediate_variable2.append(vars[1])
                        intermediate_node2.append(node)
                    if(guard_value[x]!=vars[3] and vars[4] != '0' and guard_variable[x]==vars[1]):
                        
                        targetnode.append(node.split()[0].replace('n',''))
                        break
                    if((guard_value[x]+'!')==vars[3] or (guard_value[x])==vars[3] and '!=' in guard_cond[x]) and vars[4] == '0' and guard_variable[x]==vars[1]:
                        
                        break
                    
            else:
                pass
        
        if targetnode != []:
            
            targetnodes.append(targetnode)
            break
        
        if len(intermediate_variable1)==1 and len(intermediate_variable2)==1:
            
            targetnode.append(intermediate_node1[0].split()[0].replace('n',''))
            targetnode.append(intermediate_node2[0].split()[0].replace('n',''))
            
        elif (len(intermediate_variable1)==0 and len(intermediate_variable2)!=0) or (len(intermediate_variable2)==0 and len(intermediate_variable1)!=0):
            
            if len(intermediate_variable2)==0:
                targetnode.append(intermediate_node1[0].split()[0].replace('n',''))
            if len(intermediate_variable1)==0:
                targetnode.append(intermediate_node2[0].split()[0].replace('n',''))
            
        else:
            for index, i in enumerate(intermediate_variable1):
                for index4, j in enumerate(intermediate_variable2):
                    
                    if(i==j):
                        
                        targetnode.append(intermediate_node1[index].split()[0].replace('n',''))
                        targetnode.append(intermediate_node2[index4].split()[0].replace('n',''))
                        break
        targetnodes.append(targetnode)
    return targetnodes

def update_edge(targetnodes, predecessors, Nodeflowx, nestednodes, inputvals, inputkeys, allpredeccessors):
    
    targetnode_list = []
    predecessors3 = []
    
    for targetnode in targetnodes:
        
        for node in Nodeflowx:
            if(node.split()[0].replace('n','')==targetnode and node.split()[len(node.split())-1] == '0'):
                
                targetnode_list.append(node)
        
        if(len(targetnode.split(','))>2):
            nextnode = targetnode.split(',')
            
            nestednode = '' 
            for index, values in enumerate(nextnode):
                
                if (index == len(nextnode)-1):
                    nextnode.pop(index)
                    nestednode = nestednode[:-1]
                else:
                    nestednode = nestednode + str(values) + ','
            
            if nestednode not in nestednodes and nestednode not in allpredeccessors:
                nestednodes.append(nestednode)

        if(targetnode_list == []):
            
            if targetnode !='' and targetnode not in predecessors  and targetnode!='10,0,1,2':
                predecessors.append(targetnode)        
        
            if(predecessors == []):
                print('path not found')

        else:
            guard_condition = targetnode_list.pop(0)
            if targetnode not in predecessors  and targetnode!='10,0,1,2':
                predecessors.append(targetnode)     
            guard_variables, guard_values, guard_cond, or1_and2_condition = ExpandGuardCondition(guard_condition)
            targetnodes = SetofStrictValues(guard_variables, guard_values, guard_cond, Nodeflowx, or1_and2_condition)
            
            for targetnodeval in targetnodes:
                
                if targetnodeval != []:
                    
                    predecessors3, nestednodes, inputvals, inputkeys = update_edge(targetnodeval, predecessors3, Nodeflowx, nestednodes, inputvals, inputkeys, allpredeccessors)
                    
                    for i in predecessors3:
                        if i not in predecessors  and i!='10,0,1,2':
                            predecessors.append(i)
                    
                if(targetnodeval == []):
                    
                    vars = []
                    guard_variables = []
                    guard_variable = ''
                    guard_values = []
                    guard_cond = []
                    or1_and2_condition = 0
                    node = guard_condition.split()[0]
                    vars = guard_condition.split()
                    for index,i in enumerate(vars):

                        if index==0 or index==(len(vars)-1) or i=='always':
                            continue
                        else:
                            
                            guard_variable = guard_variable + ' ' + i
                    if 'or' in vars or 'and'  in vars:
                        if 'or' in vars:
                            variables = guard_variable.split('or')
                            or1_and2_condition = 1
                        if 'and' in vars:
                            variables = guard_variable.split('and')
                            or1_and2_condition = 2
                        if or1_and2_condition!=1 or or1_and2_condition!=2:
                            or1_and2_condition = 0
                        
                        for i in variables:
                            
                            guard_variables.append(i.split()[0])
                            guard_cond.append(i.split()[len(i.split())-2])
                            guard_values.append(i.split()[len(i.split())-1])
                        
                    else:
                        varssplit = guard_variable.split()
                        if len(varssplit)==3:
                            
                            guard_variables.append(varssplit[0])
                            guard_values.append(varssplit[len(varssplit)-1])
                            guard_cond.append(varssplit[len(varssplit)-2])
                    for i in range(len(guard_variables)):
                        
                        
                        inputvals.append(guard_variables[i])
                        inputkeys.append(guard_values[i])
    return predecessors, nestednodes, inputvals, inputkeys

def clockedge(lines, index4, node, Nodeinfo, case):
    
    always = []
    always1 = []
    Condition = []
    Nodeinfo1 = []
    Nodeinfo = []
    connection = 0
    index3 = 0
    x=0
    linelist = list(lines[index4])
    line = lines[index4]
    if '//' in line:
        line = line.split('//')[0]
    if ':' in line:
        line = line.split(':')[0]
    line1 = line.replace('(','')
    line2 = line1.replace(')','')
    line3 = line2.replace('@','')  
    line4 = cleanlines(line3).replace('always','').replace('_ff','')
    i = 0
    
    if '(' in line and ')' not in line and ';' not in line and 'begin' not in line: 
        
        x=1
        line1 = line.replace('(','')
        line2 = line1.replace(')','')
        line3 = line2.replace('@','')  
        line4 = cleanlines(line3).replace('always','').replace('_ff','')
        while ')' not in line4:
            
            line4 = line4 + ' ' + lines[index4+x]
            
            x = x+1
            
        line1 = line4.replace('(','')
        line2 = line1.replace(')','')
        line3 = line2.replace('@','')  
        line5 = cleanlines(line3).replace('always','').replace('_ff','')
        
        line6 = line5.split('or')
        
        for i in line6:
            always.append(i.replace(' ','') + ' != 0!')
        node = node + 1
        always1.append('n' + str(node) + ',0 ' +' always ' + ' or '.join(always) + ' ' + str(connection))
        for a in always1:
            Nodeinfo1.append(a)
        
    else:
        if ',' in line4:
            line5 = line4.split(',')
            for i in range(len(line5)):
                if 'posedge' in line5[i]:
                    line6 = line5[i].split()
                    always.append(line6[1] + ' == 1')
                elif 'negedge' in line5[i]:
                    line6 = line5[i].split()
                    always.append(line6[1] + ' == 0')
            node = node + 1
            
            always1.append('n' + str(node) + ',0 ' + 'always ' + ' or '.join(always) + ' ' + str(connection))
            for a in always1:
                Nodeinfo1.append(a)
        
        elif ' or ' in line4:
            
            line5 = line4.split('or')  
            for i in range(len(line5)):
                if 'posedge' in line5[i]:
                    line6 = line5[i].split()
                    always.append(line6[1] + ' == 1')
                elif 'negedge' in line5[i]:
                    line6 = line5[i].split()
                    always.append(line6[1] + ' == 0')
                elif '==' in line5[i]:
                    always.append(line5[i])
                else:
                    line6 = line5[i].split()
                    
                    always.append(line6[0] + ' != 0!')
            
            node = node + 1
            always1.append('n' + str(node) + ',0 ' + 'always ' + ' or '.join(always) + ' ' + str(connection))
            for a in always1:
                Nodeinfo1.append(a)
        elif '*' in line4:            
            node = node + 1            
            always.append('n' + str(node) + ',0 ' + 'always ' + 'True' + ' ' + str(connection))
            for a in always:
                Nodeinfo1.append(a)        
        elif 'posedge' in line4 or 'negedge' in line4:
            line5 = line4
            if 'posedge' in line5:
                line6 = line5.replace('posedge','')
                node = node + 1
                
                always.append('n' + str(node) + ',0 ' + 'always ' + line6 + ' == 1' + ' ' + str(connection))
            elif 'negedge' in line5:
                line6 = line5.replace('negedge','')
                node = node + 1
                
                always.append('n' + str(node) + ',0 ' + 'always ' + line6 + ' == 0' + ' ' + str(connection))
            for a in always:
                Nodeinfo1.append(a)
        
        else:
            if '(' in line and '@' in line and ')' in line:
                start = line.find("(") + len("(")
                end = line.find(")")
                line6 = line[start:end]
                node = node + 1
                
                always.append('n' + str(node) + ',0 ' + 'always ' + line6 + ' != 0!' + ' ' + str(connection))
            elif '(' in line and '@' in line and ')' not in line and ':' not in line and ';' not in line and 'begin' not in line:
                x=1
                while ')' not in line:
                    line = line + lines[index4+x]
                    x = x+1
                if ')' in line:
                    line6 = line + lines[index4+x]
                node = node + 1
                
                always.append('n' + str(node) + ',0 ' + 'always ' + line6 + ' == 1' + ' ' + str(connection))
            for a in always:
                Nodeinfo1.append(a)

    if index4 < (index4+x):
        
        index4 = index4+x

    formark = 0
    indentref = 0
    indent = 0
    indentmark = 0
    check = 0
    indentcount = 0
    i = 0
    connection = 0
    
    if 'always' in line and ('if ' in line or 'if(' in line) and ('<=' in line or '=' in line or '|->' in line) and ';' in line:
        
        indent = 0
        if indentmark == 0:
            nextlinelist = list(line)
            for value in nextlinelist:
                if value == '\t':
                    indent = indent + 8
                elif value == ' ':
                    indent = indent + 1
                elif value != ' ':
                    break
            indentmark = 1
            indentref = indent
            indent = 0
        if indentmark == 1:
            nextlinelist = list(line)
            for value in nextlinelist:
                if value == '\t':
                    indent = indent + 8
                elif value == ' ':
                    indent = indent + 1
                elif value != ' ':
                    break
            
            if indent<=indentref:
                nodenested = str(node) + ',0'
                
                Nodeinfo, index3, nodestr = nestedifelsecondition(lines, index4+i , nodenested, Nodeinfo, connection)
                nodestr1 = nodestr.split(',')[0]
                node = int(nodestr1)
                
                indent = 0
            else:
                indent = 0
            i = index3 - index4
            

    elif('always' in lines[index4] and 'begin' in lines[index4]):
       
        for indent in list(lines[index4]):
            if indent == '\t':
                indentcount = indentcount + 8
            elif indent == ' ':
                indentcount = indentcount + 1
            elif indent != ' ':
                break
        line = lines[index4+i]
        
    elif('always' in lines[index4] and 'begin' not in lines[index4] ):
        i = i+1
        line = lines[index4+i]
       

    if line.replace('\n','').replace('\t','').replace(' ','').split(':')[0] == 'begin':
       
        for indent in list(line):
            if indent == '\t':
                indentcount = indentcount + 8
            elif indent == ' ':
                indentcount = indentcount + 1
            elif indent != ' ':
                break
        i = i+1
        line = lines[index4+i]
    nextindentcount = 0
    
    for indent in line:
        if indent == '\t':
            nextindentcount = nextindentcount + 8
        elif indent == ' ':
            nextindentcount = nextindentcount + 1
        elif indent != ' ':
            break
    
    while nextindentcount>indentcount:
        
        if '//' in line:
            line1 = line.split('//')
            line = line1[0]
        formark = 0
        indentref = 0
        indent = 0
        indentmark = 0
        check = 0
        if (('assign' in line or '=' in line) or '<=' in line) and '?' in line:
            
            if ';' not in line:
                if '//' in line:
                    line1 = line.split('//')
                    line = line1[0]
                linegen = line.replace('\n','')
                nex = 1
                nexline = lines[index4+i+nex]
                
                while ';' not in nexline:
                    
                    if '//' in nexline:
                        line1 = nexline.split('//')
                        line = line1[0]
                    else:
                        line = nexline.replace('\n','')
                    linegen = linegen + line.replace('\n','')
                    nex = nex + 1
                    nexline = lines[index4+i+nex]
                    if '//' in line:
                        nexline = nexline.split('//')[0]
                else:  
                    if '//' in nexline:
                        line1 = nexline.split('//')
                        line = line1[0]
                    else:
                        line = nexline.replace('\n','')
                    linegen = linegen + line.replace('\n','').replace(' ','').replace('\t','')
                    
                    node, Nodeinfo = assignmentif(linegen, node, Nodeinfo, 0, '')
            else:
                node, Nodeinfo = assignmentif(line, node, Nodeinfo, 0, '')
           
        if 'if ' in line and ('begin' in line or 'begin' in lines[index4+i+1]) and 'else' not in line:
            
            indent = 0
            if indentmark == 0:
                nextlinelist = list(line)
                indent = 0
                for value in nextlinelist:
                    if value == '\t':
                        indent = indent + 8
                    elif value == ' ':
                        indent = indent + 1
                    elif value != ' ':
                        break
                indentmark = 1
                indentref = indent
                indent  = 0
            if indentmark == 1:
                nextlinelist = list(line)
                for value in nextlinelist:
                    if value == '\t':
                        indent = indent + 8
                    elif value == ' ':
                        indent = indent + 1
                    elif value != ' ':
                        break
                if indent<=indentref:
                    nodenested = str(node) + ',0'
                    Nodeinfo, index3, nodestr = nestedifelsecondition(lines, index4+i , nodenested, Nodeinfo, connection)
                    nodestr1 = nodestr.split(',')[0]
                    node = int(nodestr1)
                    i = index3 - index4 - 1
                
                indent = 0
        elif 'if ' in line or ('if(' in line and ')' in line):
            
            indent = 0
            if indentmark == 0:
                nextlinelist = list(line)
                for value in nextlinelist:
                    if value == '\t':
                        indent = indent + 8
                    elif value == ' ':
                        indent = indent + 1
                    elif value != ' ':
                        break
                indentmark = 1
                indentref = indent
                indent = 0
            if indentmark == 1:
                nextlinelist = list(line)
                for value in nextlinelist:
                    if value == '\t':
                        indent = indent + 8
                    elif value == ' ':
                        indent = indent + 1
                    elif value != ' ':
                        break
                if indent<=indentref:
                    nodenested = str(node) + ',0'
                    
                    Nodeinfo, index3, nodestr = nestedifelsecondition(lines, index4+i , nodenested, Nodeinfo, connection)
                    
                    nodestr1 = nodestr.split(',')[0]
                    node = int(nodestr1)
                    indent = 0
                else:
                    indent = 0
                i = index3 - index4 - 1
            
        if ('for (' in line or 'for(' in line) and ('//' not in line.split()[0] and '//' not in line.split()[1]):
            
            if 'begin' not in lines[index4+i + 1]:
                continue
            recordNode = []
            for things in Nodeinfo:
                recordNode.append(things)
            formark = 1
            
            forline = line.split(';')
            loopstart = forline[0].replace('for','').replace('(','').replace(' ','').split('=')
            loopvariable = loopstart[0].replace('int','')
            for things in parameter:
                if things.split()[0] in loopstart[1]:
                    loopstart[1] = loopstart[1].replace(things.split()[0],things.split()[1])
                    break
            try: loopstart[1] = eval(loopstart[1])
            except: loopstart[1] = 1
            loopbegin = int(loopstart[1])
            if '<' in forline[1]:
                loopend = forline[1].replace(loopvariable,'').replace('<','').replace('=','').replace(' ','')
            elif '>' in forline[1]:
                loopend = forline[1].replace(loopvariable,'').replace('>','').replace('=','').replace(' ','')
            for things in parameter:
                if things.split()[0] in loopend:
                    loopend = loopend.replace(things.split()[0],things.split()[1])
                    break
            try:loopend = eval(loopend)
            except: loopend = 1
            if 'begin' in lines[index4 +i+ 1]:
                forbegin = list(lines[index4+i+1])
                indentcount = 0
                for indentx in forbegin:
                    if indentx == ' ':
                        indentcount = indentcount + 1
                    else:
                        break
            
        if 'case' in line and 'endcase' not in line and '//' not in line and ('case(' in line or 'case (' in line):
            
            nodenested = str(node) + ',0,0'
            Nodeinfo, index3, node = nestedcasestatement(lines, index4+i, nodenested, Nodeinfo, 1)
            i = index3-index4
        if ('<=' in line or ' = ' in line) and '?' not in line:
            nex=0
            if ';' not in line:
                if '//' in line:
                    line1 = line.split('//')
                    line = line1[0]
                nex = 1
                nexline = lines[index4+i+nex]
                
                while ';' not in nexline:
                    if '//' in nexline:
                        line1 = nexline.split('//')
                        line = line1[0]
                    else:
                        nexline = nexline.replace('\n','')
                    line = line + nexline.replace('\n','')
                   
                    nex = nex + 1
                    nexline = lines[index4+i+nex]
                    
                    if '//' in line:
                        nexline = nexline.split('//')[0]
                else:  
                    if '//' in nexline:
                        line1 = nexline.split('//')
                        line = line+line1[0]
                    else:
                        line = line+nexline.replace('\n','')
            i = i+nex
            
            line = (line.replace('\n','').replace('\t',''))
            values = line.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                
                values, valueline = onelinecondition(values)
                line = ' '.join(values)
                connection = connection + 1
                Nodeinfo.append('n' + str(node)+',0'+ ' ' + valueline + ' ' + str(connection))
              
        i = i+1
        line = lines[index4+i]
        while line == '\n' or line == ' ' or line == '' or line == '\t':

            i = i+1
            line = lines[index4+i]
           
        nextindentcount = 0
        for indent in list(line):
            if indent == '\t':
                nextindentcount = nextindentcount + 8
            elif indent == ' ':
                nextindentcount = nextindentcount + 1
            elif indent != ' ':
                break
    
    if nextindentcount==indentcount and 'end ' in line:
        i = i+1
        line = lines[index4+i]
    
    else:
        if Nodeinfo!=[]:
            
            for nodeval in Nodeinfo:
                Nodeinfo1.append(nodeval)
        
        return Nodeinfo1, index4 + i , node    
    
    if Nodeinfo!=[]:
        
        for nodeval in Nodeinfo:
            Nodeinfo1.append(nodeval)
    return Nodeinfo1, index4 + i , node

def assignmentif(line, node, Nodeinfo, nested, nodenested):
    
    node = node + 1
    if '//' in line:
        line = line.split('//')[0]
    
    Connection = []
    breakingline = line.split('?') 
    if len(breakingline) > 2:
        
        ifstatement = []
        passstatement = []
        if ' <= ' in breakingline[0]:
            breakingline0 = breakingline[0].split('<=')
        elif ' = ' in breakingline[0] and 'assign' in breakingline[0]:
            breakingline0 = breakingline[0].split(' = ') 
        assignvalue = breakingline0[0].replace('assign','').replace(' ','').replace('(','').replace(')','')
        ifstatement.append(breakingline0[1].replace(' ',''))
        for index, things in enumerate(breakingline):
            
            if ':' in things:
                if index != len(breakingline) - 1:
                    newthings = things.replace('(','').replace(')','').split(':')
                    
                    newthings1 = newthings[1].split()
                    newthings1 = ' '.join(newthings1)
                    ifstatement.append(newthings1)
                    newthings2 = newthings[0].replace(' ','')
                    passstatement.append(newthings2)
                else:
                    
                    new = things.replace('(','').replace(')','').replace(';','').replace('`','').replace(' ','').split(':')
                    for x in new:
                        passstatement.append(x) 
            elif index != 0 and ':' not in things:
                newthings = things.replace('(','').replace(')','').split()
                newthings = ' '.join(newthings)
                ifstatement.append(newthings)
        connection = 0
        for index, thing in enumerate(ifstatement):
            if nested == 0:                
                connection = 0                
                statement1 = 'n'+ str(node) + ',' + str(index) + ' ' + ifstatement[index] + ' ' + str(connection)                
                Connection.append(statement1)
            else:
                statement1 = 'n'+ nodenested + ' ' + ifstatement[index] + ' ' + str(connection)                
                Connection.append(statement1)
            if index == 0:
                if nested == 0:
                    
                    connection = connection + 1
                    statement2 = 'n'+ str(node) + ',0' + ' ' + assignvalue + ' = ' + passstatement[index] + ' ' + str(connection)
                    Connection.append(statement2)
                    continue
                else:
                    statement2 = 'n'+ nodenested + ' ' + assignvalue + ' = ' + passstatement[len(passstatement)-1] + ' ' + str(connection)
                    Connection.append(statement2)
                    connection = connection + 1
                    continue
            
            connection = connection + 1
            if nested == 0:
                statement2 = 'n'+ str(node) + ',' + str(index) + ' ' + assignvalue + ' = ' + passstatement[index] + ' ' + str(connection)
            else:
                statement2 = 'n'+ nodenested + ' ' + assignvalue + ' = ' + passstatement[index] + ' ' + str(connection)

            Connection.append(statement2)
            connection = connection + 1
            if index == len(ifstatement) - 1:
                if nested == 0:
                    statement2 = 'n'+ str(node) + ',' + str(index) + ' ' + assignvalue + ' = ' + passstatement[index] + ' ' + str(connection)
                else:
                    statement2 = 'n'+ nodenested + ' ' + assignvalue + ' = ' + passstatement[index] + ' ' + str(connection)
                Connection.append(statement2)
                continue
        Nodeinfo.append(Connection)    
        return node, Nodeinfo
    if '<=' in breakingline[0]:
        breakingline0 = breakingline[0].split('<=')
    elif ' = ' in breakingline[0] and 'assign' in breakingline[0]:
        breakingline0 = breakingline[0].split(' = ')
   
    breakingline1 = breakingline[1].split(':')
    assignvalue = breakingline0[0].replace('assign','').replace(' ','').replace('\n','')
    ifstatement = breakingline0[1].replace(' ','').replace('\n','')
    passstatement = breakingline1[0].replace(' ','').replace('\n','')
    elsestatement = breakingline1[1].replace(' ','').replace('\n','')
    if nested == 0:
        connection = 0
        
        firststatement = 'n' + str(node) + ',0' + ' if ' + ifstatement + ' ' + str(connection)
        connection = connection + 1
        Connection.append(firststatement)
        secondstatement = 'n' + str(node)+ ',0'  + ' ' + assignvalue + ' = ' + passstatement + ' ' + str(connection)
        connection = connection + 1
        Connection.append(secondstatement)
        thirstatement = 'n' + str(node)+ ',0'  + ' ' + assignvalue + ' = ' + elsestatement + ' ' + str(connection)
        Connection.append(thirstatement)
        Nodeinfo.append(Connection)
        return node ,Nodeinfo
    else:
        connection = 0
        firststatement = 'n' + nodenested + ' if ' + ifstatement + ' ' + str(connection)
        connection = connection + 1
        Connection.append(firststatement)
        secondstatement = 'n' + nodenested + ' ' + assignvalue + ' = ' + passstatement + ' ' + str(connection)
        connection = connection + 1
        Connection.append(secondstatement)
        thirstatement = 'n' + nodenested + ' ' + assignvalue + ' = ' + elsestatement + ' ' + str(connection)
        Connection.append(thirstatement)
        Nodeinfo.append(Connection)
        return nodenested ,Nodeinfo

def nestedifelsecondition(lines, index4, node, Nodeinfo1, connection):
    
    i=0
    nestedif = []
    ifline = ''
    assignmentstatements = []
    nextline = lines[index4 + i]
    x=i
    nodenested = node
    Condition = []
    oneline = 0
    indentcount = 0
    recentindentcount = 0
    nextindentcount = 0
    parentifcount = 0
    parentifindent = 0
    
    for indent in list(lines[index4]):
        if indent == '\t':
            indentcount = indentcount + 8
        elif indent == ' ':
            indentcount = indentcount + 1
        elif indent != ' ':
            break
    parentifindent = ifindent = indentcount
    ifcount = 0
    for indent in list(lines[index4 + 1]):
        if indent == '\t':
            recentindentcount = recentindentcount + 8
        elif indent == ' ':
            recentindentcount = recentindentcount + 1
        elif indent != ' ':
            break
    while (recentindentcount>indentcount) or ((indentcount == recentindentcount) and (('if ' in nextline or 'if(' in nextline or 'else' in nextline) or ('<=' in nextline and 'else' in lines[index4+x-1]) or ('if' in nextline and nextindentcount>indentcount))):
        
        if '//' in nextline:
            nextline = nextline.split('//')[0]
        nextline = nextline.replace('`','')
        if ('else' in nextline or 'if ' in nextline or 'if(' in nextline) and ';' in nextline and (' = ' in nextline or 'assign ' in nextline or ' <= ' in nextline or '|->' in nextline):
            
            if '(' in nextline and ')' in nextline and ('if ' in nextline or 'if(' in nextline):
                
                start = nextline.find("(") + len("(")
                end = nextline.rfind(")")
                line7 = nextline[start:end]
                ifindent = 0
                for indent in list(lines[index4+x]):
                    if indent == '\t':
                        ifindent = ifindent + 8
                    elif indent == ' ':
                        ifindent = ifindent + 1
                    elif indent != ' ':
                        break
                if (parentifindent < ifindent or ifcount == 0):
                    
                    ifcount = 1
                    nodenested = nodenested  +',' + str(0)
                elif parentifindent == ifindent and ifcount!=0:
                    nextnode = nodenested.split(',')
                    nodenested = '' 
                    for index, values in enumerate(nextnode):
                        
                        if (index == len(nextnode)-1):
                            values = int(values) + 1
                            nodenested = nodenested + str(values)
                        else:
                            nodenested = nodenested + str(values) + ','
                    
                    connection = 0
                line7 = cleanlines(line7)
                line8 = line7.split()
                parentifindent = 0
                if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                    
                    Condition1 = []
                    if '&&' in line7:
                        line10 = line7.split('&&')
                    elif '&' in line7:
                        line10 = line7.split('&')
                    else:
                        line10 = line8
                     
                    for ii, instance1 in enumerate(line10):
                        if '||' in instance1:
                            instance2 = instance1.split('||')
                            line10.pop(ii)
                            for newitem in instance2:
                                line10.insert(ii, newitem)
                            
                        if '|' in instance1:
                            instance2 = instance1.split('|')
                            line10.pop(ii)
                             
                            for newitem in instance2:
                                line10.insert(ii, newitem)
                    for instance in line10:
                        if '==' in instance or '>=' in instance:
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                            continue
                        elif '!=' in instance:
                            instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                            continue
                        elif '~' in instance or '!' in instance and '!=' not in instance:
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                            Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                        else:
                             
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                             
                            Condition1.append(instance + ' == 1')
                    for index1, elements in enumerate(line8):
                        if '&&' == elements or '||' == elements:
                            continue
                        if '==' in elements or '!=' in elements:
                            continue
                        
                        for replacement in Condition1:
                            if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                line8[index1] = line8[index1].replace(elements, replacement)
                            elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                line8[index1] = line8[index1].replace(elements, replacement)
                    line8 = ' '.join(line8).replace('(','').replace(')','')
                    line9 = line8.replace('&&',' and ')
                    line10 = line9.replace('||',' or ')
                    line10 = line10.replace('&', ' and ')
                    line11 = line10.replace('|', ' or ')
                    connection = 0                    
                    ifline = line11
                    Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))                    
                    nestedif.append(nextline) 
                else:                   
                     
                    line10 = line7.replace('(','').replace(')','')
                    line10 = line10.replace(' ','')
                    
                    if '==' in line10 or '>=' in line10:
                        line8 = line10.replace('==',' == ').replace('>=',' >= ')
                    elif '!=' in line10:
                        line8 = line10.replace('!=',' != ')
                    elif '~' in line10 or '!' in line10 and '!=' not in line10:
                        line8 = line10.replace('~','').replace('!','') + ' == 0'
                    else:
                        line8 = line10 + ' == 1'
                    connection = 0
                    
                    ifline = line8
                    Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                     
                
            if 'else' in nextline: 
                ifindent = 0
                for indent in list(lines[index4+x]):
                    if indent == '\t':
                        ifindent = ifindent + 8
                    elif indent == ' ':
                        ifindent = ifindent + 1
                    elif indent != ' ':
                        break
                
                ifcount = 1
                nextnode = nodenested.split(',')
                nodenested = '' 
                for index, values in enumerate(nextnode):
                    
                    if (index == len(nextnode)-1):
                        values = int(values) + 1
                        nodenested = nodenested + str(values)
                    else:
                        nodenested = nodenested + str(values) + ','
                
                connection = 0
                parentifindent = 0
                if 'or' in ifline or 'and' in ifline:
                    iflinetemp = ''
                    
                    if 'or' in ifline:
                        splitline = []
                        linesplit = []
                        
                        linesplit = ifline.split('or')
                        for ind,s in enumerate(linesplit):
                            
                            if ind == len(linesplit)-1:
                                s = s.replace(';','')
                            splitline = s.split()
                            
                            for inde, j in enumerate(splitline):
                                if len(splitline)-1==inde:
                                    iflinetemp = iflinetemp + j
                                else:
                                    iflinetemp = iflinetemp + j + ' '
                            if ind != len(linesplit)-1:
                                iflinetemp = iflinetemp + ' or '
                    if 'and' in ifline:
                        splitline = []
                        linesplit = []
                        
                        linesplit = ifline.split('and')
                        for ind,s in enumerate(linesplit):
                            
                            if ind == len(linesplit)-1:
                                s = s.replace(';','')
                            splitline = s.split()
                            
                            for inde, j in enumerate(splitline):
                                if len(splitline)-1==inde:
                                    iflinetemp = iflinetemp + j
                                else:
                                    iflinetemp = iflinetemp + j + ' '
                            if ind != len(linesplit)-1:
                                iflinetemp = iflinetemp + ' and '
                     
                    ifline = iflinetemp
                    
                ifline = ifline.replace('==', '!=').replace('>=', '<').replace('<=', '>').replace('>', '<=').replace('<', '>=').replace('!=', '==')
                
                connection = 0
                Condition.append('n' + nodenested +' ' + ifline + '!' +  ' ' + str(connection))
                nextline.replace('else ','').replace(':','')
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
            if ('<=' in nextline or ' = ' in nextline) and '?' not in nextline and ';' in nextline:
            
                         
                nextline = (nextline.replace('\n','').replace('\t','').replace('if(','').replace('if (','').replace('if ','').replace(')','').replace(line7,'').replace('else',''))
                
                values = nextline.split()
                for vals in values:
                    if (vals == '=' or vals == '<=') and '==' != vals:
                        oneline = 1
                if oneline == 1:
                    
                    values, valueline = onelinecondition(values)
                    line = ' '.join(values)
                
                if 'if' in nextline or 'else' in nextline:
                    connection = 0
                
                connection = connection + 1
                if oneline == 1:
                    
                    
                    Condition.append('n' + nodenested + ' ' + valueline + ' ' + str(connection))
                    
        elif 'else' not in nextline and '<=' not in nextline and ' = ' not in nextline and 'assign ' not in nextline and ('if ' in nextline or 'if(' in nextline or 'if (' in nextline) and 'else if' not in nextline:

            ifindent = 0
            for indent in list(lines[index4+x]):
                if indent == '\t':
                    ifindent = ifindent + 8
                elif indent == ' ':
                    ifindent = ifindent + 1
                elif indent != ' ':
                    break
            while '<=' not in lines[index4+x+1] and ' = ' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and '<=' not in nextline  and ' = ' not in nextline and 'begin' not in nextline:
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                nextline=nextline.replace('\n','')
                nextline = (nextline)+ ' ' +lines[index4+x+1].replace('\t','').replace('\n','').replace(' ','')
                
                x=x+1
            if (parentifindent < ifindent or ifcount == 0):
                
                ifcount = 1
                nodenested = nodenested  +',' + str(0)
              
            elif parentifindent == ifindent and ifcount!=0 and ('end' not in lines[index4+x-1] and 'end' not in lines[index4+x-2]):
                
                nextnode = nodenested.split(',')
                nodenested = '' 
                for index, values in enumerate(nextnode):
                    
                    if (index == len(nextnode)-1):
                        values = int(values) + 1
                        nodenested = nodenested + str(values)
                    else:
                        nodenested = nodenested + str(values) + ','
                
                connection = 0
            
            line7 = cleanlines(nextline)
            line8 = line7.split()
            parentifindent = ifindent
            
            if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                
                Condition1 = []
                if '&&' in line7:
                    line10 = line7.split('&&')
                elif '&' in line7:
                    line10 = line7.split('&')
                else:
                    line10 = line8
                
                for ii, instance1 in enumerate(line10):
                    if '||' in instance1:
                        instance2 = instance1.split('||')
                        line10.pop(ii)
                        for newitem in instance2:
                            line10.insert(ii, newitem)
                        
                    if '|' in instance1:
                        instance2 = instance1.split('|')
                        line10.pop(ii)
                         
                        for newitem in instance2:
                            line10.insert(ii, newitem)
                for instance in line10:
                    if '==' in instance or '>=' in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        continue
                    elif '!=' in instance:
                        instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                        continue
                    elif '~' in instance or '!' in instance and '!=' not in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        
                        Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                    else:
                         
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                         
                        Condition1.append(instance + ' == 1')
                for index1, elements in enumerate(line8):
                    if '&&' == elements or '||' == elements:
                        continue
                    if '==' in elements or '!=' in elements:
                        continue
                    
                    for replacement in Condition1:
                         
                        
                        if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                            line8[index1] = line8[index1].replace(elements, replacement)
                        elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                            line8[index1] = line8[index1].replace(elements, replacement)
                line8 = ' '.join(line8).replace('(','').replace(')','')
                line9 = line8.replace('&&',' and ')
                line10 = line9.replace('||',' or ')
                line10 = line10.replace('&', ' and ')
                line11 = line10.replace('|', ' or ')
                connection = 0
                ifline = line11
                Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                nestedif.append(nextline)

            else:
                line10 = line7.replace('(','').replace(')','')
                line10 = line10.replace(' ','')
                
                if '==' in line10 or '>=' in line10:
                    line8 = line10.replace('==',' == ').replace('>=',' >= ')
                elif '!=' in line10:
                    line8 = line10.replace('!=',' != ')
                elif '~' in line10 or '!' in line10 and '!=' not in line10:
                    line8 = line10.replace('~','').replace('!','') + ' == 0'
                else:
                    line8 = line10 + ' == 1'
                connection = 0
                
                ifline = line8
                Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
        elif (('<=' in nextline or ' = ' in nextline) and '?' not in nextline) or ('++' in nextline or '--' in nextline):
            
            nextlinelist = nextline.split()
            if '++' in nextline or '--' in nextline:
                
                for i in nextlinelist:
                    if '++' in i:
                        
                        varval = i.replace('++','').replace(';','').replace('`','')
                        varvalue = varval + ' = ' + varval + ' + 1'
                        nextline = nextline.replace(i, varvalue)
                    if '--' in i:
                        varval = i.replace('--','')
                        varvalue = varval + ' = ' + varval + ' - 1'
                        nextline = nextline.replace(i, varvalue)
                    
            if ('<=' not in lines[index4+x+1] and '<=' not in nextline  and ' = ' not in nextline and 'begin' not in nextline and 'else' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'end' not in lines[index4+x+1]):
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                if '//' in lines[index4+x+1]:
                    lines[index4+x+1] = lines[index4+x+1].split('//')[0]
                nextline=nextline.replace('\n','')
                nextline = (nextline) +' '+lines[index4+x+1].replace('\t','').replace('\n','').replace(' ','')
                x=x+1
                
            nextline = (nextline.replace('\n','').replace('\t',''))
            values = nextline.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                values, valueline = onelinecondition(values)
                line = ' '.join(values)
            
            if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])) or 'end' in lines[index4+x-1]:
                connection = 0
            
            connection = connection + 1
            if oneline == 1:
                Condition.append('n' + nodenested + ' ' + valueline.replace('`','') + ' ' + str(connection))
                
        elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:
            
            if ( ' = ' not in lines[index4+x+1] and 'begin' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'end' not in lines[index4+x+1]):
              
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                if '//' in lines[index4+x+1]:
                    lines[index4+x+1] = lines[index4+x+1].split('//')[0]
                nextline=nextline.replace('\n','')
                nextline = (nextline) +' '+lines[index4+x+1].replace('\t','').replace('\n','').replace(' ','')
                
                x=x+1
                
            nextline = nextline.replace('\n','').replace('\t','')
            while ' = ' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                 
                nextline=nextline.replace('\n','')
                nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                
                x=x+1
                nextline = lines[index4+x]
            if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
                nextline=nextline.replace('\n','')
                nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                
                x=x+1
            values = nextline.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                line = ' '.join(values)
            
            if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):

                connection = 0
            connection = connection + 1
            for assignstmts in assignmentstatements:
                for assignstmt in assignstmts:
                    Condition.append(assignstmt)
                
        else:
            
            nextindentcount = 0
            linelist = list(nextline)
            for indent in linelist:
                if indent == '\t':
                    nextindentcount = nextindentcount + 8
                elif indent == ' ':
                    nextindentcount = nextindentcount + 1
                elif indent != ' ':
                    break
            nextnextindentcount = 0
            nextnextlinelist = list(lines[index4+x+1])
            for indent in nextnextlinelist:
                if indent == '\t':
                    nextnextindentcount = nextnextindentcount + 8
                elif indent == ' ':
                    nextnextindentcount = nextnextindentcount + 1
                elif indent != ' ':
                    break 
            
            if (nextindentcount >= recentindentcount):
                if 'end' in nextline:
                    if ('else ' in lines[index4+x+1] or 'if ' in lines[index4+x+1]) and nextnextindentcount == nextindentcount:
                        
                        pass
                    else:
                        
                        nextnode = nodenested.split(',')
                        nodenested = '' 
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                              
                                nextnode.pop(index)
                                
                                nodenested = nodenested[:-1]
                                
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                        connection = 0
                    
                    
                if 'else if' in nextline:
                    
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline):
                       
                        
                        while ' <= ' not in lines[index4+x+1] and ' = ' not in lines[index4+x+1] and '++' not in lines[index4+x+1] and '--' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                        
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                        
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()
                        
                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                             
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                             
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                    
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                        
                            for instance in line10:
                                
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    
                                    
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0
                            
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:

                        assignmentstatements.append(nextline.replace('\n','').replace('\t',''))
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):

                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if '//' in nextline:
                            nextline = nextline.split('//')[0]
                        if oneline == 1:
                             
                            Condition.append('n' + nodenested + ' ' + valueline + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:

                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        while ' = ' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                            
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if '//' in nextline:
                            nextline = nextline.split('//')[0]
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                Condition.append(assignstmt)
                            

                if 'else' in nextline and 'if' not in nextline:
                    x=x+1
                    nextline = lines[index4+x]
                    if not(nextnextindentcount == nextindentcount and 'else' in lines[index4+x-1]):
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                            
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1) and not(values==''):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                    if 'or' in ifline or 'and' in ifline:
                        iflinetemp = ''
                        
                        if 'or' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('or')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + ' or '
                        if 'and' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('and')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + '! and '
                         
                        ifline = iflinetemp
                        

                    ifline = ifline.replace('!=', '==').replace('==', '!=').replace('>=', '<').replace('<=', '>').replace('>', '<=').replace('<', '>=')
                    connection = 0
                    Condition.append('n' + nodenested +' ' + ifline + '!' +  ' ' + str(connection))
                    
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline) and 'else if' not in nextline and 'else' not in nextline:
                        
                        while '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()
                        
                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                            
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                            
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                     
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                         
                            for instance in line10:
                                
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    
                                    
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if oneline == 1:
                            Condition.append('n' + nodenested + ' ' + valueline + ' '+ str(connection))
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:

                        
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        while '<=' not in lines[index4+x+1] and ' = ' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                            
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                
                                Condition.append(assignstmt)
                            
               
            elif recentindentcount>nextindentcount and nextindentcount>=indentcount and ('else' in nextline or ('end' in nextline and 'else' in lines[index4+x+1])):
               
                if 'end' in nextline:                   
                    pass
                   
                if 'else' in nextline and 'if' not in nextline:
                    
                    if 'or' in ifline or 'and' in ifline:
                        iflinetemp = ''
                        
                        if 'or' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('or')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + ' or '
                        if 'and' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('and')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + ' and '
                         
                        ifline = iflinetemp
                         
                    ifline = ifline.replace('==', '!=').replace('>=', '<').replace('<=', '>').replace('>', '<=').replace('<', '>=').replace('!=', '==')
                    
                    connection = 0
                    Condition.append('n' + nodenested +' ' + ifline + '!' +  ' ' + str(connection))
                
                    x=x+1
                    nextline = lines[index4+x]
                    
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline):
                        
                        
                        while '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        nodenested = nodenested  +',' + str(0)
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()
                        
                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                            
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                            
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                     
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                            for instance in line10:
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:

                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        
                        
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if oneline == 1:
                             
                            Condition.append('n' + nodenested + ' ' + valueline + ' '+ str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:

                        nextline = (nextline.replace('\n','').replace('\t',''))
                        while ' = ' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                            
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                
                                Condition.append(assignstmt)
                            
                elif 'else' in nextline and 'if' in nextline:
                    
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline):
                        
                        while '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                    
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                                break
                            else:
                                nodenested = nodenested + str(values) + ','
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()

                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                            
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                            
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                     
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                         
                            for instance in line10:
                                
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    
                                    
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        
                       
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if oneline == 1:
                             
                            Condition.append('n' + nodenested + ' ' + valueline + ' '+ str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        while ' = ' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                        
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                
                                Condition.append(assignstmt)
                            
            elif recentindentcount>nextindentcount and recentindentcount>indentcount and ('else ' not in nextline and 'if ' not in nextline) and (parentifindent<ifindent):
                nextnode = nodenested.split(',')
                nodenested = ''
                    
                for index, values in enumerate(nextnode):
                    
                    if (index == len(nextnode)-1):
                      
                        nextnode.pop(index)
                        
                        nodenested = nodenested[:-1]
                        
                    else:
                        nodenested = nodenested + str(values) + ','
                
            elif (nextindentcount < recentindentcount):
                if 'end' in nextline:
                    
                    if 'end' in lines[index4+x+1]:
                        
                        nextnode = nodenested.split(',')
                        nodenested = '' 
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                              
                                nextnode.pop(index)
                                
                                nodenested = nodenested[:-1]
                                
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                        connection = 0
                    if ('else ' in lines[index4+x+1] or 'if ' in lines[index4+x+1]) or (('else ' in lines[index4+x+2] or 'if ' in lines[index4+x+2]) and ('\n' in lines[index4+x+1] or '' in lines[index4+x+1])):
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                            else:
                                nodenested = nodenested + str(values) + ','
                    
                if 'else if' in nextline:
                    
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline):
                       
                        
                        while ' <= ' not in lines[index4+x+1] and ' = ' not in lines[index4+x+1] and '++' not in lines[index4+x+1] and '--' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                        
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                        
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()
                        
                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                             
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                             
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                    
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                            
                            for instance in line10:
                                
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    
                                    
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0                          
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:

                        assignmentstatements.append(nextline.replace('\n','').replace('\t',''))
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):

                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if '//' in nextline:
                            nextline = nextline.split('//')[0]
                        if oneline == 1:                            
                            
                            Condition.append('n' + nodenested + ' ' + valueline + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        while ' = ' not in lines[index4+x+1] and '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                            
                        
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if '//' in nextline:
                            nextline = nextline.split('//')[0]
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                
                                Condition.append(assignstmt)
                            
                if 'else' in nextline and 'if' not in nextline:
                    x=x+1
                    nextline = lines[index4+x]
                    if not(nextnextindentcount == nextindentcount and 'else' in lines[index4+x-1]):
                        
                        nextnode = nodenested.split(',')
                        nodenested = ''
                            
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1) and not(values==''):
                                values = int(values) + 1
                                nodenested = nodenested + str(values)
                            else:
                                nodenested = nodenested + str(values) + ','
                        
                    if 'or' in ifline or 'and' in ifline:
                        iflinetemp = ''
                        
                        if 'or' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('or')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + ' or '
                        if 'and' in ifline:
                            splitline = []
                            linesplit = []
                            
                            linesplit = ifline.split('and')
                            for ind,s in enumerate(linesplit):
                                
                                if ind == len(linesplit)-1:
                                    s = s.replace(';','')
                                splitline = s.split()
                                
                                for inde, j in enumerate(splitline):
                                    if len(splitline)-1==inde:
                                        iflinetemp = iflinetemp + j
                                    else:
                                        iflinetemp = iflinetemp + j + ' '
                                if ind != len(linesplit)-1:
                                    iflinetemp = iflinetemp + ' and '
                         
                        ifline = iflinetemp
                         
                    ifline = ifline.replace('==', '!=').replace('>=', '<').replace('<=', '>').replace('>', '<=').replace('<', '>=').replace('!=', '==')
                    
                    connection = 0
                    Condition.append('n' + nodenested +' ' + ifline + '!' +  ' ' + str(connection))
                
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    if ('if ' in nextline or 'if(' in nextline or 'if (' in nextline) and 'else if' not in nextline and 'else' not in nextline:
                        
                        
                        while '<=' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1]:
                            
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        value = nextline.split()
                        line7 = cleanlines(nextline)
                        line8 = line7.split()
                        
                        if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                            
                            Condition1 = []
                            if '&&' in line7:
                                line10 = line7.split('&&')
                            elif '&' in line7:
                                line10 = line7.split('&')
                            else:
                                line10 = line8
                            
                            for ii, instance1 in enumerate(line10):
                                if '||' in instance1:
                                    instance2 = instance1.split('||')
                                    line10.pop(ii)
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                    
                                if '|' in instance1:
                                    instance2 = instance1.split('|')
                                    line10.pop(ii)
                                     
                                    for newitem in instance2:
                                        line10.insert(ii, newitem)
                                        
                            for instance in line10:
                                
                                if '==' in instance or '>=' in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '!=' in instance:
                                    instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                                    continue
                                elif '~' in instance or '!' in instance and '!=' not in instance:
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                                else:
                                    
                                    instance = instance.replace(' ','').replace('(','').replace(')','')
                                    
                                    Condition1.append(instance + ' == 1')
                            for index1, elements in enumerate(line8):
                                if '&&' == elements or '||' == elements:
                                    continue
                                if '==' in elements or '!=' in elements:
                                    continue
                                
                                for replacement in Condition1:
                                    
                                    
                                    if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                                    elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                        line8[index1] = line8[index1].replace(elements, replacement)
                            line8 = ' '.join(line8).replace('(','').replace(')','')
                            line9 = line8.replace('&&',' and ')
                            line10 = line9.replace('||',' or ')
                            line10 = line10.replace('&', ' and ')
                            line11 = line10.replace('|', ' or ')
                            connection = 0
                            
                            ifline = line11

                            Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                            
                            nestedif.append(nextline) 
                        else:
                            
                            
                            line10 = line7.replace('(','').replace(')','')
                            line10 = line10.replace(' ','')
                            
                            
                            if '==' in line10 or '>=' in line10:
                                line8 = line10.replace('==',' == ').replace('>=',' >= ')
                            elif '!=' in line10:
                                line8 = line10.replace('!=',' != ')
                            elif '~' in line10 or '!' in line10 and '!=' not in line10:
                                line8 = line10.replace('~','').replace('!','') + ' == 0'
                            else:
                                line8 = line10 + ' == 1'
                            connection = 0
                            
                            ifline = line8

                            Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:
                        
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                        
                       
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        if oneline == 1:
                            
                            Condition.append('n' + nodenested + ' ' + valueline + ' '+ str(connection))
                            
                    elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:
                        nextline = (nextline.replace('\n','').replace('\t',''))
                        
                        while '<=' not in lines[index4+x+1] and ' = ' not in lines[index4+x+1] and 'else ' not in lines[index4+x+1] and 'if ' not in  lines[index4+x+1] and 'assign' not in lines[index4+x+1] and '//' not in lines[index4+x+1] and ';' not in lines[index4+x+1] and 'end' not in lines[index4+x+1]:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                             
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                            nextline = lines[index4+x]
                        if ';' in nextline and '<=' not in nextline and ' = ' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                            if '//' in nextline:
                                nextline = nextline.split('//')[0]
                            
                            nextline=nextline.replace('\n','')
                            nextline = (nextline)+lines[index4+x+1].replace('\t','').replace('\n','')
                            
                            x=x+1
                        values = nextline.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, nodenested)
                            
                        if 'if' in lines[index4+x-1] or 'else' in lines[index4+x-1] or ('begin' in lines[index4+x-1] and ('if' in lines[index4+x-2] or 'else' in lines[index4+x-2])):
                            connection = 0
                       
                        connection = connection + 1
                        nextline = lines[index4 + i]
                        for assignstmts in assignmentstatements:
                            for assignstmt in assignstmts:
                                
                                Condition.append(assignstmt)
            recentindentcount = nextindentcount
        
        x=x+1
        nextline = lines[index4+x]
        
        while(nextline == '\n' or nextline == '\t' or nextline == ' '):
            x=x+1
            nextline = lines[index4+x]
        if 'end' not in nextline:
            nextindentcount = 0
            linelist = list(nextline)
            for indent in linelist:
                if indent == '\t':
                    nextindentcount = nextindentcount + 8
                elif indent == ' ':
                    nextindentcount = nextindentcount + 1
                elif indent != ' ':
                    break
            recentindentcount = nextindentcount
            
    for i in Condition:
        
        Nodeinfo1.append(i)
        
    return Nodeinfo1,index4+x,node

def ifelsecondition(lines, index4, node, Nodeinfo, case):
    
    ifcond = 1
    oneline = 0
    Connection = 0
    if '//' in lines[index4]:
        lines[index4] = lines[index4].split('//')[0]
    linelist = list(lines[index4])
    
    line = lines[index4]
    if '//' in line:
        line = line.split('//')[0]
    if case == 1:
        
        line = []
        count = 0
        for index, val in enumerate(linelist):
            if ':' in val and count == 0:
                line = []
                count = 1
                continue
            line.append(val)
        line = ''.join(line)
    indentcount = 0
    
    
    values = line.split()
    for indent in linelist:
        if indent == '\t':
            indentcount = indentcount + 8
        elif indent == ' ':
            indentcount = indentcount + 1
        elif indent != ' ':
            break
    
    for vals in values:
        if (vals == '=' or vals == '<=') and '==' != vals:
            oneline = 1
    if oneline == 1:
        values, valueline = onelinecondition(values)
        line = ' '.join(values)
    Condition = []  
    line7 = cleanlines(line)
    line8 = line7.split()

    if ('else' in line or 'if ' in line or 'if(' in line) and ';' in line and (' = ' in line or 'assign ' in line or ' <= ' in line or '|->' in line):
        
        if '(' in line and ')' in line and ('if ' in line or 'if(' in line):
            
            line1 = line[(line.find("if")+len("if")):]
            start = line1.find("(") + len("(")
            end = line1.rfind(")")
            line7 = line1[start:end]
            values = []
            values = line7.split()
            
            ifindent = 0
            for indent in list(line):
                if indent == '\t':
                    ifindent = ifindent + 8
                elif indent == ' ':
                    ifindent = ifindent + 1
                elif indent != ' ':
                    break
            
            line7 = cleanlines(line7)
            line8 = line7.split()
            
            if '&&' in values or '||' in values or '&' in values:
                
                Condition1 = []
                if '&&' in line7:
                    line10 = line7.split('&&')
                elif '&' in line7:
                    line10 = line7.split('&')
                else:
                    line10 = line8
                for ii, instance1 in enumerate(line10):
                    if '||' in instance1:
                        instance2 = instance1.split('||')
                        line10.pop(ii)
                        for newitem in instance2:
                            line10.insert(ii, newitem)
                
                for instance in line10:
                    if '==' in instance or '>=' in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        continue
                    elif '!=' in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        continue
                    elif '~' in instance or '!' in instance and '!=' not in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                    else:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        Condition1.append(instance + ' == 1')
                for index1, elements in enumerate(line8):
                    if '&&' == elements or '||' == elements:
                        continue
                    if '==' in elements:
                        continue
                    
                    for replacement in Condition1:
                        if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                            line8[index1] = line8[index1].replace(elements, replacement)
                        elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                            line8[index1] = line8[index1].replace(elements, replacement)
                line8 = ' '.join(line8).replace('(','').replace(')','')
                line9 = line8.replace('&&',' and ')
                line10 = line9.replace('||',' or ')
                line10 = line10.replace('&', ' and ')
                line10 = line10.replace('|', ' or ')
                
                node = node + 1
                Connection = 0
                
                Condition.append('n' + str(node)+ ',0' + ' ' + line10 + ' '+ str(Connection))
                
         
                nextline = lines[index4 + 1]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
            else:
                
                line10 = line7.replace('(','').replace(')','')
                line10 = line10.replace(' ','')
                if '==' in line10 or '>=' in line10:
                    line8 = line10.replace('==',' == ').replace('>=',' >= ')
                elif '!=' in line10:
                    line8 = line10.replace('!=',' != ')
                elif '~' in line10 or '!' in line10 and '!=' not in line10:
                    line8 = line10.replace('~','').replace('!','') + ' == 0'
                else:
                    line8 = line10 + ' == 1'
                node = node + 1
                Connection = 0
                
                Condition.append('n' + str(node)+ ',0' + ' ' + line8 + ' '+ str(Connection))
                
                nextline = lines[index4 + 1]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
        if 'else' in line: 
            ifindent = 0
            for indent in list(lines[index4+x]):
                if indent == '\t':
                    ifindent = ifindent + 8
                elif indent == ' ':
                    ifindent = ifindent + 1
                elif indent != ' ':
                    break
            
            ifcount = 1
            nextnode = nodenested.split(',')
            nodenested = '' 
            for index, values in enumerate(nextnode):
                
                if (index == len(nextnode)-1):
                    values = int(values) + 1
                    nodenested = nodenested + str(values)
                else:
                    nodenested = nodenested + str(values) + ','
            
            connection = 0
            parentifindent = 0
            line.replace('else ','').replace(':','')
            
            if '//' in line:
                line = line.split('//')[0]
            
        if ('<=' in line or ' = ' in line or '|->' in line) and '?' not in line and ';' in line:
        
            
            
                        
            line = (line.replace('\n','').replace('\t','').replace('if(','').replace('if (','').replace('if ','').replace(')','').replace(line7,'').replace('else',''))
            
            values = line.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                
                values, valueline = onelinecondition(values)
                line = ' '.join(values)
            
            if 'if' in line or 'else' in line:
                Connection = 0
            
            Connection = Connection + 1

            if '|->' in line: 
                start = line.find("|->") + len("|->")
                line1 = line[start:].replace(';','').replace('`','').replace('&&',' and ').replace('||',' or ').replace('&',' and ').replace('|', ' or').replace('==', ' <= ')

                
                Condition.append('n' + str(node)+ ',0' + ' ' + line1 + str(Connection))
            if oneline == 1:
                
                Condition.append('n' + str(node)+ ',0' + ' ' + valueline + ' ' + str(Connection))
            
    elif '&&' in values or '||' in values or '&' in values:
        
        Condition1 = []
        if '&&' in line7:
            line10 = line7.split('&&')
        elif '&' in line7:
            line10 = line7.split('&')
        else:
            line10 = line8
        for ii, instance1 in enumerate(line10):
            if '||' in instance1:
                instance2 = instance1.split('||')
                line10.pop(ii)
                for newitem in instance2:
                    line10.insert(ii, newitem)
        
        for instance in line10:
            if '==' in instance or '>=' in instance:
                instance = instance.replace(' ','').replace('(','').replace(')','')
                continue
            elif '!=' in instance:
                instance = instance.replace(' ','').replace('(','').replace(')','')
                continue
            elif '~' in instance or '!' in instance and '!=' not in instance:
                instance = instance.replace(' ','').replace('(','').replace(')','')
                Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
            else:
                instance = instance.replace(' ','').replace('(','').replace(')','')
                Condition1.append(instance + ' == 1')
        for index1, elements in enumerate(line8):
            if '&&' == elements or '||' == elements:
                continue
            if '==' in elements:
                continue
            
            for replacement in Condition1:
                if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                    line8[index1] = line8[index1].replace(elements, replacement)
                elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                    line8[index1] = line8[index1].replace(elements, replacement)
        line8 = ' '.join(line8).replace('(','').replace(')','')
        line9 = line8.replace('&&',' and ')
        line10 = line9.replace('||',' or ')
        line10 = line10.replace('&', ' and ')
        line10 = line10.replace('|', ' or ')
        
        node = node + 1
        Connection = 0
        
        Condition.append('n' + str(node)+ ',0' + ' ' + line10 + ' '+ str(Connection))
        
        nextline = lines[index4 + 1]
        if '//' in nextline:
            nextline = nextline.split('//')[0]
    else:
        
        line10 = line7.replace('(','').replace(')','')
        line10 = line10.replace(' ','')
        if '==' in line10 or '>=' in line10:
            line8 = line10.replace('==',' == ').replace('>=',' >= ')
        elif '!=' in line10:
            line8 = line10.replace('!=',' != ')
        elif '~' in line10 or '!' in line10 and '!=' not in line10:
            line8 = line10.replace('~','').replace('!','') + ' == 0'
        else:
            line8 = line10 + ' == 1'
        node = node + 1
        Connection = 0
        
        Condition.append('n' + str(node)+ ',0' + ' ' + line8 + ' '+ str(Connection))
        nextline = lines[index4 + 1]
        if '//' in nextline:
            nextline = nextline.split('//')[0]
        
        

    if oneline == 1:
        
        Condition.append('n' + str(node)+ ',0'  + ' ' + valueline + ' '+ str(Connection))
        
    i = 1
    stop = 0
    checkb = 0
    while stop != 1:
        
        oneline = 0
        assignmentstatements = []
        try: nextnextline = lines[index4+1+i]
        except: nextnextline = ''
        
        if ('end ' in nextline or 'end\n' in nextline or 'endmodule' in nextline):
            
            indent2 = 0
            nextlinelist = list(nextline)
            for value in nextlinelist:
                if value == '\t':
                    indent2 = indent2 + 8
                elif value == ' ':
                    indent2 = indent2 + 1
                elif value != ' ':
                    break
            if 'endmodule' in nextline:
                
                i = i-1
                stop = 1
            
            if indent2 <= indentcount and 'else' not in lines[index4+i+1]:
                
                stop = 1
            else:
                i = i+1
                nextline = lines[index4+i]
            
        if 'case' in nextline and 'endcase' not in nextline and '//' not in nextline and ('case(' in nextline or 'case (' in nextline):
            
            nextlinecheck = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            x = i
            while  'endcase' not in nextlinecheck:
                x = x + 1
                nextlinecheck = lines[index4 + x]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
            
            Nodeinfo1 = []
            Nodeinfo1, index3, node = nestedcasestatement(lines, index4 + i, str(node), Nodeinfo1, 0)
            for nodeflow in Nodeinfo1:
                if isinstance(nodeflow, str):
                    
                    Condition.append(nodeflow)
                
            
            i = x
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            continue
        
        elif 'always' in nextline:
            
            indent2 = 0
            nextlinelist = list(nextline)
            for value in nextlinelist:
                if value == '\t':
                    indent2 = indent2 + 8
                elif value == ' ':
                    indent2 = indent2 + 1
                elif value != ' ':
                    break
            if indent2 <= indentcount:
                stop = 1
                continue
            Nodeinfo1 = []
            Nodeinfo1, index3, node = clockedge(lines, index4+i, node, Nodeinfo1, case)            
            i = index3 - index4 + 1
            
            for nodeflow in Nodeinfo1:
                for nodeflows in nodeflow: 
                    if Condition == []:
                        node = node + 1
                        nodeflows1 = (nodeflow + ' 0').replace('always', 'n'+ node)
                        
                        nodeflows1 = ' '.join(nodeflows1.split())
                        
                        Condition.append(nodeflows1)
                        
                        
                    elif Condition != []:
                        thisflow = int(Condition[len(Condition)-1].split()[len(Condition[len(Condition)-1].split())-1])
                        newflow =  thisflow
                        node = node + 1
                        nodeflows1 = (nodeflows + ' ' + str(newflow)).replace('always', 'n'+ str(node))
                        
                        nodeflows1 = ' '.join(nodeflows1.split())
                        
                        Condition.append(nodeflows1)
                        
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
        
        if ('else' in nextline or 'if ' in nextline or 'if(' in nextline) and ';' in nextline and (' = ' in nextline or 'assign ' in nextline or ' <= ' in nextline):
            
            if '(' in nextline and ')' in nextline:
                start = nextline.find("(") + len("(")
                end = nextline.find(")")
                line7 = nextline[start:end]
                line8 = line7.split()
                
                if '&&' in line8 or '||' in line8 or '&' in line8 or '|' in line8:
                    
                    Condition1 = []
                    if '&&' in line7:
                        line10 = line7.split('&&')
                    elif '&' in line7:
                        line10 = line7.split('&')
                    else:
                        line10 = line8
                     
                    for ii, instance1 in enumerate(line10):
                        if '||' in instance1:
                            instance2 = instance1.split('||')
                            line10.pop(ii)
                            for newitem in instance2:
                                line10.insert(ii, newitem)
                            
                        if '|' in instance1:
                            instance2 = instance1.split('|')
                            line10.pop(ii)
                             
                            for newitem in instance2:
                                line10.insert(ii, newitem)
                                 
                    for instance in line10:
                         
                        if '==' in instance or '>=' in instance:
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                            continue
                        elif '!=' in instance:
                            instance = instance.replace('!=', ' != ').replace(' ','').replace('(','').replace(')','')
                            continue
                        elif '~' in instance or '!' in instance and '!=' not in instance:
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                            Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                        else:
                             
                            instance = instance.replace(' ','').replace('(','').replace(')','')
                             
                            Condition1.append(instance + ' == 1')
                    for index1, elements in enumerate(line8):
                        if '&&' == elements or '||' == elements:
                            continue
                        if '==' in elements or '!=' in elements:
                            continue
                        
                        for replacement in Condition1:
                             
                            
                            if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                                line8[index1] = line8[index1].replace(elements, replacement)
                            elif elements.replace(' ','').replace('(','').replace(')','') in replacement:
                                line8[index1] = line8[index1].replace(elements, replacement)
                    line8 = ' '.join(line8).replace('(','').replace(')','')
                    line9 = line8.replace('&&',' and ')
                    line10 = line9.replace('||',' or ')
                    line10 = line10.replace('&', ' and ')
                    line11 = line10.replace('|', ' or ')
                    connection = 0
                    
                    ifline = line11

                    Condition.append('n' + nodenested +' ' + line11 + ' ' + str(connection))
                    
                    nestedif.append(nextline) 
                else:
                    
                    line10 = line7.replace('(','').replace(')','')
                    line10 = line10.replace(' ','')
                    
                    if '==' in line10 or '>=' in line10:
                        line8 = line10.replace('==',' == ').replace('>=',' >= ')
                    elif '!=' in line10:
                        line8 = line10.replace('!=',' != ')
                    elif '~' in line10 or '!' in line10 and '!=' not in line10:
                        line8 = line10.replace('~','').replace('!','') + ' == 0'
                    else:
                        line8 = line10 + ' == 1'
                    connection = 0
                    
                    ifline = line8

                    Condition.append('n' + nodenested +' ' + line8 + ' ' + str(connection))
                     
            if 'else' in nextline: 
                
                
                if not(nextnextindentcount == nextindentcount and 'else' in lines[index4+x-1]):
                    
                    nextnode = nodenested.split(',')
                    nodenested = ''
                    
                        
                    for index, values in enumerate(nextnode):
                        
                        if (index == len(nextnode)-1) and not(values==''):
                            values = int(values) + 1
                            nodenested = nodenested + str(values)
                        else:
                            nodenested = nodenested + str(values) + ','
                    
                nextline.replace('else ','').replace(':','')
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
            if ('<=' in nextline or ' = ' in nextline) and '?' not in nextline and ';' in nextline:
                         
                nextline = (nextline.replace('\n','').replace('\t',''))
                values = nextline.split()
                for vals in values:
                    if (vals == '=' or vals == '<=') and '==' != vals:
                        oneline = 1
                if oneline == 1:
                    
                    values, valueline = onelinecondition(values)
                    line = ' '.join(values)
                
                
                if 'if' in nextline or 'else' in nextline:
                    connection = 0
                
                connection = connection + 1
                
                if oneline == 1:
                    
                    Condition.append('n' + nodenested + ' ' + valueline + ' ' + str(connection))
                    
        elif ('if ' in nextline or 'if(' in nextline or ('if (' in nextline and ')' in nextline)) and 'else' not in nextline :
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
            indent1 = 0
            nextlinelist = list(nextline)
            
            for value in nextlinelist:
                if value == '\t':
                    indent1 = indent1 + 8
                elif value == ' ':
                    indent1 = indent1 + 1
                elif value != ' ':
                    break
            if indent1 <= indentcount:
                stop = 1
                
            elif indentcount < indent1:
                Nodeinfo1 = []
                
                nodenested = str(node) + ',0'
                
                Nodeinfo1, index3, nodestr = nestedifelsecondition(lines, index4+i , nodenested, Nodeinfo1, Connection)
                nodestr1 = nodestr.split(',')[0]
                node = int(nodestr1)
                i = index3 - index4
                for nodeflow in Nodeinfo1:
                    if isinstance(nodeflow, str):
                        
                        
                        Condition.append(nodeflow)
                        nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
        
        elif 'else if' in nextline:
            
            values = nextline.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                values, valueline = onelinecondition(values)
                line = ' '.join(values)
                               
            line7 = cleanlines(nextline)
            line8 = line7.split()
            if '&&' in values or '||' in values or '&' in values:
                Condition1 = []
                if '&&' in line7:
                    line10 = line7.split('&&')
                if '&' in line7:
                    line10 = line7.split('&')
                for ii, instance1 in enumerate(line10):
                    if '||' in instance1:
                        instance2 = instance1.split('||')
                        line10.pop(ii)
                        for newitem in instance2:
                            line10.insert(ii, newitem)
                for instance in line10:
                    if '==' in instance or '>=' in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        continue
                    elif '~' in instance or '!' in instance:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        Condition1.append(instance.replace('~','').replace('!','') + ' == 0')
                    else:
                        instance = instance.replace(' ','').replace('(','').replace(')','')
                        Condition1.append(instance + ' == 1')
                for index1, elements in enumerate(line8):
                    if '&&' == elements or '||' == elements:
                        continue
                    if '==' in elements:
                        continue
                    for replacement in Condition1:
                        if elements.replace('~','').replace('!','').replace('(','').replace(')','') in replacement:
                            line8[index1] = line8[index1].replace(elements, replacement)
                
                line8 = ' '.join(line8).replace('(','').replace(')','')
                line9 = line8.replace('&&',' and ')
                line10 = line9.replace('||',' or ')
                line10 = line10.replace('&',' and ').replace('|', ' or ')
                Connection = 0
                
                node = node + 1
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + line10 + ' '+ str(Connection))
                
                i = i + 1
                nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
            else:
                line10 = line7.replace('(','').replace(')','')
                line10 = line10.replace(' ','')
                if '==' in line10 or '>=' in line10:
                    line8 = line10
                elif '~' in line10:
                    line8 = line10.replace('~','') + ' == 0'
                else:
                    line8 = line10 + ' == 1'
                Connection = 0
                node = node + 1
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + line8 + ' '+ str(Connection))
                
                i = i + 1
                nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
                
            if oneline == 1:
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + valueline + ' '+ str(Connection))
                node = node + 1
            
            if ('if ' in nextline or 'if(' in nextline) and 'else' not in nextline or (('if(' in nextline and ')' in nextline)) :
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
                indent1 = 0
                nextlinelist = list(nextline)
                
                for value in nextlinelist:
                    if value == '\t':
                        indent1 = indent1 + 8
                    elif value == ' ':
                        indent1 = indent1 + 1
                    elif value != ' ':
                        break
                if indent1 <= indentcount:
                    stop = 1
                elif indentcount < indent1:
                    Nodeinfo1 = []
                    
                        
                        
                    nodenested = str(node) + ',0'
                    Nodeinfo1, index3, nodestr = nestedifelsecondition(lines, index4+i, nodenested, Nodeinfo1, Connection)
                    
                    nodestr1 = nodestr.split(',')[0]
                    node = int(nodestr1)
                    
                    
                    i = index3 - index4
                    for nodeflow in Nodeinfo1:
                        if isinstance(nodeflow, str):
                            
                            
                            Condition.append(nodeflow)
                            
        elif 'else' in nextline and 'if' not in nextline:
            
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
            Connection = 0
            node = node + 1
            
            i = i + 1
            nextline = lines[index4+i]
            
            values = nextline.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                values, valueline = onelinecondition(values)
                line = ' '.join(values)
            
            Connection = Connection + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
            if ('if ' in nextline or 'if(' in nextline) and 'else' not in nextline or (('if(' in nextline and ')' in nextline) ) :
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
                indent1 = 0
                nextlinelist = list(nextline)
                
                for value in nextlinelist:
                    if value == '\t':
                        indent1 = indent1 + 8
                    elif value == ' ':
                        indent1 = indent1 + 1
                    elif value != ' ':
                        break
                
                if indent1 <= indentcount:
                    stop = 1
                    
                elif indentcount < indent1:
                    Nodeinfo1 = []
                    
                    nodenested = str(node) + ',0'
                    Nodeinfo1, index3, nodestr = nestedifelsecondition(lines, index4+i, nodenested, Nodeinfo1, Connection)
                    nodestr1 = nodestr.split(',')[0]
                    node = int(nodestr1)
                    
                    
                    i = index3 - index4
                    for nodeflow in Nodeinfo1:
                        if isinstance(nodeflow, str):
                            
                            Condition.append(nodeflow)
                    
                    nextline = lines[index4 + i]
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    
            if oneline == 1:
                
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + valueline + ' '+ str(Connection))
                
            i = i + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
          
        elif ('<=' in nextline or ' = ' in nextline) and '?' not in nextline:
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            nextline9 = cleanlines(nextline)
            nextline9 = nextline9.replace(' ','').replace(';','').replace('`','')
            if 'if' in lines[index4+i-1] or 'else' in lines[index4+i-1]:
                Connection = 0
            
            if '<=' in nextline9:
                nextline9 = nextline9.replace('<=',' <= ')
            if '=' in nextline9 and '<=' not in nextline9:
                nextline9 = nextline9.replace('=',' = ')
            Connection = Connection + 1
            
            Condition.append('n' + str(node)+ ',0'  + ' ' + nextline9 + ' ' + str(Connection))
            i = i + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
        elif ('<=' in nextline or ' = ' in nextline) and '?' in nextline:

            
            
            nextline = (nextline.replace('\n','').replace('\t',''))
            
            while '<=' not in lines[index4+i+1] and ' = ' not in lines[index4+i+1] and 'else ' not in lines[index4+i+1] and 'if ' not in  lines[index4+i+1] and 'assign' not in lines[index4+i+1] and '//' not in lines[index4+i+1] and ';' not in lines[index4+i+1] and 'end' not in lines[index4+i+1]:
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                 
                nextline=nextline.replace('\n','')
                nextline = (nextline)+lines[index4+i+1].replace('\t','').replace('\n','')
                
                i=i+1
                nextline = lines[index4+i]
            if ';' in nextline and ' = ' not in nextline and '<=' not in nextline and 'else ' not in nextline and 'if ' not in  nextline and 'assign' not in nextline and '//' not in nextline and ';' not in nextline and 'end' not in nextline:
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                
                nextline=nextline.replace('\n','')
                nextline = (nextline)+lines[index4+i+1].replace('\t','').replace('\n','')
                
                i=i+1

            values = nextline.split()
            for vals in values:
                if (vals == '=' or vals == '<=') and '==' != vals:
                    oneline = 1
            if oneline == 1:
                
                
                nodenested, assignmentstatements = assignmentif(nextline, 0, assignmentstatements, 1, str(node)+ ',0')
                
            
            
            if 'if' in lines[index4+i-1] or 'else' in lines[index4+i-1]:
                Connection = 0
            
            Connection = Connection + 1
            
            for assignstmts in assignmentstatements:
                for assignstmt in assignstmts:
                    
                    
                    
                    
                    Condition.append(assignstmt)
                
            i = i + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
        
        elif checkb == 1:
            
            nextline3 = nextline.replace(' ','').replace('\n','').replace('\t','')
            Condition2 = Condition2 + ' ' + nextline3 
            if '}' in nextline:
                checkb = 0
                Condition2 = Condition2 + ' ' + str(Connection)
                
                Condition.append(Condition2)
        
        else:
            
            if cleanlines(nextline) == '' or 'else' in nextnextline :
                i = i + 1
                nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                continue
            if cleanlines(line) != '':    
                indent2 = 0
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                nextlinelist = list(nextline)
                for value in nextlinelist:
                    if value == '\t':
                        indent2 = indent2 + 8
                    elif value == ' ':
                        indent2 = indent2 + 1
                    elif value != ' ':
                        break
                if indent2 <= indentcount:
                
                    stop = 1
                    continue
                else:
                    i = i + 1
                    nextline = lines[index4 + i]
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
            else:
                i = i + 1
                
                nextline = lines[index4 + i]
                
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
    if Condition != []:
        
        for j in Condition:           
            Nodeinfo.append(j)
        
    
    return Nodeinfo, index4 + i , node

def nodeflowadd(Condition, nodeflows, thisflow):
    for nodeflows1 in nodeflows: 
        if isinstance(nodeflows ,str):
            newflow =  thisflow + int(nodeflows.split()[len(nodeflows.split())-1])
            nodeflows1 = nodeflows.replace(nodeflows[len(nodeflows)-1], str(newflow))
            nodeflows1 = ' '.join(nodeflows1.split())
            
            Condition.append(nodeflows1)
            
        else:
            Condition = nodeflowadd(Condition, nodeflows1, thisflow)
            
    return Condition
   
def cleanlines(line):
    line1 = line.replace('end','')
    if 'if(' in line or 'if ' in line or 'if (' in line:
        line2 = line1.replace('if ','')
        line2 = line2.replace('if(','')
        line2 = line2.replace('if (','')
    else:
        line2 = line1
    line3 = line2.replace('else','')
    line4 = line3.replace('begin','')
    line5 = line4.replace('\t','')
    line6 = line5.replace('\n','')
    line7 = line6.replace('\r','')
    if '//' in line7:
        line7 = line7.split('//')[0]
    return line7

def onelinecondition(values):
    x = []
    x1 = []
    
    for index, val in enumerate(values):
        if ':' in val and 'if' not in values:
            end = val.find("[")
            valu = val[:end]
            x.append(valu)
            continue
        x.append(val)
        if val == '<=' or val == '=':
            x.pop()
            x.pop()
            break
    for index1, val in enumerate(values):
        if index1 < index - 1:
            continue
        x1.append(val)
    x1 = ' '.join(x1)
    if '&&' in x1 or '||' in x1 or '&' in x1 or '|' in x1:
        x1 = x1.replace('&&',' and ').replace('||',' or ').replace('&',' and ').replace('|', ' or')
    if '<=' in x1:
        x1 = x1.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') 
    elif '=' in x1 and '==' not in x1:
        x1 = x1.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
    return x, x1

def casestatement(lines, index4, node, Nodeinfo, ifcond):
    case = 1
    line = lines[index4]
    linevalue = line.split('(')
    variable = linevalue[1].replace(')','').replace('\n','')
    i = 1
    nextline = lines[index4 + i]
    if '//' in nextline:
        nextline = nextline.split('//')[0]
    indentcount = 0
    linelist = list(lines[index4])
    for indent in linelist:
        if indent == ' ':
            indentcount = indentcount + 1
        elif indent != ' ':
            break
    Condition = []
    Connection = 0
    default = 0
    read = 0
    checkb = 0
    
    while 'endcase' not in nextline:
        nextline = nextline.replace('\n','')
        if '//' in nextline:
            nextline2 = nextline.split('//')
            nextline = nextline2[0].replace('\n','')
        
        if nextline.replace(' ','').replace('\t','').replace('\n','') == 'end':
            i = i + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            continue
        nextline1 = nextline.split()
        nextline = ' '.join(nextline1)
        if '//' in nextline:
            nextline2 = nextline.split('//')
            nextline = nextline2[0].replace('\n','')                                
            if 'end' in nextline:
                nextline = nextline.replace(' ','')
                if nextline == 'end':
                    i = i + 1
                    nextline = lines[index4 + i]
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    continue
        if nextline == '':
            i = i + 1
            nextline = lines[index4 + i]
            continue
        indent1 = 0
        variable1 = []
        
        nextlinevalue = list(nextline)
        if 'default' in nextline:
            default = 1
            if Condition!=[]:
                Nodeinfo.append(Condition)
            
            
            assignment = nextline.split(':')
            assignment1 = assignment[1].split()
            
            nextline3 = ' '.join(assignment1)
            if nextline3.replace(' ','') == 'begin' or nextline3.replace(' ','') == '':
                read = 1
                i = i + 1
                nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                continue
            if "'0" in nextline3 or "'1" in nextline3:
                nextline3 = nextline3.replace("'",'')
            if '<=' in nextline3:
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
            elif '=' in nextline3:
                
                Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
               
                Nodeinfo.append(Condition)
                
                node = node + 1
                i = i + 1
                nextline = lines[index4 + i]
                if '//' in nextline:
                    nextline = nextline.split('//')[0]
                continue
        elif 'if' in nextline and 'else' not in nextline and ':' not in nextline:
            
            if '//' in lines[index4+i]:
                lines[index4+i] = lines[index4+i].split('//')[0]
            nextlinecheck = lines[index4 + i]
            x = i
            while ':' not in nextlinecheck and 'endcase' not in nextlinecheck:
                x = x + 1
                nextlinecheck = lines[index4 + x]
            
                
            Nodeinfo1 = []
            Nodeinfo1, index3, nodestr = nestedifelsecondition(lines, index4 + i, str(node), Nodeinfo1, case)
            
            nodestr1 = nodestr.split(',')[0]
            node = int(nodestr1)
            

            i = index3 - index4
            
            for nodeflow in Nodeinfo1:
                for nodeflows in nodeflow: 
                    if isinstance(nodeflows ,str):
                        Condition.append(nodeflows)
                        
            nextline = lines[index4 + i]

        elif ':' in nextline and ('<='  in nextline or '=' in nextline or 'if' in nextline or 'begin' in nextline):
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            if Condition != []:
                Nodeinfo.append(Condition)
                
            
            if nextline.count(':') > 1:
                assignment1 = nextline.split(':')
                
                assignment1.pop(0)
                
                assignment2 = ':'.join(assignment1)
                assignment = ['',assignment2]
            elif nextline.count(':') == 1:
                assignment1 = nextline.split(':')[0].replace(' ','')
                Connection = 0
                Nodeinfo.append('n' + str(node)+ ',0'  +' ' + variable + ' == ' + assignment1 + ' ' + str(Connection))
                node = node + 1
            else:
                assignment = nextline.split(':')
        elif '<=' in nextline or '=' in nextline:
            assignment = nextline.split()
            nextline3 = ' '.join(assignment)
            if '<=' in nextline3:
                Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
            elif '=' in nextline3:
                nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                if ' <=  <= ' in nextline3:
                    nextline3 = nextline3.replace(' <=  <= ', ' == ')
                Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3 + ' ' + str(Connection))
                                
            node = node + 1
        elif checkb == 1:
            nextline3 = nextline.replace(' ','').replace('\n','').replace('\t','')
            Condition2 = Condition2 + ' ' + nextline3 
            if '}' in nextline:
                checkb = 0
                Condition2 = Condition2 + ' ' + str(Connection)
                Condition.append(Condition2)
        for val in nextlinevalue:
            if val == ' ':
                indent1 = indent1 + 1
            else:
                variable1.append(val)
            
                equal = ''.join(variable1)
            if val ==':' and ('`' in nextline or "'h" in equal or "'b" in equal):
                equal = equal.replace(':','')
                nextline3 =  variable + ' == ' + equal
                Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                
                Connection = Connection + 1
                node = node + 1
                if len(nextline.split()) < 2:
                    break
                elif assignment[1] == '' or assignment[1].replace(' ','') == 'begin':
                    break
                elif 'if' in assignment[1]:
                    if '//' in lines[index4+i]:
                        lines[index4 + i] = lines[index4 + i].split('//')[0]
                    nextlinecheck = lines[index4 + i]
                    x = i
                    while (':' not in nextlinecheck or ('`' not in nextlinecheck and "'h" not in nextlinecheck and "'b" not in nextlinecheck )) and 'endcase' not in nextlinecheck:
                        x = x + 1
                        nextlinecheck = lines[index4 + x]
            
                    
                    Nodeinfo1 = []
                    Nodeinfo1, index3, node = ifelsecondition(lines, index4 + i, node, Nodeinfo1, case)
                    
                    i = index3 - index4

                    for nodeflow in Nodeinfo1:
                        if isinstance(nodeflow, str):
                            Condition.append(nodeflow)
                        
                    i = x
                    nextline = lines[index4 + i]
                    break
                else:
                    assignment1 = assignment[1].split()
                    assignment1 = ' '.join(assignment1)
                    nextline3 = assignment1.replace(';','').replace('`','')
                    if ("'0" in nextline3 or "'1" in nextline3) and ':' not in nextline3:
                        nextline3 = nextline3.replace("'",'')
                        
                        if '<=' in nextline3:
                            Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        elif '=' in nextline3:
                            Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        node = node + 1
                        break
                    elif '{' in nextline3 and '}' not in nextline3:
                        if '<=' in nextline3:
                            Condition2 = 'n' + str(node)+ ',0'  + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','')
                        elif '=' in nextline3:
                            Condition2 = 'n' + str(node)+ ',0'  + ' ' + nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                        checkb = 1
                        node = node + 1
                        break
                    else:
                        if '<=' in nextline3:
                            
                            Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        elif '=' in nextline3:
                            
                            nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                            if ' <=  <= ' in nextline3:
                                nextline3 = nextline3.replace(' <=  <= ', ' == ')
                            Condition.append('n' + str(node)+ ',0'  + ' ' + nextline3 + ' ' + str(Connection))
                            
                        node = node + 1
                        break
        i = i + 1
        nextline = lines[index4 + i]
    
        if default == 0 or (default == 1 and read == 1):
            
            for allval in Condition:
                Nodeinfo.append(allval)
                
            Condition = []

        
     
    return Nodeinfo, index4+i, node

def nestedcasestatement(lines, index4, node, Nodeinfo, notnested):
    
    case = 0
    line = lines[index4]
    if '//' in line:
        line = line.split('//')[0]
    if'/*' in line and '*/' in line:
        start =line.find('/*')+len('/*')
        end = line.find('*/')
        comment = line[start-2:end+2]
        line = line.replace(comment,'')
       
    linevalue = line.split('(')
   
    variable = linevalue[1].replace(')','').replace('\n','')
    i = 0
    
    nextline = lines[index4 + i]
    if '//' in nextline:
        nextline = nextline.split('//')[0]
    indentcount = 0
    linelist = list(lines[index4])
    for indent in linelist:
        if indent == ' ':
            indentcount = indentcount + 1
        elif indent != ' ':
            break
    Condition = []
    Connection = 0
    default = 0
    read = 0
    checkb = 0
    breakpoint
    while 'endcase' not in nextline:
                
        nextline = nextline.replace('\n','').replace('`','')
        if '//' in nextline:
            nextline2 = nextline.split('//')
            nextline = nextline2[0].replace('\n','')
        
        if nextline.replace(' ','').replace('\t','').replace('\n','') == 'end':
            i = i + 1
            nextline = lines[index4 + i]
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            continue
        nextline1 = nextline.split()
        nextline = ' '.join(nextline1)

        if '//' in nextline:
            nextline2 = nextline.split('//')
            nextline = nextline2[0].replace('\n','')                                
            if 'end' in nextline:
                nextline = nextline.replace(' ','')
                if nextline == 'end':
                    i = i + 1
                    nextline = lines[index4 + i]
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    continue
        
        if nextline == '':
            i = i + 1
            nextline = lines[index4 + i]
            continue
        
        indent1 = 0
        variable1 = []
        
        nextlinevalue = list(nextline)
        
        if 'default' in nextline:
            default = 1
            nextlinecheck = lines[index4 + i].replace('default','')
            if nextlinecheck[1]==';' or nextlinecheck[1]==' ':
                
                i = i+1
                nextline = lines[index4 + i]
                
                continue
            else:    
                
                assignment = nextline.split(':')
                assignment1 = assignment[1].split()
                
                nextline3 = ' '.join(assignment1)
                Connection = 0
                if nextline3.replace(' ','') == 'begin' or nextline3.replace(' ','') == '':
                    read = 1
                    i = i + 1
                    nextline = lines[index4 + i]
                    if '//' in nextline:
                        nextline = nextline.split('//')[0]
                    
                    continue
                elif '<=' in nextline3 or '=' in nextline3:
                    Connection = Connection + 1
                    if '<=' in nextline3:
                        
                        Condition.append('n' + node + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                    elif '=' in nextline3:
                        
                        nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                        if ' <=  <= ' in nextline3:
                            nextline3 = nextline3.replace(' <=  <= ', ' == ')
                        
                        Condition.append('n' + node + ' ' + nextline3 + ' ' + str(Connection))    

        elif ('if' in nextline and 'else' not in nextline and ':' not in nextline):
            
            if '//' in lines[index4+i]:
                lines[index4+i] = lines[index4+i].split('//')[0]
            nextlinecheck = lines[index4 + i]
            x = i
            while ':' not in nextlinecheck and 'endcase' not in nextlinecheck:
                x = x + 1
                nextlinecheck = lines[index4 + x]
            
                
            Nodeinfo1 = []
            
            Nodeinfo1, index3, node = nestedifelsecondition(lines, index4 + i, str(node), Nodeinfo1, case)
            
            
            
            i = index3 - index4 - 1
            
            for nodeflows in Nodeinfo1:
                if isinstance(nodeflows ,str):
                    Condition.append(nodeflows)
                    
            nextline = lines[index4 + i]

        elif ':' in nextline and ('<='  in nextline or '=' in nextline or 'if' in nextline or 'begin' in nextline):
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            if Condition != []:
                Nodeinfo.append(Condition)
                
            
            if nextline.count(':') > 1:
                end = nextline.rfind(":")
                assignment1 = nextline[:end]
                
                assignment1 = nextline.split(':')
                
                assignment1.pop(0)
                
                assignment2 = ':'.join(assignment1)
                assignment = ['',assignment2]
            elif nextline.count(':') == 1:
                end = nextline.rfind(":")
                assignment1 = nextline[:end]
                
                assignment1 = nextline.split(':')[0].replace(' ','')
                Connection = 0
                nextnode = node.split(',')
                    
                if len(nextnode) == 1:
                    if notnested == 1:
                        node = node + ',0'
                    else:    
                        node = node + ',0,0'
                else:
                    node = ''
                    for index, values in enumerate(nextnode):
                        
                        if (index == len(nextnode)-1):
                            values = int(values) + 1
                            node = node + str(values)
                        else:
                            node = node + str(values) + ','
                

                Nodeinfo.append('n' + str(node) +' ' + variable + ' == ' + assignment1 + ' ' + str(Connection))
                
                
                
            else:
                assignment = nextline.split(':')
            if '<=' in nextline or '=' in nextline:
                start = nextline.find(":") + len(":")
                assignment1 = nextline[start:]
                
                assignment = assignment1.split()
                nextline3 = ' '.join(assignment)
                Connection = Connection + 1
                if '<=' in nextline3:
                    
                    Condition.append('n' + node + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                elif '=' in nextline3:
                    
                    nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                    if ' <=  <= ' in nextline3:
                        nextline3 = nextline3.replace(' <=  <= ', ' == ')
                    
                    Condition.append('n' + node + ' ' + nextline3 + ' ' + str(Connection))
                                  
                
                

        elif ':' in nextline:
            
            if '//' in nextline:
                nextline = nextline.split('//')[0]
            
            if Condition != []:
                Nodeinfo.append(Condition)
                
            
            if nextline.count(':') > 1:
                assignment1 = nextline.split(':')
                
                assignment1.pop(0)
                
                assignment2 = ':'.join(assignment1)
                assignment = ['',assignment2]
            elif nextline.count(':') == 1:
                assignment1 = nextline.split(':')[0].replace(' ','')
                Connection = 0
                nextnode = node.split(',')
                    
                if len(nextnode) == 1:
                    if notnested == 1:
                        node = node + ',0'
                    else:    
                        node = node + ',0,0'
                else:
                    node = ''
                    for index, values in enumerate(nextnode):
                        
                        if (index == len(nextnode)-1):
                            values = int(values) + 1
                            node = node + str(values)
                        else:
                            node = node + str(values) + ','
                

                Nodeinfo.append('n' + str(node) +' ' + variable + ' == ' + assignment1 + ' ' + str(Connection))
                
                
                
            else:
                assignment = nextline.split(':')
        
        elif '<=' in nextline or '=' in nextline:
            assignment = nextline.split()
            nextline3 = ' '.join(assignment)
            nextnode = node.split(',')
                
            Connection = Connection + 1
            if '<=' in nextline3:
                
                Condition.append('n' + node + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
            elif '=' in nextline3:
                
                nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                if ' <=  <= ' in nextline3:
                    nextline3 = nextline3.replace(' <=  <= ', ' == ')
                
                Condition.append('n' + node + ' ' + nextline3 + ' ' + str(Connection))
                       
            
        
        elif checkb == 1:
            nextline3 = nextline.replace(' ','').replace('\n','').replace('\t','')
            Condition2 = Condition2 + ' ' + nextline3 
            if '}' in nextline:
                checkb = 0
                Condition2 = Condition2 + ' ' + str(Connection)
                
                Condition.append(Condition2)
        
        for val in nextlinevalue:
            if val == ' ':
                indent1 = indent1 + 1
            else:
                variable1.append(val)

                equal = ''.join(variable1)
            if val ==':' and ("'h" in equal or "'b" in equal):
                equal = equal.replace(':','')
                nextline3 =  variable + ' == ' + equal
                
                Condition.append('n' + str(node) + ' ' + nextline3.replace(';','').replace('`','') + ' ' + str(Connection))
                Connection = Connection + 1
                nextnode = node.split(',')
                node = ''
                for index, values in enumerate(nextnode):
                    
                    if (index == len(nextnode)-1):
                        values = int(values) + 1
                        node = node + str(values)
                    else:
                        node = node + str(values) + ','
            
                if len(nextline.split()) < 2:
                    break
                elif assignment[1] == '' or assignment[1].replace(' ','') == 'begin':
                    break
                elif 'if' in assignment[1]:
                    
                    if '//' in lines[index4+i]:
                        lines[index4 + i] = lines[index4 + i].split('//')[0]
                    nextlinecheck = lines[index4 + i]
                    x = i
                    while (':' not in nextlinecheck or ('`' not in nextlinecheck and "'h" not in nextlinecheck and "'b" not in nextlinecheck )) and 'endcase' not in nextlinecheck:
                        x = x + 1
                        nextlinecheck = lines[index4 + x]
            
                    
                    Nodeinfo1 = []
                    Nodeinfo1, index3, node = nestedifelsecondition(lines, index4 + i, node, Nodeinfo1, case)
                    
                    i = index3 - index4

                    for nodeflow in Nodeinfo1:
                        if isinstance(nodeflow, str):
                            
                            Condition.append(nodeflow)
                        
                    i = x
                    nextline = lines[index4 + i]
                    break
                else:
                    assignment1 = assignment[1].split()
                    assignment1 = ' '.join(assignment1)
                    nextline3 = assignment1.replace(';','').replace('`','')
                    if ("'0" in nextline3 or "'1" in nextline3) and ':' not in nextline3:
                        nextline3 = nextline3.replace("'",'')
                        
                        if '<=' in nextline3:
                            
                            Condition.append('n' + str(node) + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        elif '=' in nextline3:
                            
                            Condition.append('n' + str(node) + ' ' + nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        node = node + 1
                        break
                    elif '{' in nextline3 and '}' not in nextline3:
                        if '<=' in nextline3:
                            Condition2 = 'n' + str(node) + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','')
                        elif '=' in nextline3:
                            Condition2 = 'n' + str(node) + ' ' + nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                        checkb = 1
                        node = node + 1
                        break
                    else:
                        if '<=' in nextline3:
                            
                            Condition.append('n' + str(node) + ' ' + nextline3.replace('<=',' <= ').replace('`','').replace(';','').replace('`','') + ' ' + str(Connection))
                        elif '=' in nextline3:
                            
                            nextline3 = nextline3.replace('=',' <= ').replace('`','').replace(';','').replace('`','')
                            if ' <=  <= ' in nextline3:
                                nextline3 = nextline3.replace(' <=  <= ', ' == ')
                            
                            Condition.append('n' + str(node) + ' ' + nextline3 + ' ' + str(Connection))
                            
                        nextnode = node.split(',')
                        node = ''
                        for index, values in enumerate(nextnode):
                            
                            if (index == len(nextnode)-1):
                                values = int(values) + 1
                                node = node + str(values)
                            else:
                                node = node + str(values) + ','
                        break
        i = i + 1
        nextline = lines[index4 + i]
    
        if default == 0 or (default == 1 and read == 1):
            
            for allval in Condition:
                Nodeinfo.append(allval)
                
            Condition = []

    else:
        
        node = node.split(',')[0]
        node = int(node)
        return Nodeinfo, index4+i, node    
    
    return Nodeinfo, index4+i, node

def RealiCFG(flpath,file1):
    Module = []
    Nodeinfo1 = []
    Condition = []
    Nodeinfo = []
    State = []
    i = 0
    node = 0
    ifcond = 0
    case = 0
    modulelist2 = []
    parameter = []
    index3 = 0
    with open(flpath + file1) as fl:
        
        for block in fl:
            
            if '.v' in block or '.sv' in block:
                Connection = 0
                with open(flpath + block.replace('\n','')) as fl1: 
                    lines = fl1.readlines()
                    fl1.close()
                    AlwaysValue = []
                formark = 0
                indentref = 0
                indent = 0
                
                indentmark = 0
                check = 0
                for index4,line in enumerate(lines):
                    if '//' in line:
                        line = line.split('//')[0]
                    Nodeinfo = []
                    connection = 0
                        
                    if index3>index4:
                        continue
                    
                    if 'module' in line and 'endmodule' not in line and 'module' == line.split()[0]:
                        check = 1
                        themodule = line.split()[1]
                        themodule1 = themodule.split('(')[0]
                        modulelist2.append(themodule1 + ' ')
                        continue

                    
                    if 'endmodule' in line:
                        parameter = []
                        check = 0
                        for items in Nodeinfo1:
                            
                            if type(items) is list:
                                for item in items:
                                    
                                    modulelist2.append(item)

                            else:
                                
                                modulelist2.append(items)
                        continue
                    
                    if check == 0:
                        continue
                    
                    if 'parameter' in line or 'localparam ' in line:
                        line = line.replace('parameter', '').replace('localparam ', '')
                        
                        line1 = line.split()
                       
                        for ind, things in enumerate(line1):
                            if '=' in line1[ind - 1]:
                                things = things.replace(';','').replace('`','')
                                para = para + ' ' + things
                                break
                            elif '=' in line1[ind + 1]:
                                para = things
                            
                        parameter.append(para)
                    

                    elif 'always' in line and '@' in line:
                        
                        Nodeinfo, index3, node = clockedge(lines, index4, node, Nodeinfo, case)
                        
                    elif (('assign' in line and '=' in line) or '<=' in line) and '?' in line:
                        
                        if ';' not in line:
                            if '//' in line:
                                line1 = line.split('//')
                                line = line1[0]
                            linegen = line.replace('\n','')
                            nex = 1
                            nexline = lines[index4+nex]
                            
                            while ';' not in nexline:
                                
                                if '//' in nexline:
                                    line1 = nexline.split('//')
                                    line = line1[0]
                                else:
                                    line = nexline.replace('\n','')
                                linegen = linegen + line.replace('\n','')
                                nex = nex + 1
                                nexline = lines[index4+nex]
                                if '//' in line:
                                    nexline = nexline.split('//')[0]
                            else:  
                                if '//' in nexline:
                                    line1 = nexline.split('//')
                                    line = line1[0]
                                else:
                                    line = nexline.replace('\n','')
                                linegen = linegen + line.replace('\n','').replace(' ','').replace('\t','')
                                
                                
                                node, Nodeinfo = assignmentif(linegen, node, Nodeinfo, 0, '')
                        else:
                            node, Nodeinfo = assignmentif(line, node, Nodeinfo, 0, '')
                    
                    elif (('assign ' in line or '=' in line) or '<=' in line) and '?' not in line and 'parameter' not in line and 'param ' not in line:
                        
                        
                        
                        nex=0
                        if ';' not in line:
                            if '//' in line:
                                line1 = line.split('//')
                                line = line1[0]
                            nex = 1
                            nexline = lines[index4+i+nex]
                            
                            while ';' not in nexline:
                                
                                
                                if '//' in nexline:
                                    line1 = nexline.split('//')
                                    line = line1[0]
                                else:
                                    nexline = nexline.replace('\n','')
                                line = line + nexline.replace('\n','')
                            
                                nex = nex + 1
                                nexline = lines[index4+i+nex]
                                
                                if '//' in line:
                                    nexline = nexline.split('//')[0]
                            else:  
                                if '//' in nexline:
                                    line1 = nexline.split('//')
                                    line = line+line1[0]
                                else:
                                    line = line+nexline.replace('\n','')
                            
                        
                        

                        i = i+nex
                        
                        line = (line.replace('\n','').replace('\t',''))
                        
                        values = line.split()
                        for vals in values:
                            if (vals == '=' or vals == '<=') and '==' != vals:
                                oneline = 1
                        if oneline == 1:
                            
                            values, valueline = onelinecondition(values)
                            line = ' '.join(values)
                            connection = connection + 1
                            node = node + 1
                            
                            Nodeinfo.append('n' + str(node)+',0'+ ' ' + valueline + ' ' + str(connection))
                    
                    
                    elif 'if ' in line and ('begin' in line or 'begin' in lines[index4+1]) and 'else' not in line:
                        
                        indent = 0
                        if indentmark == 0:
                            nextlinelist = list(line)
                            indent = 0
                            for value in nextlinelist:
                                if value == '\t':
                                    indent = indent + 8
                                elif value == ' ':
                                    indent = indent + 1
                                elif value != ' ':
                                    break
                            indentmark = 1
                            indentref = indent
                            indent  = 0
                        if indentmark == 1:
                            nextlinelist = list(line)
                            for value in nextlinelist:
                                if value == '\t':
                                    indent = indent + 8
                                elif value == ' ':
                                    indent = indent + 1
                                elif value != ' ':
                                    break
                            
                            if indent<=indentref:
                                
                                Nodeinfo, index3, node = ifelsecondition(lines, index4, node, Nodeinfo, case)
                            i = index3 - index4

                            for nodeflow in Nodeinfo:
                                if isinstance(nodeflow, str):
                                    
                                    Condition.append(nodeflow)
                                    nextline = lines[index4 + i]
                                    
                                    indent = 0
                                else:
                                    indent = 0
                        
                    elif 'if ' in line or ('if(' in line and ')' in line):
                        
                        indent = 0
                        if indentmark == 0:
                            nextlinelist = list(line)
                            for value in nextlinelist:
                                if value == '\t':
                                    indent = indent + 8
                                elif value == ' ':
                                    indent = indent + 1
                                elif value != ' ':
                                    break
                            indentmark = 1
                            indentref = indent
                            indent = 0
                        if indentmark == 1:
                            nextlinelist = list(line)
                            for value in nextlinelist:
                                if value == '\t':
                                    indent = indent + 8
                                elif value == ' ':
                                    indent = indent + 1
                                elif value != ' ':
                                    break
                            if indent<=indentref:
                                Nodeinfo, index3, node = ifelsecondition(lines, index4, node, Nodeinfo, case)
                                
                                indent = 0
                            else:
                                indent = 0
                        
                    elif ('for (' in line or 'for(' in line) and ('//' not in line.split()[0] and '//' not in line.split()[1]):
                       
                        if 'begin' not in lines[index4 + 1]:
                            continue
                        recordNode = []
                        for things in Nodeinfo:
                            recordNode.append(things)
                        formark = 1
                        
                        forline = line.split(';')
                        loopstart = forline[0].replace('for','').replace('(','').replace(' ','').split('=')
                        loopvariable = loopstart[0].replace('int','')
                        for things in parameter:
                            if things.split()[0] in loopstart[1]:
                                loopstart[1] = loopstart[1].replace(things.split()[0],things.split()[1])
                                break
                        try: loopstart[1] = eval(loopstart[1])
                        except: loopstart[1] = 1
                        loopbegin = int(loopstart[1])
                        if '<' in forline[1]:
                            loopend = forline[1].replace(loopvariable,'').replace('<','').replace('=','').replace(' ','')
                        elif '>' in forline[1]:
                            loopend = forline[1].replace(loopvariable,'').replace('>','').replace('=','').replace(' ','')
                        for things in parameter:
                            if things.split()[0] in loopend:
                                loopend = loopend.replace(things.split()[0],things.split()[1])
                                break
                        try:loopend = eval(loopend)
                        except: loopend = 1
                       
                        if 'begin' in lines[index4 + 1]:
                            forbegin = list(lines[index4+1])
                            indentcount = 0
                            for indentx in forbegin:
                                if indentx == ' ':
                                    indentcount = indentcount + 1
                                if indentx == '\t':
                                    indentcount = indentcount + 8
                                else:
                                    break
                    
                    elif 'end' in line and formark == 1:
                        endline = list(line)
                        indentend = 0
                        for indent in endline:
                            if indent == ' ':
                                indentend = indentend + 1
                            if indent == ' ':
                                indentend = indentend + 8
                            else:
                                break
                        if indentend == indentcount:
                            formark = 0
                            
                            if Nodeinfo != recordNode:
                                loopNode = []
                                changenode = 0
                                check = 0
                                
                                if loopend >= loopbegin:
                                    loop = loopend - loopbegin
                                elif loopbegin > loopend:
                                    loop = loopbegin - loopend
                                for i in range(loop):
                                    for noderow in Nodeinfo:
                                        if noderow in recordNode:
                                            continue
                                        
                                        elif noderow not in recordNode and check == 0:
                                            changenode = int(noderow[0].split()[0].replace('n',''))
                                            check = 1
                                        loopcondition = []
                                        for node1 in noderow:
                                            newnode =node1.replace(loopvariable + ' ',str(i) + ' ')
                                            for things in parameter:
                                                if things.split()[0] in newnode and '<=' not in newnode:
                                                    newnode = newnode.replace(things.split()[0],things.split()[1])
                                                    break
                                            
                                            newnode = newnode.split()  
                                            
                                            
                                            newnode1 = ' '.join(newnode)
                                                
                                            newnode1 = newnode1.replace(newnode[0],'n'+str(changenode))
                                            loopcondition.append(newnode1)
                                            changenode = changenode + 1  
                                        loopNode.append(loopcondition)
                                
                                for noderow in loopNode:
                                    if '==' in noderow[0]:
                                        noderow1 = noderow[0].split()
                                        noderow1.pop()
                                        noderow1.pop(0)
                                        try:xx = eval(' '.join(noderow1))
                                        except: xx = True
                                        
                                        if not xx:
                                            continue
                                    
                                    recordNode.append(noderow)
                                
                                Nodeinfo = recordNode  
                    
                    elif 'case' in line and 'endcase' not in line and '//' not in line and ('case(' in line or 'case (' in line):
                        
                        node = node+1
                        Nodeinfo, index3, node = nestedcasestatement(lines, index4, str(node), Nodeinfo, 1)
                        
                    
                    if Nodeinfo!=[]:
                        
                        for nodeval in Nodeinfo:    
                            Nodeinfo1.append(nodeval)
                       
    return Nodeinfo1, modulelist2

def nodelist(node, nodeavail):
    
    if type(node) is list:
        for node1 in node:
            nodeavail = nodelist(node1, nodeavail)
        return nodeavail
    elif type(node) is str:
        nodeavail.append(node.split()[0])
        
        return nodeavail


predecessors3 = []
nodetoreach = []

flpath1 = 'RTL/All_RTL/'
with open(flpath1 + "RTLFiles.txt") as fl:
        
        moduleline = fl.readlines()
        fl.close()

for index, i in enumerate(moduleline):
    modulenumber = index+ 1

Always = []
Allmodules = []

for i in range(modulenumber):
    file2 = "RTLFiles_" + str(i) + ".txt"
    
    Nodeflowx1, Nodeflowx = RealiCFG(flpath1, file2)
    print(Nodeflowx)
    
inputkeys = []
inputvals = []
firstnode = input("Choose which node to reach: " )
conditioncheck = input("Variable to check: ")
with open('C://rtlContest/RTL-CFG/input_node.txt', 'w') as f:
    for i in Nodeflowx:
        if conditioncheck.split()[0] in i and firstnode in i:
            i.split()
            f.write("%s %s\n" % (i.split()[1], i.split()[3]))

path, inputvals, inputkeys = EdgeRealignment(firstnode, Nodeflowx, 1, [])

print(path)
with open('C://rtlContest/RTL-CFG/input_value.txt', 'w') as f:
    for i,value in enumerate(inputkeys):
        for j,val in enumerate(inputvals):
            if i==j:
                f.write("%s %s\n" % (val, value))
