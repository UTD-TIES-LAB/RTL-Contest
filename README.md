# RTL-Contest
Concolic Testing on RTL for Detecting Security Vulnerabilities

## Getting Started
Prerequisites:<br />
•	Icarus Verilog <br />
•	Python 3.8<br />

## Roadmap
•	Create a directory \RTL\RTLVerilog and add the Verilog files to the folder RTLVerilog.<br />
•	Execute the module_track python file.<br />
•	This copies the files to a folder All_RTL in the RTL folder.<br />
•	Execute the CFG-Path Specification python file.<br />
•	This creates a list of nodes with every condition and assignment statements.<br />
•	Select a targetnode for the path specification and provide the target statement.<br />
•	This generates the path specification along with the input values required to reach the node.<br />
•	The inputvalues are stored in the file input_values.txt.<br />
•	In the concolic_testing python file, add the clock signals to the variable togglevariables at line 742 and execute the the python file.<br />
•	This creates and executes the template modlue and testbench created for concolic testing. These files will be stored in the folder C:\iverilog<br />
•	In the testcase.txt file, add testcases that have to be verified and run the testcases.py file.<br />
