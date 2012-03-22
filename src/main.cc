#include <string>
#include <iostream>
#include <stdlib.h>

#include "execute.h" 

using namespace std;

string inputfilename;
string outputfilename;

void check_args(int argc, char* argv[]) {

	string param;
	bool input = false, output = false;
	int i = 1;
	
	while (i<argc) {
		param = argv[i];
		if (param == "-o") {
			i++;
			outputfilename = argv[i];
			output = true;
		} else if (param == "-i") {
			i++;
			inputfilename = argv[i];
			input = true;
		} else if (param != "-i" && i == 1) {
			inputfilename = argv[i];
			input = true;
		} else {
			cout << "Invalid parameters...\n";
			exit(1);
		}
		i++;
	}
	if (!input) {
		cout << "You must specify a valid input file...\n";
		exit(1);
	}
	if (!output)
		outputfilename = "out.smt";
}

int main(int argc, char* argv[]) {

	execute run;
	
	try {
		check_args(argc, argv);
	} catch (int i) {
		return 1;
	}

	run.exec(inputfilename,outputfilename);
	
	return 0;
}
