#include "dpi_types.h"

void print_int(int int_in)
{
        printf("Just received a value of %d.\n", int_in);
}

void print_logic(svLogic logic_in)
{
	switch (logic_in) 
	{
		case sv_0: printf("Just received a value of logic 0.\n");
			   break;
		case sv_1: printf("Just received a value of logic 1.\n");
			   break;
		case sv_z: printf("Just received a value of logic Z.\n");
			   break;
		case sv_x: printf("Just received a value of logic X.\n");
			   break;
	}
}
