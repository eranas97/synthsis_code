#include "dpi_types.h"

int c_CarWaiting()
{
    printf("There's a car waiting on the other side. \n");
	printf("Initiate change sequence ...\n");
	sv_YellowLight();
	sv_WaitForRed();
	sv_RedLight();
	return 0;
}
