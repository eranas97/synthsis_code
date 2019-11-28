###
### Makefile for integrated Drill demo
###
### This demo uses the current directory as its "DRILLROOT"... there is no need to set
### the DRILL_HOME environment variable. You should set the "BROWSER" env variable to
### point to a relatively modern browser (Firefox 3.x or better, if possible).
###
### To run the demo for the first time, or to reset the demo to its original state, type
### "make reload". This will reload the database from scratch and bring up the dashboard.
###
### On subsequent runs, type "make demo" or just "make". This will invoke the dashboard
### without resetting the database (to test and/or demonstrate persistence).
###
### If the configuration is edited manually (config/dashboards.xml), type "make reset"
### to update the database with the modified configuration.
###

# This just brings up the demo dashboard (database must already exist)

demo:			db/drill.umdb
				/usr/bin/env DRILL_HOME= drill -cwd -browse

# This regenerates the database AND brings up the demo dashboard

reload:			realclean demo

# This reloads the entire database from scratch

db/drill.umdb:	config/bugaboo.xml config/bugaboo_data.xml config/subzero.xml config/subzero_data.xml config/dashboards.xml
				drill -cwd -import $?

# This resets the "demo" dashboard configuration to the initial state

reset:
			drill -cwd -import config/dashboards.xml

# This clears the database and reloads the dummy data (taken from dbDemo)

dbDemo:
			drill -cwd -import config/bugaboo.xml
			drill -cwd -import config/bugaboo_data.xml
			drill -cwd -import config/subzero.xml
			drill -cwd -import config/subzero_data.xml

# To view the configuration on stdout

seeconfig:
			drill -cwd -uri '/export/config?type=dashboard&instance=demo&name=config'

# To clean up the demo directory (realclean also deletes the database)

clean:
			/bin/rm -rf *.xml *.svg *.sql *.debug *.vstf

realclean:	clean
			/bin/rm -rf db
