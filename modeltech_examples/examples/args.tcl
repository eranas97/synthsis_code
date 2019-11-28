# If no command line arguments are passed perform no actions
if {$argc > 0} {
# Print out the filename of the script
puts "The name of the script is: $argv0"
# Print out the count of the arguments passed
puts "Total count of arguments passed is: $argc"
# Print out a list of the arguments
puts "The arguments passed are: $argv"
# Using the List Index of argv print a specific argument
puts "The first argument passed was [lindex $argv 0]"
}