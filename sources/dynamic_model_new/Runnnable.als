open Path
open Object_Model
open operations


run{
	#Commit > 0
	#State = 2
	#contains > 1
	#Path > 0
	#pathparent = 1
	some s,s' : State | commit[s,s'] 
	
} for 5
