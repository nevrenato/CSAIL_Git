open Path
open Object_Model


pred commit[s,s':State]{
	index.s' = index.s
	head.s' = head.s
	branches.s' = branches.s
	(head.s').(marks.s').parent = (head.s).(marks.s)
	
}

run{
	some s:State | some Commit & objects.s
	some File
} for 3 but 1 State
