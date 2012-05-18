open Path
open Object_Model


pred commit[s,s':State]{
	index.s' = index.s

//	no head.s =>{
//		head.s' = Master
//		branches.s' = Master
//		(head.s').(marks.s') in RootCommit
//	}else{
		head.s' = head.s
		branches.s' = branches.s
		(head.s').(marks.s').parent = (head.s).(marks.s)
//	}

	(index.s).path.*pathparent = (head.s').(marks.s').abs.univ
	all f:index.s | f.path -> f.blob in (head.s').(marks.s').abs
	objects.s' = objects.s + (head.s').(marks.s') + univ.((head.s').(marks.s').abs)
}

run{
	//some s:State | some Commit & objects.s
	//some File
	some s,s':State | s!=s' && commit[s,s'] && some objects.s & Commit 
} for 4 but 2 State
