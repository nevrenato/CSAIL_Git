open Path
open Object_Model

pred commit[s,s':State]{
	index.s' = index.s
	
	no head.s =>{
		head.s' = Master
		branches.s' = Master
		(head.s').(marks.s') in RootCommit
	}else{
		head.s' = head.s
		branches.s' = branches.s
		marks.s' - (head.s -> Commit) = marks.s - (head.s -> Commit) //think better about this
		(head.s').(marks.s').parent = (head.s).(marks.s)
	}

	(index.s).path.*pathparent = (head.s').(marks.s').abs.univ
	all f:index.s | f.path -> f.blob in (head.s').(marks.s').abs
	objects.s' = objects.s + (head.s').(marks.s') + univ.((head.s').(marks.s').abs)
}

pred add[s,s':State, f:File]{
	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s + f - ((f.path).~path -f)
}

pred rm[s,s':State,f:File]{
	//pre conditions
		//file on index
		f in index.s
		//the content of the file is the same as in the last commit
		f.path -> f.blob in (head.s).(marks.s).abs


	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s - f
}



pred branch[s,s':State,b:Branch]{
	//pre condition
		b not in branches.s

	head.s' = head.s
	branches.s' = branches.s + b
	marks.s' = marks.s + b -> (head.s).(marks.s)
	objects.s' = objects.s
	index.s' = index.s
}

pred branchDel[s,s':State, b:Branch]{
	
	//pre condition
		//the branch exists
		b in branches.s
		//the branch is not pointed by Head
		b not in (head.s)
		//the branch is already merged with the head
		b.marks.s in (head.s).(marks.s).^parent
	
	head.s' = head.s
	branches.s' = branches.s - b
	marks.s' = marks.s - b -> Commit
	objects.s' = objects.s
	index.s' = index.s 
}

pred checkout[s,s':State,b:Branch]{
	// usefull instances
	(head.s) != b

	//pre condition
		//the branch is on s
		b in branches.s

	(head.s').(marks.s').abs in s.pathcontents

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
}

run{
//	#Commit = 1
	//some pathparent.pathparent
//	some s:State, c:objects.s | some c & Commit && some index.s
//	some disj s,s': State, p:Path | commit[s,s'] and p not in (index.(s'+s)).path and no pathparent.p and some index.s
//	some disj s: State, p:Path | p not in (index.(s)).path and no pathparent.p and some index.s and some objects.s & Commit
	some s1,s2,s3,s4:State, f:File{
		commit[s1,s2]
		f.path not in index.s2.path
		add[s2,s3,f]
		commit[s3,s4]
	}
} for 6 but 4 State
