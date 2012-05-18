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
	
	head.s' = head.s
	branches.s' = branches.s - b
	marks.s' = marks.s - b -> (head.s).(marks.s)
	objects.s' = objects.s
	index.s' = index.s
}

pred checkout[s,s':State,b:Branch]{
	//pre condition
		//the branch is on s
		b in branches.s

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s
}

run{
	//some s,s':State | s!=s' && commit[s,s'] && no head.s && some head.s'
	//some pathparent.pathparent 
	//some s,s':State, f:File | s!=s' && rm[s,s',f]
	some disj s1,s2,s3,s4,s5,s6,s7:State, disj b1:Branch, disj f1,f2:File {
		add[s1,s2,f1]
		commit[s2,s3]
		branch[s3,s4,b1] && b1 != Master
		checkout[s4,s5,b1]
		add[s5,s6,f2]
		commit[s6,s7]
	}
} for 5 but 8 State
