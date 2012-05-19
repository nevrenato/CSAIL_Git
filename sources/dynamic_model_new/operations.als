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

	 // teste
	b.(marks.s) in ((head.s).(marks.s)).^parent
//	b.(marks.s) != (head.s).(marks.s)
	
	head.s' = head.s
	branches.s' = branches.s - b
	marks.s' = marks.s - b -> (b.(marks.s))
	objects.s' = objects.s
	index.s' = index.s 
}



fun comFls[b : Branch, s : State ] : set File {
	path.(b.(marks.s).(abs.univ))
}

pred checkout[s,s':State,b:Branch]{
	// usefull instances
	(head.s) != b

	//pre condition
		//the branch is on s
	b in branches.s

	b.(marks.s) != (head.s).(marks.s) => 
	no (index.s - comFls[(head.s),s]).path & comFls[b,s].path					

	// pos condition 
	index.s' = index.s - comFls[(head.s),s] + comFls[b,s]

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s

}



run{
	some disj s,s',s'' : State, b : Branch | commit[s,s'] and  checkout[s',s'',b]


} for 4 but 4 State
