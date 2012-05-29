open Path
open Object_Model
open util/ordering[State]

-- to aid visualization
//associates paths with blob from index on a certain state
fun pathcontents: State -> Path -> Blob{
	{s:State, p:Path, b:Blob | some f:index.s | f.path = p and f.blob = b}
}

//it gives the paths that are on index
fun files : State -> Path {
	{s : State, p : Path | some p.(s.pathcontents) }
}

pred commit[s,s':State]{

	some index.s
	index.s' = index.s
	
	// about branches
	no head.s =>{
		head.s' = Master
		branches.s' = head.s'
		(head.s').(marks.s') in RootCommit
	}else{
		head.s' = head.s
		branches.s' = branches.s
		(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s 
		(head.s').(marks.s') != (head.s).(marks.s)
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
		b.marks.s in (head.s).(marks.s).*parent
	
	head.s' = head.s
	branches.s' = branches.s - b
	marks.s' = marks.s - b -> Commit
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


pred merge[s,s' : State, b : Branch] {
	
	// pre conditions
	some (head.s).(marks.s) and some b.(marks.s)
	some (head.s).(marks.s).*parent & b.(marks.s).^parent
	(head.s).(marks.s) != b.(marks.s)

	head.s' = head.s 
	branches.s' = branches.s
	(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s
	index.s' = comFls[head.s,s']

	// debug
	not (head.s).(marks.s) in b.(marks.s).^parent
	// nothing happens
	b.(marks.s) in (head.s).(marks.s).^parent implies (head.s).(marks.s) = (head.s).(marks.s') 
	// fast-foward
	(head.s).(marks.s) in b.(marks.s).^parent implies { 
		(head.s).marks.s' = b.marks.s
	}
	else {
		(head.s).(marks.s').parent = ((head.s)+b).(marks.s)
		(head.s).(marks.s').abs.univ = ((head.s)+b).(marks.s).abs.univ
		all f : (comFls[head.s,s] & comFls[b,s]) | f in comFls[head.s,s']
	 	all f : (comFls[head.s,s] - comFls[b,s]) | f in comFls[head.s,s']
		all f : (comFls[b,s] - comFls[head.s,s]) | f in comFls[head.s,s']
	}
	
}



run {
	no objects.first
	no index.first
	all s : State, s' : s.next | commit[s,s'] or (some f : File | add[s,s',f])	
} for 9 but 9 State

