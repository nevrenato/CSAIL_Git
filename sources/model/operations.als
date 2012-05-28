open Path
open Object_Model

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
		(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s //think better about this
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


pred merge[s,s' : State, b,b' : Branch] {
	
	// pre conditions
	b = head.s 
	some b.(marks.s) and some b'.(marks.s)
	some b.(marks.s).*parent & b'.(marks.s).^parent
	b.(marks.s) != b'.(marks.s)

	head.s' = head.s 
	branches.s' = branches.s
	(Branch -b) <: marks.s' = (Branch -b) <: marks.s

	// nothing happens
	b'.(marks.s) in b.(marks.s).^parent implies b.(marks.s) = b.(marks.s')

	// debug
	not b.(marks.s) in b'.(marks.s).^parent
 
	// fast-foward
	b.(marks.s) in b'.(marks.s).^parent implies { 
		b.marks.s' = b'.marks.s
		some s'' : State | commit[s'',s']   
	}

	else {
		b.(marks.s').parent = (b+b').(marks.s)
		b.(marks.s').abs.univ = (b+b').(marks.s).abs.univ
		/*all p : b.(marks.s').abs.univ {
						
		} */
	 /*			
			// all paths
			all p : b.(marks.s').abs.univ  { 
			  			// conflict		
							(p.(b.(marks.s).abs) in Tree ) and p in b.(marks.s).abs.univ & b'.(marks.s).abs.univ => {
										p.(b.marks.s.abs) != p.(b'.marks.s.abs) =>  { p.(b.(marks.s').abs) not in p.((b+b').(marks.s).abs) }
									  																				else  p.(b.(marks.s').abs) = p.(b.(marks.s).abs) 
							}
							// no conflict
							else { 
							p in b.(marks.s).abs.univ => p.(b.marks.s'.abs) = p.(b.(marks.s).abs)
							p in b'.(marks.s).abs.univ => p.(b.marks.s'.abs) = p.(b'.(marks.s).abs)
							}
			 }  
    */
	}
	
}

run {
	#Branch = 2
	some s1,s2 : State, b,b' : Branch | merge[s1,s2,b,b']
} for 6 but 2 State




pred rebase[s,s' : State, b,b' : Branch] {


}
