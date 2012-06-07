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



pred invariant[s:State]{
		//all object from one state descend from one of its commit
		(objects.s - Commit) in (objects.s).points.*(contents.Name)
		
		//referential integrity for the content of a tree
		all t : objects.s & Tree | t.contents.Name in objects.s
		//referential integrity for commits
		all c:objects.s & Commit | c.points in objects.s and c.parent in objects.s
		//referential integrity for marks
		marks.s in branches.s -> one objects.s
		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s & (marks.s).Commit
		//all trees have content
		all t:objects.s & Tree | some t.contains
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

pred checkout[s,s':State,b:Branch]{
	//pre condition
	b in branches.s
	b != head.s 

	let CA=(head.s).(marks.s).abs :> Blob, IA=s.pathcontents, CB=(b.marks.s).abs :> Blob{
		//precondition
		all f:index.s | f.path -> f.blob in (IA - CA) 
								implies (f.path in CB.univ 
												implies (f.path -> f.blob in CB or (f.path).CA = (f.path).CB)
												else f.path not in CA.univ)

		s'.pathcontents = CB ++ (IA - CA)
	}

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	marks.s' = marks.s
}

pred merge[s,s' : State, b : Branch] {
	// pre conditions
	some (head.s).(marks.s).*parent & b.(marks.s).^parent
	(head.s).(marks.s).points != b.(marks.s).points
	not (b.marks.s) in (head.s).(marks.s).^parent
	
	// debug
	not (head.s).(marks.s) in b.(marks.s).^parent
	
	// fast-foward
	(head.s).(marks.s) in b.(marks.s).^parent implies { 
		(head.s).marks.s' = b.marks.s 
		objects.s' = objects.s		
		s'.pathcontents = (head.s').(marks.s').abs :> Blob
	}
	// the other case
	else {
		(head.s').(marks.s').parent = ((head.s)+b).(marks.s)
		((head.s)+b).(marks.s).abs.univ = (head.s').(marks.s').abs.univ
		let CA = (head.s).(marks.s).abs :> Blob, CB=(b.marks.s).abs :> Blob, CC = (head.s).(marks.s').abs :> Blob {
			no s.pathcontents - CA			
			CA & CB in CC
			(Path - CB.univ) <: CA + (Path - CA.univ) <: CB in CC
			s'.pathcontents = CC
		}
	}

	objects.s' = objects.s + univ.((head.s').(marks.s').abs) + (head.s').(marks.s')
	head.s' = head.s 
	branches.s' = branches.s
  	(Branch - head.s') <: marks.s' = (Branch - head.s) <: marks.s
}
assert x{
	all s0,s1,s2,s3,s4,s5,s6,s7,s8:State, f,f2,f3:File, b:Branch | no head.s0
									and no index.s0
									and add[s0,s1,f]
									and commit[s1,s2]
									and branch[s2,s3,b]
									and add[s3,s4,f2] and f2.path!=f.path
									and commit[s4,s5]
									and rm[s5,s6,f2]
									and add[s6,s7,f3] and (f3.path).pathparent = f2.path
									and checkout[s7,s8,b]
									implies f3.path in (index.s8).path
}

run {
	some s:State | invariant[s] and some head.s and #(head.s).(marks.s).abs > 2
	one Commit
	one Branch
	#File > 1
	no path.Root
	#pathparent.Root > 2
} for 5 but 1 State

check x for 8 but 9 State
run {
		some s0,s1,s2,s3,s4,s5,s6,s7,s8:State, f,f2,f3:File, b:Branch | no head.s0
									and no index.s0
									and add[s0,s1,f]
									and commit[s1,s2]
									and branch[s2,s3,b]
									and add[s3,s4,f2] and f2.path!=f.path
									and commit[s4,s5]
									and rm[s5,s6,f2]
									and add[s6,s7,f3] and (f3.path).pathparent = f2.path
									and checkout[s7,s8,b]
} for 5 but 9 State

