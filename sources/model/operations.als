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

run{
	some s,s':State, b:Branch | checkout[s,s',b]
}for 7 but 2 State

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

run {
		some disj s0,s1 : State, b : Branch | invariant[s0]
				and merge[s0,s1,b]
				and (head.s0).(marks.s0).points != (head.s1).(marks.s1).points
				and (head.s1).(marks.s1).points != (b.marks.s0).points
} for 8 but 2 State

