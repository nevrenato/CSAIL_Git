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

fun filesCommit[c:Commit]:set File{
	{f:File |  f.path in c.abs.Blob and f.blob = (f.path).(c.abs)}
}

pred filesSanity[c:Commit]{
	all p:c.abs.Blob | some path.p
}

pred checkout[s,s':State,b:Branch]{
	//pre condition
	b in branches.s

	let CA=(head.s).(marks.s).abs & Path -> Blob, IA=s.pathcontents, CB=(b.marks.s).abs & Path -> Blob{
		
		s'.pathcontents = CB ++ (IA - CA)
		
		//all f:index.s | f.path -> f.blob in (IA - CA) implies 
		all f:index.s | f.path -> f.blob in (IA - CA) 
								implies (f.path in CB.univ 
									implies (f.path -> f.blob in CB or (f.path).CA = (f.path).CB)
									else f.path not in CA.univ)
	}

	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
}

run{
/*	some s,s': State, b:Branch | checkout[s,s',b] 
											and invariant[s]
											and invariant[s']
										//	and #index.s' > 2
											and some index.s 
											and some index.s' 
										//	and index.s != index.s'
											and (head.s).(marks.s).points != (head.s').(marks.s').points
											and some f:index.s' | f.path not in (head.s').(marks.s').abs.univ
*/
	some s0,s1,s2:State, b:Branch | commit[s0,s1]
											and checkout[s1,s2,b]
											and (head.s1) != b
						
}for 5 but 3 State


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
		some s1,s2 : State, b : Branch | checkout[s1,s2,b]
} for 6 but 2 State

