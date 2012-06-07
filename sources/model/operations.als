open Path
open Object_Model

-- to aid visualization
//associates paths with blob from index on a certain state
fun pathcontents: State -> Path -> Blob{
	{s:State, p:Path, b:Blob | some f:index.s | f.path = p and f.blob = b}
}

-- it gives the paths that are on index
fun files : State -> Path {
	{s : State, p : Path | some p.(s.pathcontents) }
}


-- Invariant used to check consistency on git
-- There is some commit iff exists at least one branch and an head
-- The current branch must exist and must have a commit
-- all objects from one state descend from one of its commits
-- referential integrity for the content of a tree, commmits and marks
-- And because git if file oriented, there cannot be
-- trees (folders) with no sons.
pred invariant[s:State]{	
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s & (marks.s).Commit
		(objects.s - Commit) in (objects.s).points.*(contents.Name)		
		all t : objects.s & Tree | t.contents.Name in objects.s
		all c:objects.s & Commit | c.points in objects.s and c.parent in objects.s
		marks.s in branches.s -> one objects.s
		all s:State, t : objects.s & Tree | some t.contains
}

-- The representation of a commit operation 
-- Some new changes have to be done since last commit, so we can make a new commit (pre)
pred commit[s,s':State]{

	-- pre condition
	some index.s

	-- pos conditions

	-- No changes have been done to the index
	index.s' = index.s
	
	-- The case of a first commit
	-- The new commit will be a Root
	-- And the master branch will be the current
	no head.s =>{
		head.s' = Master
		branches.s' = head.s'
		(head.s').(marks.s') in RootCommit
	}

	-- If there are already commits in the repository
	-- The information about branches will be the same, except
	-- that the current branch will point to the new commit
	-- The parent of the new commit will be the last
	else{
		head.s' = head.s
		branches.s' = branches.s
		(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s 
		-- The following cannot be necessary
		--(head.s').(marks.s') != (head.s).(marks.s)
		(head.s').(marks.s').parent = (head.s).(marks.s)
	}

	-- All files on the index must be on the commit also
	(index.s).path.*pathparent = (head.s').(marks.s').abs.univ
	all f:index.s | f.path -> f.blob in (head.s').(marks.s').abs

	-- The new objects refering to the new
	-- commit must exist on the system (referential integrity)
	objects.s' = objects.s + (head.s').(marks.s') + univ.((head.s').(marks.s').abs) 
}


-- The representation of the add operation
-- The only difference from one state to the other is that is guaranteed
-- that the new file is in the index
pred add[s,s':State, f:File]{
	
	-- pos conditions
	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s

	-- The new file must be added to the index, and all files
	-- with the same path must be removed
	index.s' = index.s + f - ((f.path).~path -f)
}

-- The representation of the remove operation
-- The only difference from one state to the other is that is guaranteed
-- that the file in question cannot be in the index
pred rm[s,s':State,f:File]{
	
	--pre conditions
	
	--file on index and it's contents are the same
	-- as in the last commit
	f in index.s
	f.path -> f.blob in (head.s).(marks.s).abs

	--pos conditions
	head.s' = head.s
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	index.s' = index.s - f
}


-- The representation of the branch operation. It
-- just creates a new branch. The new branch cannot
-- exist previous to the operation
pred branch[s,s':State,b:Branch]{
	
	--pre conditions
	b not in branches.s

	-- pos conditions
	head.s' = head.s
	branches.s' = branches.s + b
	objects.s' = objects.s
	index.s' = index.s

	-- The new branch must point to the current commit
	marks.s' = marks.s + b -> (head.s).(marks.s)
}

-- The representation of the branch delete operation. It
-- just removes a previously existing branch
pred branchDel[s,s':State, b:Branch]{
	
	--pre conditions
	
	-- The branch must previoulsy exist and cannot be
	-- the current branch. Also it's information must
	-- and can be achived by the current branch
	b in branches.s
	b not in (head.s)
	b.marks.s in (head.s).(marks.s).*parent

	-- pos conditions
	head.s' = head.s
	branches.s' = branches.s - b
	objects.s' = objects.s
	index.s' = index.s

	-- Removal of all commits pointed by the branch
	marks.s' = marks.s - b -> Commit
}


-- The representation of the checkout operation.
-- The recommended way to use checkout, is first to commit all things
-- and then checkout. Otherwise some strange things can happen.
-- The branch to wich you want to checkout must exist and cannot be the one
-- you already are.

pred checkout[s,s':State,b:Branch]{

	--pre conditions
	b in branches.s
	b != head.s 


	let CA=(head.s).(marks.s).abs :> Blob, IA=s.pathcontents, CB=(b.marks.s).abs :> Blob{
	
	-- pre conditions
	-- This one is tricky. 
	-- There cannot be Newly Modified files not saved in the last commit such that they
	-- exist also on the commit of the branch to wich we want to jump but with a different content.
	-- Except if it's previous (saved) content is equal to the content in the 
	-- commit to wich we want to branch.
		all f:index.s | f.path -> f.blob in (IA - CA) => (f.path in CB.univ => (f.path -> f.blob in CB or (f.path).CA = (f.path).CB)
											else f.path not in CA.univ)
	-- alternative
	-- all f : index.s | f.path -> f.blob in ((CA.univ <: IA) - CA) and f.path in CB.univ => (f.path -> f.blob in CB or (f.path).CA = (f.path).CB)


	-- pos conditions
	-- The new index must accumulate the information of the commit of the new branch and new previous index, with the information
	-- of the index taking priority over the commit
		s'.pathcontents = CB ++ (IA - CA)
	}

	-- pos conditions
	head.s' = b
	branches.s' = branches.s
	marks.s' = marks.s
	objects.s' = objects.s
	marks.s' = marks.s
}

-- The representation of the merge operation. A merge has two ways
-- to work : Fast-Forward or normal merge.
-- In order for a merge to be done, the two branches cannot point to
-- the same commit, and the current cannot be more recent than of branch b
pred merge[s,s' : State, b : Branch] {
	
	-- pre conditions
	
	-- This may be not needed
	some (head.s).(marks.s).*parent & b.(marks.s).^parent
	(head.s).(marks.s).points != b.(marks.s).points
	not (b.marks.s) in (head.s).(marks.s).^parent
	
	-- pos conditions 
	
	-- The fast-forward situation. The current commit is older than of branch
	-- b so the head will point to the commit pointed by b
	(head.s).(marks.s) in b.(marks.s).^parent implies { 
		(head.s).marks.s' = b.marks.s 
		objects.s' = objects.s		
		s'.pathcontents = (head.s').(marks.s').abs :> Blob
	}


	-- Normal merge situation. Where the two commits have (usually) a common 
	-- ancestor, and a new merge commit will be created if not conflicts are
	-- found.
	else {
		-- The merge commit will have as parents the commits we want to merge. And
		-- the new commit will have all the content that it's parents have.
		(head.s').(marks.s').parent = ((head.s)+b).(marks.s)
		((head.s)+b).(marks.s).abs.univ = (head.s').(marks.s').abs.univ

		let CA = (head.s).(marks.s).abs :> Blob, CB=(b.marks.s).abs :> Blob, CC = (head.s).(marks.s').abs :> Blob {
		
			-- All files must be previously saved. (pre condition)
			no s.pathcontents - CA			

			-- pos conditions
			-- The information common to the parents must exist on the new commit.
			-- Also all information existing only on one of the parents must also exist on 
			-- the new commit. And the new index must be consistent with the new commit
			-- If any file conflicts it's new content can be anything
			CA & CB in CC
			(Path - CB.univ) <: CA + (Path - CA.univ) <: CB in CC
			s'.pathcontents = CC
		}
	}

	-- referential integrity
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

