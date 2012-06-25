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
	-- there must be something new to commit
	(head.s).(marks.s).abs :> Blob != s.pathcontents
	-- there cannot be unmerge conflicts	
	no unmerge.s

	-- pos conditions
	-- The case of a first commit
	-- The new commit will be a Root
	-- And the master branch will be the current
	no head.s =>{
		head.s' = Master
		branches.s' = head.s'
		(head.s').(marks.s') in RootCommit
		(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s 
	}

	-- If there are already commits in the repository
	-- The information about branches will be the same, except
	-- that the current branch will point to the new commit
	-- The parent of the new commit will be the last
	else{
		head.s' = head.s
		branches.s' = branches.s
		(Branch - head.s) <: marks.s' = (Branch - head.s) <: marks.s 
		(head.s').(marks.s').parent = (head.s).(marks.s) + merge.s
	}

	-- All files on the index must be on the commit also
	(index.s).path.*pathparent = (head.s').(marks.s').abs.univ
	all f:index.s | f.path -> f.blob in (head.s').(marks.s').abs

	-- The new objects refering to the new
	-- commit must exist on the system (referential integrity)
	objects.s' = objects.s + (head.s').(marks.s') + univ.((head.s').(marks.s').abs) 


	-- there is no more merge situation
	no merge.s'
  unmerge.s' = unmerge.s
	-- No changes have been done to the index
	index.s' = index.s
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
	merge.s = merge.s'
	unmerge.s = unmerge.s' - f.path

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
	merge.s = merge.s'
  unmerge.s = unmerge.s' - f.path
}


-- The representation of the branch operation. It
-- just creates a new branch. The new branch cannot
-- exist previous to the operation
pred branch[s,s':State,b:Branch]{
	
	--pre conditions
	b not in branches.s
	some head.s

	-- pos conditions
	head.s' = head.s
	branches.s' = branches.s + b
	objects.s' = objects.s
	index.s' = index.s
	merge.s = merge.s'
 	unmerge.s = unmerge.s' 

	-- The new branch must point to the current commit
	marks.s' = marks.s + b -> (head.s).(marks.s)
}


-- The representation of the branch remove operation. It
-- just removes a previously existing branch
pred branchRm[s,s':State, b:Branch]{
	
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
	merge.s = merge.s'
	unmerge.s = unmerge.s'

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
	merge.s = merge.s'
	unmerge.s = unmerge.s'
}




-- The representation of the merge operation. A merge has two ways
-- to work : Fast-Forward or normal 3-way merge.
-- In order for a merge to be done, the two branches cannot point to
-- the same commit, and the current cannot be more recent than of branch b
pred merge[s,s' : State, b : Branch] {	
	-- pre conditions
	-- head can't be descedent of b
	-- no uncommitted changes on head
	no (head.s).(marks.s).*parent & b.(marks.s)
	(head.s).(marks.s).abs :> Blob = s.pathcontents	

	-- The fast-forward situation. The current commit is older than of branch
	-- b so the head will point to the commit pointed by b, and the index is going
  -- to be updated
	some b.(marks.s).^parent & (head.s).(marks.s) implies { 
		-- pos conditions
		(head.s).marks.s' = b.marks.s 
		s'.pathcontents = (head.s').(marks.s').abs :> Blob	
		head.s' = b
		merge.s = merge.s'
		unmerge.s = unmerge.s'
	}
	-- 3-way merge situation. 
	else {
		let ancestors = (head.s).(marks.s).^parent & b.(marks.s).^parent, 
				cc'= (ancestors - ancestors.parent), cc = cc'.abs :> Blob,
				ch = (head.s).(marks.s).abs :> Blob, cb = b.(marks.s).abs :> Blob {	
					-- pre conditions
					-- the must be a common ancestor
					one cc'
		
					-- modify conflict
					-- delete/modify conflict
					unmerge.s' = (ch+cb).univ - (ch & cb).univ - (ch & cc).univ - (cb & cc).univ 
					-- building the index accordingly with the conflicts
					s'.pathcontents = ch + cb - unmerge.s' -> Blob - cc & (cc - cb) - cc & (cb - ch) 				
				
					no unmerge.s' => { /* the commit situation */ }
					else  { 
										merge.s' = b.(marks.s) + head.s.(marks.s)
										head.s' = head.s	
					} 
		}
	}
	
	-- pos conditions
	branches.s' = branches.s
	(Branch - head.s') <: marks.s' = marks.s
	objects.s' = objects.s

}

run { some s,s' : State , b : Branch | merge[s,s',b] } for 4 but 2 State
