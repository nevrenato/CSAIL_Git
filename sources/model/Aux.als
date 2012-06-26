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
-- Two commits that are direct relatives cannot have the same content
pred invariant[s:State]{	
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s & (marks.s).Commit
		(objects.s - Commit) in (objects.s).points.*(contents.Name)
		all t : objects.s & Tree | t.contents.Name in objects.s
		all c:objects.s & Commit | c.points in objects.s and c.parent in objects.s
		marks.s in branches.s -> one objects.s
		all s:State, t : objects.s & Tree | some t.contains
		all c,c': Commit | c' in c.parent => c.points != c'.points  
}
