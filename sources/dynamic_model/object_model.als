open state

sig Sha{
	shas: set State
}

abstract sig Object {
	namedBy : Sha one -> State
}
sig Blob extends Object{
	blobs: set State
}
sig Tree extends Object {
	references : (Tree+Blob) some -> State,
	trees: set State
}

sig Commit extends Object{
   	points : Tree one -> State,
  	parent : Commit set -> State,
	commits: set State
}
sig RootCommit extends Commit{}

sig Tag extends Object{
	marks : Commit -> State,
	tags: set State
}

//general
pred inv[s:State]{
	//only Trees can share names
	namedBy.s.~(namedBy.s) - (trees.s) -> (trees.s) in iden
}

//trees
pred invTrees[s:State] {
	// a tree cannot reference itself
	no ^(references.s) & iden
	//two trees have the same name iff they have the same content (pag 11)
	all t,t':trees.s | t.namedBy.s = t'.namedBy.s <=> t.references.s = t'.references.s
	//all trees must have at least one son
	all t : Tree | some t.references
}

// Assumptions
pred assumptions[s:State] {
	// A blob must have a parent - NO! - (gitComm pag 120) a blob sha may exist on index, so the blob must exist
	//Blob in Tree.references 
	// A tree must have a parent or it is pointed by a commit
	trees.s in (trees.s).references.s + (commits.s).points.s
	// A tree can have at most one parent
  	//references.(iden & (Tree->Tree)).~references  in iden
	all t:trees.s | lone (references.s).t
	// There are no models with sha's alone
	shas.s in (blobs + trees + commits + tags).s.(namedBy.s)
	//tags, always marks some commit
	tags.s in (marks.s).(commits.s)
	// A root tree can only be pointed by One commit
  	points.s.~(points.s) in iden
	// A non root tree cannot be pointed by a commit
  	no (commits.s).(points.s) & (trees.s).(references.s)
}

//commits
pred invCommits[s:State]{	
	// A commit cannot be an ancestor of itself
  	no ^(parent.s) & iden
	//RootCommit don't have a parent
	no RootCommit.(parent.s)
	//All Commits descend from a RootCommit
	commits.s in *(parent.s).(commits.s & RootCommit)
}

fact{
	all s:State | inv[s] && invTrees[s] && assumptions[s] && invCommits[s]
	//everything on a state, belongs to that states
	all s:State |{	(parent.s) in (commits.s) -> (commits.s) 
							(references.s) in trees.s -> (trees + blobs).s
							(points.s) in (commits.s) -> (trees.s)
							(namedBy.s) in (blobs + trees + commits + tags).s -> shas.s
					}
	
	//all objects belong to a state
	Object in (trees + blobs + commits + tags).State
}

run {
	some Tree -> Blob
} for 3
