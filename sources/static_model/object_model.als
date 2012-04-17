open util/ordering [StateOM]
sig StateOM{}

sig Sha{
	shas: set StateOM
}

abstract sig Object {
	namedBy : Sha one -> StateOM,
	objects: set StateOM
}
sig Blob extends Object{}
sig Tree extends Object {
	references : (Tree+Blob) set -> StateOM
}

sig Commit extends Object{
   	points : Tree one -> StateOM,
  	parent : Commit set -> StateOM
}
some sig RootCommit extends Commit{}

sig Tag extends Object{
	marks : Commit -> StateOM
}

//general
pred inv[s:StateOM]{
	//only Trees can share names
	namedBy.s.~(namedBy.s) - (Tree & objects.s) -> (Tree & objects.s) in iden
}

//trees
pred invTrees[s:StateOM] {
	// a tree cannot reference itself
	no ^(references.s) & iden
	//two trees have the same name iff they have the same content (pag 11)
	all t,t':objects.s & Tree | t.namedBy.s = t'.namedBy.s <=> t.references.s = t'.references.s
}

// Assumptions
pred assumptions[s:StateOM] {
	// A blob must have a parent - NO! - (gitComm pag 120) a blob sha may exist on index, so the blob must exist
	//Blob in Tree.references 
	// A tree must have a parent or it is pointed by a commit
	objects.s & Tree in (objects.s & Tree).references.s + (objects.s & Commit).points.s
	// There are no models with sha's alone
	shas.s in (objects.s).(namedBy.s)
	// A root tree can only be pointed by One commit
  	points.s.~(points.s) in iden
	// A tree can have at most one parent
  	//references.(iden & (Tree->Tree)).~references  in iden
	all t:objects.s & Tree | lone (references.s).t
	// A non root tree cannot be pointed by a commit
  	no (objects.s & Commit).(points.s) & (objects.s & Tree).(references.s)
}

//commits
pred invCommits[s:StateOM]{	
	// A commit cannot be an ancestor of itself
  	no ^(parent.s) & iden
	//RootCommit don't have a parent
	no RootCommit.(parent.s)
	//All Commits descend from a RootCommit
	objects.s & Commit in *(parent.s).(objects.s & RootCommit)
}

fact{
	all s:StateOM | inv[s] && invTrees[s] && assumptions[s] && invCommits[s]
	//everything on a state, belongs to that states
	all s:StateOM |{	(parent.s) in (objects.s + Commit) -> (objects.s + Commit) 
						(references.s) in objects.s -> objects.s
						(points.s) in (objects.s + Commit) -> (objects.s & Tree)
						(namedBy.s) in objects.s -> shas.s
					}
}

run {
	#Commit > 1
	#references > 1
} for 6 but 1 StateOM
