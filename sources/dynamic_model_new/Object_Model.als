open Objects

some sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree,
	parent : set Commit
}


sig Tag extends Object {
	marks : Commit
}


fact {
	// A commit cannot be an ancestor of itself
	no ^parent & iden

	// RootCommits don't have a parent
	no RootCommit.parent
}
