open Objects

sig RootCommit extends Commit {}


sig Commit extends Object {
	points : one Tree,
	parent : Commit set -> State
}

sig Branch{

	marks: Commit -> State,

	// In wich states exist
	branches: set State,

	// the current branch...
	head: set State
}

lone sig master extends Branch{}

fact {

	all s:State{
		// A commit cannot be an ancestor of itself
		no ^(parent.s) & iden

		// RootCommits doesn't have a parent
		no RootCommit.parent.s

		// All commits (except RootCommit) need to have at least one parent
		all c : ((Commit - RootCommit) & objects.s) | some c.parent.s

		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s
	
		//referential integrity
		parent.s in objects.s -> objects.s
		marks.s in branches.s -> one objects.s
		
	}

}
run{

} for 5 but exactly 2 State
