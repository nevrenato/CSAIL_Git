open Objects

some sig RootCommit extends Commit {}


sig Commit extends Object {
	points : Tree,
	parent : State -> set Commit,

}

one sig Head extends Object {
	pointsToLast : State -> one Commit

}

fact {

	all s : State {
			let r = {c : Commit, c' : Commit | c->s->c' in parent} {
		
			// A commit cannot be an ancestor of itself
			no ^r & iden

			// RootCommits don't have a parent
			no RootCommit.r

			// All commits (except RootCommit) need to have at least one parent
			//all c : Commit - RootCommit | some c.r
      }
	}

}
