open Objects
open Path

sig Commit extends Object {
	points : Tree,
	parent : set Commit,
	abs: Path -> Object
}

sig RootCommit extends Commit {}

sig Branch{
	marks: Commit one -> State,
	branches: set State,
	head: set State
}

lone sig Master extends Branch{}

fact {
	//no cycles
	no ^parent & iden

	all s:State{
		//there is one commit iff there is at least one branch and an head
		some Commit & objects.s <=> some marks.s && one head.s
		head.s in branches.s & (marks.s).Commit

		//this must only be checked in the properties
		//all t:objects.s & Tree | some t.contains
	}

	all c: Commit{
		c not in RootCommit <=> some c.parent
		let objs = c.points.*(contents.Name){
			c.abs in Path some -> lone objs
			(c.abs).(c.points) in Root
			all p,q : (c.abs).univ | p -> q in pathparent implies q.(c.abs) -> p.(c.abs) -> p.name in contents
			all t,o : objs, n : Name | t -> o -> n in contents implies all y : c.abs.t | some x : c.abs.o | x -> y in pathparent and x.name = n
		}
	}
}
