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
