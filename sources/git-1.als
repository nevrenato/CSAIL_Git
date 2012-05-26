--open util/ordering[State]

sig State {}

abstract sig Object {
	objects : set State
}

sig Blob extends Object {}

sig Commit extends Object {
	points : Tree,
	parent : lone Commit,
	head : set State,
	abs : Path -> Object
}

sig Tree extends Object {
	contains : (Tree+Blob) lone -> Name 
}

fun contents : Tree -> Name -> Object {
	{t : Tree, n : Name, o : Object | t -> o -> n in contains}
}

fun nonobjects : State -> Object {
	{s : State, o : Object | o not in objects.s}
}

fact {
	all t,t' : Tree | t.contains = t'.contains implies t=t'
}

sig Name {}

fact {
	all c,c' : Commit | c.points = c'.points and c.parent = c'.parent implies c=c'
	no ^(parent :> Commit) & iden
	no ^(contains.Name) & iden
}

fact {
	all s : State {
		all c : objects.s & Commit {
			c.points in objects.s and c.parent in objects.s
			let objs = c.points.*(contains.Name) {
				c.abs in Path some -> lone objs
				(c.abs).(c.points) in Root
				all p,q : (c.abs).univ | p -> q in parent implies q.(c.abs) -> p.(c.abs) -> p.name in contains
				all t,o : objs, n : Name | t -> o -> n in contains implies some x : c.abs.o, y : c.abs.t | x -> y in parent and x.name = n
			}
		}


		lone head.s
		head.s in objects.s
		(objects.s - Commit) in (objects.s).points.*(contains.Name)
		all t : objects.s & Tree | t.contains.Name in objects.s

		all t : objects.s & Tree | some t.contains
	}
}

sig Path {
	parent : lone Path,
	name : Name
}

one sig Root extends Path {}

fact {
	all p : Path - Root | some p.parent and p not in p.^parent
	all p : Path, disj p1,p2 : parent.p | p1.name != p2.name
	no Root.parent
}

sig File {
	path : Path,
	blob : Blob,
	index : set State
}

fun pathcontents : State -> Path -> Blob {
	{s : State, p : Path, b : Blob | some f : index.s | f.path = p and f.blob = b}
}

fun files : State -> Path {
	{s : State, p : Path | some p.(s.pathcontents) }
}

fact {
	all s : State, f : index.s {
		no (f.path).^parent & (index.s).path
		f.path not in Root
	}
	all s : State, disj f1,f2 : index.s | f1.path != f2.path
}

pred commit [s,s' : State] {
	some index.s
--	some head.s implies (head.s).points != (head.s').points

	index.s' = index.s
	(head.s').parent = head.s
	(index.s).path.*parent = (head.s').abs.univ
	all f : index.s | f.path -> f.blob in (head.s').abs
	objects.s' = objects.s + head.s' + univ.((head.s').abs)

}


check {
	all s0,s1,s2 : State | commit[s0,s1] and commit[s1,s2] implies (head.s1).points = (head.s2).points
} for 7 but 3 State

pred add [s,s' : State, f : File] {
	f not in index.s
	index.s' = index.s + f
	head.s' = head.s
	objects.s' = objects.s
}

/*
fact {
	no objects.first
	no index.first
	all s : State, s' : s.next | commit[s,s'] or (some f : File | add[s,s',f])
}

run {some s : State | #(Commit & objects.s) > 1} for 7 but 5 State
*/
