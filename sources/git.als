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

//contents :: (Tree -> Object -> Name) -> (Tree -> Name -> Object)
fun contents : Tree -> Name -> Object {
	{t : Tree, n : Name, o : Object | t -> o -> n in contains}
}

//objects not in state
fun nonobjects : State -> Object {
	{s : State, o : Object | o not in objects.s}
}

fact {
	all t,t' : Tree | t.contains = t'.contains implies t=t' //check1
}

sig Name {}

fact {
	all c,c' : Commit | c.points = c'.points and c.parent = c'.parent implies c=c' //disagree, checked on git. they will only share the same tree
	no ^(parent :> Commit) & iden //check3
	no ^(contains.Name) & iden //check2
}

fact {
	all s : State {
		all c : objects.s & Commit {
			c.points in objects.s //check4
			c.parent in objects.s//check5
			let objs = c.points.*(contains.Name) {
				c.abs in Path some -> lone objs
				(c.abs).(c.points) in Root
				all p,q : (c.abs).univ | p -> q in parent implies q.(c.abs) -> p.(c.abs) -> p.name in contains
				//not all n:Name ------- 
				all t,o : objs, n : Name | t -> o -> n in contains implies some x : c.abs.o, y : c.abs.t | x -> y in parent and x.name = n
			}
		}
		lone head.s//head is not an object on our model
		head.s in objects.s //same

		(objects.s - Commit) in (objects.s).points.*(contains.Name) //not sure, ask Prof Alcino and update our model
		all t : objects.s & Tree | t.contains.Name in objects.s //check 6
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
	all s:State, t : objects.s & Tree | some t.contents
}

run {

//		some p:Path | p not in Commit.abs.Object &&
//		 all p':(p.^parent)-Root | p' not in Commit.abs.Object
		some Commit & objects.State
} for 6 but exactly 1 State

pred commit [s,s' : State] {
	-- just to generate nice instances
	#index.s > 1 and objects.s != objects.s' and (head.s).points != (head.s').points and some objects.s

	index.s' = index.s
	(head.s').parent = head.s
	(index.s).path.*parent = (head.s').abs.univ
	all f : index.s | f.path -> f.blob in (head.s').abs
	objects.s' = objects.s + head.s' + univ.((head.s').abs)
}

run commit for 5 but 2 State
