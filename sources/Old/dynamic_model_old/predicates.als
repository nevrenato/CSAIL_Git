open index

pred init[s,s':State]{

}

pred add[s,s':State, f:File]{
	//pre conditions
	f in wdobjects.s //f belongs to initial state

	//operations
	namedBy.s' = namedBy.s
	blobs.s' = blobs.s
	references.s' = references.s
	trees.s' = trees.s
	points.s' = points.s
  	parent.s' = parent.s
	commits.s' = commits.s
	marks.s' = marks.s
	tags.s' = tags.s
	wdparent.s' = wdparent.s
  	wdobjects.s' = wdobjects.s
	content.s' = content.s
	stage.s' = stage.s + indexes.s -> f.(content.s) -> f
	indexes.s' = indexes.s

	//post conditions
}

pred rm[s,s':State, f:File]{
	//pre conditions
	f.content.s in (indexes.s).(stage.s).wdobjects.s//f belongs to initial state

	//operations
	namedBy.s' = namedBy.s
	blobs.s' = blobs.s
	references.s' = references.s
	trees.s' = trees.s
	points.s' = points.s
  	parent.s' = parent.s
	commits.s' = commits.s
	marks.s' = marks.s
	tags.s' = tags.s
	wdparent.s' = wdparent.s
  	wdobjects.s' = wdobjects.s
	content.s' = content.s
	stage.s' = stage.s - indexes.s -> f.(content.s) -> f
	indexes.s' = indexes.s

	//post conditions
}

pred rmm[s,s':State, f:File]{
 	f in wdobjects.s
  	wdobjects.s' = wdobjects.s - f
	wdparent.s' = wdparent.s - f -> Dir
	content.s' = content.s - f -> Sha
}

run{
	some disj s,s':State, f:File | rmm[s,s',f] //&& stage.s != stage.s'
}for 3 but exactly 2 State
