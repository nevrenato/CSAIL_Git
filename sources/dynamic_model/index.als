open working_directory
open object_model

one sig Index{
	stage: Sha one -> File -> State,
	indexes: set State
}

pred invIndex[s:State]{
	stage.s in indexes.s -> shas.s -> wdobjects.s
	(indexes.s).(stage.s).File in (blobs.s).namedBy.s
	// All sha's must be or in Index or in Object Model
	shas.s in (indexes.s).(stage.s).(wdobjects.s)+ (commits.s+trees.s.*(references.s)).namedBy.s
}

fact{
	all s:State | invIndex[s]

	Index in indexes.State
}

run{
} for 3 but exactly 2 State
