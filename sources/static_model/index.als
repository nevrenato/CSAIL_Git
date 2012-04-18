open working_directory
open object_model

one sig Index{
	stage: Sha one -> File -> State,
	entries: set State
}

pred invIndex[s:State]{
	stage.s in entries.s -> shas.s -> wdobjects.s
	(entries.s).(stage.s).File in (blobs.s).namedBy.s
}

fact{
	all s:State | invIndex[s]

	Index in entries.State
}

run{
} for 3 but 1 State
