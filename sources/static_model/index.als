open working_directory
open object_model

one sig Index{
	stage: Sha one -> File
}

pred invIndex[]{
	Index.stage.File in Blob.namedBy
}

fact{
	invIndex[]
}

run{
} for 3
