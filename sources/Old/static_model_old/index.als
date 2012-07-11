open working_directory
open object_model

one sig Index{
	
  stage: Sha one -> File
}

pred invIndex[]{

	// Resulting tree from index ?
	Index.stage.File in Blob.namedBy

	// All sha's must be or in Index or in Object Model
	Sha in (Index.stage).File + (Commit+Tree.*references).namedBy
}

fact{
	invIndex[]
}

run {} for 6

