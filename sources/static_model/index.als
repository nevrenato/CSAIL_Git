open working_directory
open object_model

one sig Index{
	entry: Sha one -> File
}

fact{
	//all Sha in entry name a Blob
	namedBy.(Index.entry.File) in Blob
	
}

run{
no Tag
one Branch
one State
}
