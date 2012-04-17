open util/ordering[Index]
open working_directory
open object_model

sig Index{
	containFiles: set File,
	containShas: set Sha, 
	stage: Sha one -> File
}{
	stage in containShas -> containFiles
	containFiles in Sha.stage
	containShas in stage.File
}

fact{
	//all Sha in stage name a Blob
	(namedBy.last).(Index.stage.File) in Blob
}

run{

} for 3 but 1 Index, 1 working_directory/State, 1 object_model/State
