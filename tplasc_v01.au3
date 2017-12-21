; **************************************************************************************************************************************
;
; Sanquin CAP laboratory TPLASC for Tecan EVO general ELISA and C1-inhibitor assays
;
; TPLASC version 0.30 Dion Methorst & Ed Nieuwenhuys, Sanquin Amsterdam, November 2017
; concatenates your Tecan EVO TPL and ASC files for direct use in LIMS database
;
; **************************************************************************************************************************************
;
; Description of execution:
;
; If an ASC-file and TPL file are present in the folders as defined by $ASCPath  & $TPLPath
; AND  the Evoware logfile Trace.txt file is present in the folder defined by $TrcTxt,
; then this program will:
;
; -	Read the ASC-file into an array
; - TrayID is extracted from ASC filename
; -	Finds corresponding TPL file with TPL_ID by comparing to TrayID
; - Read the TPL file into an array
; - Obsolete lines in the ASC and TPL array are deleted to equalize array dimensions
; - The TrayID.evo file is created in the folder defined by $TPLASCPath
; - Header lines with checksum are written to the TrayID.evo file
; - TPL array entries are read 1 by 1 in a loop, in each cycle the corresponding entry in the ASC array is looked up
; - In each cycle of the same loop the ASC and TPL data with checksum are written to the TrayID.evo file
; - Footer lines with Evoware logfilenames and checksum are appended to the TrayID.evo file
; - While the script is running the SendAndLog function is logging all the crucial events in the scripts
; - The errorhandling may be incomplete but thusfar hasn't shown any problems that might indicate such
;
; **************************************************************************************************************************************
;
; Changelog
;
; July 2013 : in development
; V0.11 	auto open TPL and ASC files : in development
; V0.12 	Added Errorhandling & logfile (not fully tested)
; V0.12 	script divided in 3 functions, added main function
; V0.13 	added log function and clearlog function;
; V0.14 	added constant for maximum number lines in logfile, added remarks for linenumbers with logfile function call
; V0.15 	writes complete lastline of ASC file to TPLASC first line: complete Magellan method filename which contains the sanquin number of the used EVO
;
; September 2014
; V0.16 	addition of checksum
;			addition of lines U; username T; trayID  and A; Evo magellan.mth with MacihneSqnNumberID
;			addition of logfilenames from logfile folder
;			checking if TrayID of ASC file matches TPL file, ends script if not
; V0.17		change 'D' identifier in $aTPL array to 'R' for result identiefier in TrayID.evo file
; V0.18		Fix error in checksum
;			Changed ;L flag in TPL file to ;L; in $aTPL output
; V0.20		Addition of function _EvoLogfiles: extracts last three logfilenames form Evoware logfile folder Trace.txt file
;			re-arrangement of function calls and passing of variables
; V0.21		ASC TrayID now used to find TPL_ID (previous version sorted on latest/newest TPL and ASC and then compared TRayID to TPL_ID)
;			Using the TrayID to find the TPL_ID allows for multiple scheduled processes (innstances) in one run
;			Logging of TrayID and TPL_ID to TPLASC logfile
; V0.22		Strip whitespace from TPL file, to identify the 'L' liquid error flag
;			Added column for liquid error input ";L;"
; December 2014
; V0.23		Move TrayID.tpl and TrayID.ASC to Zipped Archive and delete original TPL & ASC-files
; April through June2015
; V0.24		added ini file section for easy adaptation of filepaths (builtin reset to default upon deletion)
; V0.25		fixed failure extracting correct logfiles from trace.txt in Tecan audittrail
;			added errorlogging for headerline in custom TPL-files
; V0.26		added toggle for Zip function in ini-file
; V0.27		disabled readonly property of TrayID.TPL file Zipfunction: FileSetAttrib($TPLPath & $TrayID & ".tpl", "-R+A", 1)
; 			better sorting of $ASC array
; V0.28		Swap SampleID comparison array: Use $aTPL as leading array instead of $aASC: see main loop in Func _TPLASC_concatenator()
;			This change allows use of TPLASC for both ELISA and C1inh assays
; V0.29		Moved TPLASC.ini location to @scriptdir
;			Adapted for Windows 10
; November 2017
; V0.30		Add E/min to ASC file
;			Disabled option to disable ZipFilesArchive as it convolutes & interferes with archiving of files
;			Updated errorhandling and logging to logfile
;
;
; ************************************************************************************************************************************
;
;						  TPL file dataformat must be as follows:
;
;						   first lines	 				H;1DD-MM-YY;hh:mm:ss
; 						   any subsequent line	 		D;LIMS_ID;SAMPLENAME;MTP_WELLPOSITION;DILUTION_PROTOCOL;ERROR_FLAG
;						   last line					L;
;
;
;						  ASC file dataformat must be as follows:
;
;						   Any Line 					SAMPLENAME;ASBORBANCE;MTP_WELLPOSITION;OK;
;						   OR
;						   Any Line						SAMPLENAME;ASBORBANCE;ASBORBANCE;ASBORBANCE;ASBORBANCE;MTP_WELLPOSITION;OK;
;						   Last Line					MagellanMethodName.mth
;
;
;						  output of TPLASC.exe: TrayID.evo file dataformat:
;
;						   first lines	 				H;1DD-MM-YY;hh:mm:ss;checksum
;														U;user;checksum
;														T;TrayID;checksum
;														A;Evo magellan.mth;checksum
; 						   any subsequent line	 		R;LIMS_ID;SAMPLE_ID;MTP_WELLPOSITION;DILUTION_PROTOCOL;ERROR_FLAG;SAMPLE_ID;ABSORBANCE;MTP_WELLPOSITION;ERROR_FLAG;checksum
;						   Evoware logfilenames			F;logfilename;checksum
;						   last line					L;checksum
;
; *************************************************************************************************************************************
; Functions
;
;	Main()
;
;	- Main executes the functions described below:
;
; 	Func _TPLASC_concatenator():
;	- A new TPLASC file, named $TrayID.evo, with data from both files is written.
; 	- The ASC array is read line by line and the MTP wellnumber herein is looked up in the TPL array
; 	- The ASC and TPL linenumbers with corresponding MTP wellnumbers are then written to $TPLASCpath & $TrayID.evo file
;
; 	Func _TPL_array(ByRef $aTPL, ByRef $TPL_ID) & Func _ASC_array(ByRef $aASC, ByRef $TrayID)
;	- The last created (newest) ASC files are read into the $aASC array
; 	- $TrayID is the name of the ASC file which is extracted from the C:\apps\EVO\ASC\ filelist read in to the $aASCsearch2D array
;	- The $TPL_ID is set as stringtrimright($aTPLsearch2D[$aIndex][0],4) array, where the $aIndex is the indexnumber of the first column
;	  in the $aTPLsearch2D array where the TPL filename 'TrayID & ".tpl"' is found.
; 	- $TPL_ID is the name of the TPL file which is extracted from the C:\apps\EVO\TPL\ filelist read in to the $aTPLsearch2D array
;
;	Func _ZipToArchive(Byref $TrayID)
;
;	- moves and zips TPL and ASC files to C:\apps\EVO\Archief\TPLzip.zip and ASCzip.zip
;
;	Func _EvoLogfiles(ByRef $Date , ByRef $Time , ByRef $Username , ByRef $Logfile1 , ByRef $Logfile2 , ByRef $Logfile3)
;	- retrieves Evoware logfilepaths, username, date and time from Evoware Trace.txt file
;
; 	Func _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;	- logs errorhandling when called in running script
;
; 	Func _ClearLogFile()
; 	- TPLASC.log file is moved to TPLASC1.log when linenumber >100, the old file is overwritten
;
;	Func _Checksum($check)
;	- Checksum for $TPLwrite & $ASCwrite strings
;
;	Func _HFchecksum($Header)
;	- checksum for header and footer lines through $Header and $Footer
;
;	Func _Emin_Asc(ByRef $aASC, ByRef $TrayID)
;	- adds E/min calculation to Asc-file for C1inh assays only
;
; **************************************************************************************************************************************
;
; Start of script
;
#include <Array.au3>
#include <file.au3>
#include <Date.au3>
#include <String.au3>
#include <GUIConstants.au3>
#include <GUIConstantsEx.au3>
#include <WindowsConstants.au3>
#include <EditConstants.au3>
#include <StaticConstants.au3>
#include <GuiStatusBar.au3>
#include <WinAPI.au3>
#include <Constants.au3>
#include <_Zip.au3>

; default TPLASC.ini will be created when not present in C:\Apps\EVO\tplasc\
If not FileExists(@scriptdir & "\TPLASC.ini") then
	Local $iniPath = "AscPath=C:\Apps\EVO\asc\" & @LF & "TplPath=C:\Apps\EVO\tpl\" & @LF & "TPLASCpath=C:\Apps\EVO\tplasc\" _
	& @LF & "LogfilePath=C:\Apps\EVO\tplasc\" & @LF & "ArchivePath=C:\apps\EVO\Archief\"& @LF
    Local $iniLog = "Logfile=1" & @LF & "Logfilename=TPLSASClog.log" & @LF & "Max_lines=500" & @LF		;& "ZipFileToArchive=1"
	IniWriteSection(@scriptdir & "\TPLASC.ini", "Paths", $iniPath)
	IniWriteSection(@scriptdir & "\TPLASC.ini", "Log", $iniLog)
	Endif
$readPaths = IniReadSection(@scriptdir & "\TPLASC.ini", "Paths")
$readLog = IniReadSection(@scriptdir & "\TPLASC.ini", "Log")
;_ArrayDisplay($readPaths)
;_ArrayDisplay($readLog)

; Defined variables
Dim Const $LOGFILE = $readLog[1][1] 				; = 1									; logfile will be created when $logfile = 1
Dim Const $MAX = $readLog[3][1]						; =500 									; max number of lines in logfile
Dim Const $ZipToAr = 1								; Zips ASC and TPL files to archive if ZipFileToArchive entry is set to YES		 ;User Input replace with: $readlog[4][1]
Global $ASCPath = $readPaths[1][1]					;"C:\apps\EVO\asc\"						; ASC file path
Global $TPLPath = $readPaths[2][1]					;"C:\apps\EVO\TPL\"						; TPL file pathfilename extracted from ASC file: MBL110File created: C:\apps\EVO\TPLASC\MBL110.evo
Global $TPLASCPath = $readPaths[3][1]				; "C:\apps\EVO\TPLASC\"					; path of TPLASC *.evo files
Global $Logname = $readPaths[4][1] & $readLog[2][1] ;$TPLASCPath &"TPLSASClog.log"			; path & name of TPLASC logfile
Global $ArchPath = $readPaths[5][1] 				;"C:\apps\EVO\Archief\"	; Archive path for copied ASC files

;local $TrcTxt = "C:\ProgramData\Tecan\Evoware\AuditTrail\log\Trace.txt" ;=Win7/8/9,
;local $TrcTxt = "C:\Program Files\Tecan\Evoware\AuditTrail\log\Trace.txt" ;= WinXP path & name of Evoware Trace.txt logfile
;
;local $aASC								; ASC file read to array from $aASCsearch2D array (1st file from list sorted on dat, use _arraydisplay to check)
;local $aTPL								; TPL file read to array from $aTPLsearch2D array (1st file from list sorted on dat, use _arraydisplay to check)
;local $header								; data for header checksum
;local footer								; data for footer checksum
;local $TPLASC 								; new *.evo file to write concatenated data to
;Local $TrayID								; ASC filename = name for the new TPLASC file = $TrayID.evo
;local $aIndex								; $aIndex = _ArraySearch($aTPLsearch2D, $TrayID & ".tpl")
;local $TPL_ID								; $TPL_ID = stringtrimright($aTPLsearch2D[$aIndex][0],4)
;local $checkTPL 							; checks for the right format of ASC folder
;local $checkASC							; checks for the right format of TPL folder
;local $aTPLsearch							; lists files in $ASCPath in array for examination
;local $aASCsearch							; lists files in $TPlPath in array for examination
;local $aTPLsearch2D						; lists file in $aTPLsearch	in array for examination
;local $aASCsearch2D						; lists file in $aASCsearch	in array for examination
;local $aASCSamLen							; length of samplename in ASC-file ; samplename is always found in front of 1st ";" in ASCline file
;local $TPLSamPos							; position of samplename in TPL file with linenumber corresponding to same samplename in Ascifile line
;local $MTPpos								; position of MTP well number is always found 1 Chr to the right of the 2nd  ";" in the ASClinenumber
;local $Well								; $Well is the MTP position: 3 characters read from the ASC line at $MTPpos
;Local $aASCSample							; Samplename from ASCline (number of the loop
;Local $TPLSample							; Samplename from the TPLfile linenumber with the same MTP position ($Well) as the ASCfile linenumber (in the loop)
;local $TPLine								; the TPL file line number at which the same MTP position is found as in the ASC file
;local $ASCLine								; the ASC file line number
;local $FileName							; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $Logdata								; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $TimeStamp							; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $hFile								; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;$TrcTxtCount								; = _FileCountLines($TrcTxt)
;$arLOG 									; array with Evoware logfiles
;$arCount									; $arLOG[0]: number of entries in $arLOG
;$filelist[3][3]							; array to write DateTime, Username and Logfile path to from $arLOG
;$DateTime 									; = StringSplit ( $filelist[0][0], " ", 1)
;$Date 										; = $DateTime[1]
;$Time										; = $DateTime[2]
;$Username									; = $filelist[0][1]
;$Logfile1									; = $filelist[0][2]
;$Logfile2									; = $filelist[1][2]
;$Logfile3									; = $filelist[2][2]
;$Windows									; = @OSVersion
;$ZipToAr									; boolean to toggle ZipToArchive function on/off
;
;<---------------------------------------------------------------------------------------------------------------------------------------
;<---------------------------------------------------------------------------------------------------------------------------------------
Func _Main()
_TPLASC_concatenator()
_ClearLogFile()
EndFunc
;<---------------------------------------------------------------------------------------------------------------------------------------
;<---------------------------------------------------------------------------------------------------------------------------------------
Func _TPLASC_concatenator()
local $aTPL = ""
local $aASC = ""
local $TrayID = ""		;stringtrimright($aASCsearch2D[1][0],4)
local $TPL_ID = ""		;stringtrimright($aTPLsearch2D[$aIndex][0],4)
local $Date = ""		;$DateTime[1]
local $Time = ""		;$DateTime[2]
local $Username =""		;$filelist[0][1]
local $Logfile1 = ""	;$filelist[0][2]
local $Logfile2 = ""	;$filelist[1][2]
local $Logfile3 = ""	;$filelist[2][2]

;Read return values to variables from help functions
_ASC_array($aASC, $TrayID)
_TPL_array($aTPL, $TPL_ID, $TrayID)
_EvoLogfiles($Date , $Time , $Username , $Logfile1 , $Logfile2 , $Logfile3)

;If TrayID.ASC and TrayID.TPL filename do not match the program will end here
If $TPL_ID<>$TrayID then
 If $LOGFILE = 1 Then _SendAndLog($TrayID & "TPL & ASC files don't match, check fileame and date", $Logname, True)
 MsgBox(4096, "Error Log", "TPL & ASC files don't match" & @CRLF)
 Exit
EndIf
local $TPLASC = fileopen($TPLASCPath & $TrayID & ".evo", 2 +8)
; write header lines & checksum		CLIS (Sanquin LIMS) commitments
; 									H;1DD-MM-YY;hh:mm:ss
;									U; user
;									T; TrayID
;									A; Evo magellan.mth
Local $header
$Header = $aTPL[1] & ";"
FileWriteline($TPLASC, $aTPL[1] & ";" & _HFchecksum($Header) &  @CRLF)
$Header = "U;Username;"& $Username & ";" & $Date & ";" & $Time & ";"
FileWriteline($TPLASC, $Header & _HFchecksum($Header) &  @CRLF)
$Header = "T;" & $TrayID & ";"
FileWriteline($TPLASC, $Header & _HFchecksum($Header) &  @CRLF)
$Header = "A;MagellanMethod;" & $aASC[$aASC[0]] & ";"
;[$aASC[0]]is the number of lines in the array; here used to read data ;from the last line of the array i.e. :  $ASC[$aASC[0]
FileWriteline($TPLASC, $Header & _HFchecksum($Header) & @CRLF)
$Header = ""
		 _ArrayDelete($aTPL, $aTPL[0])											;TPL array adjusted to read in loop
		 _ArrayDelete($aTPL, 1)
		 _ArrayDelete($aTPL, 0)
		 _ArrayDelete($aASC, $aASC[0])											;ASC array adjusted to read in loop
		 _ArrayDelete($aASC, 0)
		;_ArrayDisplay($aASC)
		 _ArraySort($aTPL, 0, 0, 0, 0, 1)											; array is sorted alphabetically
		;_ArraySort($aASC, 0, 0, 0, 0, 1)

;_ArrayDisplay($aTPL)
;_ArrayDisplay($aASC)

;for $ASCline = 0 to ubound($aTPL)-1
for $TPLine = 0 to ubound($aTPL)-1

	  ;$MTPpos = stringinstr($aASC[$ASCLine], ";", 0, 2) +1						; position of MTP well number is always found 1 Chr to the right of the 2nd  ";" in the ASClinenumber
	  $MTPpos = stringinstr($aTPL[$TPLine], ";", 0,3)+1
	  $Well = stringmid($aTPL[$TPLine],$MTPpos, 3)								; $Well is the MTP position: 3 characters read from the TPL line at $MTPpos
	  ;$Well = stringmid($aASC[$ASCLine],$MTPpos, 3)
	  $ASCLine = _ArraySearch($aASC, $Well,0,0,0,1,3,False)							; the ASC file line number at which the same MTP position is found as in the TPL file
	  $aASCSamLen= stringinstr($aASC[$ASCLine], ";", 0, 1) -1					; length of samplename in ASC-file ; samplename is always found in front of 1st ";" in ASCline file
	  $TPLSamPos = stringinstr($aTPL[$TPLine], ";", 0, 2) +1					; position of samplename in TPL file with linenumber corresponding to same samplename in Ascifile line
	  $aASCSample = stringleft($aASC[$ASCLine], $aASCSamLen)  					; Samplename from ASCline (number of the loop)
	  $TPLSample = stringmid($aTPL[$TPLine], $TPLSampos, $aASCSamLen)			; Samplename from the TPLfile linenumber with the same MTP position ($Well) as the ASCfile linenumber (in the loop)
	  $TPLwrite = StringStripWS($aTPL[$TPLine],2)
	  $ASCwrite = StringStripWS($aASC[$ASCLine],1)

; msgbox(4096,"",$MTPpos & " " & $Well & " " & $TPLine& " " & $ASCLine & " " & $aASCSamLen & " " & $TPLSamPos & @CRLF & $aASCSample & " " & $TPLSample & " " & $TPLwrite & " " & $ASCwrite)
	 Select
		Case $aASCSample = $TPLSample											; determines whether the ASC samplename is the same as the TPL samplename and if so:
			FileWriteline($TPLASC, $TPLwrite & $ASCwrite & _Checksum($TPLwrite, $ASCwrite) & @CRLF) 	; write the matching TPL and ASC data to the TPLASC file
																										; format: R;LIMS_ID;SAMPLENAME;MTP_WELLPOSITION;checksum
	    Case $aASCSample <> $TPLSample																	; if samplenames are not exactly the same a message pops up: check the line numbers int he ASC and
			If $LOGFILE = 1 Then _SendAndLog($aASCSample & " & " _
			& $TPLSample & " do not match." & @CRLF _
			& "check TPL filelinenumber " & $TPLine & @CRLF _
			& "check ASC filelinenumber " & $ASCLine, $Logname, True)			; writes not matching linenumbers to logfile ASC en TPL linenumbers
	  EndSelect
next

; write footer lines & checksum			F;Evoware logfilename1 ;checksum
;										F;Evoware logfilename2 ;checksum
;										F;Evoware logfilename3 ;checksum
;										L;checksum
$Footer = "F;" & $Logfile1 & ";"
FileWriteline($TPLASC, $Footer & _HFchecksum($Footer)& @CRLF)
$Footer = "F;" & $Logfile2 & ";"
FileWriteline($TPLASC, $Footer & _HFchecksum($Footer)& @CRLF)
$Footer = "F;" & $Logfile3 & ";"
FileWriteline($TPLASC, $Footer & _HFchecksum($Footer)& @CRLF)
$Footer = "L;"
FileWriteline($TPLASC, $Footer & _HFchecksum($Footer)& @CRLF)
$Footer = ""
If $LOGFILE = 1 Then _SendAndLog("Logfile1: " & $Logfile1 , $Logname, True)
If $LOGFILE = 1 Then _SendAndLog("Logfile2: " & $Logfile2 , $Logname, True)
If $LOGFILE = 1 Then _SendAndLog("Logfile3: " & $Logfile3 & ";" & ".evo", $Logname, True)
If $LOGFILE = 1 Then _SendAndLog("File created: " & $TPLASCPath & $TrayID & ".evo", $Logname, True)

; append E/min to ASC file before it is zipped to archive
; Select case to restrict execution only for C1inh assays
Select
	Case StringLeft($TrayID,5) = "c1est"
		_Emin_Asc($aASC, $TrayID)
	Case StringLeft($TrayID,5) = "c1inh"
		_Emin_Asc($aASC, $TrayID)
EndSelect

; Zip TPL & ASC files to archive, or not...
Select
   Case $ZipToAr = 1
	  _ZipToArchive($TrayID)
   Case $ZipToAr = 0
	  msgbox(4096, "TPLASC.exe message","TPL and ASC files are not zipped to archive" & @CRLF & "check and edit @scriptdir &\TPLASC.ini file", 3)
   Case Else
	  msgbox(4096, "TPLASC.exe message","@scriptdir &\TPLASC.ini file is corrupted" & @CRLF _
	  & "TPLASC.exe message","TPL and ASC files are not zipped to archive" & @CRLF & "@scriptdir &\TPLASC.ini file will be reset to default", 3)
	  FileDelete(@scriptdir & "\TPLASC.ini")
EndSelect
fileclose($TPLASCPath & $TrayID & ".evo")
fileclose($ASCPath & $TrayID & ".asc")
fileclose($TPLPath & $TrayID & ".tpl")
EndFunc ;_TPLASC_concatenator()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _ZipToArchive($TrayID);ByRef $ArchPath, ByRef $TPLPath,
If not fileexists($ArchPath & "TPLzip.zip") then _Zip_Create($ArchPath & "TPLzip.zip",0)
If not fileexists($ArchPath & "ASCzip.zip") then _Zip_Create($ArchPath & "ASCzip.zip",0)
FileSetAttrib($TPLPath & $TrayID & ".tpl", "-R+A", 1)
If Not FileSetAttrib($TPLPath & $TrayID & ".tpl", "-R+A", 1) Then
        MsgBox($MB_SYSTEMMODAL, "Error", "Problem setting TPL-fie attributes.",3)
    EndIf
FileSetAttrib($ASCPath & $TrayID & ".asc", "-R+A", 1)
If Not FileSetAttrib($ASCPath & $TrayID & ".asc", "-R+A", 1) Then
        MsgBox($MB_SYSTEMMODAL, "Error", "Problem setting ASC-file attributes.",3)
    EndIf
_Zip_AddItem($ArchPath & "TPLzip.zip", $TPLPath & $TrayID & ".tpl" , ""  , 21)
_Zip_AddItem($ArchPath & "ASCzip.zip" , $ASCPath & $TrayID & ".asc" ,  "" , 21)
If @error = 0 then
	Select
		Case FileExists($ArchPath & "ASCzip.zip")
			_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl copied to " & $Archpath & "ASCzip & TPLzip archives.", $Logname, True)
			filedelete($ASCPath & $TrayID & ".asc")
			filedelete($TPLPath & $TrayID & ".tpl")
			_SendAndLog("The original " & $TrayID & ".asc & " & $TrayID & ".tpl were deleted after copying to TPLzip archives.", $Logname, True)
		Case Not FileExists($ArchPath & "TPLzip.zip")
			_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl NOT added to" & $Archpath & "ASCzip & TPLzip archives.", $Logname, True)
			_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl NOT deleted from their directories.", $Logname, True)
			_SendAndLog("Something went wrong. Check your assay: Joblist OK? Barcodes OK?", $Logname, True)
	EndSelect
EndIf

EndFunc ; _ZipToArchive
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func  _ASC_array(ByRef $aASC, ByRef $TrayID)

; Retrieve ASC File for concatenation with TPL file
; Global $ASCPath = "C:\apps\EVO\asc\"
$checkASC = StringRegExp($ASCPath,"^.+\\$",0)
	  If $checkASC = 0 Then $ASCPath = $ASCPath & "\"
		 If @error = -1 Then
			If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log", "   " & $ASCPath & " has no files" & @CRLF & @CRLF & _
			"    ! Script aborted !")
		 Exit
	  EndIf
$aASCsearch = _FileListToArray($ASCPath,"*.Asc",1)
	  If Not IsArray($aASCsearch) Then
		 If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log", "   " & $ASCPath & " has no files" & @CRLF & @CRLF & _
			"   ! Script aborted !")
		 Exit
	  EndIf
Global $aASCsearch2D[10][2]
ReDim $aASCsearch2D[$aASCsearch[0]+1][2]
$aASCsearch2D[0][0] = $aASCsearch[0]
For $i=1 to $aASCsearch[0]
    $aASCsearch2D[$i][0] = $aASCsearch[$i]
    $aASCsearch2D[$i][1] = FileGetTime($ASCPath & $aASCsearch[$i],0,1)
Next
_ArraySort($aASCsearch2D,1,1,"",1)
_FileReadToArray($ASCPath & $aASCsearch2D[1][0], $aASC)

; Retrieve TrayID = ASC filename
$TrayID = stringtrimright($aASCsearch2D[1][0],4)
	  If @error = -1 then
		 If $LOGFILE = 1 Then _SendAndLog($TrayID & "TrayID error", $Logname, True)
		 MsgBox(4096, "Error Log", "TrayID format incorrect" & @CRLF)
		 Exit
	  EndIf
If $LOGFILE = 1 Then _SendAndLog("ASC file extracted from C:\apps\EVO\ASC folder: " & $aASCsearch2D[1][0] & ";file date & time of creation: " & $aASCsearch2D[1][1], $Logname, True)

;_ArrayDisplay($aASC)
EndFunc ; _ASC_array()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _Emin_Asc(ByRef $aASC, ByRef $TrayID)

; calculate E/min for C1inh assays for emergency procedure when LIMS is offline
; Retrieve ASC File for concatenation with TPL file
; Global $ASCPath = "C:\apps\EVO\asc\" (by default)
$checkASC = StringRegExp($ASCPath,"^.+\\$",0)
	  If $checkASC = 0 Then $ASCPath = $ASCPath & "\"
		 If @error = -1 Then
			If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log", "   " & $ASCPath & " has no files" & @CRLF & @CRLF & _
			"    ! Script aborted !")
		 Exit
	  EndIf
$aASCsearch = _FileListToArray($ASCPath,"*.Asc",1)
	  If Not IsArray($aASCsearch) Then
		 If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log", "   " & $ASCPath & " has no files" & @CRLF & @CRLF & _
			"   ! Script aborted !")
		 Exit
	  EndIf
Global $aASCsearch2D[10][2]
ReDim $aASCsearch2D[$aASCsearch[0]+1][2]
$aASCsearch2D[0][0] = $aASCsearch[0]
For $i=1 to $aASCsearch[0]
    $aASCsearch2D[$i][0] = $aASCsearch[$i]
    $aASCsearch2D[$i][1] = FileGetTime($ASCPath & $aASCsearch[$i],0,1)
Next
_ArraySort($aASCsearch2D,1,1,"",1)
_FileReadToArray($ASCPath & $aASCsearch2D[1][0], $aASC)

; Retrieve TrayID = ASC filename
$TrayID = stringtrimright($aASCsearch2D[1][0],4)

; Add E/min to ASC file!
For $i=1 to $aASC[0]-1
    $aEmin = Stringsplit($aASC[$i],";")
	;_ArrayDisplay($aEmin)
	If $aEmin[0]=8 then													; size of array is only 8 for C1inh assays so calculation of E/min is skipped if otherwise!
		global $strEmin
		$Round = Round(($aEmin[5]-$aEmin[2])/3, 5)*1000
		$RoundFormat = StringFormat ("%.2f",$Round )
		$strEmin = $aEmin[1] & "; E/min = " & $Roundformat & ";"		; $aEmin[1] = SampleID ;msgbox(4096,"E/min", $strEmin)
		$aASC[$i] = $strEmin
		FileWrite($ASCPath & $TrayID & ".asc", $aASC[$i] & @CRLF)
	EndIf
Next

If $LOGFILE = 1 Then _SendAndLog("C1inh assay E/Min data added to ASC file. File date & time of creation: " & $aASCsearch2D[1][1], $Logname, True)

FileClose($ASCPath & $TrayID & ".asc")
;_ArrayDisplay($aASC)
EndFunc ; _Emin_Asc()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _TPL_array(ByRef $aTPL, ByRef $TPL_ID, $TrayID)

; Retrieve TPL File for concatenation with ASC file
; Global $TPLPath = "C:\apps\EVO\TPL\"
$checkTPL = StringRegExp($TPLPath,"^.+\\$",0)
	  If $checkTPL = 0 Then $TPLath = $TPLPath & "\"
		 If @error = -1 then
			Msgbox(0,"Error Log", $TPLPath & " has no files" & @CRLF & @CRLF & _
			"   ! Script aborted !")
			If $LOGFILE = 1 Then _SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
			Exit
		 EndIf
$aTPLsearch = _FileListToArray($TPLPath,"*.TPL",1)
	  If Not IsArray($aTPLsearch) Then
		  Msgbox(0,"Error Log", $TPLPath & " has no files" & @CRLF & @CRLF & _
			"   ! Script aborted !")
			If $LOGFILE = 1 Then _SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
		  Exit
	  EndIf
Global $aTPLsearch2D[10][2]
ReDim $aTPLsearch2D[$aTPLsearch[0]+1][2]
$aTPLsearch2D[0][0] = $aTPLsearch[0]
For $i=1 to $aTPLsearch[0]
    $aTPLsearch2D[$i][0] = $aTPLsearch[$i]
    $aTPLsearch2D[$i][1] = FileGetTime($TPLPath & $aTPLsearch[$i],0,1)
Next
_ArraySort($aTPLsearch2D,1,1,"",1)
; original sort array on filetime and choose the newest/latest file for comparison with
;_FileReadToArray($TPLPath & $aTPLsearch2D[1][0], $aTPL))
$aIndex = _ArraySearch($aTPLsearch2D, $TrayID & ".tpl")
If @error then
	  If $LOGFILE = 1 Then _SendAndLog($TrayID & ".tpl file does not exist in TPL file folder, script aborted", $Logname, True)
		  MsgBox(4096, "Error Log", "Array index incorrect, " & @CRLF & _
		  $TrayID & ".tpl file does not exist in TPL file folder" & @CRLF & @CRLF & _
		  "! script aborted !")
	  Exit
EndIf
_FileReadToArray($TPLPath & $aTPLsearch2D[$aIndex][0] , $aTPL)
If stringleft($aTPL[1],2)<> "H;" then
	  MsgBox(4096, "Error Log", "Array index incorrect, " & @CRLF & _
		 $TrayID & ".tpl :first line in file does not contain H; date & time header" & @CRLF & @CRLF & _
		 "! check "& $TrayID & ".tpl, script aborted !")
		 If $LOGFILE = 1 Then _SendAndLog($TrayID & ".tpl :first line in file does not contain H; date & time header, script aborted", $Logname, True)
	  Exit
   EndIf

; change 'D' to 'R' in $aTPL array
For $j = 1 to ubound($aTPL)-1
	 $aTPL[$j] = StringStripWS($aTPL[$j], $STR_STRIPLEADING + $STR_STRIPTRAILING)
	Local $DtoR
	If StringLeft ( $aTPL[$j], 1 ) = "D" Then
	$DtoR = StringReplace ($aTPL[$j], "D" , "R" , 1, 0 )
	$aTPL[$j] = $DtoR
	EndIf
	; Check for liquid error flag, add ";"
	Local $L
	If Stringright ( $aTPL[$j], 2 ) = ";L" Then
		$L = StringReplace ($aTPL[$j], ";L" , ";L;" , 1, 0)
		$aTPL[$j] = $L
	ElseIf Stringright ( $aTPL[$j], 1 ) = ";" Then
		$L = stringreplace($aTPL[$j], ";", ";;", -1, 0)
		$aTPL[$j] = $L
	EndIf
Next

; Retrieve TPL filename ID
	$TPL_ID = stringtrimright($aTPLsearch2D[$aIndex][0],4)
	  If @error = -1 then
		 If $LOGFILE = 1 Then _SendAndLog($TPL_ID & "TPL_ID error", $Logname, True)
		 MsgBox(4096, "Error Log", "TPL_ID format incorrect" & @CRLF)
		 Exit
	  EndIf
If $LOGFILE = 1 Then _SendAndLog("TPL filename from ASC file TrayID comparison: " & $aTPLsearch2D[$aIndex][0], $Logname, True)	; write TPL filename to logfile
; filemanagement for future use:
;_ArrayDisplay($aTPL)
EndFunc ; _TPL_array()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _EvoLogfiles(ByRef $Date , ByRef $Time , ByRef $Username , ByRef $Logfile1 , ByRef $Logfile2 , ByRef $Logfile3)
; Function Evowarelogfiles data retrieval for TPLASC from Trace.txt
; Format Trace.txt in "C:\ProgramData\Tecan\Evoware\AuditTrail\log\Trace.txt"
; 2014.09.22 08:56:04  twin			C:\Program Files\TECAN\EVOware\Audittrail\Log\EVO_20140922_085604.LOG
; 2014.09.22 08:56:05  twin			C:\Program Files\TECAN\EVOware\Audittrail\Log\USR_20140922_085604.LOG
; 2014.09.22 08:56:05  twin			C:\Program Files\TECAN\EVOware\Audittrail\Log\ERR_20140922_085604.LOG
local $Windows = @OSVersion
Dim $arLOG
Dim $filelist[3][3]
local $TrcTxt
		$TrcTxt = "C:\ProgramData\Tecan\Evoware\AuditTrail\log\trace.txt"
Select	; determine Windows OS version to select path of Evoware Trace.txt
   Case $Windows = "WIN_10" OR "WIN_81" OR "WIN_8" OR "WIN_7"
		 $TrcTxt = "C:\ProgramData\Tecan\Evoware\AuditTrail\log\trace.txt"
					;C:\ProgramData\Tecan\Evoware\Auditrail\log
		 If @error then
		 If $LOGFILE = 1 Then _SendAndLog("C:\ProgramData\Tecan\Evoware\AuditTrail\log\trace.txt not found, script aborted", $Logname, True)
			 MsgBox(4096, "Error Log", "Array index incorrect, " & @CRLF & _
			 "C:\ProgramData\Tecan\Evoware\AuditTrail\log\trace.txt not found" & @CRLF & @CRLF & _
			 "! script aborted !")
		 Exit
		 EndIf
	Case $Windows = "WIN_XP"
		 $TrcTxt = "C:\Program Files\Tecan\Evoware\AuditTrail\log\trace.txt"
		 If @error then
		 If $LOGFILE = 1 Then _SendAndLog("C:\Program Files\Tecan\Evoware\AuditTrail\log\trace.txt not found, script aborted", $Logname, True)
			 MsgBox(4096, "Error Log", "Array index incorrect, " & @CRLF & _
			 "C:\Program Files\Tecan\Evoware\AuditTrail\log\trace.txt" & @CRLF & @CRLF & _
			 "! script aborted !")
		 Exit
		 EndIf
EndSelect

; count lines in Trace.txt and read entries to array
local $TrcTxtCount = _FileCountLines($TrcTxt)
_FileReadToArray($TrcTxt, $arLOG)
local $arCount = $arLOG[0]

;_arraydisplay($arLOG)
; delete all non-.log files from array...
local $i = 0
For $h = $TrcTxtCount to 1 step -1
   If Stringright($arLOG[$h], 4) = ".log" then
	   ; Split the first found LOG file entry from $arLOG to $Logfile array
	   local $Logfile = StringSplit ( stringreplace($arLOG[$h], "  ", ";"), ";", 1)
	   $j= $Logfile[0]
		  While $j>0 						;delete empty entries in $Logfile
			  If  $Logfile[$j] = "" then _arraydelete($Logfile,$j)
			  $j = $j-1
		  Wend
	   $filelist[$i][0] = $Logfile[1]	; Date & Time
	   $filelist[$i][1] = $Logfile[2]	; Username
	   $filelist[$i][2] = $Logfile[3]	; Evoware Logfile path
	   $i = $i+1
   ElseIf @error Then
	  MsgBox($MB_SYSTEMMODAL, "Error", "Error reading trace.txt")
	  Exit
   EndIf
   $TrcTxtCount = $TrcTxtCount-1
   If $i = 3 then ExitLoop
   Next

;_ArrayDisplay($filelist)
$DateTime = StringSplit ( $filelist[0][0], " ", 1)
$Date = $DateTime[1]
$Time = $DateTime[2]
$Username = $filelist[0][1]
$Logfile1 = $filelist[0][2]
$Logfile2 = $filelist[1][2]
$Logfile3 = $filelist[2][2]
EndFunc ;_EvoLogfiles()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)

;line		log
;	252		If $LOGFILE = 1 Then _SendAndLog($TrayID & "TPL & ASC files don't match, check fileame and date", $Logname, True)
;	313		If $LOGFILE = 1 Then _SendAndLog($aASCSample & " & " _
;			& $TPLSample & " do not match." & @CRLF _
;			& "check TPL filelinenumber " & $TPLine & @CRLF _
;			& "check ASC filelinenumber " & $ASCLine, $Logname, True)		; writes not matching linenumbers to logfile ASC en TPL linenumbers
;	334 	If $LOGFILE = 1 Then _SendAndLog("Logfile1: " & $Logfile1 , $Logname, True)
;	335		If $LOGFILE = 1 Then _SendAndLog("Logfile2: " & $Logfile2 , $Logname, True)
;	336		If $LOGFILE = 1 Then _SendAndLog("Logfile3: " & $Logfile3 & ";" & ".evo", $Logname, True)
;	337		If $LOGFILE = 1 Then _SendAndLog("File created: " & $TPLASCPath & $TrayID & ".evo", $Logname, True)
;	376		_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl added to" & $Archpath & "ASCzip & TPLzip archives.", $Logname, True)
;	379		_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl deleted from their directories.", $Logname, True)
;	381		_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl NOT added to" & $Archpath & "ASCzip & TPLzip archives.", $Logname, True)
;	382		_SendAndLog($TrayID & ".asc & " & $TrayID & ".tpl NOT deleted from their directories.", $Logname, True)
;	383		_SendAndLog("Something went wrong. Check your assay: Joblist OK? Barcodes OK?", $Logname, True)
;	397		If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
;	405		If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
;	426		If $LOGFILE = 1 Then _SendAndLog($TrayID & "TrayID error", $Logname, True)
;	431		If $LOGFILE = 1 Then _SendAndLog("ASC file extracted from C:\apps\EVO\ASC folder: " & $aASCsearch2D[1][0] & ";file date & time of creation: " & $aASCsearch2D[1][1], $Logname, True)
;	447		If $LOGFILE = 1 Then _SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
;	455		If $LOGFILE = 1 Then _SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
;	473		If $LOGFILE = 1 Then _SendAndLog($TrayID & ".tpl file does not exist in TPL file folder, script aborted", $Logname, True)
;	486		If $LOGFILE = 1 Then _SendAndLog($TPL_ID & "TPL_ID error", $Logname, True)
; 	513		If $LOGFILE = 1 Then _SendAndLog($TrayID & ".tpl :first line in file does not contain H; date & time header, script aborted", $Logname, True)
;	518		If $LOGFILE = 1 Then _SendAndLog("TPL filename from ASC file TrayID comparison: " & $aTPLsearch2D[$aIndex][0], $Logname, True)
;	540		If $LOGFILE = 1 Then _SendAndLog("C:\ProgramData\Tecan\Evoware\AuditTrail\log\trace.txt not found, script aborted", $Logname, True)
;	549		If $LOGFILE = 1 Then _SendAndLog("C:\Program Files\Tecan\Evoware\AuditTrail\log\trace.txt not found, script aborted", $Logname, True)
If $Filename == -1 Then $Filename = $Logname ;$TPLASCPath &"TPLSASClog.log"
   ;Send($Logdata)
   $hFile = FileOpen($FileName, 1)
    If $hFile <> -1 Then
        If $TimeStamp = True Then $Logdata = _Now() & ' ; ' & $Logdata
        FileWriteLine($hFile, $Logdata)
        FileClose($Filename)
    EndIf
EndFunc ;_SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _ClearLogFile()

; checks logfile: if existing logfile exceeds maximum number of lines ($MAX) a new logfile1 will be made.
If $LOGFILE = 1	then Fileopen($Logname, 1)
   If _filecountlines($logname) > $MAX then
	  filemove($logname, stringtrimright($logname,4) & "1.log", 1 +8)
	  fileopen($logname, 2+8)
   EndIf
   Fileclose($Logname)
EndFunc ;Func _ClearLogFile()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _Checksum($TPLwrite, $ASCwrite)
Local $count = StringToASCIIArray($TPLwrite & $ASCwrite)
Local $sum
Local $add
Global $checksum
For $k= 0 to Ubound($count)-1
	$add = $count[$k]
	$Sum = $add + $sum
Next
$checksum = Mod($sum, 64) +33
return($checksum)
EndFunc ;_Checksum($TPLwrite, $ASCwrite)
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _HFchecksum($Header)
;$Heder or $Footer
Local $count = StringToASCIIArray($Header)
Local $sum
Local $add
Global $checksum
For $k= 0 to Ubound($count)-1
	$add = $count[$k]
	$Sum = $add + $sum
Next
$checksum = Mod($sum , 64) +33
return($checksum)
EndFunc ;Func _ClearLogFile()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
; Execution of script:
_Main()

