; **************************************************************************************************************************************
;
; TPLASC version 0.16 Dion Methorst & Ed Nieuwenhuys, Sanquin IPB IMMC/CAP, August 2013.
; concatenates your Tecan EVO TPL and ASCII files for direct use in LIMS database
;
; **************************************************************************************************************************************
;
; If an ASCII file and TPL file are present in the folders as defined by $ASCPath  & $TPLPath
; then this script will:
; -	read the TPL file into an array
; -	read the ASCII file into an array
; - TrayID is extracted from ASCII filename
; - ASCII and TPL array obsolete filelines are then deleted to equal dimension
; - ASCII filelines are read 1 by 1 in a loop, in each cycle the corresponding line in the TPL file is looked up
; - In the same loop each cycle the ASCII and TPL data is written to the TPLASC file
; - The TPLASC.evo file is made in the folder defined by $TPLASCPath
; - While the script is running the SendAndLog function is logging all the crucial events in the scripts
; - This errorhandling may be incomplete but thusfar hasn't shown any problems that might indicate such
;
; **************************************************************************************************************************************
;
; Changelog
;
; July 2013 : in development
; V0.11 auto open TPL and ASCII files : in development
; V0.12 Added Errorhandling & logfile (not fully tested)
; V0.12 script divided in 3 functions, added main function
; V0.13 added log function and clearlog function;
; V0.14 added constant for maximum number lines in logfile, added remarks for linenumbers with logfile function call
; V0.15 writes complete lastline of ASCII file to TPLASC first line: complete Magellan method filename which contains the sanquin number of the used EVO
;
; September 2014
; V0.16 	addition of checksom
;			addition of lines U; username T; trayID  and A; Evo magellan.mth with MacihneSqnNumberID
;			addition of logfilenames from logfile folder
;			checking if TrayID of ASCii file matches TPL file, ends script if not
;			change 'D' identiefier in $aTPL array to 'R' for result identiefier in TrayID.evo file
;
; **************************************************************************************************************************************
;
;						   TPL file dataformat must be as follows:
;
;						   first lines	 				H;1DD-MM-YY;hh:mm:ss
;														U; user
;														T; TrayID
;														A; Evo magellan.mth
;
; D wordt een R?		   any subsequent line	 		R;LIMS_ID;SAMPLENAME;MTP_WELLPOSITION;;
;
;						   Evoware logfilenames			F;
;
;						   last line					L;
;
;						   ASCII file dataformat must be as follows:
;
;						   Any Line 					SAMPLENAME;ASBORBANCE;MTP_WELLPOSITION;OK;
;						   Last Line					MagellanMethodName.mth
;
; **************************************************************************************************************************************
; Functions
;
;	Main()
;
;	- Main carries out/calls the function that are described below:
;
; 	Func _TPL_array() & Func _ASC_array():
;	- The last created (newest) TPL and ASCii files are read into a TPL and an ASC array
;
; 	Func _TPLASC_concatenator():
;	- A new TPLASC file, named $TrayID.evo, with data from both files is written.
; 	- $TrayID is the name of the ASCII file which is extracted from the C:\apps\EVO\ASC\ filelist read in to the $aASCsearch2D array
; 	- The ASCII array is read line by line and the MTP wellnumber herein is looked up in the TPL array
; 	- The ASC and TPL linenumbers with corresponding MTP wellnumbers are then written to $TPLASCpath & $TrayID.evo file
;
; 	Func _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;	- logs errorhandling when called in running script
;
; 	Func _ClearLogFile()
; 	- TPLASC.log file is moved to TPLASC1.log when linenumber >100, the old file is overwritten
;
;	Func _Checksum($check)
;
; **************************************************************************************************************************************

; Start of script
#include <Array.au3>
#include <file.au3>
#include <Date.au3>
#include <GUIConstants.au3>
#include <GUIConstantsEx.au3>
#include <WindowsConstants.au3>
#include <EditConstants.au3>
#include <StaticConstants.au3>
#include <GuiStatusBar.au3>
#include <WinAPI.au3>
#include <Constants.au3>
#include <String.au3>
;#include <_Zip.au3>

; Defines
Dim Const $LOGFILE = 1						; logfile will be created when $logfile = 1
Dim Const $MAX = 100						; max number of lines in logfile
Global $ASCPath = "C:\apps\EVO\asc\"		; ASCII file path
Global $TPLPath = "C:\apps\EVO\TPL\"		; TPL file pathfilename extracted from ASCII file: MBL110File created: C:\apps\EVO\TPLASC\MBL110.evo
Global $TPLASCPath = "C:\apps\EVO\TPLASC\"	; path of TPLASC *.evo files
Global $Logname = $TPLASCPath &"TPLSASClog.log"; path & name of logfile
Global $aASC								; ASCII file read to array from $aASCsearch2D array (1st file from list sorted on dat, use _arraydisplay to check)
Global $aTPL								; TPL file read to array from $aTPLsearch2D array (1st file from list sorted on dat, use _arraydisplay to check)
Global $TPLASC 								; new *.evo file to write concatenated data to
Local $TrayID								; ASCII filename = name for the new TPLASC file = $TrayID.evo
local $checkTPL 							; checks for the right format of ASCII folder
local $checkASC								; checks for the right format of TPL folder
local $aTPLsearch							; lists files in $ASCPath in array for examination
local $aASCsearch							; lists files in $TPlPath in array for examination
local $aTPLsearch2D							; lists file in $aTPLsearch	in array for examination
local $aASCsearch2D							; lists file in $aASCsearch	in array for examination
local $aASCSamLen							; length of samplename in ASC-file ; samplename is always found in front of 1st ";" in ASCline file
local $TPLSamPos							; position of samplename in TPL file with linenumber corresponding to same samplename in Ascifile line
local $MTPpos								; position of MTP well number is always found 1 Chr to the right of the 2nd  ";" in the ASClinenumber
local $Well									; $Well is the MTP position: 3 characters read from the ASCii line at $MTPpos
Local $aASCSample							; Samplename from ASCline (number of the loop
Local $TPLSample							; Samplename from the TPLfile linenumber with the same MTP position ($Well) as the ASCfile linenumber (in the loop)
local $TPLine								; the TPL file line number at which the same MTP position is found as in the ASCii file
local $ASCLine								; the ASCII file line number
;local $FileName							; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $Logdata								; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $TimeStamp							; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)
;local $hFile								; _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)

;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Func _Main()

_TPL_array()
_ASC_array()
_TPLASC_concatenator()
_ClearLogFile()

EndFunc

;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _TPL_array()

; Retrieve TPL File for concatenation with ASC file
; Global $TPLPath = "C:\apps\EVO\TPL\"

$checkTPL = StringRegExp($TPLPath,"^.+\\$",0)
	  If $checkTPL = 0 Then $TPLath = $TPLPath & "\"
		 If @error = -1 then
			Msgbox(0,"","Sorry but " & $TPLPath & " has no files")
			If $LOGFILE = 1 Then _SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
			Exit
		 EndIf

$aTPLsearch = _FileListToArray($TPLPath,"*.TPL",1)
	  If Not IsArray($aTPLsearch) Then
		  Msgbox(0,"","Sorry but " & $TPLPath & " has no files")
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
_ArrayDisplay($aTPLsearch2D)
_FileReadToArray($TPLPath & $aTPLsearch2D[1][0], $aTPL)

; change 'D' to 'R' in $aTPL array
For $j = 1 to ubound($aTPL)-1
	Local $DtoR
	If StringLeft ( $aTPL[$j], 1 ) = "D" Then
	$DtoR = StringReplace ($aTPL[$j], "D" , "R" , 1, 0 )
	$aTPL[$j] = $DtoR
	EndIf
Next
;_ArrayDisplay($aTPL)

EndFunc
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _ASC_array()

; Retrieve ASCII File for concatenation with TPL file
; Global $ASCPath = "C:\apps\EVO\asc\"

$checkASC = StringRegExp($ASCPath,"^.+\\$",0)
	  If $checkASC = 0 Then $ASCPath = $ASCPath & "\"
		 If @error = -1 Then
			If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log","Sorry but " & $ASCPath & " has no files")
		 Exit
	  EndIf

$aASCsearch = _FileListToArray($ASCPath,"*.Asc",1)
	  If Not IsArray($aASCsearch) Then
		 If $LOGFILE = 1 Then _SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
			Msgbox(0,"Error Log","Sorry but " & $ASCPath & " has no files")
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
_ArrayDisplay($aASCsearch2D)
_FileReadToArray($ASCPath & $aASCsearch2D[1][0], $aASC)
_ArrayDisplay($aASC)

EndFunc
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _TPLASC_concatenator()

; Get TrayID & prepare arrays for concatenation

; Retrieve TrayID from the ASCII folder first file in the list: always the newest file
Local	$TrayID = stringtrimright($aASCsearch2D[1][0],4)
	  If @error = -1 then
		 If $LOGFILE = 1 Then _SendAndLog($TrayID & "TrayID error", $Logname, True)
		 MsgBox(4096, "Error Log", "TrayID format incorrect" & @CRLF)
		 Exit
	  EndIf

; change to: TrayID ASC is always trayID TPL, if not: ABORT

; Retrieve TPLfileID from the TPL folder first file in the list: always the newest file
Local	$TPL_ID = stringtrimright($aTPLsearch2D[1][0],4)
	  If @error = -1 then
		 If $LOGFILE = 1 Then _SendAndLog($TrayID & "TPL_ID error", $Logname, True)
		 MsgBox(4096, "Error Log", "TPL_ID format incorrect" & @CRLF)
		 Exit
	  EndIf

	  ;If TrayID and TPL filename do not match the program will end here
	  If $TPL_ID<>$TrayID then
		 If $LOGFILE = 1 Then _SendAndLog($TrayID & "TPL & ASCII files don't match, check fileame and date", $Logname, True)
		 MsgBox(4096, "Error Log", "TPL & ASCII files don't match" & @CRLF)
		 Exit
	  EndIf

Global $TPLASC = fileopen($TPLASCPath & $TrayID & ".evo", 2 +8)

; CLIS (Sanquin LIMS) commitments write first lines
; 									H;1DD-MM-YY;hh:mm:ss
;									U; user
;									T; TrayID
;									A; Evo magellan.mth

FileWriteline($TPLASC, $aTPL[1] & ";" & $TrayID & ";MagellanMethod;" & $aASC[$aASC[0]] & ";" & "_checksum" &  @CRLF)
FileWriteline($TPLASC, "U;Username; Not Implemented SEP2014, soon to be retrieved from EVOware logfiles..." & ";" & "_checksum" &  @CRLF)
FileWriteline($TPLASC, "T;" & $TrayID & ";" & "_checksum"&  @CRLF)
FileWriteline($TPLASC, "A;MagellanMethod;" & $aASC[$aASC[0]] & ";" & "_checksum"& @CRLF)

; H;18-07-13;09:54:24;MBL110;MagellanMethod;MBL_EVO28211.mth
; write header with H;date;time;EVO;machine ;[$aASC[0]]is the number of lines in the array; here used to read data ;from the last line of the array i.e. :  $ASC[$aASC[0]

		 _ArrayDelete($aTPL, $aTPL[0])											;TPL array adjusted to read in loop
		 _ArrayDelete($aTPL, 1)
		 _ArrayDelete($aTPL, 0)

		 _ArrayDelete($aASC, $aASC[0])											;ASCii array adjusted to read in loop
		 _ArrayDelete($aASC, 0)

		 _ArraySort($aTPL, 0, 0, 0, 0)											; array is sorted alphabetically
		 _ArraySort($aASC, 0, 0, 1, 0)

		 _ArrayDisplay($aTPL)													; display the resulting array after deletion of the 1st and last lines
		 _ArrayDisplay($aASC)

		 If $LOGFILE = 1 Then _SendAndLog("filename extracted from ASCII file: " & $TrayID, $Logname, True)	; write TrayID/ASCII filename to logfile

for $ASCLine = 0 to ubound($aASC)-1

	  $MTPpos = stringinstr($aASC[$ASCLine], ";", 0, 2) +1						; position of MTP well number is always found 1 Chr to the right of the 2nd  ";" in the ASClinenumber
	  $Well = stringmid($aASC[$ASCLine],$MTPpos, 3)								; $Well is the MTP position: 3 characters read from the ASCii line at $MTPpos
	  $TPLine = _ArraySearch($aTPL, $Well,0,0,0,1,1)							; the TPL file line number at which the same MTP position is found as in the ASCii file

	  $aASCSamLen= stringinstr($aASC[$ASCLine], ";", 0, 1) -1					; length of samplename in ASC-file ; samplename is always found in front of 1st ";" in ASCline file
	  $TPLSamPos = stringinstr($aTPL[$TPLine], ";", 0, 2) +1					; position of samplename in TPL file with linenumber corresponding to same samplename in Ascifile line

	  $aASCSample = stringleft($aASC[$ASCLine], $aASCSamLen)  					; Samplename from ASCline (number of the loop)
	  $TPLSample = stringmid($aTPL[$TPLine], $TPLSampos, $aASCSamLen)			; Samplename from the TPLfile linenumber with the same MTP position ($Well) as the ASCfile linenumber (in the loop)

	  $TPLwrite = StringStripWS($aTPL[$TPLine],2)
	  $ASCwrite = StringStripWS($aASC[$ASCLine],1)


	  Select
		 Case $aASCSample = $TPLSample											; determines whether the ASC samplename is the same as the TPL samplename and if so,

			FileWriteline($TPLASC, StringStripWS($aTPL[$TPLine],2) & StringStripWS($aASC[$ASCLine],1) & "_checksum" & @CRLF) ; write the matching TPL and ASCii data to the TPLASC file

		 Case $aASCSample <> $TPLSample											; if samplenames are not exactly the same a message pops up: check the line numbers int he ASC and tPL files

		 If $LOGFILE = 1 Then _SendAndLog($aASCSample & " & " & $TPLSample & " do not match." & @CRLF _
													  & "check TPL filelinenumber " & $TPLine & @CRLF _
													  & "check ASCII filelinenumber " & $ASCLine, $Logname, True)
																				 ; writes not matching linenumbers to logfile ASCII en TPL linenumbers
	  EndSelect

next

FileWriteline($TPLASC, "F; Evoware Logfile names and location will be written here;" & "_checksum"& @CRLF)
FileWriteline($TPLASC, "F; Not Implemented SEP2014, soon to be retrieved from EVOware logfiles...;" & "_checksum"&  @CRLF)
FileWriteline($TPLASC, "L;" & "_checksum"& @CRLF)

If $LOGFILE = 1 Then _SendAndLog("File created: " & $TPLASCPath & $TrayID & ".evo", $Logname, True)

fileclose($TPLASC)

EndFunc ; Func The TPLASC Concatenator
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _SendAndLog($Logdata, $Filename = -1, $TimeStamp = False)

;line		log
;100/107	_SendAndLog($TPLPath & " has no *.TPL files", $Logname, True)
;135/142	_SendAndLog($ASCPath & " has no *.ASC files", $Logname, True)
;169		_SendAndLog($TrayID & "TrayID error", $Logname, True)
;194		_SendAndLog("filename extracted from ASCII file: " & $TrayID, $Logname, True)
;215	  	_SendAndLog($aASCSample & " & " & $TPLSample & " do not match." & @CRLF _
;										& "check TPL filelinenumber " & $TPLine & @CRLF _
;										& "check ASCII filelinenumber " & $ASCLine, $Logname, True, $Logname, True
;223		 _SendAndLog("File created: " & $TPLASCPath & $TrayID & ".evo", $Logname, True)
;230		_SendAndLog($TrayID & "TPL & ASCII files don't match, check fileame and date", $Logname, True)
;
If $Filename == -1 Then $Filename = $Logname ;$TPLASCPath &"TPLSASClog.log"
   ;Send($Logdata)
   $hFile = FileOpen($FileName, 1)
    If $hFile <> -1 Then
        If $TimeStamp = True Then $Logdata = _Now() & ' ; ' & $Logdata
        FileWriteLine($hFile, $Logdata)
        FileClose($Filename)
    EndIf
EndFunc
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _ClearLogFile()

If $LOGFILE = 1	then Fileopen($Logname, 1)
   If _filecountlines($logname) > $MAX then
	  filemove($logname, stringtrimright($logname,4) & "1.log", 1 +8)
	  ;_Zip_Create(stringtrimright($logname,4) & "1.log")
	  fileopen($logname, 2+8)
   EndIf
   Fileclose($Logname)

EndFunc ;Func _ClearLogFile()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Func _Checksum()



EndFunc ;Func _ClearLogFile()
;<----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
; Execution of script:
_Main()

