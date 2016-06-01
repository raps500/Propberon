MODULE Base;

IMPORT
	SYSTEM, Kernel32, Console;
	
CONST
	WordSize* = 8; CharSize* = 2; MaxChar* = 65535; SetUpperLimit* = 64;
	MaxInt* = 9223372036854775807; MinInt* = -MaxInt - 1; MaxIdentLen* = 63;
	MaxStrLen* = 255; MaxExtension* = 8; MaxRecordTypes* = 512;
	MaxModules* = 256; MaxExportTypes* = 1024;
	
	(* Object class/Item mode *)
	cHead* = 0; cModule* = 1; cVar* = 2; cRef* = 3; cConst* = 4;
	cField* = 5; cType* = 6; cProc* = 7; cSProc* = 8; cSFunc* = 9;
	mReg* = 10; mRegI* = 11; mCond* = 12; mXreg* = 13;
	
	clsVariable* = {cVar, cRef, mRegI};
	clsValue* = clsVariable	+ {cConst, mReg, mCond, cProc, mXreg};

	(* Type form *)
	tInteger* = 0; tBoolean* = 1; tSet* = 2; tChar* = 3;
	tReal* = 4; tPointer* = 5; tProcedure* = 6;
	tArray* = 7; tRecord* = 8; tString* = 9; tNil* = 10;
	tAddress* = 11;
	
	typeSimple* = {tInteger, tBoolean, tSet, tReal, tChar};
	typeAddress* = {tPointer, tProcedure, tAddress, tNil};
	typePointer* = {tPointer, tAddress};
	typeScalar* = typeSimple + typeAddress;
	typeNumberic* = {tInteger, tReal};
	typeCharacter* = {tChar, tString};
	typeHasExt* = {tRecord, tPointer};
	
	(* Win32 specifics *)
	HeapHandle* = -64;
	ExitProcess* = -56;
	LoadLibraryW* = -48;
	GetProcAddress* = -40;
	GetProcessHeap* = -32;
	HeapAlloc* = -24;
	HeapFree* = -16;
	
TYPE
	FileHandle* = RECORD handle: Kernel32.HANDLE END;
	IdentStr* = ARRAY MaxIdentLen + 1 OF CHAR;
	String* = ARRAY MaxStrLen + 1 OF CHAR;
	
	Type* = POINTER TO TypeDesc;
	Object* = POINTER TO ObjectDesc;
	
	TypeDesc* = RECORD
		ref*, mod*: INTEGER;
		modname*: POINTER TO RECORD s*: IdentStr END;
		extensible*, unsafe*: BOOLEAN;
		form*, size*, len*, nptr*, alignment*, parblksize*: INTEGER;
		base*: Type;
		obj*, fields*: Object
	END;
	
	ObjectDesc* = RECORD
		nilable*, tagged*, param*, readonly*, export*: BOOLEAN;
		name*: IdentStr;
		class*, lev*, expno*: INTEGER;
		type*: Type;
		next*, dsc*: Object;
		val*, val2*: INTEGER
	END;
	
	Item* = RECORD
		readonly*, param*, tagged*: BOOLEAN;
		mode*, lev*: INTEGER;
		obj*: Object; type*: Type;
		r*, a*, b*, c*: INTEGER
	END;

VAR
	guard* : Object;
	
	(* Predefined Types *)
	intType*, int8Type*, int16Type*, int32Type*: Type;
	byteType*, card16Type*, card32Type*: Type;
	boolType*, setType*, charType*, char8Type*, nilType*: Type;
	realType*, longrealType*: Type;
	stringType*, string8Type*: Type;
	sysByteType*, byteArrayType*: Type;
	
	LoadLibraryFuncType*: Type;
	GetProcAddressFuncType*: Type;
	HeapAllocFuncType*: Type;
	HeapFreeFuncType*: Type;
	
	predefinedTypes*: ARRAY 32 OF Type;
	preTypeNo*: INTEGER;
	
	CplFlag* : RECORD
		overflowCheck*, divideCheck*, arrayCheck*: BOOLEAN;
		typeCheck*, nilCheck*: BOOLEAN;
		main*, console*: BOOLEAN
	END;
	
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* Strings *)
	
PROCEDURE StrEqual* (s1, s2: ARRAY OF CHAR) : BOOLEAN;
	VAR i: INTEGER;
BEGIN
	i := 0;
	WHILE (i < LEN(s1)) & (i < LEN(s2)) & (s1[i] # 0X) & (s1[i] = s2[i]) DO
		INC (i)
	END;
	RETURN (i < LEN(s1)) & (i < LEN(s2)) & (s1[i] = s2[i])
		OR (LEN(s1) = LEN(s2)) & (i = LEN(s1))
		OR (i = LEN(s2)) & (s1[i] = 0X)
		OR (i = LEN(s1)) & (s2[i] = 0X)
END StrEqual;

PROCEDURE StrCopy* (src: ARRAY OF CHAR; VAR dst: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN
	i := 0;
	WHILE (i < LEN(dst) - 1) & (i < LEN(src)) & (src[i] # 0X) DO
		dst[i] := src[i]; INC(i)
	END;
	dst[i] := 0X
END StrCopy;

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* System functions wrappers *)

PROCEDURE File_existed* (filename: ARRAY OF CHAR): BOOLEAN;
	VAR attr: CARD32;
BEGIN attr := Kernel32.GetFileAttributesW(filename);
	RETURN attr # ORD(Kernel32.INVALID_FILE_ATTRIBUTES)
END File_existed;
	
PROCEDURE Open* (VAR file: FileHandle; filename: ARRAY OF CHAR) : BOOLEAN;
    VAR
	flag : BOOLEAN;
BEGIN
	flag := TRUE;
	IF File_existed(filename) THEN
		file.handle := Kernel32.CreateFileW(
			filename, ORD(Kernel32.GENERIC_READ + Kernel32.GENERIC_WRITE),
			0, NIL, Kernel32.OPEN_EXISTING, 0, 0
		)
	ELSE Console.WriteString ('File does not exist!'); Console.WriteLn;
	  flag := FALSE
	END
	RETURN flag
END Open;
	
PROCEDURE Rewrite* (VAR file: FileHandle; filename: ARRAY OF CHAR);
BEGIN
	file.handle := Kernel32.CreateFileW(
		filename, ORD(Kernel32.GENERIC_READ + Kernel32.GENERIC_WRITE),
		0, NIL, Kernel32.CREATE_ALWAYS, 0, 0
	)
END Rewrite;

PROCEDURE Close* (VAR file : FileHandle);
	VAR bRes: Kernel32.BOOL;
BEGIN
	IF file.handle # 0 THEN
		bRes := Kernel32.CloseHandle (file.handle); file.handle := 0
	END
END Close;

PROCEDURE Rename_file* (oldname, newname: ARRAY OF CHAR);
	VAR bRes: Kernel32.BOOL;
BEGIN
	bRes := Kernel32.MoveFileW (oldname, newname)
END Rename_file;

PROCEDURE Delete_file* (filename : ARRAY OF CHAR);
	VAR bRes: Kernel32.BOOL;
BEGIN
	bRes := Kernel32.DeleteFileW (filename)
END Delete_file;

(* -------------------------------------------------------------------------- *)

PROCEDURE Read* (VAR file: FileHandle; VAR n: CHAR);
	VAR bRes: Kernel32.BOOL; buf: BYTE; byteRead: CARD32;
        nn :INTEGER;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, 1, byteRead, NIL);
        nn := buf;
	IF (bRes = 0) OR (byteRead # 1) THEN n := 0X ELSE n := CHR(nn) END
END Read;

PROCEDURE Read_byte* (VAR file: FileHandle; VAR n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf: BYTE; byteRead: CARD32;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, 1, byteRead, NIL);
	IF (bRes = 0) OR (byteRead # 1) THEN n := -1 ELSE n := buf END
END Read_byte;
	
PROCEDURE Read_2bytes* (VAR file: FileHandle; VAR n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf: CARD16; byteRead: CARD32;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, 2, byteRead, NIL);
	IF (bRes = 0) OR (byteRead # 2) THEN n := -1 ELSE n := buf END
END Read_2bytes;

PROCEDURE Read_string* (VAR file: FileHandle; VAR str: ARRAY OF CHAR);
	VAR i, n: INTEGER;
BEGIN i := -1; n := 0;
	REPEAT INC (i); Read_2bytes (file, n); str[i] := CHR(n)
	UNTIL n = 0
END Read_string;
	
PROCEDURE Read_4bytes* (VAR file: FileHandle; VAR n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf, byteRead: CARD32;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, 4, byteRead, NIL);
	IF (bRes = 0) OR (byteRead # 4) THEN n := -1 ELSE n := buf END
END Read_4bytes;
	
PROCEDURE Read_8bytes* (VAR file : FileHandle; VAR n : INTEGER);
	VAR bRes: Kernel32.BOOL; buf: INTEGER; byteRead: CARD32;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, 8, byteRead, NIL);
	IF (bRes = 0) OR (byteRead # 8) THEN n := -1 ELSE n := buf END
END Read_8bytes;

PROCEDURE Read_bytes* (
	VAR file: FileHandle; VAR buf: ARRAY OF SYSTEM.BYTE; VAR byteRead: INTEGER
);
	VAR bRes: Kernel32.BOOL; bRead: CARD32;
BEGIN
	bRes := Kernel32.ReadFile (file.handle, buf, LEN(buf), bRead, NIL);
	byteRead := bRead
END Read_bytes;

(* -------------------------------------------------------------------------- *)
	
PROCEDURE Write_byte* (VAR file: FileHandle; n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf: BYTE; byteWritten: CARD32;
BEGIN buf := n;
	bRes := Kernel32.WriteFile (file.handle, buf, 1, byteWritten, NIL)
END Write_byte;

PROCEDURE Write* (VAR file: FileHandle; str: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN i := 0;
	WHILE (i < LEN(str)) & (str[i] # 0X) DO
		Write_byte (file, ORD(str[i])); INC (i)
	END;
END Write;

PROCEDURE WriteLn* (VAR file: FileHandle; str: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN i := 0;
	WHILE (i < LEN(str)) & (str[i] # 0X) DO
		Write_byte (file, ORD(str[i])); INC (i)
	END;
	Write_byte (file, 10);
	Write_byte (file, 13)
END WriteLn;

PROCEDURE WriteString* (VAR file: FileHandle; str: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN i := 0;
	WHILE (i < LEN(str)) & (str[i] # 0X) DO
		Write_byte (file, ORD(str[i])); INC (i)
	END;
END WriteString;

PROCEDURE Write_ansi_str* (VAR file: FileHandle; str: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN i := 0;
	WHILE (i < LEN(str)) & (str[i] # 0X) DO
		Write_byte (file, ORD(str[i])); INC (i)
	END;
	Write_byte (file, 0)
END Write_ansi_str;
	
PROCEDURE Write_2bytes* (VAR file: FileHandle; n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf: CARD16; byteWritten: CARD32;
BEGIN buf := n;
	bRes := Kernel32.WriteFile (file.handle, buf, 2, byteWritten, NIL)
END Write_2bytes;

PROCEDURE Write_string* (VAR file: FileHandle; str: ARRAY OF CHAR);
	VAR i: INTEGER;
BEGIN i := 0;
	WHILE (i < LEN(str)) & (str[i] # 0X) DO
		Write_2bytes (file, ORD(str[i])); INC (i)
	END;
	Write_2bytes (file, 0)
END Write_string;
	
PROCEDURE Write_4bytes* (VAR file: FileHandle; n: INTEGER);
	VAR bRes: Kernel32.BOOL; buf, byteWritten: CARD32;
BEGIN buf := n;
	bRes := Kernel32.WriteFile (file.handle, buf, 4, byteWritten, NIL)
END Write_4bytes;
	
PROCEDURE Write_8bytes* (VAR file : FileHandle; n : INTEGER);
	VAR bRes: Kernel32.BOOL; byteWritten: CARD32;
BEGIN
	bRes := Kernel32.WriteFile (file.handle, n, 8, byteWritten, NIL)
END Write_8bytes;

PROCEDURE Write_bytes* (
	VAR file: FileHandle;
	VAR buf: ARRAY OF SYSTEM.BYTE;
	VAR byteWritten: INTEGER
);
	VAR bRes: Kernel32.BOOL; bWritten: CARD32;
BEGIN
	bRes := Kernel32.WriteFile (file.handle, buf, LEN(buf), bWritten, NIL);
	byteWritten := bWritten
END Write_bytes;

PROCEDURE Write_bytes2* (
	VAR file: FileHandle; bufAdr: INTEGER; VAR byteWritten: INTEGER
);
	TYPE ByteArray = ARRAY OF BYTE;
	VAR bRes: Kernel32.BOOL; bWritten: CARD32;
BEGIN
	bRes := Kernel32.WriteFile (
		file.handle, bufAdr{ByteArray}, byteWritten, bWritten, NIL
	);
	byteWritten := bWritten
END Write_bytes2;

PROCEDURE FilePos* (VAR file: FileHandle): INTEGER;
	VAR bRes: Kernel32.BOOL; byteToMove, newPointer: Kernel32.LARGE_INTEGER;
BEGIN byteToMove.QuadPart := 0;
	bRes := Kernel32.SetFilePointerEx(
		file.handle, byteToMove, newPointer, Kernel32.FILE_CURRENT
	);
	RETURN newPointer.QuadPart
END FilePos;

PROCEDURE Seek* (VAR file: FileHandle; pos: INTEGER);
	VAR bRes: Kernel32.BOOL; byteToMove, newPointer: Kernel32.LARGE_INTEGER;
BEGIN byteToMove.QuadPart := pos;
	bRes := Kernel32.SetFilePointerEx(
		file.handle, byteToMove, newPointer, Kernel32.FILE_BEGIN
	)
END Seek;

PROCEDURE SeekRel* (VAR file: FileHandle; offset: INTEGER);
	VAR bRes: Kernel32.BOOL; byteToMove, newPointer: Kernel32.LARGE_INTEGER;
BEGIN byteToMove.QuadPart := offset;
	bRes := Kernel32.SetFilePointerEx(
		file.handle, byteToMove, newPointer, Kernel32.FILE_CURRENT
	)
END SeekRel;

PROCEDURE GetTickCount*() : INTEGER;
	RETURN Kernel32.GetTickCount()
END GetTickCount;

PROCEDURE GetArg* (VAR out: ARRAY OF CHAR; VAR paramLen: INTEGER; n: INTEGER);
	VAR i, k: INTEGER; buf: Kernel32.LPVOID;
BEGIN buf := Kernel32.GetCommandLineW(); i := 0;
	WHILE n > 0 DO
		WHILE (buf{Kernel32.WSTR}[i] # ' ') & (buf{Kernel32.WSTR}[i] # 0X) DO
			INC (i)
		END;
		IF buf{Kernel32.WSTR}[i] = 0X THEN n := 0
		ELSIF buf{Kernel32.WSTR}[i] = ' ' THEN DEC (n);
			WHILE buf{Kernel32.WSTR}[i] = ' ' DO INC (i) END
		END
	END;
	k := 0; paramLen := 0;
	WHILE (buf{Kernel32.WSTR}[i] # ' ') & (buf{Kernel32.WSTR}[i] # 0X) DO
		IF k < LEN(out) THEN out[k] := buf{Kernel32.WSTR}[i] END;
		INC (k); INC (i); INC (paramLen)
	END;
	IF k < LEN(out) THEN out[k] := 0X END
END GetArg;

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
	
PROCEDURE NewType* (VAR typ: Type; form: INTEGER);
BEGIN
	NEW (typ);
	typ.form := form;
	typ.mod := -1;
	typ.ref := -1;
	typ.nptr := 0;
	typ.extensible := FALSE;
	typ.unsafe := FALSE
END NewType;

PROCEDURE NewPredefinedType (VAR typ: Type; form, size: INTEGER);
BEGIN
	NewType (typ, form);
	typ.mod := -2;
	typ.size := size;
	typ.alignment := size;
	INC (preTypeNo); predefinedTypes[preTypeNo] := typ;
	typ.ref := preTypeNo
END NewPredefinedType;

PROCEDURE IsSignedType* (typ: Type) : BOOLEAN;
	RETURN (typ = int8Type) OR (typ = int16Type) OR (typ = int32Type)
END IsSignedType;

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

PROCEDURE WriteInt* (VAR f: FileHandle; n: INTEGER);
	VAR finish: BOOLEAN; b: INTEGER;
BEGIN
	REPEAT b := n MOD 128; finish := (n >= -64) & (n < 64);
		IF finish THEN b := b + 128 ELSE n := n DIV 128 END;
		Write_byte (f, b)
	UNTIL finish
END WriteInt;

PROCEDURE ReadInt* (VAR f: FileHandle; VAR n: INTEGER);
	VAR finish: BOOLEAN; i, b, k: INTEGER;
BEGIN n := 0; i := 1; k := 1;
	REPEAT Read_byte (f, b);
		IF i < 10 THEN
			finish := b >= 128; b := b MOD 128; n := n + b * k;
			IF i # 9 THEN k := k * 128 END; INC (i);
			IF finish & (b >= 64) THEN
				IF i # 9 THEN n := n + (-1 * k) ELSE n := n + MinInt END
			END
		ELSIF i = 10 THEN
			finish := TRUE; IF b = 127 THEN n := n + MinInt END
		ELSE ASSERT(FALSE)
		END
	UNTIL finish
END ReadInt;

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

PROCEDURE SetCompilerFlag* (pragma: ARRAY OF CHAR);
BEGIN
	IF StrEqual(pragma,'MAIN') THEN CplFlag.main := TRUE
	ELSIF StrEqual(pragma,'CONSOLE') THEN
		CplFlag.main := TRUE; CplFlag.console := TRUE
	END
END SetCompilerFlag;

PROCEDURE ResetCompilerFlag*;
BEGIN
	CplFlag.divideCheck := TRUE;
	CplFlag.arrayCheck := TRUE;
	CplFlag.typeCheck := TRUE;
	CplFlag.nilCheck := TRUE;
	CplFlag.overflowCheck := FALSE;
	CplFlag.main := FALSE;
	CplFlag.console := FALSE
END ResetCompilerFlag;
	
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

BEGIN
	NEW (guard); guard.class := cHead;
	preTypeNo := 0; predefinedTypes[0] := NIL;
	
	NewPredefinedType (intType, tInteger, WordSize);
	NewPredefinedType (int8Type, tInteger, 1);
	NewPredefinedType (int16Type, tInteger, 2);
	NewPredefinedType (int32Type, tInteger, 4);
	
	NewPredefinedType (byteType, tInteger, 1);
	NewPredefinedType (card16Type, tInteger, 2);
	NewPredefinedType (card32Type, tInteger, 4);
	
	NewPredefinedType (boolType, tBoolean, 1);
	NewPredefinedType (setType, tSet, WordSize);
	
	NewPredefinedType (charType, tChar, CharSize);
	NewPredefinedType (char8Type, tChar, 1);
	
	NewPredefinedType (nilType, tNil, WordSize);
	
	NewPredefinedType (realType, tReal, 4);
	NewPredefinedType (longrealType, tReal, 8);
	
	NewPredefinedType (stringType, tString, CharSize);
	stringType.base := charType;
	NewPredefinedType (string8Type, tString, 1);
	string8Type.base := char8Type;
	
	NewPredefinedType (sysByteType, tInteger, 1);
	NewPredefinedType (byteArrayType, tArray, 1);
	byteArrayType.base := sysByteType;
	
	NewPredefinedType (LoadLibraryFuncType, tProcedure, WordSize);
	LoadLibraryFuncType.parblksize := WordSize;
	
	NewPredefinedType (GetProcAddressFuncType, tProcedure, WordSize);
	LoadLibraryFuncType.parblksize := WordSize * 2;
	
	NewPredefinedType (HeapAllocFuncType, tProcedure, WordSize);
	HeapAllocFuncType.parblksize := WordSize * 3;
	
	NewPredefinedType (HeapFreeFuncType, tProcedure, WordSize);
	HeapFreeFuncType.parblksize := WordSize * 3
END Base.