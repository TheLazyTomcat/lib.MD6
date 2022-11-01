unit MD6;

interface

uses
  SysUtils, Classes,
  AuxTypes, HashBase;

{===============================================================================
    Library-specific exceptions
===============================================================================}
type
  EMD6Exception = class(EHASHException);

  EMD6InvalidValue      = class(EMD6Exception);
  EMD6InvalidHash       = class(EMD6Exception);
  EMD6InvalidState      = class(EMD6Exception);
  EMD6IncompatibleClass = class(EMD6Exception);
  EMD6IncompatibleSize  = class(EMD6Exception);

{===============================================================================
    Common types
===============================================================================}
type
  TMD6 = packed array of UInt8;

  TMD6_224 = packed array[0..27] of UInt8;    PMD6_224 = ^TMD6_224;
  TMD6_256 = packed array[0..31] of UInt8;    PMD6_256 = ^TMD6_256;
  TMD6_384 = packed array[0..47] of UInt8;    PMD6_384 = ^TMD6_384;
  TMD6_512 = packed array[0..63] of UInt8;    PMD6_512 = ^TMD6_512;

  TMD6Key = packed array of UInt8;

{===============================================================================
--------------------------------------------------------------------------------
                                    TMD6Hash
--------------------------------------------------------------------------------
===============================================================================}
type
  TMD6Word = UInt64;

  TMD6ProcessingBlock = array of TMD6Word;

  TMD6ProcessingNode = record
    Index:  Int64;
    Bytes:  TMemSize; // number of bytes already stored in block
    Block:  TMD6ProcessingBlock;
  end;

  TMD6ProcessingState = record
    Levels: array of TMD6ProcessingNode;
  end;

{===============================================================================
    TMD6Hash - class declaration
===============================================================================}
type
  TMD6Hash = class(TBlockHash)
  protected
    fMD6:         TMD6;
    fHashBits:    Integer;  // whole bytes only (div 8)
    fKey:         TMD6Key;  // max length 64
    fRounds:      Integer;  // default is 40 + (fHashBits / 4)
    fRoundsDef:   Boolean;  // indicates if rounds were set explicitly (false) or implicitly (true)
    fModeControl: Integer;  // >= 0 (not explicitly limited)
    fState:       TMD6ProcessingState;
    // getters setters
    Function GetMD6: TMD6; virtual;
    procedure SetHashBits(Value: Integer); virtual;
    Function GetKey: TMD6Key; virtual;
    procedure PutKey(Value: TMD6Key); virtual;
    procedure SetRounds(Value: Integer); virtual;
    procedure SetModeControl(Value: Integer); virtual;
    // main processing
    procedure CompressBlock(var Block: TMD6ProcessingBlock); virtual;
    procedure AddTreeLevel; virtual;
    procedure ProcessTreeNode(Level: Integer; const Data); virtual;
    procedure ProcessTreeNodeFinal(Level: Integer; PadBytes: TMemSize); virtual;
    // inherited processing
    procedure ProcessBlock(const Block); override;
    procedure ProcessFirst(const Block); override;
    procedure ProcessLast; override;
    // init/final
    procedure Initialize; override;
  public
    class Function MD6ToLE(MD6: TMD6): TMD6; virtual;
    class Function MD6ToBE(MD6: TMD6): TMD6; virtual;
    class Function MD6FromLE(MD6: TMD6): TMD6; virtual;
    class Function MD6FromBE(MD6: TMD6): TMD6; virtual;
    Function HashSize: TMemSize; reintroduce;
    class Function HashName: String; override;
    class Function HashEndianness: THashEndianness; override;
    class Function HashFinalization: Boolean; override;
    constructor CreateAndInitFrom(Hash: THashBase); overload; override;
    constructor CreateAndInitFrom(Hash: TMD6); overload; virtual;
    procedure Init; override;
    Function Compare(Hash: THashBase): Integer; override;
    Function AsString: String; override;
    procedure FromString(const Str: String); override;
    procedure FromStringDef(const Str: String; const Default: TMD6); reintroduce;
    procedure SaveToStream(Stream: TStream; Endianness: THashEndianness = heDefault); override;
    procedure LoadFromStream(Stream: TStream; Endianness: THashEndianness = heDefault); override;
    procedure SetKey(const Key; Size: TMemSize); overload; virtual;
    procedure SetKey(const Key: String); overload; virtual;
    property MD6: TMD6 read GetMD6;
    property HashBits: Integer read fHashBits write SetHashBits;
    property Key: TMD6Key read GetKey write PutKey;
    property Rounds: Integer read fRounds write SetRounds;
    property ModeControl: Integer read fModeControl write SetModeControl;
  end;

implementation

uses
  Math,
  StrRect, BitOps;

{===============================================================================
--------------------------------------------------------------------------------
                                    TMD6Hash
--------------------------------------------------------------------------------
===============================================================================}
{===============================================================================
    TMD6Hash - Implementation constants
===============================================================================}
const
  MD6_BITS_MAX     = 512;
  MD6_BITS_DEFAULT = 512;

  MD6_MODE_DEFAULT = 64;

  MD6_KEY_MAXLEN = 64;        // in bytes

  MD6_CHUNK_SIZE = 128;       // bytes (16 words)
  MD6_CHUNK_LEN  = 16;        // words

  MD6_BLOCK_LEN       = 89;   // words
  MD6_BLOCK_KEYSTART  = 15;
  MD6_BLOCK_KEYEND    = 22;
  MD6_BLOCK_DATASTART = 25;
  MD6_BLOCK_CAPACITY  = 512;  // bytes (64 words)
  MD6_BLOCK_IDX_U     = 23;   // position of unique node ID word
  MD6_BLOCK_IDX_V     = 24;   // position of control word

  // fractional part of sqrt(6)
  MD6_VEC_Q: array[0..14] of TMD6Word = (
    TMD6Word($7311c2812425cfa0), TMD6Word($6432286434aac8e7),
    TMD6Word($b60450e9ef68b7c1), TMD6Word($e8fb23908d9f06f1),
    TMD6Word($dd2e76cba691e5bf), TMD6Word($0cd0d63b2c30bc41),
    TMD6Word($1f8ccf6823058f8a), TMD6Word($54e5ed5b88e3775d),
    TMD6Word($4ad12aae0a6d6031), TMD6Word($3e7f16bb88222e0d),
    TMD6Word($8af8671d3fb50c2c), TMD6Word($995ad1178bd25c31),
    TMD6Word($c878c1dd04c4b633), TMD6Word($3b72066c7a1552ac),
    TMD6Word($0d6f3522631effcb));

  MD6_S_0    = TMD6Word($0123456789abcdef);
  MD6_S_MASK = TMD6Word($7311c2812425cfa0);

(*
--------------------------------------------------------------------------------
  Following constants are not used anywhere in the code, they are instead
  directly expanded into numerals where needed.
--------------------------------------------------------------------------------
{
  Round constants MD6_S can be calculated like this:

  MD6_S[0] := MD6_S_0;
  For i := 1 to High(MD6_S) do
    MD6_S[i] := ROL(MD6_S[i - 1],1) xor (MD6_S[i - 1] and MD6_S_STAR)
}
  MD6_S: array[0..167] of TMD6Word = (
    TMD6Word($0123456789ABCDEF), TMD6Word($0347CACE1376567E),
    TMD6Word($058E571C26C8EADC), TMD6Word($0A1CEC3869911F38),
    TMD6Word($16291870F3233150), TMD6Word($3E5330E1C66763A0),
    TMD6Word($4EB7614288EB84E0), TMD6Word($DF7F828511F68D60),
    TMD6Word($EDEE878B23C997E1), TMD6Word($BADD8D976792A863),
    TMD6Word($47AA9BAFEB25D8E7), TMD6Word($CC55B5DEF66E796E),
    TMD6Word($D8BAEB3DC8F8BBFD), TMD6Word($E165147A91D1FC5B),
    TMD6Word($A3CB28F523A234B7), TMD6Word($6497516B67646DCF),
    TMD6Word($A93FE2D7EAEC961E), TMD6Word($736E072EF5FDAA3D),
    TMD6Word($95DC0C5DCFDEDE5A), TMD6Word($3AA818BA9BB972B5),
    TMD6Word($475031F53753A7CA), TMD6Word($CDB0636B4AA6C814),
    TMD6Word($DA7084D795695829), TMD6Word($E6F1892E2EF3F873),
    TMD6Word($AFF2925C79C638C7), TMD6Word($7CF5A6B8D388790F),
    TMD6Word($89FACFF1A710BB1E), TMD6Word($12E55D626A21FD3D),
    TMD6Word($37CBFAC4F462375A), TMD6Word($5C963709CCE469B4),
    TMD6Word($E93C6C129DEC9AC8), TMD6Word($B36898253FFDBF11),
    TMD6Word($55D1B04B5BDEF123), TMD6Word($FAB2E097B7B92366),
    TMD6Word($877501AE4B5345ED), TMD6Word($0DFB03DC96A7CE7B),
    TMD6Word($1AE70539296A52D6), TMD6Word($27CF0A7372F4E72C),
    TMD6Word($6C9F16E7C5CD0978), TMD6Word($B92F2F4E8F9F1BD0),
    TMD6Word($435F5C9D1B3B3C21), TMD6Word($C5AFF9BB36577462),
    TMD6Word($CA5E33F748ABACE5), TMD6Word($D6AC656F9176D56B),
    TMD6Word($FF588ADE22C96FF7), TMD6Word($8DA1973C6593904F),
    TMD6Word($1A42AC78EF26A09F), TMD6Word($2685D8F1FA69C1BE),
    TMD6Word($6F0A7162D4F242DC), TMD6Word($BD14A2C5ADC4C738),
    TMD6Word($4B39C70A7F8D4951), TMD6Word($D5624C14DB1FDBA2),
    TMD6Word($FBC4D829B63A7CE5), TMD6Word($848970524854B56B),
    TMD6Word($0913A0A490ADEFF7), TMD6Word($1336C1C9217E104E),
    TMD6Word($357D431362D8209C), TMD6Word($5BEBC427E5B041B8),
    TMD6Word($E4D6484EEF40C2D0), TMD6Word($A9BCD09DFA814721),
    TMD6Word($726961BAD503C963), TMD6Word($96D383F5AE065BE6),
    TMD6Word($3FB6856A7808FC6D), TMD6Word($4C7D8AD4D01134FA),
    TMD6Word($D8EA9729A0236D54), TMD6Word($E1D5AC52606797A9),
    TMD6Word($A2BAD8A4E0EAA8F3), TMD6Word($676571C9E1F5D947),
    TMD6Word($ADCBA312E3CE7B8E), TMD6Word($7A96C425E798BC9D),
    TMD6Word($873D484AEB31F5BA), TMD6Word($0D6BD095F6422ED5),
    TMD6Word($1BD661AAC884532A), TMD6Word($24BC83D5910CE574),
    TMD6Word($6969852A221D0FC8), TMD6Word($B3D28A54643F1010),
    TMD6Word($54B596A8EC5B2021), TMD6Word($F97AAFD1FCB74062),
    TMD6Word($83E5DD22DD4BC0E5), TMD6Word($04CA7A45BE96416B),
    TMD6Word($0994B68A5928C3F6), TMD6Word($1239EF94B271444C),
    TMD6Word($36621DA944C3CC98), TMD6Word($5EC43BD38D8655B0),
    TMD6Word($EF8875261F08EEC0), TMD6Word($BC10AA4C3A111301),
    TMD6Word($4831D69854232503), TMD6Word($D0726FB0AC674F06),
    TMD6Word($F0F49DE17CEBD10D), TMD6Word($91F9BB43DDF6631B),
    TMD6Word($32E2F486BFC88537), TMD6Word($57C5298D5B918F4E),
    TMD6Word($FC8B539BB722919C), TMD6Word($8917E5B64A65A2B9),
    TMD6Word($133E0BEC94EEC7D3), TMD6Word($356C15592DF94826),
    TMD6Word($5BD82AB37FD3D86C), TMD6Word($E4A057E7DBA678F8),
    TMD6Word($A940ED4EB768B951), TMD6Word($73811A9D4AF1FBA3),
    TMD6Word($940337BB95C23CE6), TMD6Word($38076DF62F84756D),
    TMD6Word($400F9B6C7B0CAFFA), TMD6Word($C01EB4D8D61DD054),
    TMD6Word($C02DE931A83E60A9), TMD6Word($C05A1262705881F3),
    TMD6Word($C0A426C4C0B18247), TMD6Word($C1484F098142868F),
    TMD6Word($C390DC1202858B9F), TMD6Word($C4317824050E9CBF),
    TMD6Word($C873B0480E19B5DF), TMD6Word($D0F6E0901832EE3F),
    TMD6Word($F1FD01A03045125F), TMD6Word($92EB03C0408F26BF),
    TMD6Word($37D70500811B4BDF), TMD6Word($5CBF0A010237DC3E),
    TMD6Word($E96F1603044A745C), TMD6Word($B3DF2E070C94ACB9),
    TMD6Word($54AF5E0F1D2DD5D3), TMD6Word($F95FFE1F3E7E6E26),
    TMD6Word($83AE3E3F58D8926D), TMD6Word($045C7E7FB1B1A6FB),
    TMD6Word($08A8BEFE4342CB56), TMD6Word($1151FF7C86855DAC),
    TMD6Word($33B23CF9090FF6F8), TMD6Word($54747973121A2B50),
    TMD6Word($F8F8B2E724345DA0), TMD6Word($81E1E74F6C4CF6E1),
    TMD6Word($02C20C9FFC9D2B63), TMD6Word($078419BEDD3F5DE6),
    TMD6Word($0C0833FDBE5BF66C), TMD6Word($1810657A58B62AF8),
    TMD6Word($20308AF4B1485F50), TMD6Word($607197694290F1A0),
    TMD6Word($A0F2ACD3852122E0), TMD6Word($61F5D9260E634761),
    TMD6Word($A2FA724C18E7C9E2), TMD6Word($67E4A69831EA5A65),
    TMD6Word($ACC9CFB043F4FEEA), TMD6Word($79925DE087CD3375),
    TMD6Word($8234FB410B9F65CA), TMD6Word($06793483173B8E15),
    TMD6Word($0EE369872A56922A), TMD6Word($1FC7938F74A9A674),
    TMD6Word($2C8EA59FCD72CAC8), TMD6Word($791DCBBE9EC55F10),
    TMD6Word($832A55FD398FF120), TMD6Word($0554EB7B531A2361),
    TMD6Word($0BB914F7A63445E2), TMD6Word($1463296E684CCE64),
    TMD6Word($38C752DCF09D52E8), TMD6Word($418FE739C13FE770),
    TMD6Word($C21E0C72825A09C0), TMD6Word($C62C18E504B41A01),
    TMD6Word($CE58314B0D4C3E03), TMD6Word($DEA062971E9C7207),
    TMD6Word($EF4087AF393CA60F), TMD6Word($BD818DDF525DCA1F),
    TMD6Word($4A029B3FA4BE5E3F), TMD6Word($D605B47E6D58F25E),
    TMD6Word($FE0AE8FCFEB126BD), TMD6Word($8E151179D9434BDB),
    TMD6Word($1E3B22F2B287DC37), TMD6Word($2E674765450A744E),
    TMD6Word($7ECFCCCB8E14AC9C), TMD6Word($8F9E5916182DD5B8),
    TMD6Word($1C2CF22C307E6ED1), TMD6Word($2859265840D89322));

  // tap positions
  MD6_TAP: array[0..4] of Integer = (17,18,21,31,67);

  // right shifts
  MD6_SHIFT_R: array[0..15] of Integer = (
    10, 5, 13, 10, 11, 12, 2, 7, 14, 15, 7, 13, 11, 7, 6, 12);

  // left shifts
  MD6_SHIFT_L: array[0..15] of Integer = (
    11, 24, 9, 16, 15, 9, 27, 15, 6, 2, 29, 8, 15, 5, 31, 9);
*)
{===============================================================================
    TMD6Hash - utility functions
===============================================================================}

Function GetControlWord(Rnds, ModeCtrl, PadBits, KeyLen, HashBits: Integer; Final: Boolean): TMD6Word;
begin
Result := 0 or
  (TMD6Word(Rnds and $FFF) shl 48) or
  (TMD6Word(ModeCtrl and $FF) shl 40) or
  (TMD6Word(Integer(IfThen(Final,1,0)) and $F) shl 36) or
  (TMD6Word(PadBits and $FFFF) shl 20) or
  (TMD6Word(KeyLen and $FF) shl 12) or
   TMD6Word(HashBits and $FFF);
end;

//------------------------------------------------------------------------------

Function GetUniqueNodeIDWord(LevelNumber: Integer; NodeIndex: Int64): TMD6Word;
begin
Result := (TMD6Word(LevelNumber and $FF) shl 56) or (NodeIndex and $00FFFFFFFFFFFFFF);
end;

{===============================================================================
--------------------------------------------------------------------------------
                                    TMD6Hash
--------------------------------------------------------------------------------
===============================================================================}
{===============================================================================
    TMD6Hash - class implementation
===============================================================================}
{-------------------------------------------------------------------------------
    TMD6Hash - protected methods
-------------------------------------------------------------------------------}

Function TMD6Hash.GetMD6: TMD6;
begin
Result := Copy(fMD6);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.SetHashBits(Value: Integer);
begin
If not IsHashing then
  begin
    If (Value > 0) and (Value <= MD6_BITS_MAX) and ((Value and 7) = 0) then
      begin
        fHashBits := Value;
        SetLength(fMD6,0);  // to prevent copying
        SetLength(fMD6,Value div 8);
        If fRoundsDef then
          begin
            If Length(fKey) > 0 then
              fRounds := Max(80,40 + (fHashBits div 4))
            else
              fRounds := 40 + (fHashBits div 4);
          end;
      end
    else raise EMD6InvalidValue.CreateFmt('TMD6Hash.SetHashBits: Invalid hash bits value (%d).',[Value]);
  end
else raise EMD6InvalidState.Create('TMD6Hash.SetHashBits: Cannot change hash bits when hashing.');
end;

//------------------------------------------------------------------------------

Function TMD6Hash.GetKey: TMD6Key;
begin
Result := Copy(fKey);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.PutKey(Value: TMD6Key);
begin
If not IsHashing then
  begin
    If Length(Value) <= MD6_KEY_MAXLEN then
      begin
        fKey := Copy(Value);
        If fRoundsDef then
          begin
            If Length(fKey) > 0 then
              fRounds := Max(80,40 + (fHashBits div 4))
            else
              fRounds := 40 + (fHashBits div 4);
          end;
      end
    else raise EMD6InvalidValue.CreateFmt('TMD6Hash.PetKey: Invalid key length (%d).',[Length(Value)]);
  end
else raise EMD6InvalidState.Create('TMD6Hash.PutKey: Cannot change key when hashing.');
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.SetRounds(Value: Integer);
begin
If not IsHashing then
  begin
    fRounds := Value;
    fRoundsDef := False;
  end
else raise EMD6InvalidState.Create('TMD6Hash.SetRounds: Cannot change rounds when hashing.');
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.SetModeControl(Value: Integer);
begin
If not IsHashing then
  begin
    If Value >= 0 then
      fModeControl := Value
    else
      raise EMD6InvalidValue.CreateFmt('TMD6Hash.SetModeControl: Invalid mode control (%d).',[Value]);
  end
else raise EMD6InvalidState.Create('TMD6Hash.SetModeControl: Cannot change mode control when hashing.');
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.CompressBlock(var Block: TMD6ProcessingBlock);
var
  i:          Integer;
  RoundConst: TMD6Word;
  x:          TMD6Word;
begin
// block is assumed to be completely prepared, only do endianness corrections
{$IFNDEF ENDIAN_BIG}
For i := MD6_BLOCK_DATASTART to Pred(MD6_BLOCK_LEN) do
  EndianSwapValue(Block[i]);
{$ENDIF}
// main calculation...
RoundConst := MD6_S_0;
i := MD6_BLOCK_LEN;
while i <= (Length(Block) - MD6_CHUNK_LEN) do
  begin
    // unrolled round (16 steps)...
    
    // step 0
    x := RoundConst xor Block[i - 89] xor Block[i - 17];
    x := x xor (Block[i - 18] and Block[i - 21]);
    x := x xor (Block[i - 31] and Block[i - 67]);
    x := x xor (x shr 10);
    Block[i] := x xor (x shl 11);

    // step 1
    x := RoundConst xor Block[i - 88] xor Block[i - 16];
    x := x xor (Block[i - 17] and Block[i - 20]);
    x := x xor (Block[i - 30] and Block[i - 66]);
    x := x xor (x shr 5);
    Block[i + 1] := x xor (x shl 24);

    // step 2
    x := RoundConst xor Block[i - 87] xor Block[i - 15];
    x := x xor (Block[i - 16] and Block[i - 19]);
    x := x xor (Block[i - 29] and Block[i - 65]);
    x := x xor (x shr 13);
    Block[i + 2] := x xor (x shl 9);

    // step 3
    x := RoundConst xor Block[i - 86] xor Block[i - 14];
    x := x xor (Block[i - 15] and Block[i - 18]);
    x := x xor (Block[i - 28] and Block[i - 64]);
    x := x xor (x shr 10);
    Block[i + 3] := x xor (x shl 16);

    // step 4
    x := RoundConst xor Block[i - 85] xor Block[i - 13];
    x := x xor (Block[i - 14] and Block[i - 17]);
    x := x xor (Block[i - 27] and Block[i - 63]);
    x := x xor (x shr 11);
    Block[i + 4] := x xor (x shl 15);

    // step 5
    x := RoundConst xor Block[i - 84] xor Block[i - 12];
    x := x xor (Block[i - 13] and Block[i - 16]);
    x := x xor (Block[i - 26] and Block[i - 62]);
    x := x xor (x shr 12);
    Block[i + 5] := x xor (x shl 9);

    // step 6
    x := RoundConst xor Block[i - 83] xor Block[i - 11];
    x := x xor (Block[i - 12] and Block[i - 15]);
    x := x xor (Block[i - 25] and Block[i - 61]);
    x := x xor (x shr 2);
    Block[i + 6] := x xor (x shl 27);

    // step 7
    x := RoundConst xor Block[i - 82] xor Block[i - 10];
    x := x xor (Block[i - 11] and Block[i - 14]);
    x := x xor (Block[i - 24] and Block[i - 60]);
    x := x xor (x shr 7);
    Block[i + 7] := x xor (x shl 15);

    // step 8
    x := RoundConst xor Block[i - 81] xor Block[i - 9];
    x := x xor (Block[i - 10] and Block[i - 13]);
    x := x xor (Block[i - 23] and Block[i - 59]);
    x := x xor (x shr 14);
    Block[i + 8] := x xor (x shl 6);

    // step 9
    x := RoundConst xor Block[i - 80] xor Block[i - 8];
    x := x xor (Block[i - 9] and Block[i - 12]);
    x := x xor (Block[i - 22] and Block[i - 58]);
    x := x xor (x shr 15);
    Block[i + 9] := x xor (x shl 2);

    // step 10
    x := RoundConst xor Block[i - 79] xor Block[i - 7];
    x := x xor (Block[i - 8] and Block[i - 11]);
    x := x xor (Block[i - 21] and Block[i - 57]);
    x := x xor (x shr 7);
    Block[i + 10] := x xor (x shl 29);

    // step 11
    x := RoundConst xor Block[i - 78] xor Block[i - 6];
    x := x xor (Block[i - 7] and Block[i - 10]);
    x := x xor (Block[i - 20] and Block[i - 56]);
    x := x xor (x shr 13);
    Block[i + 11] := x xor (x shl 8);

    // step 12
    x := RoundConst xor Block[i - 77] xor Block[i - 5];
    x := x xor (Block[i - 6] and Block[i - 9]);
    x := x xor (Block[i - 19] and Block[i - 55]);
    x := x xor (x shr 11);
    Block[i + 12] := x xor (x shl 15);

    // step 13
    x := RoundConst xor Block[i - 76] xor Block[i - 4];
    x := x xor (Block[i - 5] and Block[i - 8]);
    x := x xor (Block[i - 18] and Block[i - 54]);
    x := x xor (x shr 7);
    Block[i + 13] := x xor (x shl 5);

    // step 14
    x := RoundConst xor Block[i - 75] xor Block[i - 3];
    x := x xor (Block[i - 4] and Block[i - 7]);
    x := x xor (Block[i - 17] and Block[i - 53]);
    x := x xor (x shr 6);
    Block[i + 14] := x xor (x shl 31);

    // step 15
    x := RoundConst xor Block[i - 74] xor Block[i - 2];
    x := x xor (Block[i - 3] and Block[i - 6]);
    x := x xor (Block[i - 16] and Block[i - 52]);
    x := x xor (x shr 12);
    Block[i + 15] := x xor (x shl 9);

    // recalculate round constant
    RoundConst := ROL(RoundConst,1) xor (RoundConst and MD6_S_MASK);
    // increment index by number of steps taken
    Inc(i,16);
  end;
// endianness corection for chaining variable (last 1024 bits, 16 words, one chunk)
{$IFNDEF ENDIAN_BIG}
For i := (Length(Block) - MD6_CHUNK_LEN) to High(Block) do
  EndianSwapValue(Block[i]);
{$ENDIF}
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.AddTreeLevel;
var
  i:  Integer;
begin
SetLength(fState.Levels,Length(fState.Levels) + 1);
with fState.Levels[High(fState.Levels)] do
  begin
    Index := 0;
    Bytes := 0;
    SetLength(Block,MD6_BLOCK_LEN + (fRounds * MD6_CHUNK_LEN));
    For i := Low(MD6_VEC_Q) to High(MD6_VEC_Q) do
      Block[i] := MD6_VEC_Q[i];
    // prepare key
    If Length(fKey) > 0 then
      begin
        Move(fKey[0],Block[MD6_BLOCK_KEYSTART],Length(fKey));
      {$IFNDEF ENDIAN_BIG}
        For i := MD6_BLOCK_KEYSTART to MD6_BLOCK_KEYEND do
          EndianSwapValue(Block[i]);
      {$ENDIF}
      end;
    // init vector for sequential processing
    If Length(fState.Levels) > fModeControl then
      Bytes := MD6_CHUNK_SIZE;  // empty chunk, SetLength intialized it to all zero
  end;
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.ProcessTreeNode(Level: Integer; const Data);
var
  ChainVar: array[0..Pred(MD6_CHUNK_SIZE)] of UInt8;
begin
If Level <= High(fState.Levels) then
  begin
  {
    Cannot use "with fState.Levels[Level] do" - the array can be reallocated
    within the function (by TreeAddLevel), which invalidates the used pointer
    in subsequent code.
  }
    If fState.Levels[Level].Bytes >= MD6_BLOCK_CAPACITY then
      begin
        with fState.Levels[Level] do
          begin
            Block[MD6_BLOCK_IDX_U] := GetUniqueNodeIDWord(Succ(Level),Index);
            Block[MD6_BLOCK_IDX_V] := GetControlWord(fRounds,fModeControl,0,Length(fKey),fHashBits,False);
            CompressBlock(Block);
            Inc(Index);
            Bytes := 0;
            Move(Block[Length(Block) - MD6_CHUNK_LEN],ChainVar,MD6_CHUNK_SIZE);
          end;
        If Succ(Level) <= fModeControl then
          begin
            If Level >= High(fState.Levels) then
              AddTreeLevel;
            ProcessTreeNode(Succ(Level),ChainVar);
          end
        else
          begin
            Move(ChainVar,fState.Levels[Level].Block[MD6_BLOCK_DATASTART],MD6_CHUNK_SIZE);
            Inc(fState.Levels[Level].Bytes,MD6_CHUNK_SIZE);
          end;
      end;
    // copy data to state block
    with fState.Levels[Level] do
      begin
        Move(Data,Pointer(PtrUInt(Addr(Block[MD6_BLOCK_DATASTART])) + PtrUInt(Bytes))^,MD6_CHUNK_SIZE);
        Inc(Bytes,MD6_CHUNK_SIZE);
      end;
  end
else raise EMD6InvalidValue.CreateFmt('TMD6Hash.TreeLevelProcess: Trying to process non-existing level (%d).',[Level]);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.ProcessTreeNodeFinal(Level: Integer; PadBytes: TMemSize);
var
  ChainVar: array[0..Pred(MD6_CHUNK_SIZE)] of UInt8;
begin
If Level <= High(fState.Levels) then
  begin
    with fState.Levels[Level] do
      begin
        If Bytes < MD6_BLOCK_CAPACITY then
          begin
            FillChar(Pointer(PtrUInt(Addr(Block[MD6_BLOCK_DATASTART])) + PtrUInt(Bytes))^,MD6_BLOCK_CAPACITY - Bytes,0);
            Inc(PadBytes,MD6_BLOCK_CAPACITY - Bytes);
          end;
        Block[MD6_BLOCK_IDX_U] := GetUniqueNodeIDWord(Succ(Level),Index);
        Block[MD6_BLOCK_IDX_V] := GetControlWord(fRounds,fModeControl,PadBytes * 8,Length(fKey),fHashBits,Level >= High(fState.Levels));
        CompressBlock(Block);
        Inc(Index);
        Bytes := 0;
      end;
    If Level < High(fState.Levels) then
      begin
        with fState.Levels[Level] do
          Move(Block[Length(Block) - MD6_CHUNK_LEN],ChainVar,MD6_CHUNK_SIZE);
        ProcessTreeNode(Succ(Level),ChainVar);
        ProcessTreeNodeFinal(Succ(Level),0);
      end
    else If Length(fMD6) > 0 then
      with fState.Levels[Level] do
        Move(Pointer(PtrUInt(Addr(Block[Length(Block)])) - PtrUInt(Length(fMD6)))^,fMD6[0],Length(fMD6)); // final hash
  end
else raise EMD6InvalidValue.CreateFmt('TMD6Hash.TreeProcessNodeFinal: Trying to process non-existing level (%d).',[Level]);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.ProcessBlock(const Block);
begin
ProcessTreeNode(0,Block);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.ProcessFirst(const Block);
begin
inherited;
ProcessTreeNode(0,Block);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.ProcessLast;
var
  PadBytes: TMemSize;
begin
If fTransCount > 0 then
  begin
    PadBytes := MD6_CHUNK_SIZE - fTransCount;
    FillChar(Pointer(PtrUInt(fTransBlock) + PtrUInt(fTransCount))^,PadBytes,0);
    ProcessTreeNode(0,fTransBlock^);
  end
else PadBytes := 0;
ProcessTreeNodeFinal(0,PadBytes);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.Initialize;
begin
fBlockSize := MD6_CHUNK_SIZE;
inherited;
Setlength(fMD6,MD6_BITS_DEFAULT div 8);
fHashBits := MD6_BITS_DEFAULT;
SetLength(fKey,0);
fRounds := 168; // 40 + (512 / 4)
fRoundsDef := True;
fModeControl := MD6_MODE_DEFAULT;
SetLength(fState.Levels,0);
end;

{-------------------------------------------------------------------------------
    TMD6Hash - public methods
-------------------------------------------------------------------------------}

class Function TMD6Hash.MD6ToLE(MD6: TMD6): TMD6;
begin
Result := Copy(MD6);
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.MD6ToBE(MD6: TMD6): TMD6;
begin
Result := Copy(MD6);
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.MD6FromLE(MD6: TMD6): TMD6;
begin
Result := Copy(MD6);
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.MD6FromBE(MD6: TMD6): TMD6;
begin
Result := Copy(MD6);
end;

//------------------------------------------------------------------------------

Function TMD6Hash.HashSize: TMemSize;
begin
Result := fHashBits div 8;
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.HashName: String;
begin
Result := 'MD6';
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.HashEndianness: THashEndianness;
begin
Result := heBig;
end;

//------------------------------------------------------------------------------

class Function TMD6Hash.HashFinalization: Boolean;
begin
Result := True;
end;

//------------------------------------------------------------------------------

constructor TMD6Hash.CreateAndInitFrom(Hash: THashBase);
var
  i:  Integer;
begin
inherited CreateAndInitFrom(Hash);
If Hash is TMD6Hash then
  begin
    fMD6 := Copy(TMD6Hash(Hash).fMD6);
    fHashBits := TMD6Hash(Hash).fHashBits;
    fKey := Copy(TMD6Hash(Hash).Key);
    fRounds := TMD6Hash(Hash).fRounds;
    fRoundsDef := TMD6Hash(Hash).fRoundsDef;
    fModeControl := TMD6Hash(Hash).fModeControl;
    // state copy
    fState := TMD6Hash(Hash).fState;
    SetLength(fState.Levels,Length(fState.Levels));
    For i := Low(fState.Levels) to High(fState.Levels) do
      SetLength(fState.Levels[i].Block,Length(fState.Levels[i].Block));
  end
else raise EMD6IncompatibleClass.CreateFmt('TMD6Hash.CreateAndInitFrom: Incompatible class (%s).',[Hash.ClassName]);
end;

//------------------------------------------------------------------------------

constructor TMD6Hash.CreateAndInitFrom(Hash: TMD6);
begin
CreateAndInit;
If (Length(Hash) > 0) and (Length(Hash) <= (MD6_BITS_MAX div 8)) then
  begin
    fMD6 := Copy(Hash);
    fHashBits := Length(fMD6) * 8;
    // other fields are left on default values
  end
else raise EMD6InvalidHash.CreateFmt('TMD6Hash.CreateAndInitFrom: Invalid hash length (%d).',[Length(Hash)]);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.Init;
begin
inherited;
SetLength(fState.Levels,0);
AddTreeLevel;
end;

//------------------------------------------------------------------------------

Function TMD6Hash.Compare(Hash: THashBase): Integer;
var
  Temp: TMD6;
  i:    Integer;
begin
If Hash is Self.ClassType then
  begin
    Result := 0;
    Temp := TMD6Hash(Hash).fMD6;
    If Length(fMD6) = Length(Temp) then
      begin
        For i := Low(fMD6) to High(fMD6) do
          If fMD6[i] > Temp[i] then
            begin
              Result := +1;
              Break;
            end
          else If fMD6[i] < Temp[i] then
            begin
              Result := -1;
              Break;
            end;
      end
    else raise EMD6IncompatibleSize.CreateFmt('TMD6Hash.Compare: Incompatible size (%d,%d).',[Length(fMD6),Length(Temp)]);
  end
else raise EMD6IncompatibleClass.CreateFmt('TMD6Hash.Compare: Incompatible class (%s).',[Hash.ClassName]);
end;

//------------------------------------------------------------------------------

Function TMD6Hash.AsString: String;
const
  HEX_TAB: array[0..15] of Char =
    ('0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F');
var
  i:  Integer;
begin
Result := StringOfChar('0',Length(fMD6) * 2);
For i := Low(fMD6) to High(fMD6) do
  begin
    Result[(i * 2) + 1] := HEX_TAB[fMD6[i] shr 4];
    Result[(i * 2) + 2] := HEX_TAB[fMD6[i] and 15];
  end;
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.FromString(const Str: String);
var
  Temp: TMD6;
  i:    Integer;
begin
If (Length(Str) >= 2) and (Length(Str) <= (MD6_BITS_MAX div 4)) then
  begin
    SetLength(Temp,Length(Str) div 2);
    For i := Low(Temp) to High(Temp) do
      Temp[i] := UInt8(StrToInt('$' + Copy(Str,(i * 2) + 1,2)));
    fMD6 := Temp;
  end
else raise EMD6InvalidHash.CreateFmt('TMD6Hash.FromString: Invalid hash length (%d).',[Length(Str) div 2]);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.FromStringDef(const Str: String; const Default: TMD6);
begin
inherited FromStringDef(Str,Default);
If not TryFromString(Str) then
  fMD6 := Copy(Default);
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.SaveToStream(Stream: TStream; Endianness: THashEndianness = heDefault);
var
  Temp: TMD6;
begin
case Endianness of
  heSystem: Temp := {$IFDEF ENDIAN_BIG}MD6ToBE{$ELSE}MD6ToLE{$ENDIF}(fMD6);
  heLittle: Temp := MD6ToLE(fMD6);
  heBig:    Temp := MD6ToBE(fMD6);
else
 {heDefault}
  Temp := fMD6;
end;
If Length(Temp) > 0 then
  Stream.WriteBuffer(Addr(Temp[0])^,Length(Temp));
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.LoadFromStream(Stream: TStream; Endianness: THashEndianness = heDefault);
var
  Temp: TMD6;
begin
SetLength(Temp,Length(fMD6));
If Length(Temp) > 0 then
  begin
    Stream.ReadBuffer(Addr(Temp[0])^,Length(Temp));
    case Endianness of
      heSystem: fMD6 := {$IFDEF ENDIAN_BIG}MD6FromBE{$ELSE}MD6FromLE{$ENDIF}(Temp);
      heLittle: fMD6 := MD6FromLE(Temp);
      heBig:    fMD6 := MD6FromBE(Temp);
    else
     {heDefault}
      fMD6 := Temp;
    end;
  end;
end;

//------------------------------------------------------------------------------

procedure TMD6Hash.SetKey(const Key; Size: TMemSize);
var
  TempKey:  TMD6Key;
begin
If Size <= MD6_KEY_MAXLEN then
  SetLength(TempKey,Size)
else
  SetLength(TempKey,MD6_KEY_MAXLEN);
If Size > 0 then
  Move(Key,Addr(TempKey[0])^,Size);
Self.Key := TempKey; // calls full setter
end;

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

procedure TMD6Hash.SetKey(const Key: String);
var
  TempStr:  UTF8String;
begin
TempStr := StrToUTF8(Key);
SetKey(PUTF8Char(TempStr)^,Length(TempStr) * SizeOf(UTF8Char));
end;

end.
