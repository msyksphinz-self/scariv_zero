package tl_pkg;

  typedef struct packed {
    logic [  2:0] opcode ; //  C 3 Operation code. Identifies the type of message carried by the channel. (Table 5.2)
    logic [  2:0] param  ; //  C 3 Parameter code. Meaning depends on a opcode; specifies transfer of caching permissions or a sub-opcode. (Sections 6.2, 7.2, 8.3)
    logic [  3:0] size   ; //  C z Logarithm of the operation size: 2^n bytes. (Section 4.6)
    logic [  3:0] source ; //  C o Unique, per-link master source identifier. (Section 5.4)
    logic [ 32:0] address; //  C a Target byte address of the operation. Must be aligned to a size. (Section 4.6)
    logic [ 15:0] mask   ; //  D w Byte lane select for messages with data. (Section 4.6)
    logic [255:0] data   ; //  D 8w Data payload for messages with data. (Section 4.6)
    logic         corrupt; //  D 1 The data in this beat is corrupt. (Section 4.5)
    logic         valid  ; //  V 1 The sender is offering progress on an operation. (Section 4.1)
    logic         ready  ; //  R 1 The receiver accepted the offered progress. (Section 4.1)
  } a_cmd;

  typedef struct packed {
    logic [:0] opcode ; // C 3 Operation code. Identifies the type of message carried by the channel. (Table 5.2)
    logic [:0] param  ; // C 3 Parameter code. Meaning depends on b opcode; specifies a transfer of caching permissions or a sub-opcode. (Section 8.3)
    logic [:0] size   ; // C z Logarithm of the operation size: 2 n bytes. (Section 4.6)
    logic [:0] source ; // C o Unique, per-link master source identifier. (Section 5.4)
    logic [:0] address; // C a Target byte address of the operation. Must be aligned to b size. (Section 4.6)
    logic [:0] mask   ; // D w Byte lane select for messages with data. (Section 4.6)
    logic [:0] data   ; // D 8w Data payload for messages with data. (Section 4.6)
    logic [:0] corrupt; // D 1 Corruption was detected in data payload. (Section 4.5)
    logic [:0] valid  ; // V 1 The sender is offering progress on an operation. (Section 4.1)
    logic [:0] ready  ; // R 1 The receiver accepted the offered progress. (Section 4.1)
  } b_cmd;

  typedef struct packed {
    logic [:0] opcode ; // C 3 Operation code. Identifies the type of message carried by the channel. (Table 5.2)
    logic [:0] param  ; // C 3 Parameter code. Meaning depends on c opcode; specifies a transfer of caching permissions. (Section 8.3)
    logic [:0] size   ; // C z Logarithm of the operation size: 2 n bytes. (Section 4.6)
    logic [:0] source ; // C o Unique, per-link master source identifier. (Section 5.4)
    logic [:0] address; // C a Target byte address of the operation. Must be aligned to c size. (Section 4.6)
    logic [:0] data   ; // D 8w Data payload for messages with data. (Section 4.6)
    logic [:0] corrupt; // D 1 Corruption was detected in data payload. (Section 4.5)
    logic [:0] valid  ; // V 1 The sender is offering progress on an operation. (Section 4.1)
    logic [:0] ready  ; // R 1 The receiver accepted the offered progress. (Section 4.1)    
  } c_cmd;

  typedef struct packed {
    logic [:0] opcode ; // C 3 Operation code. Identifies the type of message carried by the channel. (Table 5.2)
    logic [:0] param  ; // C 2 Parameter code. Meaning depends on d opcode; specifies permissions to transfer or a sub-opcode. (Sections 6.2, 7.2, 8.3)
    logic [:0] size   ; // C z Logarithm of the operation size: 2 n bytes. (Section 4.6)
    logic [:0] source ; // C o Unique, per-link master source identifier. (Section 5.4)
    logic [:0] sink   ; // C i Unique, per-link slave sink identifier. (Section 5.4)
    logic [:0] denied ; // C 1 The slave was unable to service the request. (Section 4.5)
    logic [:0] data   ; // D 8w Data payload for messages with data. (Section 4.6)
    logic [:0] corrupt; // D 1 Corruption was detected in the data payload. (Section 4.5)
    logic [:0] valid  ; // V 1 The sender is offering progress on an operation. (Section 4.1)
    logic [:0] ready  ; // R 1 The receiver accepted the offered progress. (Section 4.1)
  } d_cmd;

  typedef struct packed {
    logic sink ; // C i Unique, per-link slave sink identifier. (Section 5.4)
    logic valid; // V 1 The sender is offering progress on an operation. (Section 4.1)
    logic ready; // R 1 The receiver accepted the offered progress. (Section 4.1)
  } e_cmd;

endpackage
