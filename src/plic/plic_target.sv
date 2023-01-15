/////////////////////////////////////////////////////////////////////
//   ,------.                    ,--.                ,--.          //
//   |  .--. ' ,---.  ,--,--.    |  |    ,---. ,---. `--' ,---.    //
//   |  '--'.'| .-. |' ,-.  |    |  |   | .-. | .-. |,--.| .--'    //
//   |  |\  \ ' '-' '\ '-'  |    |  '--.' '-' ' '-' ||  |\ `--.    //
//   `--' '--' `---'  `--`--'    `-----' `---' `-   /`--' `---'    //
//                                             `---'               //
//   RISC-V Platform-Level Interrupt Controller                    //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//             Copyright (C) 2017 ROA Logic BV                     //
//             www.roalogic.com                                    //
//                                                                 //
//   This source file may be used and distributed without          //
//   restriction provided that this copyright statement is not     //
//   removed from the file and that any derivative work contains   //
//   the original copyright notice and the associated disclaimer.  //
//                                                                 //
//      THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY        //
//   EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     //
//   TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS     //
//   FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR OR     //
//   CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,  //
//   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT  //
//   NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;  //
//   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)      //
//   HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN     //
//   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR  //
//   OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS          //
//   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  //
//                                                                 //
/////////////////////////////////////////////////////////////////////

// +FHDR -  Semiconductor Reuse Standard File Header Section  -------
// FILE NAME      : plic_target.sv
// DEPARTMENT     :
// AUTHOR         : rherveille
// AUTHOR'S EMAIL :
// ------------------------------------------------------------------
// RELEASE HISTORY
// VERSION DATE        AUTHOR      DESCRIPTION
// 1.0     2017-07-01  rherveille  initial release
// ------------------------------------------------------------------
// KEYWORDS : RISC-V PLATFORM LEVEL INTERRUPT CONTROLLER - PLIC
// ------------------------------------------------------------------
// PURPOSE  : PLIC Target
//            Generates Interrupt Request and ID for each target
// ------------------------------------------------------------------
// PARAMETERS
//  PARAM NAME        RANGE  DESCRIPTION              DEFAULT UNITS
//  SOURCES           1+     No. of interupt sources  8
//  PRIORITIES        1+     No. of priority levels   8
// ------------------------------------------------------------------
// REUSE ISSUES 
//   Reset Strategy      : external asynchronous active low; rst_ni
//   Clock Domains       : 1, clk, rising edge
//   Critical Timing     :
//   Test Features       : na
//   Asynchronous I/F    : no
//   Scan Methodology    : na
//   Instantiations      : plic_priority_index
//   Synthesizable (y/n) : Yes
//   Other               :                                         
// -FHDR-------------------------------------------------------------

module plic_target #(
  parameter SOURCES = 8,
  parameter PRIORITIES = 7,

  //These should be localparams, but that's not supported by all tools yet
  parameter SOURCES_BITS  = $clog2(SOURCES +1), //0=reserved
  parameter PRIORITY_BITS = $clog2(PRIORITIES)
)
(
  input                          rst_ni,               //Active low asynchronous reset
                                 clk_i,                //System clock

  input      [SOURCES_BITS -1:0] id_i       [SOURCES], //Interrupt source
  input      [PRIORITY_BITS-1:0] priority_i [SOURCES], //Interrupt Priority

  input      [PRIORITY_BITS-1:0] threshold_i,          //Interrupt Priority Threshold

  output reg                     ireq_o,               //Interrupt Request (EIP)
  output reg [SOURCES_BITS -1:0] id_o                  //Interrupt ID
);
  //////////////////////////////////////////////////////////////////
  //
  // Constant
  //


  //////////////////////////////////////////////////////////////////
  //
  // Variables
  //
  logic [SOURCES_BITS -1:0] id;
  logic [PRIORITY_BITS-1:0] pr;


  //////////////////////////////////////////////////////////////////
  //
  // Module Body
  //

  /** Select highest priority pending interrupt
   */
  plic_priority_index #(
    .SOURCES    ( SOURCES    ),
    .PRIORITIES ( PRIORITIES ),
    .HI         ( SOURCES -1 ),
    .LO         ( 0          )
  )
  priority_index_tree (
    .priority_i ( priority_i ),
    .idx_i      ( id_i       ),
    .priority_o ( pr         ),
    .idx_o      ( id         )
  );


  /** Generate output
  */
  always @(posedge clk_i,negedge rst_ni)
    if      (!rst_ni          ) ireq_o <= 1'b0;
    else if ( pr > threshold_i) ireq_o <= 1'b1;
    else                        ireq_o <= 1'b0;

  always @(posedge clk_i)
    id_o <= id;

endmodule : plic_target
