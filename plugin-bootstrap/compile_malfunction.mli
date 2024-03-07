type bool = True  | False 
type byte = X00  | X01  | X02  | X03  | X04  | X05  | X06  | X07  | X08  | X09  | X0a  | X0b  | X0c  | X0d  | X0e  | X0f  | X10  | X11  | X12  | X13  | X14  | X15  | X16  | X17  | X18  | X19  | X1a  | X1b  | X1c  | X1d  | X1e  | X1f  | X20  | X21  | X22  | X23  | X24  | X25  | X26  | X27  | X28  | X29  | X2a  | X2b  | X2c  | X2d  | X2e  | X2f  | X30  | X31  | X32  | X33  | X34  | X35  | X36  | X37  | X38  | X39  | X3a  | X3b  | X3c  | X3d  | X3e  | X3f  | X40  | X41  | X42  | X43  | X44  | X45  | X46  | X47  | X48  | X49  | X4a  | X4b  | X4c  | X4d  | X4e  | X4f  | X50  | X51  | X52  | X53  | X54  | X55  | X56  | X57  | X58  | X59  | X5a  | X5b  | X5c  | X5d  | X5e  | X5f  | X60  | X61  | X62  | X63  | X64  | X65  | X66  | X67  | X68  | X69  | X6a  | X6b  | X6c  | X6d  | X6e  | X6f  | X70  | X71  | X72  | X73  | X74  | X75  | X76  | X77  | X78  | X79  | X7a  | X7b  | X7c  | X7d  | X7e  | X7f  | X80  | X81  | X82  | X83  | X84  | X85  | X86  | X87  | X88  | X89  | X8a  | X8b  | X8c  | X8d  | X8e  | X8f  | X90  | X91  | X92  | X93  | X94  | X95  | X96  | X97  | X98  | X99  | X9a  | X9b  | X9c  | X9d  | X9e  | X9f  | Xa0  | Xa1  | Xa2  | Xa3  | Xa4  | Xa5  | Xa6  | Xa7  | Xa8  | Xa9  | Xaa  | Xab  | Xac  | Xad  | Xae  | Xaf  | Xb0  | Xb1  | Xb2  | Xb3  | Xb4  | Xb5  | Xb6  | Xb7  | Xb8  | Xb9  | Xba  | Xbb  | Xbc  | Xbd  | Xbe  | Xbf  | Xc0  | Xc1  | Xc2  | Xc3  | Xc4  | Xc5  | Xc6  | Xc7  | Xc8  | Xc9  | Xca  | Xcb  | Xcc  | Xcd  | Xce  | Xcf  | Xd0  | Xd1  | Xd2  | Xd3  | Xd4  | Xd5  | Xd6  | Xd7  | Xd8  | Xd9  | Xda  | Xdb  | Xdc  | Xdd  | Xde  | Xdf  | Xe0  | Xe1  | Xe2  | Xe3  | Xe4  | Xe5  | Xe6  | Xe7  | Xe8  | Xe9  | Xea  | Xeb  | Xec  | Xed  | Xee  | Xef  | Xf0  | Xf1  | Xf2  | Xf3  | Xf4  | Xf5  | Xf6  | Xf7  | Xf8  | Xf9  | Xfa  | Xfb  | Xfc  | Xfd  | Xfe  | Xff 
type t = EmptyString  | String of byte * t
type nat = O  | S of nat
type modpath = MPfile of t  list | MPbound of t  list * t * nat | MPdot of modpath * t
type positive = XI of positive | XO of positive | XH 
type z = Z0  | Zpos of positive | Zneg of positive
type tree = Leaf  | Node of z * tree * (modpath * t) * tree
type t_ = { this : tree ; is_ok : Obj.t (* not supported *) ;  }
type dearging_config = { overridden_masks : (modpath * t) -> (bool  list)  option ; do_trim_const_masks : bool ; do_trim_ctor_masks : bool ;  }
type unsafe_passes = { cofix_to_lazy : bool;
    reorder_constructors : bool;
    inlining : bool;
    unboxing : bool;
    betared : bool }
type erasure_configuration = { enable_unsafe : unsafe_passes ; enable_typed_erasure : bool ; enable_fast_remove_params : bool ; dearging_config : dearging_config ; 
    inlined_constants : t_ }
type 'id prim_def = Global of 'id * 'id | Primitive of t * nat | Erased 
type malfunction_pipeline_config = { erasure_config : erasure_configuration ; prims : (t * t  prim_def)  list ;  }
type program_type = Standalone | Shared_lib of t * t

val compile_malfunction_gen : malfunction_pipeline_config -> program_type -> 
    TemplateProgram.template_program -> t list * t