Hacspec_lib.vo Hacspec_lib.glob Hacspec_lib.v.beautified Hacspec_lib.required_vo: Hacspec_lib.v 
Hacspec_lib.vio: Hacspec_lib.v 
Hacspec_lib.vos Hacspec_lib.vok Hacspec_lib.required_vos: Hacspec_lib.v 
Core.vo Core.glob Core.v.beautified Core.required_vo: Core.v 
Core.vio: Core.v 
Core.vos Core.vok Core.required_vos: Core.v 
Hacspec_ovn.vo Hacspec_ovn.glob Hacspec_ovn.v.beautified Hacspec_ovn.required_vo: Hacspec_ovn.v Core.vo Hacspec_lib.vo
Hacspec_ovn.vio: Hacspec_ovn.v Core.vio Hacspec_lib.vio
Hacspec_ovn.vos Hacspec_ovn.vok Hacspec_ovn.required_vos: Hacspec_ovn.v Core.vos Hacspec_lib.vos
