AsmGen.vo AsmGen.glob AsmGen.v.beautified AsmGen.required_vo: AsmGen.v CpdtTactics.vo
AsmGen.vio: AsmGen.v CpdtTactics.vio
AsmGen.vos AsmGen.vok AsmGen.required_vos: AsmGen.v CpdtTactics.vos
CpdtTactics.vo CpdtTactics.glob CpdtTactics.v.beautified CpdtTactics.required_vo: CpdtTactics.v 
CpdtTactics.vio: CpdtTactics.v 
CpdtTactics.vos CpdtTactics.vok CpdtTactics.required_vos: CpdtTactics.v 
partial_map.vo partial_map.glob partial_map.v.beautified partial_map.required_vo: partial_map.v 
partial_map.vio: partial_map.v 
partial_map.vos partial_map.vok partial_map.required_vos: partial_map.v 
progLog.vo progLog.glob progLog.v.beautified progLog.required_vo: progLog.v AsmGen.vo
progLog.vio: progLog.v AsmGen.vio
progLog.vos progLog.vok progLog.required_vos: progLog.v AsmGen.vos
