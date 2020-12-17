src/xbigop.vo src/xbigop.glob src/xbigop.v.beautified src/xbigop.required_vo: src/xbigop.v 
src/xbigop.vio: src/xbigop.v 
src/xbigop.vos src/xbigop.vok src/xbigop.required_vos: src/xbigop.v 
src/relorder.vo src/relorder.glob src/relorder.v.beautified src/relorder.required_vo: src/relorder.v src/xbigop.vo
src/relorder.vio: src/relorder.v src/xbigop.vio
src/relorder.vos src/relorder.vok src/relorder.required_vos: src/relorder.v src/xbigop.vos
