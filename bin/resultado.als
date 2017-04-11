/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= programa_wap
 * loopUnroll= 1
 * removeQuantifiers= true
 * strictUnrolling= true
 */ 

//-------------- prelude--------------//
module moduleId
open Integer32
open util/sequniv as sequniv
fun fun_reach[h: univ, 
              type: set univ, 
              field: univ -> univ
]: set univ { 
  h.*(field & type->(type+null)) & type 
}

one
sig Null{}
abstract sig char {}
abstract sig Exception{}
one sig E1 extends Exception{}
fun shl[l,r: Int]: Int { l << r } 
fun sshr[l,r: Int]: Int { l >> r } 
fun ushr[l,r: Int]: Int { l >>> r } 

fun fun_univ_equals[
  l:univ, 
  r: univ 
]: boolean { 
  (equ[l,r]) => true else false 
} 

fun fun_set_add[
  l: set univ,
  e: univ
]: set univ { 
  l+e 
} 

fun fun_set_remove[
  l: set univ,
  e: univ
]: set univ {
  l-e
}
fun fun_set_contains[
  l: set univ,
  e: univ
]: boolean {
  (e in l) => true else false 
} 
pred isSubset[
  l: set univ,
  r: set univ
] {
  (l in r) 
} 
pred isNotSubset[
  l: set univ,
  r: set univ
] {
  (l !in r) 
} 
fun fun_set_size[s: set univ]: Int { #s } 

fun fun_not_empty_set[s: set univ]: boolean { (#s = 0) => false else true } 

pred pred_empty_set[l: set univ] { (no l) } 

pred pred_set_some[l: set univ] { some l } 

pred pred_set_one[l: set univ] { one l } 

pred pred_set_lone[l: set univ] { lone l } 


fun fun_set_intersection[
  l: set univ,
  r: set univ
]: set univ {
  l & r 
} 
fun fun_set_difference[
  l: set univ,
  r: set univ
]: set univ {
  l - r 
} 
fun fun_set_sum[
  s: set Int
]: Int {
  sum s 
} 
pred pred_empty_list[l: seq univ] { (no l) } 

fun fun_list_add[
  l: seq univ,
  e: univ
]: seq univ {
  sequniv/add[l,e] 
} 

fun fun_list_get[
  l: seq univ, 
  index: Int
]: univ { 
  index.l 
} 

fun fun_list_contains[
  l: seq univ, 
  e: univ
]: boolean { 
  (e in Int.l) => true else false 
} 

fun fun_list_remove[
  l: seq univ, 
  index: Int
]: seq univ { 
  sequniv/delete[l,index] 
} 

fun fun_list_size[s: seq univ]: Int { #s } 

fun fun_list_equals[
  s1:seq univ, 
  s2: seq univ
]: boolean { 
  (s1=s2) => true else false 
} 

fun fun_list_empty[s: seq univ]: boolean { (#s = 0) => true else false } 

pred pred_empty_map[map: univ -> univ] { (no map) } 

fun fun_map_put[
  map: univ->univ, 
  k: univ, 
  v: univ
]: univ-> univ { 
  map ++ (k->v) 
}

fun fun_map_contains_key[
  map: univ -> univ, 
  k: univ
]: boolean { 
  (some k.map) => true else false 
}

fun fun_map_remove[
  map: univ -> univ, 
  k: univ
]: univ->univ {
  map - (k->univ) 
} 

fun fun_map_get[
  map: univ -> univ, 
  k: univ
]: univ { 
  (some k.map) => k.map else null 
} 

fun fun_map_is_empty[
  map: univ -> univ, 
]: boolean { 
  (some map) => false else true 
}

fun fun_map_clear[
  mapEntries1: univ -> univ -> univ, 
  map: univ
]: univ -> univ -> univ { 
  mapEntries1 - (map -> univ -> univ)
}

fun fun_map_size[
  map: univ -> univ, 
]: univ {
  #map 
} 

pred isEmptyOrNull[u: univ] { u in null } 
fun fun_closure[
  rel: univ -> univ 
]: univ -> univ {
  ^rel 
} 

fun fun_reflexive_closure[
  rel: univ -> univ 
]: univ -> univ {
  *rel 
} 

fun fun_transpose[
  rel: univ -> univ 
]: univ -> univ {
  ~rel 
} 


fun rel_override[
  r:univ->univ,
  k:univ, 
  v:univ
]: univ->univ { 
  r - (k->univ) + (k->v) 
} 


pred pred_in[n: univ, t: set univ] { n in t } 

pred instanceOf[n: univ, t: set univ] { n in t } 

pred isCasteableTo[n: univ, t: set univ] { (n in t) or (n = null) }
abstract sig actionExec{}
pred pos_gen_Int[y:Int]{
 some i: Int | y = i
}
pred pos_gen_bool[y:boolean]{
 some i: boolean | y = i
}
pred pos_gen_I32[y:JavaPrimitiveIntegerValue]{
  some i: JavaPrimitiveIntegerValue | pred_java_primitive_integer_value_eq[y,i]
}
pred pos_add_null[s:JavaPrimitiveIntegerValue,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}


pred pos_verify_null[s:JavaPrimitiveIntegerValue+null,b:boolean]{
   equ[s,null] implies equ[b,false]
   not equ[s,null] implies equ[b,true]
}
pred pos_vaciar[s:set univ]{
    no s
}
pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue}





// accion que asigna el parametro de retorno generado por alguna otra accion previa al parametro entero 2


pred pre_assign_intJ2[a: boolean]{
a=true
}

pred pos_assign_intJ2[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  a: JavaPrimitiveIntegerValue,a': JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue,ret':JavaPrimitiveIntegerValue,
  valid: boolean,valid':boolean,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{
  values=values' and size=size' and vac=vac' and valid=valid' and ret=ret' and a'= ret' 
}
/*scope:1*/


pred precondition_stack_pop
[vac:boolean,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{    
  sequence[values] and vac=false
}





pred postcondition_stack_pop 
[ vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue
]
{

myseq_card[values,size] and pred_java_primitive_integer_value_add[size',i321,size,false] and 

(some a:JavaPrimitiveIntegerValue |  a=int32_max[values.JavaPrimitiveIntegerValue] and values'=values-(a->ret) and (a->ret) in values and 
                                     pred_java_primitive_integer_value_eq[ret,a.values]) 


and (pred_java_primitive_integer_value_eq[size',i320] implies vac'=true)
and (pred_java_primitive_integer_value_neq[size',i320] implies vac'=false)
}
/*scope:1*/





pred pre_add_element[]{}

pred pos_add_element[
  e: JavaPrimitiveIntegerValue,e':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  vac:boolean,vac':boolean]
{
  sequence[values] and 
  myseq_card[values,size] and  values'=values+(size->e) and
  pred_java_primitive_integer_value_add[size,i321,size',false] and vac'=false
}
/*scope:1*/


pred postcondition_Lista_get 
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  indice: JavaPrimitiveIntegerValue,
  retorno: JavaPrimitiveIntegerValue,
  size:JavaPrimitiveIntegerValue,
  size':JavaPrimitiveIntegerValue
]
{
      sequence[values] and values'=values and  pred_java_primitive_integer_value_eq[retorno,values[indice]] and 
pred_java_primitive_integer_value_eq[size,size']
    

}


pred precondition_Lista_get
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  indice: JavaPrimitiveIntegerValue
]
{
   not (no indice.values) and sequence[values] 

}
/*scope:0*/


pred pre_assign_bool[a: boolean]{
a=true
}

pred pos_assign_bool[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  a: boolean,a': boolean,
  ret: boolean,ret':boolean,
  valid: boolean,valid':boolean,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{
  values=values' and size=size' and vac=vac' and valid=valid' and ret=ret' and a'= ret' 
}
/*scope:1*/


pred postcondition_setsize
[i:JavaPrimitiveIntegerValue,i':JavaPrimitiveIntegerValue,vac:boolean,vac':boolean,size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue, values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values': JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{

 pred_java_primitive_integer_value_eq[i,i'] and 
  myseq_card[values,size] and 
 pred_java_primitive_integer_value_eq[i,size'] and 
 (pred_java_primitive_integer_value_eq[i,i320] implies vac'=true) and 
 (pred_java_primitive_integer_value_gt[i,i320] implies vac'=false) and


(pred_java_primitive_integer_value_eq[i,size] implies values=values') and 


 ((pred_java_primitive_integer_value_lt[i,size]  and  pred_java_primitive_integer_value_gt_zero[i]) 
implies 
(
   values' in values  and 

all j: values.JavaPrimitiveIntegerValue |
   
      
    (pred_java_primitive_integer_value_lt[j,i] implies  (j in values'.JavaPrimitiveIntegerValue)) and 
    (pred_java_primitive_integer_value_gte[j,i] implies  not (j in values'.JavaPrimitiveIntegerValue)) 
)
)

and

(pred_java_primitive_integer_value_gt[i,size] implies 
(
(all p:JavaPrimitiveIntegerValue |(pred_java_primitive_integer_value_gte[p,size] and  pred_java_primitive_integer_value_lt[p,i])
implies p->Null in values') 
 and values in values' and 
(let dom = values.JavaPrimitiveIntegerValue | values' - (dom->Null) = values'  )



)
)
}





pred precondition_setsize
[v:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),i:JavaPrimitiveIntegerValue]{
sequence[v] and pred_java_primitive_integer_value_gte[i,i320]
}
/*scope:0*/
pred precondition_stack_push[values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{
sequence[values] 
}

pred postcondition_stack_push[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  e: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret:JavaPrimitiveIntegerValue
]
{
 sequence[values] and pred_java_primitive_integer_value_eq[size,size'] and
 myseq_card[values,size] and  values'=values+(size->e) and
 pred_java_primitive_integer_value_add[size,i321,size',false] and vac'=false and 
 pred_java_primitive_integer_value_eq[ret,e]
}
/*scope:1*/


pred postcondition_clear
[vac:boolean,vac':boolean,size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue, values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values': JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{ pred_java_primitive_integer_value_eq[size',i320] and sequence[values'] and vac'=true
}

pred precondition_clear
[v: JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{
sequence[v]
}
/*scope:0*/
pred postcondition_Lista_eat 
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  indice: JavaPrimitiveIntegerValue,
  retorno: JavaPrimitiveIntegerValue,
  size:JavaPrimitiveIntegerValue,
  size':JavaPrimitiveIntegerValue
]
{
      sequence[values] and values'=values and  pred_java_primitive_integer_value_eq[retorno,values[indice]] and 
pred_java_primitive_integer_value_eq[size,size']
    

}


pred precondition_Lista_eat
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  indice: JavaPrimitiveIntegerValue
]
{
   not (no indice.values) and sequence[values] 

}
/*scope:0*/


pred postcondition_le[size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue]
{
  sequence[values] and values'=values and pred_java_primitive_integer_value_eq[size,size'] and
  myseq_card[values,size] and ret=values[fun_java_primitive_integer_value_sub[size,i321]]
}


pred precondition_le[thisType_1:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/


pred pre_size[]{}

pred pos_size [vac:boolean,vac':boolean,
   size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
   return_int':JavaPrimitiveIntegerValue, 
   values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{ 

  sequence[values] and values'=values and vac=vac' and 
  myseq_card[values,return_int'] and 
  pred_java_primitive_integer_value_eq[size,return_int'] and 
  pred_java_primitive_integer_value_eq[size,size'] 
}
/*scope:0*/










pred postcondition_Lista_contains[elem:JavaPrimitiveIntegerValue,elem':JavaPrimitiveIntegerValue,vac:boolean,vac':boolean,size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),return_bool: boolean]
{ 

 vac=vac' values'=values and 

(( not (no values.elem ) implies equ[return_bool, true])
     and
  ((no values.elem ) implies equ[return_bool, false] ))
and 
 myseq_card[values,size] and pred_java_primitive_integer_value_eq[size,size'] and pred_java_primitive_integer_value_eq[elem,elem'] 


}


pred precondition_Lista_contains[values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{
    sequence[values] 
}
/*scope:0*/

pred pre_add[values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{}

pred pos_add[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  e: JavaPrimitiveIntegerValue,  e': JavaPrimitiveIntegerValue, 
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  return_bool:boolean
]
{
 sequence[values] and myseq_card[values,size] and  values'=values+(size->e) and
  pred_java_primitive_integer_value_add[size,i321,size',false] and vac'=false and 
  pred_java_primitive_integer_value_eq[e,e'] and return_bool=true
}
/*scope:1*/


pred pre_iea[size:JavaPrimitiveIntegerValue,indice: JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{   (not (no indice.values) or pred_java_primitive_integer_value_eq[indice,size] ) and  sequence[values] 
 }



pred pos_iea
[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  elem: JavaPrimitiveIntegerValue,  elem': JavaPrimitiveIntegerValue,
  indice:JavaPrimitiveIntegerValue,indice':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{
        vac'=false and myseq_card[values,size]
        pred_java_primitive_integer_value_add[size,i321,size',true] and
	pred_java_primitive_integer_value_eq[indice,indice'] and 
	pred_java_primitive_integer_value_eq[elem,elem'] and 
	sequence[values] and 
        (indice->elem) in values' and
        (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies (
	(pred_java_primitive_integer_value_lt[a,indice] implies  (a->b) in values' ) and
	(pred_java_primitive_integer_value_gt[a,indice] implies  (fun_java_primitive_integer_value_add[a,i321]->b) in values' )
        )) and JavaPrimitiveIntegerValue.values'= JavaPrimitiveIntegerValue.values + elem
}
/*scope:1*/







pred pre_add2[size:JavaPrimitiveIntegerValue,indice: JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{   (not (no indice.values) or pred_java_primitive_integer_value_eq[indice,size] ) and  sequence[values] 
 }



pred pos_add2
[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  elem: JavaPrimitiveIntegerValue,  elem': JavaPrimitiveIntegerValue,
  indice:JavaPrimitiveIntegerValue,indice':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{
        vac'=false and myseq_card[values,size]
        pred_java_primitive_integer_value_add[size,i321,size',true] and
	pred_java_primitive_integer_value_eq[indice,indice'] and 
	pred_java_primitive_integer_value_eq[elem,elem'] and 
	sequence[values] and 
        (indice->elem) in values' and
        (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies (
	(pred_java_primitive_integer_value_lt[a,indice] implies  (a->b) in values' ) and
	(pred_java_primitive_integer_value_gt[a,indice] implies  (fun_java_primitive_integer_value_add[a,i321]->b) in values' )
        )) and JavaPrimitiveIntegerValue.values'= JavaPrimitiveIntegerValue.values + elem
}
/*scope:1*/


pred postcondition_removeallelements
[vac:boolean,vac':boolean,size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue, values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values': JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{ 
 pred_java_primitive_integer_value_eq[size',i320] and vac'=true and sequence[values]


}

pred precondition_removeallelements
[v: JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{
sequence[v]
}
/*scope:0*/
pred precondition_Lista_set_element
[ indice:JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{  not (no indice.values) and sequence[values]}


pred postcondition_Lista_set_element
[ size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  indice: JavaPrimitiveIntegerValue,
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  retorno:JavaPrimitiveIntegerValue
]
{
  pred_java_primitive_integer_value_eq[size,size'] and myseq_card[values,size] and
  sequence[values]  and retorno=indice.values and values'=values++(indice->elem) and sequence[values']
}
/*scope:0*/


pred postcondition_sle3[size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue]
{
  sequence[values] and values'=values and pred_java_primitive_integer_value_eq[size,size'] and
  myseq_card[values,size] and ret=values[fun_java_primitive_integer_value_sub[size,i321]]
}


pred precondition_sle3[thisType_1:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{      
    sequence[thisType_1] and not (no thisType_1)
}
/*scope:0*/


pred postcondition_Lista_isEmpty 
[ /*elem:JavaPrimitiveIntegerValue,elem': JavaPrimitiveIntegerValue,
  elem2:JavaPrimitiveIntegerValue,elem2':JavaPrimitiveIntegerValue,*/
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  return_bool: boolean 
]
{       // pred_java_primitive_integer_value_eq[elem,elem'] and pred_java_primitive_integer_value_eq[elem2,elem2'] and 
     (equ[return_bool, true] iff no values) and values=values' and 
     myseq_card[values,size] and pred_java_primitive_integer_value_eq[size,size']
}


pred precondition_Lista_isEmpty
[ values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]{
sequence[values]
}
/*scope:0*/


pred postcondition_Lista_remove_fo2
[ size:JavaPrimitiveIntegerValue, size':JavaPrimitiveIntegerValue, 
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: boolean,
  vac:boolean,
  vac':boolean]
{  (pred_java_primitive_integer_value_eq[size',i320] implies vac'=true) and 
   (pred_java_primitive_integer_value_neq[size',i320] implies vac'=false) and 

   myseq_card[values,size] and sequence[values] and sequence[values'] and
   (((no values.elem)  and ret=false and values=values' and pred_java_primitive_integer_value_eq[size',size]) 
    or

   
   (ret=true and pred_java_primitive_integer_value_add[size',i321,size,false]  and 
   (some i :JavaPrimitiveIntegerValue |
	    (i->elem) in values and 
            (all a,b:JavaPrimitiveIntegerValue | (a->b) in values  implies (
        	( pred_java_primitive_integer_value_lt[a,i]  implies (a->b) in values'  and   pred_java_primitive_integer_value_neq[b,elem])    and
		( pred_java_primitive_integer_value_lt[i,a]  implies ((fun_java_primitive_integer_value_sub[a,i321])->b) in values')) 
                                    ))))
}


pred precondition_Lista_remove_fo2
[]{ }
/*scope:1*/

pred precondition_Lista_set_elementA
[ indice:JavaPrimitiveIntegerValue,values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)]
{  not (no indice.values) and sequence[values]}


pred postcondition_Lista_set_elementA
[ size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  indice: JavaPrimitiveIntegerValue,
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  retorno:JavaPrimitiveIntegerValue
]
{
  pred_java_primitive_integer_value_eq[size,size'] and myseq_card[values,size] and
  sequence[values]  and retorno=indice.values and values'=values++(indice->elem) and sequence[values']
}
/*scope:0*/


//Elimina un elemento del vector, se pasa el indice como parametro  y retorna el elemento removido
pred precondition_Lista_remove_m
[
  indice:JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]{  not (no indice.values)
}

pred postcondition_Lista_remove_m
[ size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  indice:JavaPrimitiveIntegerValue, 
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue,
  vac:boolean,
  vac':boolean


]
{




(pred_java_primitive_integer_value_eq[size',i320] implies vac'=true) and 
   (pred_java_primitive_integer_value_neq[size',i320] implies vac'=false) and 


  sequence[values] and sequence[values']  and 

  pred_java_primitive_integer_value_eq[ret,indice.values]  

and 

 (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies 
	(( pred_java_primitive_integer_value_lt[a,indice] implies (a->b) in  values') and
	 ( pred_java_primitive_integer_value_gt[a,indice] implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values'))
) and 
  JavaPrimitiveIntegerValue.values' + indice.values = JavaPrimitiveIntegerValue.values  

and  myseq_card[values,size] and  let ss=fun_java_primitive_integer_value_sub[size,i321] |
   not (((ss)->JavaPrimitiveIntegerValue) in values')  and myseq_card[values',ss] 

}
/*scope:1*/



pred postcondition_Lista_get_first 
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue
]
{
   sequence[values] and values'=values and
   pred_java_primitive_integer_value_eq[ret,values[i320]] and 
   pred_java_primitive_integer_value_eq[size,size']
} 


pred precondition_Lista_get_first
[
  thisType_1:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{  sequence[thisType_1] and not (no thisType_1)}
/*scope:0*/ 
pred postcondition_stack_search 
[
  size:JavaPrimitiveIntegerValue,
  size':JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  v: JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue
]
{

    sequence[values]  and values'=values and pred_java_primitive_integer_value_eq[size,size'] and
    myseq_card[values,size]
   
   (( some i:JavaPrimitiveIntegerValue | i->v  in values and pred_java_primitive_integer_value_eq[ret,i]) or
   ( no values.v   and  pred_java_primitive_integer_value_eq[ret,i32m1]))
      
 
} 


pred precondition_stack_search
[
  thisType_1:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{      
    sequence[thisType_1] 
}
/*scope:0*/ 
pred postcondition_Lista_get_firstA 
[
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: JavaPrimitiveIntegerValue,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue
]
{
   sequence[values] and values'=values and
   pred_java_primitive_integer_value_eq[ret,values[i320]] and 
   pred_java_primitive_integer_value_eq[size,size']
} 


pred precondition_Lista_get_firstA
[
  thisType_1:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{  sequence[thisType_1] and not (no thisType_1)}
/*scope:0*/ 
pred pre_assign_intJ[a: boolean]{
a=true
}

pred pos_assign_intJ[
  vac:boolean,vac':boolean,
  size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  a: JavaPrimitiveIntegerValue,a': JavaPrimitiveIntegerValue,
  ret: JavaPrimitiveIntegerValue,ret':JavaPrimitiveIntegerValue,
  valid: boolean,valid':boolean,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]
{
  values=values' and size=size' and vac=vac' and valid=valid' and ret=ret' and a'= ret' 
}
/*scope:1*/


//Elimina un elemento del vector, se pasa el indice como parametro  y retorna void 
pred precondition_Lista_remove_mat
[
  indice:JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)
]{  not (no indice.values)
}

pred postcondition_Lista_remove_mat
[ size:JavaPrimitiveIntegerValue,size':JavaPrimitiveIntegerValue,
  indice:JavaPrimitiveIntegerValue, 
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),vac:boolean,vac':boolean]
{

(pred_java_primitive_integer_value_eq[size',i320] implies vac'=true) and 
   (pred_java_primitive_integer_value_neq[size',i320] implies vac'=false) and 

  sequence[values] and sequence[values']    

and 

 (all a,b:JavaPrimitiveIntegerValue | (a->b) in values implies 
	(( pred_java_primitive_integer_value_lt[a,indice] implies (a->b) in  values') and
	 ( pred_java_primitive_integer_value_gt[a,indice] implies (fun_java_primitive_integer_value_sub[a,i321]->b) in values'))
) and 
  JavaPrimitiveIntegerValue.values' + indice.values = JavaPrimitiveIntegerValue.values  

and  myseq_card[values,size] and  let ss=fun_java_primitive_integer_value_sub[size,i321] |
   not (((ss)->JavaPrimitiveIntegerValue) in values')  and myseq_card[values',ss] 

}
/*scope:1*/


//Elimina un elemento del vector y retorna un boolean 

pred postcondition_Lista_remove_fo
[ size:JavaPrimitiveIntegerValue, size':JavaPrimitiveIntegerValue, 
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  values':JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),
  ret: boolean,vac:boolean,vac':boolean
]
{ 

   (pred_java_primitive_integer_value_eq[size',i320] implies vac'=true) and 
   (pred_java_primitive_integer_value_neq[size',i320] implies vac'=false) and
   myseq_card[values,size] and sequence[values] and sequence[values'] and
   (((no values.elem)  and ret=false and values=values' and pred_java_primitive_integer_value_eq[size',size]) 
    or

   
   (ret=true and pred_java_primitive_integer_value_add[size',i321,size,false]  and 
   (some i :JavaPrimitiveIntegerValue |
	    (i->elem) in values and 
            (all a,b:JavaPrimitiveIntegerValue | (a->b) in values  implies (
        	( pred_java_primitive_integer_value_lt[a,i]  implies (a->b) in values'  and   pred_java_primitive_integer_value_neq[b,elem])    and
		( pred_java_primitive_integer_value_lt[i,a]  implies ((fun_java_primitive_integer_value_sub[a,i321])->b) in values')) 
                                    ))))
}


pred precondition_Lista_remove_fo
[]{ }
/*scope:1*/




one
sig assign_int2_action extends actionExec{}
one sig stack_pop_action extends actionExec{}
one sig vector_addElement_action extends actionExec{}
one sig Lista_get extends actionExec{}
one sig assign_bool_action extends actionExec{}
one sig vector_setsize_action extends actionExec{}
one sig stack_push_action extends actionExec{}
one sig vector_clear_action extends actionExec{}
one sig vector_elementAt_action extends actionExec{}
one sig vector_lastElement_action extends actionExec{}
one sig vector_size_action extends actionExec{}
one sig stack_contains_action extends actionExec{}
one sig vector_add_action extends actionExec{}
one sig vector_insertElement_action extends actionExec{}
one sig stack_addIndexItem_action extends actionExec{}
one sig vector_removeallelements_action extends actionExec{}
one sig stack_setElement_action extends actionExec{}
one sig vector_peek_action extends actionExec{}
one sig stack_empty_action extends actionExec{}
one sig vector_remove_action extends actionExec{}
one sig stack_set_action extends actionExec{}
one sig vector_removeIndex_action extends actionExec{}
one sig get_first extends actionExec{}
one sig stack_search_action extends actionExec{}
one sig stack_firstElement_action extends actionExec{}
one sig assign_int_action extends actionExec{}
one sig vector_removeElementAt_action extends actionExec{}
one sig vector_removeElement_action extends actionExec{}
pred pred_not[p_0:JavaPrimitiveIntegerValue,p_1:JavaPrimitiveIntegerValue,p_2:boolean,p_3:boolean,p_4:JavaPrimitiveIntegerValue,p_5:JavaPrimitiveIntegerValue,p_6:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),p_7:JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null),p_8:boolean,b:boolean]{ not(postcondition_Lista_contains[p_0,p_1,p_2,p_3,p_4,p_5,p_6,p_7,p_8] and b=true)}
 



pred assign_bool_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  bool_1_0: boolean,
  bool_1_1: boolean,
  return_bool_0: boolean,
  return_bool_1: boolean,
  valid_bool_0: boolean,
  valid_bool_1: boolean,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_assign_bool[valid_bool_0]
  and 
  pos_assign_bool[vac_0,
                 vac_1,
                 size_0,
                 size_1,
                 bool_1_0,
                 bool_1_1,
                 return_bool_0,
                 return_bool_1,
                 valid_bool_0,
                 valid_bool_1,
                 thisType_1_0,
                 thisType_1_1]
}


pred stack_set_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_set_elementA[intJ_1_0,
                                 thisType_1_0]
  and 
  postcondition_Lista_set_elementA[size_0,
                                  size_1,
                                  intJ_1_0,
                                  intJ_2_0,
                                  thisType_1_0,
                                  thisType_1_1,
                                  return_Jint_1_1]
}


pred vector_addElement_action[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean
]{
  pre_add_element[]
  and 
  pos_add_element[intJ_1_0,
                 intJ_1_1,
                 thisType_1_0,
                 thisType_1_1,
                 size_0,
                 size_1,
                 vac_0,
                 vac_1]
}


pred vector_removeIndex_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean
]{
  precondition_Lista_remove_m[intJ_1_0,
                             thisType_1_0]
  and 
  postcondition_Lista_remove_m[size_0,
                              size_1,
                              intJ_1_0,
                              thisType_1_0,
                              thisType_1_1,
                              return_Jint_1_1,
                              vac_0,
                              vac_1]
}


pred vector_removeElementAt_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  vac_0: boolean,
  vac_1: boolean
]{
  precondition_Lista_remove_mat[intJ_1_0,
                               thisType_1_0]
  and 
  postcondition_Lista_remove_mat[size_0,
                                size_1,
                                intJ_1_0,
                                thisType_1_0,
                                thisType_1_1,
                                vac_0,
                                vac_1]
}


pred vector_insertElement_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  intJ_2_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_iea[size_0,
         intJ_1_0,
         thisType_1_0]
  and 
  pos_iea[vac_0,
         vac_1,
         size_0,
         size_1,
         intJ_1_0,
         intJ_1_1,
         intJ_2_0,
         intJ_2_1,
         thisType_1_0,
         thisType_1_1]
}


pred gen_bool[
  x_1: boolean
]{
  TruePred[]
  and 
  pos_gen_bool[x_1]
}


pred stack_pop_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_stack_pop[vac_0,
                        thisType_1_0]
  and 
  postcondition_stack_pop[vac_0,
                         vac_1,
                         size_0,
                         size_1,
                         thisType_1_0,
                         thisType_1_1,
                         return_Jint_1_1]
}


pred get_first[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_get_first[thisType_1_0]
  and 
  postcondition_Lista_get_first[thisType_1_0,
                               thisType_1_1,
                               return_intJ_1_1,
                               size_0,
                               size_1]
}


pred gen_intJ[
  x_1: JavaPrimitiveIntegerValue
]{
  TruePred[]
  and 
  pos_gen_I32[x_1]
}


pred stack_empty_action[
  return_bool_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_Lista_isEmpty[thisType_1_0]
  and 
  postcondition_Lista_isEmpty[size_0,
                             size_1,
                             thisType_1_0,
                             thisType_1_1,
                             return_bool_1]
}


pred vector_elementAt_action[
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_eat[thisType_1_0,
                        intJ_1_0]
  and 
  postcondition_Lista_eat[thisType_1_0,
                         thisType_1_1,
                         intJ_1_0,
                         return_Jint_1_1,
                         size_0,
                         size_1]
}


pred stack_contains_action[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean,
  return_bool_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_Lista_contains[thisType_1_0]
  and 
  postcondition_Lista_contains[intJ_1_0,
                              intJ_1_1,
                              vac_0,
                              vac_1,
                              size_0,
                              size_1,
                              thisType_1_0,
                              thisType_1_1,
                              return_bool_1]
}


pred vector_removeElement_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_bool_1: boolean,
  vac_0: boolean,
  vac_1: boolean
]{
  precondition_Lista_remove_fo[]
  and 
  postcondition_Lista_remove_fo[size_0,
                               size_1,
                               intJ_1_0,
                               thisType_1_0,
                               thisType_1_1,
                               return_bool_1,
                               vac_0,
                               vac_1]
}


pred vector_lastElement_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_le[thisType_1_0]
  and 
  postcondition_le[size_0,
                  size_1,
                  thisType_1_0,
                  thisType_1_0,
                  return_Jint_1_1]
}


pred vector_removeallelements_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_removeallelements[thisType_1_0]
  and 
  postcondition_removeallelements[vac_0,
                                 vac_1,
                                 size_0,
                                 size_1,
                                 thisType_1_0,
                                 thisType_1_1]
}


pred assign_int2_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  intJ_2_1: JavaPrimitiveIntegerValue,
  return_Jint_1_0: JavaPrimitiveIntegerValue,
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  valid_intJ_0: boolean,
  valid_intJ_1: boolean,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_assign_intJ[valid_intJ_0]
  and 
  pos_assign_intJ[vac_0,
                 vac_1,
                 size_0,
                 size_1,
                 intJ_2_0,
                 intJ_2_1,
                 return_Jint_1_0,
                 return_Jint_1_1,
                 valid_intJ_0,
                 valid_intJ_1,
                 thisType_1_0,
                 thisType_1_1]
}


pred stack_push_action[
  intJ_1_0: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_stack_push[thisType_1_0]
  and 
  postcondition_stack_push[vac_0,
                          vac_1,
                          size_0,
                          size_1,
                          intJ_1_0,
                          thisType_1_0,
                          thisType_1_1,
                          return_Jint_1_1]
}


pred vector_setsize_action[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_setsize[thisType_1_0,
                      intJ_1_0]
  and 
  postcondition_setsize[intJ_1_0,
                       intJ_1_1,
                       vac_0,
                       vac_1,
                       size_0,
                       size_1,
                       thisType_1_0,
                       thisType_1_1]
}


pred vector_remove_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_bool_1: boolean,
  vac_0: boolean,
  vac_1: boolean
]{
  precondition_Lista_remove_fo2[]
  and 
  postcondition_Lista_remove_fo2[size_0,
                                size_1,
                                intJ_1_0,
                                thisType_1_0,
                                thisType_1_1,
                                return_bool_1,
                                vac_0,
                                vac_1]
}


pred stack_setElement_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_set_element[intJ_1_0,
                                thisType_1_0]
  and 
  postcondition_Lista_set_element[size_0,
                                 size_1,
                                 intJ_1_0,
                                 intJ_2_0,
                                 thisType_1_0,
                                 thisType_1_1,
                                 return_Jint_1_1]
}


pred init_set[
  s_1: set univ
]{
  TruePred[]
  and 
  pos_vaciar[s_1]
}


pred assign_int_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  return_Jint_1_0: JavaPrimitiveIntegerValue,
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  valid_intJ_0: boolean,
  valid_intJ_1: boolean,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_assign_intJ[valid_intJ_0]
  and 
  pos_assign_intJ[vac_0,
                 vac_1,
                 size_0,
                 size_1,
                 intJ_1_0,
                 intJ_1_1,
                 return_Jint_1_0,
                 return_Jint_1_1,
                 valid_intJ_0,
                 valid_intJ_1,
                 thisType_1_0,
                 thisType_1_1]
}


pred vector_peek_action[
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_Jint_1_1: JavaPrimitiveIntegerValue
]{
  precondition_sle3[thisType_1_0]
  and 
  postcondition_sle3[size_0,
                    size_1,
                    thisType_1_0,
                    thisType_1_0,
                    return_Jint_1_1]
}


pred stack_search_action[
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_stack_search[thisType_1_0]
  and 
  postcondition_stack_search[size_0,
                            size_1,
                            thisType_1_0,
                            thisType_1_1,
                            intJ_1_0,
                            return_Jint_1_1]
}


pred gen_intA[
  x_1: Int
]{
  TruePred[]
  and 
  pos_gen_Int[x_1]
}


pred vector_add_action[
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  return_bool_1: boolean
]{
  pre_add[thisType_1_0]
  and 
  pos_add[vac_0,
         vac_1,
         size_0,
         size_1,
         intJ_1_0,
         intJ_1_1,
         thisType_1_0,
         thisType_1_1,
         return_bool_1]
}


pred vector_clear_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  precondition_clear[thisType_1_0]
  and 
  postcondition_clear[vac_0,
                     vac_1,
                     size_0,
                     size_1,
                     thisType_1_0,
                     thisType_1_1]
}


pred stack_addIndexItem_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  intJ_2_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_add2[size_0,
          intJ_1_0,
          thisType_1_0]
  and 
  pos_add2[vac_0,
          vac_1,
          size_0,
          size_1,
          intJ_1_0,
          intJ_1_1,
          intJ_2_0,
          intJ_2_1,
          thisType_1_0,
          thisType_1_1]
}


pred vector_size_action[
  vac_0: boolean,
  vac_1: boolean,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null )
]{
  pre_size[]
  and 
  pos_size[vac_0,
          vac_1,
          size_0,
          size_1,
          return_Jint_1_1,
          thisType_1_0,
          thisType_1_1]
}


pred Lista_get[
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  intJ_1_0: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_get[thisType_1_0,
                        intJ_1_0]
  and 
  postcondition_Lista_get[thisType_1_0,
                         thisType_1_1,
                         intJ_1_0,
                         return_Jint_1_1,
                         size_0,
                         size_1]
}


pred verify_null[
  s_0: JavaPrimitiveIntegerValue,
  b_1: boolean
]{
  TruePred[]
  and 
  pos_add_null[s_0,
              b_1]
}


pred stack_firstElement_action[
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue
]{
  precondition_Lista_get_firstA[thisType_1_0]
  and 
  postcondition_Lista_get_firstA[thisType_1_0,
                                thisType_1_1,
                                return_intJ_1_1,
                                size_0,
                                size_1]
}
one sig QF {
  ac_1: actionExec,
  bool_1_0: boolean,
  bool_1_1: boolean,
  intJ_1_0: JavaPrimitiveIntegerValue,
  intJ_1_1: JavaPrimitiveIntegerValue,
  intJ_1_2: JavaPrimitiveIntegerValue,
  intJ_2_0: JavaPrimitiveIntegerValue,
  intJ_2_1: JavaPrimitiveIntegerValue,
  intJ_2_2: JavaPrimitiveIntegerValue,
  return_Jint_1_0: JavaPrimitiveIntegerValue,
  return_Jint_1_1: JavaPrimitiveIntegerValue,
  return_bool_0: boolean,
  return_bool_1: boolean,
  return_intJ_1_0: JavaPrimitiveIntegerValue,
  return_intJ_1_1: JavaPrimitiveIntegerValue,
  size_0: JavaPrimitiveIntegerValue,
  size_1: JavaPrimitiveIntegerValue,
  thisType_1_0: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  thisType_1_1: JavaPrimitiveIntegerValue -> ( JavaPrimitiveIntegerValue + Null ),
  vac_0: boolean,
  vac_1: boolean,
  valid_bool_1: boolean,
  valid_bool_2: boolean,
  valid_intJ_1: boolean,
  valid_intJ_2: boolean
}


fact {
  precondition_Lista_contains[QF.thisType_1_0]
}

fact {
  QF.valid_bool_1=false
}

fact {
  QF.valid_intJ_1=false
}

fact {
  (
    (
      (
        (
          (
            (
              (
                (
                  (
                    gen_intJ[QF.intJ_1_2]
                    and 
                    vector_remove_action[QF.size_0,
                                        QF.size_1,
                                        QF.intJ_1_2,
                                        QF.thisType_1_0,
                                        QF.thisType_1_1,
                                        QF.return_bool_1,
                                        QF.vac_0,
                                        QF.vac_1]
                    and 
                    (
                      QF.ac_1=vector_remove_action)
                    and 
                    (
                      QF.valid_bool_2=true)
                  )
                  or 
                  (
                    gen_intJ[QF.intJ_1_2]
                    and 
                    vector_removeElement_action[QF.size_0,
                                               QF.size_1,
                                               QF.intJ_1_2,
                                               QF.thisType_1_0,
                                               QF.thisType_1_1,
                                               QF.return_bool_1,
                                               QF.vac_0,
                                               QF.vac_1]
                    and 
                    (
                      QF.ac_1=vector_removeElement_action)
                    and 
                    (
                      QF.valid_bool_2=true)
                  )
                )
                and 
                (
                  QF.valid_intJ_1=QF.valid_intJ_2)
                and 
                (
                  QF.return_Jint_1_0=QF.return_Jint_1_1)
              )
              or 
              (
                gen_intJ[QF.intJ_1_2]
                and 
                vector_removeIndex_action[QF.size_0,
                                         QF.size_1,
                                         QF.intJ_1_2,
                                         QF.thisType_1_0,
                                         QF.thisType_1_1,
                                         QF.return_Jint_1_1,
                                         QF.vac_0,
                                         QF.vac_1]
                and 
                (
                  QF.ac_1=vector_removeIndex_action)
                and 
                verify_null[QF.return_Jint_1_1,
                           QF.valid_intJ_2]
                and 
                (
                  QF.return_bool_0=QF.return_bool_1)
                and 
                (
                  QF.valid_bool_1=QF.valid_bool_2)
              )
              
              or 
              (
                stack_empty_action[QF.return_bool_1,
                                  QF.size_0,
                                  QF.size_1,
                                  QF.thisType_1_0,
                                  QF.thisType_1_1]
                and 
                (
                  QF.ac_1=stack_empty_action)
                and 
                (
                  QF.valid_bool_2=true)
                and 
                (
                  QF.valid_intJ_1=QF.valid_intJ_2)
                and 
                (
                  QF.vac_0=QF.vac_1)
                and 
                (
                  QF.return_Jint_1_0=QF.return_Jint_1_1)
                and 
                (
                  QF.intJ_1_0=QF.intJ_1_2)
              )
              
              or 
              (
                gen_intJ[QF.intJ_1_2]
                and 
                Lista_get[QF.return_Jint_1_1,
                         QF.intJ_1_2,
                         QF.thisType_1_0,
                         QF.thisType_1_1,
                         QF.size_0,
                         QF.size_1]
                and 
                (
                  QF.ac_1=Lista_get)
                and 
                verify_null[QF.return_Jint_1_1,
                           QF.valid_intJ_2]
                and 
                (
                  QF.return_bool_0=QF.return_bool_1)
                and 
                (
                  QF.vac_0=QF.vac_1)
                and 
                (
                  QF.valid_bool_1=QF.valid_bool_2)
              )
            )
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
          )
          or 
          (
            stack_firstElement_action[QF.return_intJ_1_1,
                                     QF.thisType_1_0,
                                     QF.thisType_1_1,
                                     QF.size_0,
                                     QF.size_1]
            and 
            (
              QF.ac_1=stack_firstElement_action)
            and 
            (
              QF.valid_intJ_1=QF.valid_intJ_2)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.vac_0=QF.vac_1)
            and 
            (
              QF.return_Jint_1_0=QF.return_Jint_1_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            vector_removeallelements_action[QF.vac_0,
                                           QF.vac_1,
                                           QF.size_0,
                                           QF.size_1,
                                           QF.thisType_1_0,
                                           QF.thisType_1_1]
            and 
            (
              QF.ac_1=vector_removeallelements_action)
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.valid_intJ_1=QF.valid_intJ_2)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.return_Jint_1_0=QF.return_Jint_1_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            assign_int_action[QF.vac_0,
                             QF.vac_1,
                             QF.size_0,
                             QF.size_1,
                             QF.intJ_1_0,
                             QF.intJ_1_2,
                             QF.return_Jint_1_0,
                             QF.return_Jint_1_1,
                             QF.valid_intJ_1,
                             QF.valid_intJ_2,
                             QF.thisType_1_0,
                             QF.thisType_1_1]
            and 
            (
              QF.ac_1=assign_int_action)
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            stack_pop_action[QF.vac_0,
                            QF.vac_1,
                            QF.size_0,
                            QF.size_1,
                            QF.thisType_1_0,
                            QF.thisType_1_1,
                            QF.return_Jint_1_1]
            and 
            (
              QF.ac_1=stack_pop_action)
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.valid_intJ_1=QF.valid_intJ_2)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            vector_lastElement_action[QF.size_0,
                                     QF.size_1,
                                     QF.thisType_1_0,
                                     QF.return_Jint_1_1]
            and 
            (
              QF.ac_1=vector_lastElement_action)
            and 
            verify_null[QF.return_Jint_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.vac_0=QF.vac_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
            and 
            (
              QF.thisType_1_0=QF.thisType_1_1)
          )
          
          or 
          (
            gen_intJ[QF.intJ_1_2]
            and 
            vector_removeElementAt_action[QF.size_0,
                                         QF.size_1,
                                         QF.intJ_1_2,
                                         QF.thisType_1_0,
                                         QF.thisType_1_1,
                                         QF.vac_0,
                                         QF.vac_1]
            and 
            (
              QF.ac_1=vector_removeElementAt_action)
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.valid_intJ_1=QF.valid_intJ_2)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.return_Jint_1_0=QF.return_Jint_1_1)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            vector_peek_action[QF.size_0,
                              QF.size_1,
                              QF.thisType_1_0,
                              QF.return_Jint_1_1]
            and 
            (
              QF.ac_1=vector_peek_action)
            and 
            verify_null[QF.return_Jint_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.vac_0=QF.vac_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
            and 
            (
              QF.thisType_1_0=QF.thisType_1_1)
          )
          
          or 
          (
            vector_size_action[QF.vac_0,
                              QF.vac_1,
                              QF.size_0,
                              QF.size_1,
                              QF.return_Jint_1_1,
                              QF.thisType_1_0,
                              QF.thisType_1_1]
            and 
            (
              QF.ac_1=vector_size_action)
            and 
            verify_null[QF.return_Jint_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.intJ_1_0=QF.intJ_1_2)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
          
          or 
          (
            gen_intJ[QF.intJ_1_2]
            and 
            stack_push_action[QF.intJ_1_2,
                             QF.vac_0,
                             QF.vac_1,
                             QF.size_0,
                             QF.size_1,
                             QF.thisType_1_0,
                             QF.thisType_1_1,
                             QF.return_Jint_1_1]
            and 
            (
              QF.ac_1=stack_push_action)
            and 
            verify_null[QF.return_Jint_1_1,
                       QF.valid_intJ_2]
            and 
            (
              QF.return_intJ_1_0=QF.return_intJ_1_1)
            and 
            (
              QF.return_bool_0=QF.return_bool_1)
            and 
            (
              QF.valid_bool_1=QF.valid_bool_2)
          )
        )
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
      )
      or 
      (
        gen_intJ[QF.intJ_1_2]
        and 
        gen_intJ[QF.intJ_2_2]
        and 
        stack_set_action[QF.size_0,
                        QF.size_1,
                        QF.intJ_1_2,
                        QF.intJ_2_2,
                        QF.thisType_1_0,
                        QF.thisType_1_1,
                        QF.return_Jint_1_1]
        and 
        (
          QF.ac_1=stack_set_action)
        and 
        verify_null[QF.return_Jint_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.vac_0=QF.vac_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        gen_intJ[QF.intJ_2_1]
        and 
        vector_insertElement_action[QF.vac_0,
                                   QF.vac_1,
                                   QF.size_0,
                                   QF.size_1,
                                   QF.intJ_1_1,
                                   QF.intJ_1_2,
                                   QF.intJ_2_1,
                                   QF.intJ_2_2,
                                   QF.thisType_1_0,
                                   QF.thisType_1_1]
        and 
        (
          QF.ac_1=vector_insertElement_action)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_2]
        and 
        vector_elementAt_action[QF.return_Jint_1_1,
                               QF.intJ_1_2,
                               QF.thisType_1_0,
                               QF.thisType_1_1,
                               QF.size_0,
                               QF.size_1]
        and 
        (
          QF.ac_1=vector_elementAt_action)
        and 
        verify_null[QF.return_Jint_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.vac_0=QF.vac_1)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        vector_clear_action[QF.vac_0,
                           QF.vac_1,
                           QF.size_0,
                           QF.size_1,
                           QF.thisType_1_0,
                           QF.thisType_1_1]
        and 
        (
          QF.ac_1=vector_clear_action)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.intJ_1_0=QF.intJ_1_2)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        gen_intJ[QF.intJ_2_1]
        and 
        stack_addIndexItem_action[QF.vac_0,
                                 QF.vac_1,
                                 QF.size_0,
                                 QF.size_1,
                                 QF.intJ_1_1,
                                 QF.intJ_1_2,
                                 QF.intJ_2_1,
                                 QF.intJ_2_2,
                                 QF.thisType_1_0,
                                 QF.thisType_1_1]
        and 
        (
          QF.ac_1=stack_addIndexItem_action)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        vector_add_action[QF.intJ_1_1,
                         QF.intJ_1_2,
                         QF.vac_0,
                         QF.vac_1,
                         QF.size_0,
                         QF.size_1,
                         QF.thisType_1_0,
                         QF.thisType_1_1,
                         QF.return_bool_1]
        and 
        (
          QF.ac_1=vector_add_action)
        and 
        (
          QF.valid_bool_2=true)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        vector_setsize_action[QF.intJ_1_1,
                             QF.intJ_1_2,
                             QF.vac_0,
                             QF.vac_1,
                             QF.size_0,
                             QF.size_1,
                             QF.thisType_1_0,
                             QF.thisType_1_1]
        and 
        (
          QF.ac_1=vector_setsize_action)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_1]
        and 
        vector_addElement_action[QF.intJ_1_1,
                                QF.intJ_1_2,
                                QF.thisType_1_0,
                                QF.thisType_1_1,
                                QF.size_0,
                                QF.size_1,
                                QF.vac_0,
                                QF.vac_1]
        and 
        (
          QF.ac_1=vector_addElement_action)
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        gen_intJ[QF.intJ_1_2]
        and 
        gen_intJ[QF.intJ_2_2]
        and 
        stack_setElement_action[QF.size_0,
                               QF.size_1,
                               QF.intJ_1_2,
                               QF.intJ_2_2,
                               QF.thisType_1_0,
                               QF.thisType_1_1,
                               QF.return_Jint_1_1]
        and 
        (
          QF.ac_1=stack_setElement_action)
        and 
        verify_null[QF.return_Jint_1_1,
                   QF.valid_intJ_2]
        and 
        (
          QF.return_intJ_1_0=QF.return_intJ_1_1)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.vac_0=QF.vac_1)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
      
      or 
      (
        get_first[QF.return_intJ_1_1,
                 QF.thisType_1_0,
                 QF.thisType_1_1,
                 QF.size_0,
                 QF.size_1]
        and 
        (
          QF.ac_1=get_first)
        and 
        (
          QF.valid_intJ_1=QF.valid_intJ_2)
        and 
        (
          QF.return_bool_0=QF.return_bool_1)
        and 
        (
          QF.vac_0=QF.vac_1)
        and 
        (
          QF.return_Jint_1_0=QF.return_Jint_1_1)
        and 
        (
          QF.intJ_1_0=QF.intJ_1_2)
        and 
        (
          QF.intJ_2_0=QF.intJ_2_2)
        and 
        (
          QF.valid_bool_1=QF.valid_bool_2)
      )
    )
    and 
    (
      QF.bool_1_0=QF.bool_1_1)
  )
  or 
  (
    assign_bool_action[QF.vac_0,
                      QF.vac_1,
                      QF.size_0,
                      QF.size_1,
                      QF.bool_1_0,
                      QF.bool_1_1,
                      QF.return_bool_0,
                      QF.return_bool_1,
                      QF.valid_bool_1,
                      QF.valid_bool_2,
                      QF.thisType_1_0,
                      QF.thisType_1_1]
    and 
    (
      QF.ac_1=assign_bool_action)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_intJ_1=QF.valid_intJ_2)
    and 
    (
      QF.return_Jint_1_0=QF.return_Jint_1_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_2)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_2)
  )
  
  or 
  (
    gen_intJ[QF.intJ_1_2]
    and 
    stack_search_action[QF.return_Jint_1_1,
                       QF.size_0,
                       QF.size_1,
                       QF.intJ_1_2,
                       QF.thisType_1_0,
                       QF.thisType_1_1]
    and 
    (
      QF.ac_1=stack_search_action)
    and 
    verify_null[QF.return_Jint_1_1,
               QF.valid_intJ_2]
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.bool_1_0=QF.bool_1_1)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.vac_0=QF.vac_1)
    and 
    (
      QF.intJ_2_0=QF.intJ_2_2)
  )
  
  or 
  (
    assign_int2_action[QF.vac_0,
                      QF.vac_1,
                      QF.size_0,
                      QF.size_1,
                      QF.intJ_2_0,
                      QF.intJ_2_2,
                      QF.return_Jint_1_0,
                      QF.return_Jint_1_1,
                      QF.valid_intJ_1,
                      QF.valid_intJ_2,
                      QF.thisType_1_0,
                      QF.thisType_1_1]
    and 
    (
      QF.ac_1=assign_int2_action)
    and 
    (
      QF.return_intJ_1_0=QF.return_intJ_1_1)
    and 
    (
      QF.valid_bool_1=QF.valid_bool_2)
    and 
    (
      QF.bool_1_0=QF.bool_1_1)
    and 
    (
      QF.return_bool_0=QF.return_bool_1)
    and 
    (
      QF.intJ_1_0=QF.intJ_1_2)
  )

}

assert programa_wap{
  pred_not[QF.intJ_1_0,
          QF.intJ_1_2,
          QF.vac_0,
          QF.vac_1,
          QF.size_0,
          QF.size_1,
          QF.thisType_1_0,
          QF.thisType_1_1,
          QF.return_bool_1,
          QF.valid_bool_2]
}
/*INI_PRE*/fact{QF.thisType_1_0 in ( i320->i32100)+( i321->i32200) and ( i320->i32100)+( i321->i32200) in QF.thisType_1_0}  one sig i32m1  extends JavaPrimitiveIntegerValue{}  one sig i320  extends JavaPrimitiveIntegerValue{}  one sig i321  extends JavaPrimitiveIntegerValue{}  one sig i322  extends JavaPrimitiveIntegerValue{}  one sig i323  extends JavaPrimitiveIntegerValue{}  one sig i32100  extends JavaPrimitiveIntegerValue{}  one sig i32200  extends JavaPrimitiveIntegerValue{}  fact{ b00 in i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->true  + i322->false  + i323->true  + i32100->false  + i32200->false  in  b00 and  b01 in i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->true  + i323->true  + i32100->false  + i32200->false  in  b01 and  b02 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  in  b02 and  b03 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  in  b03 and  b04 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b04 and  b05 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->false  in  b05 and  b06 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->true  + i32200->true  in  b06 and  b07 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->true  in  b07 and  b08 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b08 and  b09 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in  b09 and b10 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b10 and b11 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b11 and b12 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b12 and b13 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b13 and b14 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b14 and b15 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b15 and b16 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b16 and b17 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b17 and b18 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b18 and b19 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b19 and b20 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b20 and b21 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b21 and b22 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b22 and b23 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b23 and b24 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b24 and b25 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b25 and b26 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b26 and b27 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b27 and b28 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b28 and b29 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b29 and b30 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b30 and b31 in i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  and i32m1->true  + i320->false  + i321->false  + i322->false  + i323->false  + i32100->false  + i32200->false  in b31} fact { QF.intJ_1_0=i320}  check programa_wap for 0 but 9 JavaPrimitiveIntegerValue  fun int32_max[es: set (i320+i321)] : lone (i320+i321) { es - es.(   i321->(i320)  )}fun int32_prevs[e: i320+i321] :set (i320+i321) { e.(   i321->(i320)   )}pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {	let dom = s.JavaPrimitiveIntegerValue |		(no dom and res = i320) or 		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])}/*FIN_PRE*/
