import os.path
import os,sys,glob,ap1,time,incrementalwa,timeoutlib,p
from sets import Set
from datetime import datetime, date, time, timedelta




'''
def gen_input_fact_i32_ot(caso,i,lista,accion,loops,pin,result,archi): #lee el elemento i de la lista i lo reemplaza en resultado.als 

	out=[]
        
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion



			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")

		
				predicado=predicado.split("\n")[0]



		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+pegar+"\/\*FIN_PRE\*\//g ' "+archi)

		result[i]=out
        
	return [pares['size'],result]
'''







def size_ent(i,lista): 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		return int(pares['size'])
	else:
	        return -1	

######################################################################################


def traer_pres_desde_archivo2(archi_texto):
    f = open(archi_texto, "r")
    res=[] 	
    t = f.readlines()
    f.close()
    for el in t:
	    r=ap1.textoEnmedio(el, "<INICIO>", "<FINAL>")
	    a=r.split('?')
	    res.append(a)
    return res	


























def read_action(caso):
 casos_de_studio= os.listdir('../examples')
 if not (caso in casos_de_studio):
    print 'Error: No existe el caso de estudio.'	 
 else:
    parametros_del_prog_dyn= set([])
    #busca la lista de acciones dentro del directorio corespondiente al caso de estudio	
    
    lista_ac = glob.glob('../examples/'+caso+'/actions/*_act')
    
    #dic es un diccionario con toda la info necesaria de cada accion	
    dic={} 

    #one_sig_actions es una lista con todas las acciones que extiende de actionExec{}		
    one_sig_actions=[]

    #para cada accion se extraen sus datos	

    for accion in lista_ac:
	f = open(accion,'r')
	texto = f.read()
	f.close
	i=texto.find('act')+3
	s=texto[i:]
	j=s.find('[')

	#name_action nombre de la accion
	name_action=s[:j].strip()
	one_sig_actions.append("one sig "+name_action+" extends actionExec{}")


	name_action=name_action.strip()
	k=s.find(']')
	p=s[j+1:k]
	parametros=p.split(',')
	invo=name_action+'['

	#pin pout pinout son listas de los parametros de cada accion (entrada, salida y entrada-salida)
	pin=[]
	pout=[]
	pinout=[]
       
       	for e in parametros:
                
		n=e.find('*/')
		es=e[e.find('/*')+2:n].strip()
		t=e[n+2:].split(':')
		name_parametro=t[0].strip()
	         
		name_tipo=t[1].strip()
	        #print pin
		parametros_del_prog_dyn.add(name_parametro.strip()+':'+name_tipo.strip())
		if es=='in':
			pin.append([name_parametro.strip(),name_tipo.strip()])
		if es=='out':
			pout.append([name_parametro.strip(),name_tipo.strip()])
		if es=='inout':
			pinout.append([name_parametro.strip(),name_tipo.strip()])
		invo=invo+name_parametro+','
	
	invo=invo[:len(invo)-1]+']'
        	#parametros de la accion

	#invocacion de la accion, faltan los inicializadores adelante y tener en cuenta si hay sets  y los valids

	#cade_prog es un string donde se construye el call de la accion con sus respectivas inicializaciones 
	cade_prog=''
	

        	
	for e in pin:
		if e[1]=='Int':
			cade_prog=cade_prog+'gen_intA['+e[0]+'] ; '
		if e[1]=='boolean':
			cade_prog=cade_prog+'gen_bool['+e[0]+'] ; '
		if e[1]=='JavaPrimitiveIntegerValue':
                        
			cade_prog=cade_prog+'gen_intJ['+e[0]+'] ; '
	
        
        cade_prog=cade_prog+invo+'; ac:='+name_action
	valid=''
	pa_out=[]
	for e in pout:
		pa_out.append(e[0])
		if e[0]=='return_intA':
			cade_prog=cade_prog+' ; valid_intA:=true'
			valid="valid_intA'"
			if(len(pout)>1):
			    cade_prog='init_set[set_intA];'+cade_prog
			    parametros_del_prog_dyn.add('set_intA:set Int')
		if e[0]=='return_bool':
			cade_prog=cade_prog+' ; valid_bool:=true'
			valid="valid_bool'"
			if(len(pout)>1):
			    cade_prog='init_set[set_bool];'+cade_prog
			    parametros_del_prog_dyn.add('set_bool:set boolean')
		if e[0]=='return_Jint_1':
			cade_prog=cade_prog+' ; verify_null[return_Jint_1,valid_intJ]'  
			valid="valid_intJ'"
			if(len(pout)>1):
			    cade_prog='init_set[set_intJ];'+cade_prog
			    parametros_del_prog_dyn.add('set_intJ:set JavaPrimitiveIntegerValue')
		if e[0]=='return_Jint_2':
			cade_prog=cade_prog+' ; verify_null[return_Jint_2,valid_intJ]'  
			valid="valid_intJ'"
		
			
	cade_prog='('+cade_prog+')'

        
	#cadena de invocacion que va a ir en la *

	s= s[s.find('{')+1:]
	i=s.find('{')
	f=s.find('}')
	precondicion_accion= s[i+1:f].strip()
	s=s[f+1:]
	i=s.find('{')
	f=s.find('}')


	poscondicion_accion= s[i+1:f].strip()
	 

	
	#scope se agrega al final de cada accion con un comentario /*scope:n*/
	scope= s[s.find('/*')+8:s.find('*/')]
	name_postcondicion=poscondicion_accion[:poscondicion_accion.find('[')].strip()
	
	n= texto.find(name_postcondicion)

	#pred_postcondicion_programa es el predicado pos de la accion rota del programa dyn.
	pred_postcondicion_programa= 'pred pred_not'
	params=texto[n+len(name_postcondicion):].strip()
	
	params=params[:params.find(']')].strip()
	#print params
	tipos= params[1:].strip().split(',')
	#print tipos
        #print '-----------------------------' 

	tipos_ac_rota_formales=[]
        #print '-----------------------------'
        #print tipos
        
        for e in tipos:
		tipos_ac_rota_formales.append(" ".join(e.split(':')[1].split()))
	
	#lista con los tipos de los parametros de la pos de la accion rota
	pl=[]
	pl1=[]

	for i in range(0,len(tipos_ac_rota_formales)):
		pl.append('p_'+str(i)+':'+tipos_ac_rota_formales[i])
		pl1.append('p_'+str(i))
	
	pos_not= pred_postcondicion_programa+"["+",".join(pl)
	cuerpo="["+",".join(pl1)+"]"
	cuerpo=name_postcondicion+cuerpo

	#se contempla el caso de que las acciones a reparar, no tengan o tengan 1 solo retorno        
	if len(pout)==0:#si tiene retorno
		pos_not=pos_not+']{ not('+cuerpo+')}'
	if len(pout)==1:#si tiene retorno
		pos_not=pos_not+',b:boolean]{ not('+cuerpo+' and b=true)}'
	
        
	p=poscondicion_accion[poscondicion_accion.find('['):poscondicion_accion.find(']')].strip()

	lista=p.split(',')
	if valid=='':
		invo_pos_not='pred_not'+p+']'
	else:
		invo_pos_not='pred_not'+p+','+valid+']'

        


	#invo_pos_not es la poscondicion actual del programa roto
	dic[accion]=[invo_pos_not,pos_not,name_action,cade_prog,poscondicion_accion,precondicion_accion,pin,scope,pa_out]

            #pametros del programa dynalloy hace un set con todos los parametros que va a tener el programa	
    parametros_del_prog_dyn.add('valid_intA:boolean')
    parametros_del_prog_dyn.add('valid_intJ:boolean')
    parametros_del_prog_dyn.add('valid_bool:boolean')
    parametros_del_prog_dyn.add('ac:actionExec')

    


    dic['parametros_dyn']=parametros_del_prog_dyn
    dic['one_sig_actions']=one_sig_actions

	
    return dic










def traer_pres_desde_archivo(archi_texto):
    f = open(archi_texto, "r")
    res=[] 	
    t = f.read()
    f.close()
    while True:
	    r=ap1.textoEnmedio(t, "<INICIO>", "<FINAL>")	
	    if (r==''):
		break
	    res.append(r) 
	    i=t.find("<FINAL>")	
	    t=t[i+7:]

    return res	



def gen_input_fact_i32(caso,i,lista,accion,loops,pin,result,archi): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	out=[]
	
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				#cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])
				#	cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		#print pares[' lista']
		print 'action to fix: '+accion+"("+cade+")"		 
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion


			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")
				predicado=predicado.split("\n")[0]
			else:
				print 'error: action not found in dictionary. '


		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+pegar+"\/\*FIN_PRE\*\//g ' "+archi)

		result[i]=out
	return [pares['size'],result]

##################################################################################################
def nume(s):
   m=s.split('.')
   if len(m)>1:
        t=m[1]  	
        return m[0]+'.'+t[0:3]
   else:
	return m[0]	
##################################################################################################







#-------------------------------------------------------------------------------------



##################################################################################################################


def size_ent(i,lista): 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		return int(pares['size'])
	else:
	        return -1
#######################







def gene(caso,nume,accion,loops,filename): 
    	cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
	predicado=''
	if (not cadena==''):
	   dic={}
	   cade=cadena.split(':') 
	   for e in cade:
		    elem=e.split(',')
		    dic[elem[0]]=elem[1] 	
                    if not dic.get(accion)==None:
         		 predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_2.als")
			 print predicado
			    #predicado=predicado.split("\n")[0]
			    #os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+predicado+"\/\*FIN_PRE\*\//g ' "+filename)
   			    #sys.exit(0)
        return 0

##############################3


def size_ent(i,lista): 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		return int(pares['size'])
	else:
	        return -1	
###############################################################33




def gener(caso,i,lista,accion,loops,pin,result,filen): #lee el elemento i de la lista i lo reemplaza en resultado.als 
	out=[]
	if (i<len(lista)):
		cade=lista[i]
		data=cade.split('?')
		pares={}
		for e in data:
		   s=e.split(':')
		   pares[s[0]]=s[1]			
		param=''
		t=int(pares['size'])+loops+1
		n=int(pares['cantidad_enteros'])+loops+1				
                check='check programa_wap for 0 but '+str(n)+" JavaPrimitiveIntegerValue " 
		parametros_de_accion_rota=pin
		res=[]
		cade=''
		p=0
		f=0
		for e in pin:
		     if (e[1]=='JavaPrimitiveIntegerValue' and p==0):	
				res.append( "QF."+e[0]+"_0="+pares['pi32_a'])
				#cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_a'])
				p=1
		     else:	
			     if(e[1]=='JavaPrimitiveIntegerValue' and p==1):	
					res.append( "QF."+e[0]+"_0="+pares['pi32_b'])
				#	cade=cade+" "+e[0]+"="+ap1.bin_to_int(pares['pi32_b'])

		     if (e[1]=='Int'and f==0):	
				res.append("eq[QF."+e[0]+"_0,"+pares['indice_a']+"]")
				cade=cade+" "+e[0]+"="+pares['indice_a']
				f=1
		     else:
	  	     	     if (e[1]=='Int'and f==1):	
				res.append("QF."+e[0]+"_0="+pares['indice_b'])
				cade=cade+" "+e[0]+"="+pares['indice_b']



		out.append(pares[' lista'])
		print pares[' lista']
		print 'action to fix: '+accion+"("+cade+")"		 
		out.append('action to fix: '+accion+"("+cade+")")

		parametros_de_acciones="fact { "+(" and ").join(res)+"} "


    	        cadena = ap1.read_config_case("../config.ini","case_"+caso)['actions']
		predicado=''

		if (not cadena==''):
			dic={}
		        cade=cadena.split(':') 
			for e in cade:
			    
			    elem=e.split(',')
			    dic[elem[0]]=elem[1] 	

		
			    # obtiene el scope de la accion almacenada para saber que archivo de aux_pred invocar. tenganse en cuenta que 
			    # por ejemplo para el predicado que indica el size depende de la entrada y de la accion



			if not dic.get(accion)==None:
				predicado= ap1.load_pred_aux("../examples/"+caso+"/models/aux_pred_"+str(int(dic.get(accion))+ int(pares['size']))+".als")

		
				predicado=predicado.split("\n")[0]



		pegar=pares['estado']+" "+parametros_de_acciones+" "+check+" "+predicado

		os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+predicado+"\/\*FIN_PRE\*\//g ' "+filen)

		result[i]=out
	return [pares['size'],result]

######################################################################################

def generate_program_dyn(caso,metodo,acciones):#acciones es una lista con las acciones del wac

	lista_ac = glob.glob('../examples/'+caso+'/actions/*_act')
	
	cade="cat ../examples/"+caso+"/actions/preludio "+" ".join(lista_ac)+" > permanent.dals"
	os.system(cade)
                

       	if not "../examples/"+caso+"/actions/"+metodo+"_act" in lista_ac:
			print 'Error : not found action '+metodo
	else:

			info=read_action(caso)
                        
			parametros_de_retorno=info['../examples/'+caso+'/actions/'+metodo+'_act'][8]
			pp="["+",".join(list(info['parametros_dyn']))+"]"
	
			acts=info.keys()
			pin=info['../examples/'+caso+'/actions/'+metodo+'_act'][6]
			scope =info['../examples/'+caso+'/actions/'+metodo+'_act'][7]
		
			acts.remove('parametros_dyn')

			one_sig_actions= "\n".join(info['one_sig_actions'])
			acts.remove('one_sig_actions')
		        
			if("../examples/"+caso+"/actions/"+metodo+"_act" in acts):
     			    	p=info["../examples/"+caso+"/actions/"+metodo+"_act"]
			        
	    			precondicion_accion_rota=p[5]	
	    			poscondicion_negada=p[4]
				

     	    		        del acts[acts.index("../examples/"+caso+"/actions/"+metodo+"_act")]
				lis=[]	

				#add_to_set[s:set univ,n:univ]
				
				for elem in acts:
					
					cade_add_set=''
					v=info[elem][3]
					if len(parametros_de_retorno)>1:
						v= v[:len(v)-1]
						#si la la cant de parametros de retorno es > 1 retornos enteros 32 
						if ("return_intJ_1" in info[elem][8] or "return_intJ_1'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_1]'
						
						if ("return_intJ_2" in info[elem][8] or "return_intJ_2'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_2]'
						
						if ("return_intJ_3" in info[elem][8] or "return_intJ_3'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_3]'

						if ("return_intJ_4" in info[elem][8] or "return_intJ_4'" in info[elem][8]):
							cade_add_set=cade_add_set +';add_to_set[set_intJ,return_intJ_4]'


	
						v=v+cade_add_set+')'

					
						
		 				

			        	lis.append(v)

				#r=";".join(lis)
				
				
                                r=gene_dyn_aux(lis,acciones) 
				prog=''
				if len(parametros_de_retorno)>1:

					if ('return_intJ_1' in parametros_de_retorno) or ('return_intJ_2' in parametros_de_retorno):
						prog=prog+'init_set[set_intJ];'
						
					
				prog=prog+'valid_intA:=false;valid_bool:=false;valid_intJ:=false;('+ r +')'		
	    			cuerpo='pre={'+precondicion_accion_rota+'}\nprogram={'+prog+'}\n post={'+poscondicion_negada+'}\n'
			        asercion=one_sig_actions+'\nassertCorrectness programa_wap'+pp+'{'+cuerpo+'}\n'+p[1]+'\n'+'check programa_wap\n'

			else:
				 print 'Error: action '+metodo+' not available.'	
         			 asercion=''

			if len(asercion)==0:
				print 'Error: action.'
			else:
				f = open('permanent.dals', "a")
                                    				
				f.write(asercion)
				f.close()
			#sys.exit(0)
##############################################3

def buscar_ac(ac,lis):
  res=''


  for e in lis:
	if e.find('ac:='+ac)>=0:
		res=e
		break;

  return res;



def gene_dyn_aux(lis,acciones):
  res=''	
  for ac in acciones:
	res=res+buscar_ac(ac,lis)+';'
  res=res[:-1]
  return res



#----------------------------------------------------------------------






def fix_1(caso,accion,pin,tiempo_to,input_file,flagp):

   
   #si flagp es True, luego de generar la lista de wac comenzara a verificar si encuentra alguno que sea permanente
   # en caso contrario lo que hara es continuar generando la lista de wac candidatos con sus respectivos loop unrolls
   result={} 	
   
   entradas=traer_pres_desde_archivo('../examples/'+caso+'/'+input_file)	

   tiempo_total_busqueda_wac=0
   tiempo_total_busqueda_wap=0
   cantidad_estados=0
   cantidad_time_out_wac=0
   cantidad_time_out_wap=0

   cont=0
   size_wac_max=10
   sum_long_wa=0	
   cont_wa=0
   tiempo_total=0
   entradas_procesadas=0	
   prom_tam_listas=0
   suma_tam_listas=0
   ttotal=0
   ttotal_sin_to=0	
   emin=10000
   temin=0
   emax=0 	
   temax=0
   to=0
   ap1.log_file('action_name?'+accion,'logfile_wap.log')   
   for i in range(0, len(entradas)):
	
	print '<control '+str(i)+'>'
        primer_wac=False
        scope='7'
        if primer_wac:
		break   
	print 'searching candidate workarounds...\n'
        ap1.log_file('state='+str(i),'logfile.log')




	tiempo_inicio_wa=datetime.now()



        cambio_i=False
        tama=size_ent(i,entradas)   

	for unroll in range(1,size_wac_max+1):

     	            ap1.run_modelo_dynalloy('temporalnew.dals','resultado.als',str(unroll))
		    #sys.exit(0)

		    t2=datetime.now()-tiempo_inicio_wa	
		    ap1.rempla('resultado.als','check programa_wap',' ') 
		    os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> resultado.als')
		    linea='size: '+str(tama)
  	            rr="echo '"+linea+"' >> ../examples/"+caso+"/results/alt1/alt1_output"
		    os.system(rr)
		                        
		    res=gen_input_fact_i32(caso,i,entradas,accion,unroll,pin,result,'resultado.als')


		    size_lista=res[0]
		    



		    p=result[i]	
		    p.append('size: '+str(tama))
		    result=res[1]
		    if not cambio_i:   
		    	    suma_tam_listas= int(size_lista)+suma_tam_listas
			    cambio_i=True 	


		    #busca todos los wa candidatos para el unroll indicado
		    aa=datetime.now()



                    #ap1.log_file('Start time finding wac:'+ str(aa) +' % unroll:'+str(unroll),'logfile.log')

		    #sys.exit(0)  
		    #ap1.log_file('action:'+str(accion)+' % state:'+str(i)+' % '+'unroll:'+str(unroll),'logfile.log')
		    time_of= timeoutlib.call_with_timeout(incrementalwa.run_incremental_alloy, 'resultado.als',100,unroll,i,accion,'wac_'+accion+'_with_'+str(unroll)+'.list')
		    #candidato="candidato_"+accion+"_"+str(unroll)+".als"
		    #os.system("cp resultado.als "+candidato)
		    #sys.exit(0)
		    bb=datetime.now()
                    #ap1.log_file('Finish time:'+str(bb)+' finding wac for unroll:'+str(unroll),'logfile.log')

		    ap1.log_file('Finish time finding wac %'+str(accion)+' % '+'unroll='+str(unroll)+' % TO='+str(time_of[1])+' % total_time='+ap1.tiempo_transcurrido(aa,bb),'logfile.log')

	            if time_of[1]:
			break # si ya se dio un timeour en el unroll corriente, no tiene sentido buscar en los de mayor unroll

		    #ap1.log_file('timeout:'+str(time_of[1]),'logfile.log')
		    
	            

		    iii=0
		    

   		    
		    if flagp: 
	                

			print 'wac_'+accion+'_with_'+str(unroll)+'.list\n'
			#sys.exit(0)

			wac_list = traer_pres_desde_archivo2('wac_'+accion+'_with_'+str(unroll)+'.list') 


	                numero=0
		        print 'Cantidad de wac a verificar: ',len(wac_list)
                        ap1.log_file('#wac-wap:'+str(len(wac_list)) +' unroll:'+str(unroll),'logfile_wap.log')
			for e in  wac_list:
			     	
			     acciones=e[1].split(',')
			     #sys.exit(0)
			     generate_program_dyn(caso,accion,acciones)
			     print 'wac :',acciones
#		             ap1.log_file('Verificando : '+str(acciones),'logfile_wap.log')



			     
			     ap1.run_modelo_dynalloy('permanent.dals','tempo_wacp.als','1')
			     
			     update_tempo_wacp('tempo_wacp.als',e[2])
			     	
		             os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> tempo_wacp.als')
	

		             os.system('echo "'+e[2]+'" >> tempo_wacp.als')

			     ap1.rempla('tempo_wacp.als','check programa_wap',' ')
		             res=gen_input_fact_i32(caso,i,entradas,accion,unroll,pin,result,'tempo_wacp.als')
			     
			     #sys.exit(0)

			     ap1.borrar_pre('tempo_wacp.als')


			     
			     	
			 
			     print 'Verificando si ' + str(acciones) +' '+e[2]+' es un wap'
			     archi= 'temporal_a_'+str(iii)+'.als'
			     os.system('cp  tempo_wacp.als '+archi)




			     ap1.log_file(('Verificando si ' + str(acciones) +' es un wap'),'logfile_wap.log')
			     time_of=timeoutlib.call_with_timeout_permament(incrementalwa.run_alloy2,archi)
		             ap1.log_file('timeout_sal:'+str(time_of[1]),'logfile_wap.log')
			     iii=iii+1
			     
			
		             
		             os.system('rm  tempo_wacp.als')
		    
   ap1.log_file('StateFin','logfile.log')

#-------------------------------------------------------------------------------------



def verificar_wap(caso,accion,k,n): # k son los enteros fijos, una constante y los otros son los que se van a mult. por la cant de unrolls.

   
   size_wac_max=5
   ap1.log_file('Checking permanent workaround for: '+accion,'logfile_wap.log')
   tiempo_inicio_wa=datetime.now()
   for unroll in range(1,size_wac_max):
			print 'wac_'+accion+'_with_'+str(unroll)+'.list\n'
			wac_list = traer_pres_desde_archivo2('wac_'+accion+'_with_'+str(unroll)+'.list') 
	                numero=0
		        print 'Cantidad de wac a verificar: ',len(wac_list)
                        #ap1.log_file('#wac-wap:'+str(len(wac_list)) +' % state:'+str(i)+' % '+'unroll:'+str(unroll),'logfile.log')
		        iii=1
			for e in  wac_list:
			     acciones=e[1].split(',')
			     generate_program_dyn(caso,accion,acciones)
			     print 'wac :',acciones
			     ap1.run_modelo_dynalloy('permanent.dals','tempo_wacp.als','1')
			     update_tempo_wacp('tempo_wacp.als',e[2])
		             os.system('echo "/*INI_PRE*/  /*FIN_PRE*/" >> tempo_wacp.als')
		             os.system('echo "'+e[2]+'" >> tempo_wacp.als')
			     ap1.borrar_pre('tempo_wacp.als')
			     ap1.rempla('tempo_wacp.als','check programa_wap',' ')
			     check='check programa_wap for 0 but '+str(k+n*len(wac_list))+" JavaPrimitiveIntegerValue " 
			     check = check + p.int_to_int32([-1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])

			     os.system(" sed -i 's/\/\*INI_PRE.*FIN_PRE\*\//\/\*INI_PRE\*\/"+check+"\/\*FIN_PRE\*\//g ' tempo_wacp.als")
			     sys.exit(0)
			     print 'Verificando si ' + str(acciones) +' '+e[2]+' es un wap'
			     archi= 'model_'+action+'_'+'unroll'+str(unroll)+'_'+str(iii)+'.als'
			     os.system('cp  tempo_wacp.als '+archi)
			     ap1.log_file('checking wac: '+str(acciones),'logfile_wap.log')
			     time_of=timeoutlib.call_with_timeout_permament(incrementalwa.run_alloy2,archi)
		             ap1.log_file('timeout_sal:'+str(time_of[1]),'logfile.log')
			     iii=iii+1
		             os.system('rm  tempo_wacp.als')
	                
#-------------------------------------------------------------------------------------


def update_tempo_wacp(filename,s):
    f = open(filename, "r")
    texto = f.read()
    f.close()
    z=-1

    for k in range(0,30):
	if s.find('QF.intJ_1_'+str(k))>=0:
				z=k;
    cab='one sig QF { '
    i=texto.find('one sig QF {')
    if i>=0:
    	pre=texto[:i]
    	pos= texto[i+14:]
   	j=pos.find('}')
	qf=pos[:j+1]
	while z>=0:
	  if qf.find('intJ_2_'+str(z))<0:
	        cab= cab + 'intJ_2_'+str(z)+': JavaPrimitiveIntegerValue,\n'
	  if qf.find('intJ_1_'+str(z))<0:
	        cab= cab + 'intJ_1_'+str(z)+': JavaPrimitiveIntegerValue,\n'
       	  z=z-1	   
        qf=cab+qf
	res=pre+qf+pos[j+1:]
        f = open(filename,"w")
                                    				
	f.write(res)
	f.close()	




#########################################################################











