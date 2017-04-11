import datetime,os,sys,re, pp_n,time,ConfigParser
from xml.dom import minidom
#from datetime import datetime, date, time, timedelta
import calendar
import os.path,time
from datetime import timedelta,date,time

#-----------------------------------------------------------------------------------------------   
# funcion read_config_case: retorna un diccionario con los valores del archivo config.ini 
#------------------------------------------------------------------------------------------------   
def read_config_case(configfile,section):
    config = ConfigParser.ConfigParser()
    config.read(configfile)
    dict1 = {}
    options = config.options(section)
    for option in options:
        try:
            dict1[option] = config.get(section, option)
            if dict1[option] == -1:
                DebugPrint("skip: %s" % option)
        except:
            print("exception on %s!" % option)
            dict1[option] = None
    return dict1


#--------------------------------------------------------
def time_time(tiempo): #el tiempo viene en forma <nume><s|m>
	res=0
        n=tiempo.split('m')
        if len(n)>1:
		res =int(n[0])*60
        n=tiempo.split('s')
        if len(n)>1:
		res=int(n[0])
        return res 


#--------------------------------------------------------
def textoEnmedio(sCadena, sDelimitador1, sDelimitador2):
      	p=sCadena.find(sDelimitador1)
      	pos2=sCadena.find(sDelimitador2)
	result=''
	if (p!=-1 and pos2!=-1):
      	     result = sCadena[p+(len(sDelimitador1)):pos2]
	return result	

	


def load_pred_aux(archivo):
    f = open(archivo)
    l = f.read()
    return l	


#-----------------------------------------------------------------------------------------------   
# funcion UNSAT: retorna 1 si en f se encuentra el string  'UNSAT'
#		 retorna 0 si en f se encuentra el string  'SAT'
#		 retorna 2 si en f no se encuentra 'SAT' ni 'UNSAT' lo implica que hay Timeout
#------------------------------------------------------------------------------------------------   


def UNSAT(f):
    f = open(f)
    l = f.read()
    if (l.find('UNSAT')>0):
		return 1
    if (l.find('SAT')>0):
		return 0
    if (l.find('Analysis finished')<0):
		return 2


    return

#-----------------------------------------------------------------------------------------   

def cal_sattime(f):
    f = open(f)
    l = f.read()
    f.close()
    ini=l.find('Solving time')+25
    fin=0	
    if ini>0:
	l=l[ini:]
	fin=l.find('\n')
    nc=l[:fin]		
    return nc.strip()



#-----------------------------------------------------------------------------------------   

def save(file_o, file_d):
	ma=open(file_o,"r")
	lineas = ma.readlines()
	ma.close()
	p=open(file_d,'w')
	for linea in lineas:
		p.write(linea)	
	p.close()



                 
	


def generar_cade_para_modelo_als(wac):
	n=1
	cade=''
	for i in wac:
		if n==len(wac):
			cade= cade + 'ac_'+str(n)+'='+i
		else:
			cade= cade + 'ac_'+str(n)+'='+i+' and '
		n=n+1
	cade='not ('+cade+')'
	return cade




def run_modelo_dynalloy(modyn,output,lu):
	os.system('java -jar ../lib/dynalloy4.jar --input ' +modyn+' --output '+output+' --unroll '+lu+' --assertion programa_wap --strictUnroll true  --removeQuantifiers true > sal')
#	os.system('java -jar ../lib/dynalloy4.jar --input ' +modyn+' --output '+output+' --unroll '+lu+' --assertion programa_wap --strictUnroll true   > sal')
        os.system('rm sal')
#########################################################################################################






def run_modelo_alloy_pewa(modalloy,i,unroll,accion,caso,j,to):
    	os.system("timeout "+ to +" java -Xmx8g -Djava.library.path=../lib/amd64-linux/ -jar ../lib/alloycli-1.6.0b3.jar  -s minisat -x uva "+modalloy+" > temp")








	if j==1:
    	   os.system("cp temp ../examples/"+caso+"/results/alt1/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
	if j==2:
    	   os.system("cp temp ../examples/"+caso+"/results/alt2/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
























#########################################################################################################
def run_modelo_alloy(modalloy,i,unroll,accion,caso,j,to):
    	os.system("timeout "+ to +" java -Xmx8g -Djava.library.path=../lib/amd64-linux/ -jar ../lib/alloycli-1.6.0b3.jar  -s minisat -x uva "+modalloy+" > temp")
	if j==1:
    	   os.system("cp temp ../examples/"+caso+"/results/alt1/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))
	if j==2:
    	   os.system("cp temp ../examples/"+caso+"/results/alt2/output_alloy_"+accion+'_control'+str(i)+'_unroll'+str(unroll))

##########################################################################################################


def extraccion__wac(solucion,qf):
  wac=[]
  # se extrae la traza correspondiente al contraejemplo.
  xmldoc = minidom.parse(solucion)
 
  if (not qf):
        lis = xmldoc.getElementsByTagName('skolem')
	for e in lis: 
		if "label" in e.attributes.keys():


                        v = e.attributes["label"].value.strip()	


			if v=="$programa_wap_ac_0" or v=="$programa_wap_ac_1" or v=="$programa_wap_ac_2" or v=="$programa_wap_ac_3" or v=="$programa_wap_ac_4"or  v=="$programa_wap_ac_5" or v=="$programa_wap_ac_6" or v=="$programa_wap_ac_7" or v=="$programa_wap_ac_8" or v=="$programa_wap_ac_9":
				data = e.toxml().split()
                                t = e.getElementsByTagName('atom')[0].toxml()
				accion = pp_n.extraer_bloque(t,'\"','$')
				wac.append(str(accion))
				data = e.toxml().split()

				
				for el in e.getElementsByTagName('atom'):
                                      # t = e.getElementsByTagName('atom')[0].toxml()
                                         
	    		   	       print el.toxml()

				#accion = pp_n.extraer_bloque(t,'\"','$')
				#wac.append(str(accion))
  else:
        
        lis = xmldoc.getElementsByTagName('field')
        for e in lis: 

		if "label" in e.attributes.keys():
                      v = e.attributes["label"].value.strip()	
		      if v=="ac_1" or v=="ac_2" or v=="ac_3" or v=="ac_4" or v=="ac_5" or v=="ac_6" or v=="ac_7" or v=="ac_8" or v=="ac_9" or v=="ac_10":

   			    for el in e.getElementsByTagName('atom'):
                                      # t = e.getElementsByTagName('atom')[0].toxml()#
				   if (el.toxml().find('QF')<0):
					     c=	el.toxml()
	    		   	             ini= c.find('=')+2
	    		   	             fini= c.find('$')
					     c=c[ini:fini].encode('ascii','ignore')
					     wac.append((v+'='+c).encode('ascii','ignore'))

  return wac

def show__wac(wac):
	res=''
	for e in wac:
		res= res +' '+ e  
	res = res + '\n'

	return res	



		     

def expor(nombre,i):
	 
	    f = open('resultado.alsuva', "r")
	    txt=f.read()
	    f.close
	 
    	    f2 = open(nombre+'_'+str(i), "w")
	
            f2.write(txt)	
            f2.close


def rempla(file_name, string_find, string_remplace): 
    f = open(file_name, "r")
    lineas = f.readlines()
    f.close()	
    ma=open(file_name,"w")
    for l in lineas:
	l = l.replace(string_find,string_remplace) 
	ma.write(l)
    ma.close()	
#########################################################################################################

def reg(archi,linea,i):
	if i==0:
    	   os.system('echo "'+linea+'" > '+archi)
	else:
	   os.system('echo "'+linea+'" >> '+archi)
#######################################################################################################

def borrar_pre(file_name):
    f = open(file_name, "r")
    lineas = f.readlines()
    f.close()	
    ma=open(file_name,"w")
    for l in lineas:
	prim=''
	rest=''
	i=l.find("fact{QF.thisType_")
	if i>=0:
	     prim =l[:i]			
	     rest=l[i:]
	     j=rest.find('}')
	     rest=rest[j+1:]
	     l = prim+rest



	j=l.find("pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue}")
	if j>=0:
	     prim =l[:j]			
	     rest=l[j+161:]
	     l = prim+rest

	i=l.find("fun int32_max[")
	if i>=0:
	     prim =l[:i]			
	     rest=l[i:]
	     j=rest.find('}')
	     rest=rest[j+1:]
	     l = prim+rest
	i=l.find("fun int32_prevs[")
	if i>=0:
	     prim =l[:i]			
	     rest=l[i:]
	     j=rest.find('}')
	     rest=rest[j+1:]
	     l = prim+rest
	i=l.find("pred myseq_card")
	if i>=0:
	     prim =l[:i]			
	     rest=l[i:]
	     j=rest.find('}')
	     rest=rest[j+1:]
	     l = prim+rest
	ma.write(l)
    lin="pred  max_32[s: set JavaPrimitiveIntegerValue, max:JavaPrimitiveIntegerValue]{ max in s and ( all e:s-max | pred_java_primitive_integer_value_gt[max,e] ) } pred myseq_card[s: JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null), res: JavaPrimitiveIntegerValue] { let dom = s.(JavaPrimitiveIntegerValue+Null) | (no dom and res = i320) or ( pred_java_primitive_integer_value_add[int32_max[dom],i321,res,false])} fun int32_max[es: set JavaPrimitiveIntegerValue] : lone JavaPrimitiveIntegerValue { { result :JavaPrimitiveIntegerValue |  max_32[es,result]}} pred sequence[s: JavaPrimitiveIntegerValue->(JavaPrimitiveIntegerValue+Null)] {comp[s.(JavaPrimitiveIntegerValue+Null)] and (all a,b,c:(JavaPrimitiveIntegerValue+Null)| ((a->b) in s and (a->c)in s) implies pred_java_primitive_integer_value_eq[b,c]) } pred comp[s : set JavaPrimitiveIntegerValue]{all i:s | pred_java_primitive_integer_value_gte[i,i320] and (pred_java_primitive_integer_value_gt[i,i320] implies (some g:JavaPrimitiveIntegerValue | g=fun_java_primitive_integer_value_sub[i,i321] and (g in s)))}"
    ma.write(lin)
    ma.close()


#########################################################################################################
def mostrar_programa(metodo_roto,wac,archi,perfiles):
	
#perfiles es un diccionario perfiles[accion]=['']

# para cada accion guardada en wac, buscar los parametros que tiene en perfiles[accion], luego para cada uno de estos parametros buscar su vaor en archi. hay que tener en cuenta que la accion que esa en la posicion 0 va a tener que buscar los parametros den archi con parametro_1. 
# puede servir una funcion auxiliar de busqueda(parametro) return valor. ej
# nota: buscar el parametro y luego el segundo valor del atom

#<field label="element_1" ID="72" parentID="54">
#   <tuple> <atom label="QF$0"/> <atom label="-1"/> </tuple>
#   <types> <type ID="54"/> <type ID="1"/> </types>
#</field>

 perfil= perfiles[metodo_roto]     
 k=len(perfil)
 cade=''
 for p in range(1,k):	
    pc=perfil[p]+'_0'

    cade=cade+ buscar_valor('resultado.alsuva',pc)+','



 cade=cade[:-1]
 parametros_actuales=metodo_roto+'('+cade+')'
 print 'Metodo roto:'
 print parametros_actuales 
 parametros_actuales='' 
 print 'Workaround candidato'
 for ac in wac:
   c=ac.find('=')
   ac=ac[c+1:]	
   nac=1	
   perfil= perfiles[ac]     
   
   k=len(perfil)
   for p in range(1,k):	
	pc=perfil[p]+'_'+str(nac)
	parametros_actuales=parametros_actuales+ buscar_valor('resultado.alsuva',pc)+','
   print ac+'('+parametros_actuales[:len(parametros_actuales)-1]+')'	



#f=listar_metodos_tipos('../input/examples/src/Lista.java')
#print f


def buscar_valor(solucion,valor):
  xmldoc = minidom.parse(solucion)
  s=''	
  for n in xmldoc.getElementsByTagName("field"):
    #print n.attributes["label"].value

	if (n.attributes["label"].value==valor):
	     s=n.childNodes[1].toxml()
	     n=s.find('/>')	
	     if (n>0):
			s=s[n:]
	   	        n=s.find('=')	
			s=s[n+2:]
			n=s.find('"')
			s=s[:n]
			break
  return s




#perfil retorna un diccionario con ek nombre del metodo como clave y el valor asociado es una lista con el retorno y los parametros
def perfil_ok(archi):
	    d={} 	
	    f = open(archi, "r")
	    t=f.read()
    	    f.close()
	    i=0	
	    	
	    while True:
		i=t.find('retorno=')
		if i!=-1:
		       t=t[i+8:]
		       j=t.find('*')  		
		       ret=t[:j]
		       lista=[ret]	
		       met=pp_n.textoEnmedio(t,'/','(')	 
		       met=met.strip()
   		       parametros=pp_n.textoEnmedio(t,'(',')')	 
		       id_parametros= parametros.split(',')


		       for m in id_parametros:
				m=m.strip()
				m = m.split(' ')
				if (len(m)>1):
				    lista.append(m[0].strip())
				    lista.append(m[1].strip())
		       d[met]=lista
		   		   
		else:
		   break
            return d



def tc(perfiles,tipos_simples):
   	
  elementos = perfiles.keys()
  res=[]
  for met in elementos:
       e=perfiles[met]	
       if not (e[0] in tipos_simples): 
		res.append(e[0])		
#       del e[:1]        		
       if len(e)==1:
		continue	
       if (len(e)>1): 
	     for i in xrange(1,len(e),2):
  	         if not (e[i] in tipos_simples):
 		      res.append(e[i])
	
  
  return list(set(res))


def tipos_compuestos(lista_tipos_compuestos):
  res=''	
  for e in lista_tipos_compuestos:
       res=res+'set_'+e+': set '+e+', '
  return res

	    


def bin_to_int(s):
	s=s[s.find('fact'):]
	l=s.split('and')
	res=''
	for e in l:
		d=e.split('=')	
		d[1]=d[1].strip()
		if(d[1]=='true'):
			res='1'+res
		else:
			res='0'+res

	return str(int(str(res),2))

def bin_to_int_old(s):
	s=s[s.find('fact'):]
	l=s.split('and')
	res=''
	for e in l:
		d=e.split('>')	
		d[1]=d[1].strip()
		if(d[1]=='true'):
			res='1'+res
		else:
			res='0'+res

	return str(int(str(res),2))

#-----------------------------------------------------------------






def conv_time(num):
	hor=(int(num/3600))  
	minu=int((num-(hor*3600))/60)  
	seg=num-((hor*3600)+(minu*60))
	return str(hor)+" h "+str(minu)+" m "+str(seg)+" s"



def dec_to_int3(x,v):
  k=0
  i=1
  s=0
  dec=x
  l=[]
  while dec>0:
      if k<0:	
	  temp=v+'.b0'+str(k)+'='
      else:
	 temp=v+'.b'+str(k)+'='
      rem=dec%2
      if rem==0:
	    temp=temp+'false'
      else:
	    temp=temp+'true'
      l.append(temp)
     
      
      s=s+(i*rem)
      dec=dec/2
      i=i*10
      k=k+1
  for i in range(k,32):
      if k<0:	
	  temp=v+'.b0'+str(k)+'='
      else:
	 temp=v+'.b'+str(k)+'='
      temp=temp+'false'
      l.append(temp)
      k=k+1
  return 'fact{\n'+'\n'.join(l)+'\n}\n'




def isto(d):
	os.system("echo $? >> kkk")
	return

isto(4)

#------------------------------
def log_file(msg,file_name):

        t=datetime.now()
		
	msg='Time:'+str(t)+' % '+msg
        
	if os.path.isfile(file_name):
		   
  	            rr="echo '"+msg+"' >> "+file_name
		    os.system(rr)
	else:
 		    rr="echo '"+msg+"' > "+file_name
		    os.system(rr)

        return




#----------------------------------
def tiempo_transcurrido(a,b):
	return str(b-a)


#-------------------------------
def hora_to_millis(hora):
    lista = hora.split(":")
    hora=int(lista[0])
    minuto=int(lista[1])
    segundo=int(lista[2].split('.')[0])
    milisegundo=lista[2].split('.')[1]
    milisegundo=float('0.'+milisegundo)/0.0010
    return milisegundo + segundo * 1000 + minuto* 60000+ hora*3600000

def millis_to_seconds(m):
    return float(m)/1000		




#----------------------------------
def sumar_hora(hora1,hora2):
    h1=datetime.datetime.strptime(hora1, "%H:%M:%S.%f" )
    lista = hora2.split(":")
    hora=int(lista[0])
    minuto=int(lista[1])
    segundo=int(lista[2].split('.')[0])
    milisegundo=lista[2].split('.')[1]
    milisegundo=float('0.'+milisegundo)/0.0010
    dh = timedelta(hours=hora) 
    dm = timedelta(minutes=minuto)          
    ds = timedelta(seconds=segundo) 
    dml= timedelta(milliseconds=milisegundo)
    

    resultado0 =h1 + dml
    resultado1 =resultado0 + ds
    resultado2 = resultado1 + dm
    resultado = resultado2 + dh
    resultado=resultado.strftime("%H:%M:%S.%f")
    return str(resultado)

def max_to(a,b):
	if a>b:
	   return a
	else:
	   return b  

#-------------------------------------------------
def procesar_logfile():
 	os.system("grep 'action==\|state=\|wac_nro=\|TO=' logfile.log > sali")

	f=open("sali","r")
	t = f.read()
	f.close()
	res=t.split("==")
	name_action= res[1]
        resto=res[2].split("\n")
        states=0
	cant_wacs=0
	promedio_wac_1=0
        pp=datetime.datetime.strptime('0:00:00.0', '%H:%M:%S.%f')
	suma_sattime_w1=pp.strftime("%H:%M:%S.%f")

        suma_sattime_w=pp.strftime("%H:%M:%S.%f")
        cant_to=0
        max_unroll=0
	promedio_wacs_encontrados=0
	flag_wac_1=False
	cant_wac1=0
 	for l in resto:
	        if l.find("state=")>0:	
			   states=states+1
			   flag_wac_1=False
	                   flag_wac=False 

	        if l.find("wac_nro=1")>0 and not flag_wac_1:
			   s=l.split('%')
			   n=int(s[1].strip().split("=")[1])
			   sattime=s[2].strip().split("=")[1].strip()
                           cant_wac1=cant_wac1+1
                           suma_sattime_w1=sumar_hora(sattime,suma_sattime_w1)  
			   
			   flag_wac_1=True
	
 		if l.find("wac_nro=")>0:
			   s=l.split('%')
			   n=int(s[1].strip().split("=")[1])
			   sattime=s[2].strip().split("=")[1].strip()

                           suma_sattime_w=sumar_hora(sattime,suma_sattime_w)  

			   cant_wacs=cant_wacs+1

 		if l.find("TO=True")>0:
			   cant_to=cant_to+1
			   s=l.split('%')[3].split('=')[1]
			   max_unroll=max_to(s,max_unroll)	
			   
 		if l.find("TO=False")>0:
			   max_unroll=max_to(s,max_unroll)
			   s=l.split('%')[3].split('=')[1]
			   max_unroll=s
	#cantidad de estados a reparar
        cantidad_de_estados=states 
	
	#maximo unrol alcanzado
	maximo_unroll_alcanzado= int(max_unroll) 

	# en el tiempo especificado en config.file
        cantidad_total_de_wac_encontrados=cant_wacs

	

	#tiempo total de sattime utilizado 
        tiempo_total_sat= suma_sattime_w

	#tiempo total de sat insumido para encontrar el wac 1 
        tiempo_total_sat_wac1 = suma_sattime_w1

	#promedio del sattime insumido para los primeros wacs. se promedian con la cantidad de los wacs1 encontrados
	if cant_wac1>0:
		tiempo_promedio_sattime_w1=str(millis_to_seconds(float(hora_to_millis(suma_sattime_w1))/cant_wac1))
	else:
		tiempo_promedio_sattime_w1='-1'


	#prmomedio del sattime general
        cantidad_total_to=cant_to
        
	if cantidad_total_de_wac_encontrados >0:
		tiempo_promedio_sattime_w=str(millis_to_seconds(float(hora_to_millis(suma_sattime_w))/cant_wacs))
	else:
		tiempo_promedio_sattime_w1='-1'
	print 'Action='+name_action +' | States='+str(cantidad_de_estados)+' | '+'Total Sat Time='+tiempo_total_sat+' | Avg.Time WAC='+tiempo_promedio_sattime_w +' seconds | #WAC found in TIME='+str(cantidad_total_de_wac_encontrados) + ' | AVG. Time First='+ str(tiempo_promedio_sattime_w1)+' seconds | #TO='+str(cantidad_total_to)+' | MaxUnroll='+max_unroll




#print millis_to_seconds(m)



#procesar_logfile()
#print sumar_hora("00:00:00.012420","0:00:00.011829")

	

#---------------------------------------------------
















'''


cut -d "=" -f 2  b > c

'''


def ff(ur,n,st,res,time,cwpu):
	 if ur==n:
	    st=st+time
	    if res=='WAP':
		cwpu=cwpu+1 
         return st,cwpu







def procesar_logfile_permanente():
        os.system('grep "wac-wap\|action_name\|sat_time\|timeout_sal" logfile_wap.log > a ;cut -d "%" -f 2  a  > b ; sed -e "s/timeout_sal://g" b > c; sed -e "s/sat_time=//g" c > d')
	f=open("d","r")
	lines = f.readlines()
	f.close()
	#CANT WAP Y WAC FOR UNROLLS
        cwpu1,cwpu2,cwpu3,cwpu4,cwpu5,cwpu6,cwpu7,cwpu8,cwpu9,cwpu10=0,0,0,0,0,0,0,0,0,0
        cwcu1,cwcu2,cwcu3,cwcu4,cwcu5,cwcu6,cwcu7,cwcu8,cwcu9,cwcu10=0,0,0,0,0,0,0,0,0,0
	#SAT TIME FOR UNROLLS
	st1,st2,st3,st4,st5,st6,st7,st8,st9,st10=0,0,0,0,0,0,0,0,0,0
	#TIEMPOS MINIMOS
	tmin=999999999
	#TO  FOR UNROLLS
	to1,to2,to3,to4,to5,to6,to7,to8,to9,to10=0,0,0,0,0,0,0,0,0,0
	ur=-1
	ant=False
	for l in lines:
	    l=l[:-1]
	    h=l.find('action_name')
	    if h>=0:
		action= l[h:len(l)-1]
	    h=l.find('unroll')
	    if h>0:
		#ur indica el unroll
		ur = int(l.split(':')[2])
		cant= int(l.split(':')[1].split(' ')[0])
		if ur==1:
		      cwcu1=cwcu1+cant
		if ur==2:
		      cwcu2=cwcu2+cant
		if ur==3:
		      cwcu3=cwcu3+cant
		if ur==4:
		      cwcu4=cwcu4+cant
		if ur==5:
		      cwcu5=cwcu5+cant
		if ur==6:
		      cwcu6=cwcu6+cant
		if ur==7:
		      cwcu7=cwcu7+cant
		if ur==8:
		      cwcu8=cwcu8+cant
		if ur==9:
		      cwcu9=cwcu9+cant
		if ur==10:
		      cwcu10=cwcu10+cant
	    if l.find('WAP')>=0 or l.find('NOT')>=0:
		      s=l.strip()
		      part=s.split(' ')
		      res=part[0].strip()
		      time=int(part[1])
		      if tmin>time:
				tmin=time
                      st1,cwpu1=ff(ur,1,st1,res,time,cwpu1)
                      st2,cwpu2=ff(ur,2,st2,res,time,cwpu2)
		      st3,cwpu3=ff(ur,3,st3,res,time,cwpu3)
                      st4,cwpu4=ff(ur,4,st4,res,time,cwpu4)
                      st5,cwpu5=ff(ur,5,st5,res,time,cwpu5)
                      st6,cwpu6=ff(ur,6,st6,res,time,cwpu6)
		      st7,cwpu7=ff(ur,7,st7,res,time,cwpu7)
                      st8,cwpu8=ff(ur,8,st8,res,time,cwpu8)
                      st9,cwpu9=ff(ur,9,st9,res,time,cwpu9)
                      st10,cwpu10=ff(ur,10,st10,res,time,cwpu10)
    	    if l.find('True')>=0:
	    	      if ur==1:
	    			to1=to1+1	
	    	      if ur==2:
	    			to2=to2+1
	    	      if ur==3:
	    			to3=to3+1
	    	      if ur==4:
	    			to4=to4+1
	    	      if ur==5:
	    			to5=to5+1
	    	      if ur==6:
	    			to6=to6+1
	    	      if ur==7:
	    			to7=to7+1
	    	      if ur==8:
	    			to8=to8+1
	    	      if ur==9:
	    			to9=to9+1
	    	      if ur==10:
	    			to10=to10+1
	if cwpu1>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap1:"+str(cwpu1)+" | avg sattime wap1:"+str(float(st1/cwpu1))+" | TO:"+str(to1)	
	if cwpu2>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap2:"+str(cwpu2)+" | avg sattime wap2:"+str(float(st2/cwpu2))+" | TO:"+str(to2)
	if cwpu3>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap3:"+str(cwpu3)+" | avg sattime wap3:"+str(float(st3/cwpu3))+" | TO:"+str(to3)
	if cwpu4>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap4:"+str(cwpu4)+" | avg sattime wap4:"+str(float(st4/cwpu4))+" | TO:"+str(to4)
	if cwpu5>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap5:"+str(cwpu5)+" | avg sattime wap5:"+str(float(st5/cwpu5))+" | TO:"+str(to5)
	if cwpu6>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap6:"+str(cwpu6)+" | avg sattime wap6:"+str(float(st6/cwpu6))+" | TO:"+str(to6)
	if cwpu7>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap7:"+str(cwpu7)+" | avg sattime wap7:"+str(float(st7/cwpu7))+" | TO:"+str(to7)
	if cwpu8>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap8:"+str(cwpu8)+" | avg sattime wap8:"+str(float(st8/cwpu8))+" | TO:"+str(to8)
	if cwpu9>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap9:"+str(cwpu9)+" | avg sattime wap9:"+str(float(st9/cwpu9))+" | TO:"+str(to9)
	if cwpu10>0:
		print "Min. sat time:"+str(tmin)
		print "accion:"+action+" | #wap10:"+str(cwpu10)+" | avg sattime wap10:"+str(float(st10/cwpu10))+" | TO:"+str(to10)










  
procesar_logfile()
print '======================================='
procesar_logfile_permanente()

