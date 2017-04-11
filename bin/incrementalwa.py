import alloy,ap1
from alloy.cli import als2cnfbed
from alloy.relations import Relations
from alloy.kodkod import Relation
from minisat import minisat
import sys, os, platform
#import time
import logging
from datetime import datetime, date, time, timedelta
import calendar


#Log  = logging.getLogger(__name__)


def var2tuple(var, rs):
    (rel_i, (atom_i0, atom_i1)) = rs.v2rt[var]
    res = "(" + rs.ind2an[atom_i0] + "," + rs.ind2an[atom_i1] + ")"
    return res


def var2element(var, rs):
    (rel_i, atom_i0) = rs.v2rt[var]
    res = "(" + rs.ind2an[atom_i0[0]] + ")"
    return res

#



'''def cr(alloy_models,cant_max,ur,state,accion,filename):
	path_als = os.path.abspath(alloy_models)
	nodename = platform.node()
	output = als2cnfbed(path_als)
	
        
	path_cnf = output.path_cnf
	path_rels = output.path_rels
	rs = Relations(path_rels)
	#acaca	
	wac_list=[]
	
	z = minisat.Zolver()


        rels = rs.rels
        
	z.read(path_cnf)
	i=0
        contador_wac=0
        first =True
        
        while True:
	    if i==cant_max:
		break 

	    verdict = z.solve()
            

            if verdict == True:
                contador_wac=contador_wac+1
		i=i+1
                cl = []
		cadelis=''
		fact='<INICIO>fact{ '  
                for j in xrange(len(rels)):
                    r = rels[j]
		    print r.name
		    if r.name.find("QF.ac_")==0:
			action= r.name[0:7]
                        
                        for v in r.vrange:
			   
                            if z.evalmodel(v) == '1':
				value=var2element(v, rs)
				value=value[1:len(value)-1]
				cadelis=cadelis+value+','
				fact=fact + action+'='+value+ ' and '
                                cl = [-v]
		fact=fact[:-5]
		
		
		cadelis=cadelis[:-1]
		fact=fact+'}<FINAL>?'+cadelis+'\n'
		
                z.addclause(cl)
		print "-----------------------------------"
		print cadelis
		print "-----------------------------------"
		print 'wac canditate : ',cadelis
		print fact 
	
		
		wac_list.append(fact)
            else:
                assert verdict == False, "ERROR: Undefined solver state"
                break
        return wac_list
'''



#def correr():
#	cr('pepe.als',100,1,0,'vector_clear','salida')


#correr()



















def run_incremental_alloy(alloy_models,cant_max,ur,state,accion,filename):
        total_time_wac=timedelta(0)
	fname=open(filename,'w')
	path_als = os.path.abspath(alloy_models)
	nodename = platform.node()
	t0 = datetime.now()
	t_before_xlation = datetime.now()
	output = als2cnfbed(path_als)

	t_after_xlation = datetime.now()
	xlation_seconds = t_after_xlation - t_before_xlation
        #print 'Time traslation als to cnf:' , xlation_seconds
        #sys.exit(0)
	path_cnf = output.path_cnf
	path_rels = output.path_rels
        #print path_rels

	#print path_rels

        
	rs = Relations(path_rels)
		
	wac_list=[]
        #print("\nCreating native solver instance")
	
	z = minisat.Zolver()
	#print "???????????????????"
	#print rs
	#print "???????????????????"
        #sys.exit(0)



        rels = rs.rels
        
	#print("Parsing {}".format(path_cnf))
	z.read(path_cnf)
	i=0
        contador_wac=0
        first =True
        
        while True:
	    if i==cant_max:
                ap1.log_file('Se alcanzo el maximo de wa encontrados','logfile.log')
		break 
            a= datetime.now()

	    inicio = datetime.now()
	    
	    verdict = z.solve()
            b= datetime.now()
            
            total_time_wac= total_time_wac + (b-a)

	    tiempo=datetime.now()-inicio
            if verdict == True:
                contador_wac=contador_wac+1
		print 'unroll='+str(ur)+' & wac_nro='+str(contador_wac)+' % satTime='+ap1.tiempo_transcurrido(a,b)
                #ap1.log_file('action:'+str(accion)+' % state:'+str(state)+' % '+'unroll:'+str(ur)+' % wac_nro:'+str(contador_wac)+' % sat_time:'+ap1.tiempo_transcurrido(a,b),'logfile.log')

 		ap1.log_file(' wac_nro='+str(contador_wac)+' % sat_time='+ap1.tiempo_transcurrido(a,b),'logfile.log')

                print 'total_wacs:'+str(contador_wac)+' % total-sat-time %'+str(total_time_wac)
                ap1.log_file('total_wacs='+str(contador_wac)+' % total-sat-time='+str(total_time_wac),'logfile.log')
	        print 'Sat time: ',str(tiempo)
		i=i+1
                cl = []
		cadelis=''

		
		fact_candidate='<INICIO>fact{ '  
		fact_permanent='fact{ ' 
                for j in xrange(len(rels)):

                    r = rels[j]


                    if r.name.find("QF.intJ_1_")==0 or r.name.find("QF.intJ_2_")==0:
			para1= r.name[0:11]
			for v in r.vrange:
                            if z.evalmodel(v) == '1':
				value=var2element(v, rs)
				value=value[1:len(value)-1]
				#print value
				#cadelis=cadelis+value+','
				fact_permanent=fact_permanent + para1+'='+value+ ' and '
                                #cl = [-v]

		    if r.name.find("QF.ac_")==0:
			action= r.name[0:7]
			#print action
			#print 'accion=>'+action
                        #para cada varible perteneciente a la relacion QF.ac_ que representa a las acciones  
                        
                        for v in r.vrange:
			   
                            if z.evalmodel(v) == '1':
				value=var2element(v, rs)
				value=value[1:len(value)-1]
				cadelis=cadelis+value+','
				fact_candidate=fact_candidate + action+'='+value+ ' and '
				fact_permanent=fact_permanent + action+'='+value+ ' and '

                                cl = [-v]
                             
		fact_permanent=fact_permanent[:-5]
		fact_candidate=fact_candidate[:-5]
		
		
		cadelis=cadelis[:-1]
		fact=fact_candidate+'}?'+cadelis+'?'+fact_permanent+'}<FINAL>\n'


		
                z.addclause(cl)

		#almacena fact el wac en un archivo
		#print 'wac canditate : \n',cadelis
		fname.write(fact)
		
		
		wac_list.append(fact)
            else:
                #ap1.log_file('unsat.. fin busqueda para el unroll corriente','logfile.log') 
                assert verdict == False, "ERROR: Undefined solver state"
                break
        fname.close()

        return wac_list


def run_alloy(alloy_model):

	path_als = os.path.abspath(alloy_model)
        
	nodename = platform.node()
	t0 = datetime.now()

	t_before_xlation = datetime.now()
	output = als2cnfbed(path_als)
	
	t_after_xlation = datetime.now()
	xlation_seconds = t_after_xlation - t_before_xlation
        print 'Time traslation als to cnf:' , xlation_seconds

	
	path_cnf = output.path_cnf
	path_rels = output.path_rels
	print '------------kkk---------'
        print path_rels
	print '---------------------'
        
	print("\nParsing {}".format(path_rels))
	rs = Relations(path_rels)



	wac_list=[]
        #print("\nCreating native solver instance")
	kk = minisat.Zolver()
        rels = rs.rels
	#print("Parsing {}".format(path_cnf))
	kk.read(path_cnf)
	tiempo=datetime.now()
	veredict = kk.solve()
	tfinal=datetime.now()-tiempo
	print 'sat time',tfinal

	if not veredict:
		print "Eureka: we found a permanent workaround!!!"
    	        ap1.log_file('WAP sat_time % '+str(tfinal),'logfile.log')
	else: 
                ap1.log_file('NO_W sat_time % '+str(tfinal),'logfile.log')
		print "NO_W The candidate workaround isn't a permanent workaround."



def run_alloy2(modalloy):

	os.system("java -Xmx8g -Djava.library.path=../lib/amd64-linux/ -jar ../lib/alloycli-1.6.0b3.jar  -s minisat -x uva "+modalloy+" > temp")
	r=ap1.UNSAT('temp')
	tfinal=''
	if(r==1 or r==0):
		tfinal=ap1.cal_sattime('temp')
	if (r==1):
		print "Eureka: we found a permanent workaround!!!"
    	        ap1.log_file('WAP sat_time='+tfinal,'logfile_wap.log')
	if (r==0):
    	        ap1.log_file('NOT sat_time='+tfinal,'logfile_wap.log')
		print "NO_W The candidate workaround isn't a permanent workaround."
	os.system("rm temp")

