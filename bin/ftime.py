import datetime
from datetime import timedelta
 
def sumar_hora(hora1,hora2):
    h1=datetime.datetime.strptime(hora1, "%H:%M:%S.%f" )
    
    lista = hora2.split(":")
    hora=int(lista[0])
    minuto=int(lista[1])
    segundo=int(lista[2].split('.')[0])
    milisegundo=int(lista[2].split('.')[1])
   

    dh = timedelta(hours=hora) 
    dm = timedelta(minutes=minuto)          
    ds = timedelta(seconds=segundo) 
    dml= timedelta(milliseconds=milisegundo)
    print dml 

    resultado0 =h1 + dml
    resultado1 =resultado0 + ds
    resultado2 = resultado1 + dm
    resultado = resultado2 + dh
    resultado=resultado.strftime("%H:%M:%S.%f")
    return str(resultado)

print(sumar_hora("00:00:00.999","00:00:00.1"))	
