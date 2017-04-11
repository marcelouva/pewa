from functools import wraps
import errno
import os,ap1
import signal
from datetime import datetime, date, time, timedelta

class TimeoutError(Exception):
    pass

def timeout(error_message=os.strerror(errno.ETIME)):
    seconds=int(ap1.read_config_case("../config.ini","options")['timeout'])
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result
        return wraps(func)(wrapper)

    return decorator







@timeout()
def call_with_timeout(funcion, parametro1, parametro2,parametro3,parametro4,parametro5,filename):
     t=datetime.now()
     try:
        funcion(parametro1,parametro2,parametro3,parametro4,parametro5,filename)
        return [datetime.now()-t,False]
     except Exception as inst:
    	print(type(inst))    # la instancia de excepcin
    	print(inst.args)     # argumentos guardados en .args
    	print(inst)
      
	return [datetime.now()-t,True]




@timeout()
def call_with_timeout_permament(funcion, parametro1):
     #t=datetime.now()
     try:		
        funcion(parametro1)
        return [0,False]
     except:
	return [0,True]


