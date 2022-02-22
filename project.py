import pynusmv
import sys

from pynusmv.fsm import BddTrans    



def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_explain_eventually(spec):
    """
    Return whether the property `spec` is eventually true in the loaded SMV model, 
    that is, whether all traces of the model satisfies the LTL formula `F spec` or not.
    Return also an explanation for why the model does not satisfy `F spec`, 
    if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `F spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `F spec`
    otherwise.

    The explanation is a tuple of alternating states and inputs, starting
    and ending with a state. The path is looping if the last state is somewhere else 
    in the sequence. States and inputs are represented by dictionaries where keys are 
    state and inputs variable of the loaded SMV model, and values are their value. 
    """

    liveness = spec_to_bdd(fsm,spec)
    reach = fsm.init
    reachSingoli = {} #Array che contiene tutti i nuovi stati raggiunti, in modo da poter ritornare il controesempio


    #inizializzazione reachSingoli

    n = 0

    for state in fsm.pick_all_states(reach):
        reachSingoli[n] = state
        n = n+1


    #avviene il primo controllo per verificare che già nello stato iniziale è verificato un controesempio

    primoControllo = pynusmv.dd.BDD.intersection(reach,liveness)



    if(fsm.count_states(primoControllo) == n): #Controllo se ha valore n poiché l'intersezione non dovrebbe rimuovere alcun elemento di reach, altrimenti vuol dire che almeno un elemento non è valido
               
        res = True
        trace = "None"
        return res,trace


    #controllo di fsm.init


    for state in fsm.pick_all_states(fsm.init):
        reach = fsm.init
        new = fsm.post(fsm.init)
        #aggiungo i new dentro raggiuntiSingoli
        i = 0
        for state in fsm.pick_all_states(new):
            reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
            i = i+1
  

        reach = pynusmv.dd.BDD.union(reach,new)

        

        intersezione = pynusmv.dd.BDD.intersection(new,liveness)
        
                
        if(fsm.count_states(intersezione) == n):

            res = True
            trace = "None"
            return res,trace


     #controllo di fsm.post(fsm.init)


    for state in fsm.pick_all_states(fsm.post(fsm.init)):

        new = fsm.post(fsm.post(fsm.init))   

        #aggiungo gli elementi di new ai singoli elementi raggiunti
        i = 0
        for state in fsm.pick_all_states(new):
            reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
            i = i+1
        reach = pynusmv.dd.BDD.union(reach,new)  
        #print(state.get_str_values())
        intersezione = pynusmv.dd.BDD.intersection(new,liveness)
        if(fsm.count_states(intersezione) == n):
     
            res = True;
            trace = "None"
            return res,trace


    termina = 0
       
    while(termina == 0): 

        precedente = fsm.count_states(reach)
        for state in fsm.pick_all_states(fsm.post(new)):
            new = fsm.post(new)
            #aggiungo gli elementi di new ai singoli elementi raggiunti
            i = 0
            for state in fsm.pick_all_states(new):
                reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
                i = i+1
            reach = pynusmv.dd.BDD.union(reach,new)
            
            if(fsm.count_states(reach) == precedente):
                termina = 1
            
        

        intersezione = pynusmv.dd.BDD.intersection(new,liveness)

        if(fsm.count_states(intersezione) ==  n):


            res = True;
            trace = "None"
            return res,trace




    indice = 0
    for j in range(n):
        if(fsm.count_states(pynusmv.dd.BDD.diff(reachSingoli[j],pynusmv.dd.BDD.intersection(reachSingoli[j],liveness))) > 0): 
            indice = j

    res = False

    for state in fsm.pick_all_states(reachSingoli[indice]): 
        print("")
        
    trace = pynusmv.dd.BDD.diff(reachSingoli[indice],pynusmv.dd.BDD.intersection(reachSingoli[indice],liveness))

    
    

    return res,trace

def check_explain_always(spec):

    """
    Return whether the property `spec` is always true in the loaded SMV model, 
    that is, whether all traces of the model satisfies the LTL formula `G spec` or not.
    Return also an explanation for why the model does not satisfy `G spec`, 
    if it is the case, or `None` otherwise.

    The result is a tuple where the first element is a boolean telling
    whether `G spec` is satisfied, and the second element is either `None` if the
    first element is `True``, or an execution of the SMV model violating `F spec`
    otherwise.

    The explanation is a tuple of alternating states and inputs, starting
    and ending with a state. The path is looping if the last state is somewhere else 
    in the sequence. States and inputs are represented by dictionaries where keys are 
    state and inputs variable of the loaded SMV model, and values are their value. 
    """

 

    liveness = spec_to_bdd(fsm,spec)
    reach = fsm.init
    reachSingoli = {} #Array che contiene tutti i nuovi stati raggiunti, in modo da poter ritornare il controesempio


    #inizializzazione reachSingoli

    n = 0
    for state in fsm.pick_all_states(reach):
        reachSingoli[n] = state
        n = n+1


    #avviene il primo controllo per verificare che già nello stato iniziale è verificato un controesempio

    primoControllo = pynusmv.dd.BDD.intersection(reach,liveness)



    if(fsm.count_states(primoControllo) < n): #Controllo se ha valore n poiché l'intersezione non dovrebbe rimuovere alcun elemento di reach, altrimenti vuol dire che almeno un elemento non è valido
         

        #controllo quale elemento è un controesempio già da inizializzazione
        i = 0
        for state in fsm.pick_all_states(reach):
            verifica = pynusmv.dd.BDD.intersection(state,liveness)
            if(fsm.count_states(verifica) == 0):
                break
            i = i+1         
        
        res = False
        trace = reachSingoli[i]
        return res,trace


    #controllo di fsm.init


    for state in fsm.pick_all_states(fsm.init):
        reach = fsm.init
        new = fsm.post(fsm.init)
        #aggiungo i new dentro raggiuntiSingoli
        i = 0
        for state in fsm.pick_all_states(new): 
            reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
            i = i+1
  

        reach = pynusmv.dd.BDD.union(reach,new)

        

        intersezione = pynusmv.dd.BDD.diff(new,pynusmv.dd.BDD.intersection(new,liveness))
        
                
        if(fsm.count_states(intersezione) > 0):

            #controllo quale elemento è un controesempio 
            i = 0
            for state in fsm.pick_all_states(new):
                verifica = pynusmv.dd.BDD.intersection(state,liveness)
                if(fsm.count_states(verifica) == 0):
                    break
                i = i+1       

            res = False;
            trace = reachSingoli[i]
            return res,trace


     #controllo di fsm.post(fsm.init)


    for state in fsm.pick_all_states(fsm.post(fsm.init)):

        new = fsm.post(fsm.post(fsm.init))   

        #aggiungo gli elementi di new ai singoli elementi raggiunti
        i = 0
        for state in fsm.pick_all_states(new):
            reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
            i = i+1
        reach = pynusmv.dd.BDD.union(reach,new)  
        #print(state.get_str_values())
        intersezione = pynusmv.dd.BDD.diff(new,pynusmv.dd.BDD.intersection(new,liveness))
        if(fsm.count_states(intersezione) > 0):

           #controllo quale elemento è un controesempio 
            i = 0
            for state in fsm.pick_all_states(new):
                verifica = pynusmv.dd.BDD.intersection(state,liveness)
                if(fsm.count_states(verifica) == 0):
                    break
                i = i+1       
            res = False;
            trace = reachSingoli[i]
            return res,trace


    termina = 0
       
    while(termina == 0): 

        precedente = fsm.count_states(reach)
        for state in fsm.pick_all_states(fsm.post(new)):
            new = fsm.post(new)
            #aggiungo gli elementi di new ai singoli elementi raggiunti
            i = 0
            for state in fsm.pick_all_states(new):
                reachSingoli[i] = pynusmv.dd.BDD.union(state,reachSingoli[i])
                i = i+1
            reach = pynusmv.dd.BDD.union(reach,new)
            
            if(fsm.count_states(reach) == precedente):
                termina = 1
            
        

        intersezione = pynusmv.dd.BDD.diff(new,pynusmv.dd.BDD.intersection(new,liveness))

        if(fsm.count_states(intersezione) > 0):

           #controllo quale elemento è un controesempio 
            i = 0
            for state in fsm.pick_all_states(new):
                verifica = pynusmv.dd.BDD.intersection(state,liveness)
                if(fsm.count_states(verifica) == 0):
                    break
                i = i+1       
            res = False;
            trace = reachSingoli[i]
            return res,trace




    res = True
    trace = "None"

    return res,trace

    

if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "example.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    #bdd = pynusmv.mc.eval_ctl_spec(fsm, spec)
    fsm = pynusmv.glob.prop_database().master.bddFsm
    print(spec)
    print(prop.type)
    if prop.type == invtype:
        print("")
        print("")
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_eventually(spec)
        print("TERMINATO")
        if res == True:
            print("Spec ",spec," is eventually true")
        else:
            print("Spec ",spec," is not eventually true")

            #visualizzazione nell'ordine corretto, senza questo procedimento il contro esempio verrebbe visualizzato in ordine sparso
 
            #il fatto che di ogni passaggio venga visualizzata solo la prima tupla è dovuto al fatto che devo visualizzare un solo controesempio 

            cont = 0
            for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,fsm.init)):
                if(cont == 0):
                    print(state.get_str_values())
                cont = cont+1

            cont = 0
            for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,fsm.post(fsm.init))):
                if(cont == 0):
                    print(state.get_str_values())
                cont = cont+1


            contatore = 2
            nuovo = fsm.post(fsm.init)
            while(contatore < fsm.count_states(trace)):
                cont = 0
                nuovo = fsm.post(nuovo)
                for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,nuovo)):
                    contatore = contatore+1
                    if(cont == 0):
                        print(state.get_str_values())
                    cont = cont+1
              
                 

        res, trace = check_explain_always(spec)
        if res == True:
            print("Spec ",spec," is always true")
        else:
            print("Spec ",spec," is not always true")


           #visualizzazione nell'ordine corretto, senza questo procedimento il contro esempio verrebbe visualizzato in ordine sparso

            for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,fsm.init)):
                print(state.get_str_values())
            if(fsm.count_states(trace) > 1): 
                for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,fsm.post(fsm.init))):
                    print(state.get_str_values())

            contatore = 2
            nuovo = fsm.post(fsm.init)
            while(contatore < fsm.count_states(trace)):

                nuovo = fsm.post(nuovo)
                for state in fsm.pick_all_states(pynusmv.dd.BDD.intersection(trace,nuovo)):
                    contatore = contatore + 1
                    print(state.get_str_values())

    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()
