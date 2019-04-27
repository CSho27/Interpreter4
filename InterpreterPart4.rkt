; If you are using scheme instead of racket, comment these two lines, uncomment the (load "simpleParser.scm") and comment the (require "simpleParser.rkt")
#lang racket
;(require "simpleParser.rkt")
; (load "simpleParser.scm")

(require "classParser.rkt")

; An interpreter for the simple language using tail recursion for the M_state functions and does not handle side effects.

; The functions that start interpret-...  all return the current environment.  These are the M_state functions.
; The functions that start eval-...  all return a value.  These are the M_value and M_boolean functions.

; The main function.  Calls parser to get the parse tree and interprets it with a new environment.  Sets default continuations for return, break, continue, throw, and "next statement"
(define interpret_outdated
  (lambda (file)
    (scheme->language
     (interpret-statement-list (parser file) (newenvironment) (lambda (v) v)
                               (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                               (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (env) env)))))

;Runs the main function in the statement provided by the parser
(define interpret
  (lambda (filename)
    (scheme->language
     (func_run 'main '() (interpret_global (parser filename) (newenvironment)) (lambda (v env) v)))))

;Executes a function given its name and paramaters
(define func_run
  (lambda (func_name func_params state throw)
    (interpret-statement-list (get_func_body func_name state) (get_func_final_state func_name func_params state throw) (lambda (v) v)
                              (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                              throw (lambda (env) env)
                              )))

;; executes a function and returns its ending state
(define func_return_env
  (lambda (func_name func_params state)
    (interpret-statement-list-env (get_func_body func_name state) (get_func_final_state func_name func_params state) (lambda (v) v)
                              (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                              (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (env) env)
                              )))
    
;Returns a given functions declared paramaters as stored in its closure
(define get_func_param_names
  (lambda (func_name state)
    (func_params_in_closure (lookup func_name state))))

(define func_params_in_closure car)

;Returns a given functions body as stored in its closure
(define get_func_body
  (lambda (func_name state)
    (func_body_in_closure (lookup func_name state))))

(define func_body_in_closure cadr)

;Returns a given functions environment as stored in its closure
(define get_func_environment
  (lambda (func_name state)
    (func_state_in_closure (lookup func_name state))))

(define func_state_in_closure caddr)

;Returns the list of values corresponding to the given list of variables as defined in the provided state
(define get_input_values
  (lambda (param_list state return throw)
    (cond
      [(null? param_list) (return param_list)]
      [else (get_input_values (cdr param_list) state (lambda (v) (return (cons (eval-expression (car param_list) state throw) v))) throw)])))

;Assigns the functions paramaters and their values in the new function environment
(define assign_func_params
  (lambda (vars vals state)
    (cond
      [(and (null? vars) (null? vals)) state]
      [(or (null? vars) (null? vals)) (myerror '"Function called with different number of paramters than expected")]
      [else (assign_func_params (cdr vars) (cdr vals) (insert (car vars) (car vals) state))])))


;Returns a given functions final state after being invoked
(define get_func_final_state
  (lambda (func_name func_params state throw)
    (assign_func_params (get_func_param_names func_name state) (get_input_values func_params state (lambda (v) v) throw) (push-frame state))))

    

; interprets a list of statements.  The state/environment from each statement is used for the next ones.
(define interpret-statement-list
  (lambda (statement-list environment return break continue throw next)
    (if (null? statement-list)
        (next environment)
        (interpret-statement (car statement-list) environment return break continue throw (lambda (env) (interpret-statement-list (cdr statement-list) env return break continue throw next))))))


;; helper for finding return statement
(define first-statement caar)
;; returns environment on return rather than value
(define interpret-statement-list-env
  (lambda (statement-list environment return break continue throw next)
    (cond
      [(null? statement-list)                            (next environment)]
      [(eq? (first-statement statement-list) 'return)    (next environment)]
      [else (interpret-statement (car statement-list) environment return break continue throw (lambda (env) (interpret-statement-list (cdr statement-list) env return break continue throw next)))])))
        

; interpret a statement in the environment with continuations for return, break, continue, throw, and "next statement"
(define interpret-statement
  (lambda (statement environment return break continue throw next)
    (cond
      ((eq? 'return (statement-type statement)) (interpret-return statement environment return throw))
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment throw next))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment throw next))
      ((eq? 'if (statement-type statement)) (interpret-if statement environment return break continue throw next))
      ((eq? 'while (statement-type statement)) (interpret-while statement environment return throw next))
      ((eq? 'continue (statement-type statement)) (continue environment))
      ((eq? 'break (statement-type statement)) (break environment))
      ((eq? 'begin (statement-type statement)) (interpret-block statement environment return break continue throw next))
      ((eq? 'throw (statement-type statement)) (interpret-throw statement environment throw))
      ((eq? 'try (statement-type statement)) (interpret-try statement environment return break continue throw next))
      ;((eq? 'funcall (statement-type statement)) (interpret-funcall statement environment return break continue throw next))
      ((eq? 'funcall (statement-type statement)) (next (interpret_func_run statement environment throw next)))
      ((eq? 'function (statement-type statement)) (next (func_define (cdr statement) environment)))
      (else (myerror "Unknown statement:" (statement-type statement))))))
 
(define interpret_func_run
  (lambda (statement environment throw next)
    (if (func_run (funcall_name statement) (funcall_params statement) environment throw)
        environment
        environment)))

; Calls the return continuation with the given expression value
(define interpret-return
  (lambda (statement environment return throw)
    (return (eval-expression (get-expr statement) environment throw))))

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-declare
  (lambda (statement environment throw next)
    (if (exists-declare-value? statement)
        (next (insert (get-declare-var statement) (eval-expression (get-declare-value statement) environment throw) environment))
        (next (insert (get-declare-var statement) 'novalue environment)))))

; Updates the environment to add a new binding for a variable
(define interpret-assign
  (lambda (statement environment throw next)
    (next (update (get-assign-lhs statement) (eval-expression (get-assign-rhs statement) environment throw) environment))))

; We need to check if there is an else condition.  Otherwise, we evaluate the expression and do the right thing.
(define interpret-if
  (lambda (statement environment return break continue throw next)
    (cond
      ((eval-expression (get-condition statement) environment throw) (interpret-statement (get-then statement) environment return break continue throw next))
      ((exists-else? statement) (interpret-statement (get-else statement) environment return break continue throw next))
      (else (next environment)))))

; Interprets a while loop.  We must create break and continue continuations for this loop
(define interpret-while
  (lambda (statement environment return throw next)
    (letrec ((loop (lambda (condition body environment)
                     (if (eval-expression condition environment throw)
                         (interpret-statement body environment return (lambda (env) (next env)) (lambda (env) (loop condition body env)) throw (lambda (env) (loop condition body env)))
                         (next environment)))))
      (loop (get-condition statement) (get-body statement) environment))))

; Interprets a block.  The break, continue, throw and "next statement" continuations must be adjusted to pop the environment
(define interpret-block
  (lambda (statement environment return break continue throw next)
    (interpret-statement-list (cdr statement)
                                         (push-frame environment)
                                         return
                                         (lambda (env) (break (pop-frame env)))
                                         (lambda (env) (continue (pop-frame env)))
                                         (lambda (v env) (throw v (pop-frame env)))
                                         (lambda (env) (next (pop-frame env))))))

; We use a continuation to throw the proper value.  Because we are not using boxes, the environment/state must be thrown as well so any environment changes will be kept
(define interpret-throw
  (lambda (statement environment throw)
    (throw (eval-expression (get-expr statement) environment throw) environment)))

; Interpret a try-catch-finally block

; Create a continuation for the throw.  If there is no catch, it has to interpret the finally block, and once that completes throw the exception.
;   Otherwise, it interprets the catch block with the exception bound to the thrown value and interprets the finally block when the catch is done
(define create-throw-catch-continuation
  (lambda (catch-statement environment return break continue throw next finally-block)
    (cond
      ((null? catch-statement) (lambda (ex env) (interpret-block finally-block env return break continue throw (lambda (env2) (throw ex env2))))) 
      ((not (eq? 'catch (statement-type catch-statement))) (myerror "Incorrect catch statement"))
      (else (lambda (ex env)
                  (interpret-statement-list 
                       (get-body catch-statement) 
                       (insert (catch-var catch-statement) ex (push-frame env))
                       return 
                       (lambda (env2) (break (pop-frame env2))) 
                       (lambda (env2) (continue (pop-frame env2))) 
                       (lambda (v env2) (throw v (pop-frame env2))) 
                       (lambda (env2) (interpret-block finally-block (pop-frame env2) return break continue throw next))))))))

; To interpret a try block, we must adjust  the return, break, continue continuations to interpret the finally block if any of them are used.
;  We must create a new throw continuation and then interpret the try block with the new continuations followed by the finally block with the old continuations
(define interpret-try
  (lambda (statement environment return break continue throw next)
    (let* ((finally-block (make-finally-block (get-finally statement)))
           (try-block (make-try-block (get-try statement)))
           (new-return (lambda (v) (interpret-block finally-block environment return break continue throw (lambda (env2) (return v)))))
           (new-break (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (break env2)))))
           (new-continue (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (continue env2)))))
           (new-throw (create-throw-catch-continuation (get-catch statement) environment return break continue throw next finally-block)))
      (interpret-block try-block environment new-return new-break new-continue new-throw (lambda (env) (interpret-block finally-block env return break continue throw next))))))

(define interpret-define
  (lambda (statement environment return break continue throw next)
      (next (func_define (function_declaration statement)  environment))))

(define interpret-funcall
  (lambda (statement environment return break continue throw next)
    (next (func_return_env (funcall_name statement) (funcall_params statement) (func-frame environment)))))
    

    
; helper methods so that I can reuse the interpret-block method on the try and finally blocks
(define make-try-block
  (lambda (try-statement)
    (cons 'begin try-statement)))

(define make-finally-block
  (lambda (finally-statement)
    (cond
      ((null? finally-statement) '(begin))
      ((not (eq? (statement-type finally-statement) 'finally)) (myerror "Incorrectly formatted finally block"))
      (else (cons 'begin (cadr finally-statement))))))

; Evaluates all possible boolean and arithmetic expressions, including constants and variables.
;(define eval-expression-old
;  (lambda (expr environment)
;    (cond
;      ((number? expr) expr)
;      ((eq? expr 'true) #t)
;      ((eq? expr 'false) #f)
;      ;Add function call somewhere in here I think so it can return a value from a function
;      ;Should check in one of these eval methods if the beginning statement is funcall, and if so call the func_run method on it
;      ((not (list? expr)) (lookup expr environment))
;      (else (eval-operator expr environment)))))

; eval-expression modified to call mvalue for simplicity
(define eval-expression
  (lambda (expr environment throw)
    (mvalue expr environment cps-lambda throw)))

;; mvalue evaluates an expression and returns a value
(define mvalue
  (lambda (expr environment cps-return throw)
    (cond
      [(null? expr)                      (error "undefined expression")]
      [(number? expr)                    (cps-return expr)]
      [(boolean? expr)                   (cps-return expr)]
      [(eq? expr 'true)                  (cps-return #t)]
      [(eq? expr 'false)                 (cps-return #f)] 
      [(not (pair? expr))                (cps-return (lookup-variable expr environment))]
      [(eq? (operator expr) 'funcall)    (cps-return (func_run (funcall_name expr) (mvalue-params (funcall_params expr) environment cps-return throw) (func-frame (funcall_name expr) environment) throw))]
      [(eq? (operator expr) '+)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (+ v1 v2))) throw)) throw)]
      [(and (eq? (operator expr) '-)     (null? (cddr expr))) (mvalue 0 environment (lambda (v1) (mvalue (operand1 expr) environment (lambda (v2) (cps-return (- v1 v2))) throw)) throw)]
      [(eq? (operator expr) '-)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (- v1 v2))) throw)) throw)]
      [(eq? (operator expr) '*)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (* v1 v2))) throw)) throw)]
      [(eq? (operator expr) '/)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (quotient v1 v2))) throw)) throw)]
      [(eq? (operator expr) '%)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (remainder v1 v2))) throw)) throw)]
      [(eq? (operator expr) '==)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (eq? v1 v2))) throw)) throw)]
      [(eq? (operator expr) '>)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (> v1 v2))) throw)) throw)]
      [(eq? (operator expr) '<)          (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (< v1 v2))) throw)) throw)]
      [(eq? (operator expr) '>=)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (>= v1 v2))) throw)) throw)]
      [(eq? (operator expr) '<=)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (<= v1 v2))) throw)) throw)]
      [(eq? (operator expr) '!=)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (not (eq? v1 v2)))) throw)) throw)]
      [(eq? (operator expr) '&&)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (and v1 v2))) throw)) throw)]
      [(eq? (operator expr) '||)         (mvalue (operand1 expr) environment (lambda (v1) (mvalue (operand2 expr) environment (lambda (v2) (cps-return (or v1 v2))) throw)) throw)]
      [(eq? (operator expr) '!)          (mvalue (operand1 expr) environment (lambda (v) (cps-return (not v))) throw)] 
      [else (myerror "Unknown operator:" (operator expr))])))

; Determines if two values are equal.  We need a special test because there are both boolean and integer types.
(define isequal
  (lambda (val1 val2)
    (if (and (number? val1) (number? val2))
        (= val1 val2)
        (eq? val1 val2))))

;; this helper function evaluates the value of each parameter before passing it in
(define mvalue-params
  (lambda (params environment cps-return throw)
    (cond
      [(null? params) '()]
      [else (mvalue (car params) environment (lambda (v) (cons v (mvalue-params (cdr params) environment cps-return throw))) throw)])))


;-----------------
; HELPER FUNCTIONS
;-----------------

; These helper functions define the operator and operands of a value expression
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)
(define funcall_name cadr)
(define funcall_params cddr)

(define exists-operand2?
  (lambda (statement)
    (not (null? (cddr statement)))))

(define exists-operand3?
  (lambda (statement)
    (not (null? (cdddr statement)))))

; these helper functions define the parts of the various statement types
(define statement-type operator)
(define get-expr operand1)
(define get-declare-var operand1)
(define get-declare-value operand2)
(define exists-declare-value? exists-operand2?)
(define get-assign-lhs operand1)
(define get-assign-rhs operand2)
(define get-condition operand1)
(define get-then operand2)
(define get-else operand3)
(define get-body operand2)
(define exists-else? exists-operand3?)
(define get-try operand1)
(define get-catch operand2)
(define get-finally operand3)
(define cps-lambda (lambda (v) v))

(define catch-var
  (lambda (catch-statement)
    (car (operand1 catch-statement))))


;------------------------
; Environment/State Functions
;------------------------

;Parses the global level statements in the program
(define interpret_global
  (lambda (parse_tree state)
    (cond
      [(null? parse_tree) state]
      [(eq? (first_stmt_type parse_tree) 'var) (interpret_global (remaining_tree parse_tree) (interpret-global-declare (first_stmt parse_tree) state))] ;global variable declaration
      [(eq? (first_stmt_type parse_tree) 'function) (interpret_global (remaining_tree parse_tree) (func_define (function_declaration parse_tree) state))] ;global function declaration
      [else (myerror "Can only use declaration statements at a global level")]
      )))

(define first_stmt_type caar)
(define first_stmt car)
(define remaining_tree cdr)
(define function_declaration cdar)

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-global-declare
  (lambda (statement environment)
    (if (exists-declare-value? statement)
        (insert (get-declare-var statement) (eval-expression (get-declare-value statement) environment (lambda (v env) v)) environment)
        (insert (get-declare-var statement) 'novalue environment))))

;Returns the new environment after the given function has been defined
;state is in format ((()())) and function is passed in format like (a (x y) ((return (+ x y)))) where 'function' has been stripped by Mstate
;Assum1: funct initialization is added to the current top layer of state, not creating a new top layer
;Assum2: function is bound to ((parameters) (body) (state when function was created plus function initialization))
;idk if these assumptions are right or not??
(define func_define
  (lambda (function state)
    (func_new_environment function (new_state_initializer function state))))

;Updates an initialized functions value in the state with the correct function closure
(define func_new_environment
  (lambda (function environment)
    (update (func_name function) (create_closure (func_params function) (func_body function) environment) environment)))

;Takes a function and the current state and initializes the function in the state
(define new_state_initializer
  (lambda (function state)
    (insert (func_name function) 'novalue state)))

;;Creates the closure that will be binded to a function name in the environment
;Closure is orderes: paramater list -> function body -> function environment
(define create_closure
  (lambda (params body func_environment)
    (cons params (cons body (cons func_environment '())))))

(define func_name car)
(define func_params cadr)
(define func_body caddr)

;; create_class_closure creates a class tuple of the format (parent (list of instance field names) (list of method names) (list of method closures))
(define create_class_closure
  (lambda (parent instances method_names method_closures)
    (cons parent (cons instances (cons method_names (list method_closures))))))

;; create_instance_closure creates a tuple of the format (class (variable names) (variable values))
(define create_instance_closure
  (lambda (class field_vars field_values)
    (cons class (cons field_vars (list field_values)))))

; create a new empty environment
(define newenvironment
  (lambda ()
    (list (newframe))))

; create an empty frame: a frame is two lists, the first are the variables and the second is the "store" of values
(define newframe
  (lambda ()
    '(() ())))

; add a frame onto the top of the environment
(define push-frame
  (lambda (environment)
    (cons (newframe) environment)))

; remove a frame from the environment
(define pop-frame
  (lambda (environment)
    (cdr environment)))

;; func-frame removes everything not in scope for its frame
(define func-frame
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined variable" var))
      ((exists-in-list? var (variables (topframe environment))) environment)
      (else (func-frame var (cdr environment))))))
    
    

; some abstractions
(define topframe car)
(define remainingframes cdr)

; does a variable exist in the environment?
(define exists?
  (lambda (var environment)
    (cond
      ((null? environment) #f)
      ((exists-in-list? var (variables (topframe environment))) #t)
      (else (exists? var (remainingframes environment))))))

; does a variable exist in a list?
(define exists-in-list?
  (lambda (var l)
    (cond
      ((null? l) #f)
      ((eq? var (car l)) #t)
      (else (exists-in-list? var (cdr l))))))

; Looks up a value in the environment.  If the value is a boolean, it converts our languages boolean type to a Scheme boolean type
(define lookup
  (lambda (var environment)
    (lookup-variable var environment)))
  
; A helper function that does the lookup.  Returns an error if the variable does not have a legal value
(define lookup-variable
  (lambda (var environment)
    (let ((value (lookup-in-env var environment)))
      (if (eq? 'novalue value)
          (myerror "error: variable without an assigned value:" var)
          value))))

; Return the value bound to a variable in the environment
(define lookup-in-env
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined variable" var))
      ((exists-in-list? var (variables (topframe environment))) (lookup-in-frame var (topframe environment)))
      (else (lookup-in-env var (cdr environment))))))

; Return the value bound to a variable in the frame
(define lookup-in-frame
  (lambda (var frame)
    (cond
      ((not (exists-in-list? var (variables frame))) (myerror "error: undefined variable" var))
      (else (language->scheme (get-value (indexof var (variables frame)) (store frame)))))))

; Get the location of a name in a list of names
(define indexof
  (lambda (var l)
    (cond
      ((null? l) 0)  ; should not happen
      ((eq? var (car l)) 0)
      (else (+ 1 (indexof var (cdr l)))))))

; Get the value stored at a given index in the list
(define get-value
  (lambda (n l)
    (cond
      [(zero? n) (unbox (car l))]
      [else (get-value (- n 1) (cdr l))])))

; Adds a new variable/value binding pair into the environment.  Gives an error if the variable already exists in this frame.
(define insert
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (myerror "error: variable is being re-declared:" var)
        (cons (add-to-frame var (box val) (car environment)) (cdr environment)))))

; Changes the binding of a variable to a new value in the environment.  Gives an error if the variable does not exist.
(define update
  (lambda (var val environment)
    (if (exists? var environment)
        ;(update-existing var (box val) environment)
        (update-existing var val environment)
        (myerror "error: variable used but not defined:" var))))

; Add a new variable/value pair to the frame.
(define add-to-frame
  (lambda (var val frame)
    (list (cons var (variables frame)) (cons (scheme->language val) (store frame)))))

; Changes the binding of a variable in the environment to a new value
(define update-existing
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (cons (update-in-frame var val (topframe environment)) (remainingframes environment))
        (cons (topframe environment) (update-existing var val (remainingframes environment))))))

; Changes the binding of a variable in the frame to a new value.
(define update-in-frame
  (lambda (var val frame)
    (list (variables frame) (update-in-frame-store var val (variables frame) (store frame)))))

; Changes a variable binding by placing the new value in the appropriate place in the store
(define update-in-frame-store
  (lambda (var val varlist vallist)
    (cond
      ;((eq? var (car varlist)) (cons (scheme->language val) (cdr vallist)))
      ((eq? var (car varlist)) (begin (set-box! (car vallist) val) vallist))
      (else (cons (car vallist) (update-in-frame-store var val (cdr varlist) (cdr vallist)))))))

; Returns the list of variables from a frame
(define variables
  (lambda (frame)
    (car frame)))

; Returns the store from a frame
(define store
  (lambda (frame)
    (cadr frame)))


; Functions to convert the Scheme #t and #f to our languages true and false, and back.

(define language->scheme
  (lambda (v) 
    (cond 
      ((eq? v 'false) #f)
      ((eq? v 'true) #t)
      (else v))))

(define scheme->language
  (lambda (v)
    (cond
      ((eq? v #f) 'false)
      ((eq? v #t) 'true)
      (else v))))

; Because the error function is not defined in R5RS scheme, I create my own:
(define error-break (lambda (v) v))
(call-with-current-continuation (lambda (k) (set! error-break k)))

(define myerror
  (lambda (str . vals)
    (letrec ((makestr (lambda (str vals)
                        (if (null? vals)
                            str
                            (makestr (string-append str (string-append " " (symbol->string (car vals)))) (cdr vals))))))
      (error-break (display (string-append str (makestr "" vals)))))))