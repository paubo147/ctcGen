import ply.yacc as yacc
import ply.lex as lex
literals=['-', '(', ')', '_']

reserved={
    r"define-fun" : "DEFINE_FUN",
    "BitVec"     : "BITVECTOR",
    "true"       : "TRUE",
    "false"      : "FALSE",
    "model"      : "MODEL",
    "Bool"       : "BOOL",
    "Int"        : "INT",
    "null"       : "NULL",
    r"_"         : "UNDERBAR",
    "-"          : "MINUS",
}

tokens=[
    "LPAR",
    "RPAR",
    "HEX",
    "NUM",
    "ID",
]+list(reserved.values())
t_MINUS=r"\-"
t_LPAR=r"\("
t_RPAR=r"\)"
t_UNDERBAR=r"_"
#t_DEFINE_FUN=r"define\-fun"

t_HEX=r"\#x[0-9a-zA-Z]+"
t_NUM=r"\d+"

t_ignore_COMMENT=r"\;.*\n"
t_ignore=" \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno+=len(t.value)

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

def t_ID(t):
    r"[a-zA-Z_][a-zA-Z0-9_-]*"
    t.type=reserved.get(t.value, "ID")
    return t


#PARSER SECTION
"""
result         : LPAR MODEL fun_defs RPAR
fun_defs       : fun_def fun_defs
               | fun_def
fun_def        : LPAR DEFINE_FUN ID fun_args fun_signature fun_body RPAR
fun_args       : LPAR arglist RPAR 
               | LPAR RPAR
arglist        : LPAR ID type RPAR arglist 
               | LPAR ID type RPAR
fun_signature  : LPAR ID types RPAR 
               | LPAR ID RPAR
types          : type types 
               | type
type           : LPAR ID types RPAR 
               | LPAR UNDERBAR BITVECTOR NUM RPAR 
               | BOOL 
               | ID 
               | INT

fun_body       : LPAR ID plain_literals RPAR

plain_literals : plain_literal plain_literals

plain_literals | HEX 
               | NUM 
               | LPAR MINUS NUM LPAR 
               | LPAR fun_body RPAR 
               | NULL
               | ID

"""

outputs={}

def p_result(p):
    "result : LPAR MODEL fun_defs RPAR"
    p[0]=p[3]

#fun_definitions
def p_fun_defs(p):
    "fun_defs       : fun_def fun_defs"
    p[0]=p[2]
    
def p_fun_defs_term(p):
    "fun_defs : fun_def"
    p[0]=p[1]
    


def p_fun_def(p):
    "fun_def        : LPAR DEFINE_FUN ID fun_args fun_signature fun_body RPAR"
    p[0]=(p[5],p[3],p[6])
    outputs[p[3]]=p[6]

def p_fun_args(p):
    "fun_args : LPAR arglist RPAR"
    

def p_fun_args_none(p):
    "fun_args : LPAR RPAR"

def p_arglist(p):
    "arglist : LPAR ID ID RPAR arglist"
    
def p_arglist_single(p):
    "arglist : LPAR ID ID RPAR"

#Signature
def p_fun_signature(p):
    "fun_signature  : LPAR ID types RPAR"
    p[0]=p[2]

def p_fun_signature_only_id(p):
    "fun_signature  : ID"
    p[0]=p[1]

def p_fun_signature_int(p):
    "fun_signature : INT"
    p[0]=p[1]

def p_types(p):
    "types           : type types"

def p_types_one(p):
    "types : type"


def p_type(p):
    "type           : LPAR ID types RPAR"

def p_type_null(p):
    "type : NULL"

def p_type_int(p):
    "type : INT"
    
def p_type_bv(p):
    "type    : LPAR UNDERBAR BITVECTOR NUM RPAR"

def p_type_bool(p):
    "type : BOOL"


def p_type_enum(p):
    "type : ID"

#function body

#def p_fun_body_single_num(p):
#    "fun_body : NUM"
#    p[0]=p[1] 

#def p_fun_body_single_negative(p):
#    "fun_body : LPAR MINUS NUM RPAR"
#    p[0]="-"+p[3]


#def p_fun_body_single(p):
#    "fun_body : plain_literal"
#    p[0]=p[1]

def p_fun_body(p):
    "fun_body       : LPAR ID plain_literals RPAR"
    p[0]=[p[2]]+p[3]
    
def p_fun_body_neg(p):
    "fun_body : LPAR MINUS NUM RPAR"
    p[0]="-"+p[3]

def p_fun_body_num(p):
    "fun_body : NUM"
    p[0]=p[1]

#def p_fun_body_single_negative(p):
#    "fun_body : LPAR MINUS NUM RPAR"
#    p[0]="-"+p[3]

def p_plain_literal_single(p):
    "plain_literals : plain_literal"
    p[0]=[p[1]]

def p_plain_literals(p):
    "plain_literals : plain_literals plain_literal"
    p[0]=p[1]+[p[2]]


def p_plain_literal_hex(p):
    "plain_literal : HEX"
    p[0]=p[1]

def p_plain_literal_num(p):
    "plain_literal : NUM"
    p[0]=p[1]

def p_plain_literal_neg_num(p):
    "plain_literal : LPAR MINUS NUM RPAR"
    p[0]="-"+p[3]

def p_plain_literal_fun_body(p):
    "plain_literal : fun_body"
    p[0]=p[1]

def p_plain_literal_enum(p):
    "plain_literal : ID"
    p[0]=p[1]

def p_plain_literal_null(p):
    "plain_literal : NULL"
    p[0]=p[1]

def p_plain_literal_bool(p):
    """plain_literal : TRUE 
                     | FALSE"""

    p[0]=p[1]


ip=""
def p_error(p):
    print ip
    print "SMT RESULTPARSER-ERROR: line {0}, value '{1}'".format(p.lineno, p.value)
    exit()


def parse(s):
    global ip
    ip=s
    lexer=lex.lex()  
    #lexer.input(s)
    #while True:
    #    tok=lexer.token()
    #    if not tok: break
    #    print tok
    parser=yacc.yacc()
    
    parser.parse(s)
    return outputs

if __name__=="__main__":
    s='''(model 
  (define-fun PeerIPv4_instance () (PeerIPv4 (IPV4_dt (_ BitVec 8))
                                             Bool
                                             (_ BitVec 32)
                                             (SatelliteInfo_dt Int Int Int Int))
    (mk_PeerIPv4 (mk_IPV4 #xbf #x00 #x00 #x00)
             #x00000000
             false
             (mk_SatelliteInfo 1236 (- 25049) 0 38)))
  (define-fun VRF_instance () (VRF (_ BitVec 32) DIST_dt (IPV4_dt (_ BitVec 8)) AdmState Int Int)
    (mk_VRF #x00000000
        (option_2 #x0000 #x00000000)
        #x00000000
        1
        (- 2147481211)
        (mk_IPV4 #x00 #x00 #x00 #x00)
        AdmState_LOCKED))
)
'''
    lexer=lex.lex()
    parser=yacc.yacc()
    
    lexer.input(s)
    parser.parse(s)
    print outputs

    #while True:
    #    tok=lexer.token()
    #    if not tok: break
    #    print tok
