import ply.yacc as yacc
import ply.lex as lex
reserved={
    r"define-fun" : "DEFINE_FUN",
    "BitVec"     : "BITVECTOR",
    "true"       : "TRUE",
    "false"      : "FALSE",
    "model"      : "MODEL",
    "Bool"       : "BOOL",
    "Int"        : "INT"
}

tokens=[
    "UNDERBAR",
    "MINUS",
    "HEX",
    "NUM",
    "ID",
    #"DEFINE_FUN",
    "LPAR",
    "RPAR",
]+list(reserved.values())

t_MINUS=r"\-"
t_LPAR=r"\("
t_RPAR=r"\)"
t_UNDERBAR=r"_"
#t_DEFINE_FUN=r"define\-fun"

t_HEX=r"\#x[0-9a-zA-Z]+"
t_NUM=r"\d+"

t_ignore_COMMENT=r"\;.*"
t_ignore=" \t\n"

def t_ID(t):
    r"[a-zA-Z][a-zA-Z0-9_-]*"
    
    t.type=reserved.get(t.value, "ID")
    return t

def t_newline(t):
    r'\n+'
    t.lexer.lineno+=len(t.value)

def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

#PARSER SECTION
"""
result         : LPAR MODEL fun_defs RPAR
fun_defs       : fun_def fun_defs
               | fun_def
fun_def        : LPAR DEFINE_FUN ID fun_args fun_signature fun_body RPAR
fun_args       : LPAR arglist RPAR 
               | LPAR RPAR
arglist        : LPAR ID ID RPAR arglist 
               | LPAR ID ID RPAR
fun_signature  : LPAR ID types RPAR
types          : type types 
               | type
type           : LPAR ID type RPAR 
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
               | ID

"""

outputs=[]


def p_result(p):
    "result : LPAR MODEL fun_defs RPAR"
    p[0]=p[3]

#fun_definitions
def p_fun_defs(p):
    "fun_defs       : fun_def fun_defs"
    outputs.append(p[1])
    p[0]=p[2]
    
def p_fun_defs_term(p):
    "fun_defs : fun_def"
    outputs.append(p[1])


def p_fun_def(p):
    "fun_def        : LPAR DEFINE_FUN ID fun_args fun_signature fun_body RPAR"
    p[0]=p[3]
    
#fun args
def p_fun_args(p):
    "fun_args       : LPAR arglist RPAR"
    p[0]=p[2]

def p_fun_args_none(p):
    "fun_args  : LPAR RPAR"
    print "no function arguments"

def p_fun_arglist(p):
    "arglist        : LPAR ID ID RPAR arglist"
    print "arglist"

def p_fun_arglist_none(p):
    "arglist : LPAR ID ID RPAR"
    print "no arglist"

#Signature
def p_fun_signature(p):
    "fun_signature  : LPAR ID types RPAR"
    print "signature"

def p_types(p):
    "types           : type types"
    print "types"

def p_types_one(p):
    "types : type"
    print "type"

def p_type(p):
    "type           : LPAR ID type RPAR"

def p_type_int(p):
    "type : INT"
    print "INT:", p[1]
    
def p_type_bv(p):
    "type    : LPAR UNDERBAR BITVECTOR NUM RPAR"
    print "bitvector ",p[4]

def p_type_bool(p):
    "type : BOOL"
    print "bool"

def p_type_enum(p):
    "type : ID"
    print "enum", p[1]


#function body 
def p_fun_body(p):
    "fun_body       : LPAR ID plain_literals RPAR"
    line=p.lineno(2)
    index=p.lexpos(2)
    print "body: ",p[2]
    
def p_plain_literals(p):
    "plain_literals : plain_literal plain_literals"
    
def p_plain_literal_single(p):
    "plain_literals : plain_literal"

def p_plain_literal_hex(p):
    "plain_literal : HEX"
    print "HEX ", p[1]

def p_plain_literal_num(p):
    "plain_literal : NUM"
    print "NUM ", p[1]

def p_plain_literal_neg_num(p):
    "plain_literal : LPAR MINUS NUM RPAR"
    print "-",p[3]

def p_plain_literal_fun_body(p):
    "plain_literal : fun_body"
    print "function body"

def p_plain_literal_enum(p):
    "plain_literal : ID"
    print "ENUM:", p[1]

def p_plain_literal_bool(p):
    """plain_literal : FALSE"""
    print "BOOL:", p[1]

def p_error(p):
    print "ERROR:",p

if __name__=="__main__":
    s=""" (model 
  (define-fun vRF_instance () (VRF (_ BitVec 32) (_ BitVec 32) (IPV4_dt (_ BitVec 8)) AdmState Int Int)
    (mk_VRF #x00000000
        #x00000000
        #x00000000
        39
        (- 2147475929)
        (mk_IPV4 #x9f #x00 #x00 #x00) AdmState_LOCKED))
  (define-fun peerIPv4_instance () (PeerIPv4 Bool (_ BitVec 32) (IPV4_dt (_ BitVec 8)))
    (mk_PeerIPv4 (mk_IPV4 #x9f #x01 #x00 #x00) #x00000000 false))
)
"""
    lexer=lex.lex()
    parser=yacc.yacc()
    
    #lexer.input(s)
    result=parser.parse(s)
    print outputs

    #while True:
    #    tok=lexer.token()
    #    if not tok: break
    #    print tok
