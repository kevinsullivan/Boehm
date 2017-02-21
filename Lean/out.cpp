#include <iostream>
#include "util/numerics/mpz.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm.h"
#include "library/io_state.h"
#include "init/init.h"

static lean::environment * g_env = nullptr;

namespace lean {
unsigned list_cases_on(lean::vm_obj const & o, lean::buffer<lean::vm_obj> & data);
lean::vm_obj nat_succ(lean::vm_obj const &);
lean::vm_obj put_str(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj nat_to_string(lean::vm_obj const &);
lean::vm_obj nat_decidable_le(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj nat_decidable_eq(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj nat_decidable_lt(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj nat_div(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj nat_mod(lean::vm_obj const &, lean::vm_obj const &);
}

lean::vm_obj main__val_2();
lean::vm_obj string_str(lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj char_sz();
lean::vm_obj char_of_nat(lean::vm_obj const &);
lean::vm_obj string_empty();
lean::vm_obj ___lean__main();
lean::vm_obj put_str_ln__val_2();
lean::vm_obj put_str_ln(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj string_quote__main__val_3();
lean::vm_obj string_quote__main__val_4();
lean::vm_obj list_append__main__rec_2(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj list_append__main(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj char_quote_core__val_10();
lean::vm_obj char_quote_core__val_11();
lean::vm_obj char_quote_core__val_12();
lean::vm_obj char_quote_core__val_13();
lean::vm_obj char_quote_core__val_14();
lean::vm_obj char_quote_core__val_15();
lean::vm_obj char_quote_core__val_16();
lean::vm_obj char_quote_core__val_17();
lean::vm_obj char_quote_core__val_18();
lean::vm_obj fin_decidable_eq__match_1__lambda_2(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj fin_decidable_eq__match_1(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj fin_decidable_eq__main(lean::vm_obj const &, lean::vm_obj const &, lean::vm_obj const &);
lean::vm_obj char_decidable_eq();
lean::vm_obj hex_digit_to_string__val_7();
lean::vm_obj hex_digit_to_string__val_8();
lean::vm_obj hex_digit_to_string__val_9();
lean::vm_obj hex_digit_to_string__val_10();
lean::vm_obj hex_digit_to_string__val_11();
lean::vm_obj hex_digit_to_string__val_12();
lean::vm_obj hex_digit_to_string(lean::vm_obj const &);
lean::vm_obj char_to_hex(lean::vm_obj const &);
lean::vm_obj char_quote_core(lean::vm_obj const &);
lean::vm_obj string_quote_aux__main__rec_2(lean::vm_obj const &);
lean::vm_obj string_quote_aux__main(lean::vm_obj const &);
lean::vm_obj string_quote__main(lean::vm_obj const &);
lean::vm_obj string_quote();
lean::vm_obj string_has_to_string();
int  main() {
     lean::initialize();
     lean::environment env;
     
     lean::name native__ir_compiler__93 = lean::name({"string", "has_to_string"});
     
     env = add_native(env, native__ir_compiler__93, string_has_to_string);
     
     lean::name native__ir_compiler__92 = lean::name({"string", "quote"});
     
     env = add_native(env, native__ir_compiler__92, string_quote);
     
     lean::name native__ir_compiler__91 = lean::name({"string", "quote", "_main"});
     
     env = add_native(env, native__ir_compiler__91, string_quote__main);
     
     lean::name native__ir_compiler__90 = lean::name({"string", "quote_aux", "_main"});
     
     env = add_native(env, native__ir_compiler__90, string_quote_aux__main);
     
     lean::name native__ir_compiler__89 = lean::name({"string", "quote_aux", "_main", "_rec_2"});
     
     env = add_native(env, native__ir_compiler__89, string_quote_aux__main__rec_2);
     
     lean::name native__ir_compiler__88 = lean::name({"char", "quote_core"});
     
     env = add_native(env, native__ir_compiler__88, char_quote_core);
     
     lean::name native__ir_compiler__87 = lean::name({"char_to_hex"});
     
     env = add_native(env, native__ir_compiler__87, char_to_hex);
     
     lean::name native__ir_compiler__86 = lean::name({"hex_digit_to_string"});
     
     env = add_native(env, native__ir_compiler__86, hex_digit_to_string);
     
     lean::name native__ir_compiler__85 = lean::name({"hex_digit_to_string", "_val_12"});
     
     env = add_native(env, native__ir_compiler__85, hex_digit_to_string__val_12);
     
     lean::name native__ir_compiler__84 = lean::name({"hex_digit_to_string", "_val_11"});
     
     env = add_native(env, native__ir_compiler__84, hex_digit_to_string__val_11);
     
     lean::name native__ir_compiler__83 = lean::name({"hex_digit_to_string", "_val_10"});
     
     env = add_native(env, native__ir_compiler__83, hex_digit_to_string__val_10);
     
     lean::name native__ir_compiler__82 = lean::name({"hex_digit_to_string", "_val_9"});
     
     env = add_native(env, native__ir_compiler__82, hex_digit_to_string__val_9);
     
     lean::name native__ir_compiler__81 = lean::name({"hex_digit_to_string", "_val_8"});
     
     env = add_native(env, native__ir_compiler__81, hex_digit_to_string__val_8);
     
     lean::name native__ir_compiler__80 = lean::name({"hex_digit_to_string", "_val_7"});
     
     env = add_native(env, native__ir_compiler__80, hex_digit_to_string__val_7);
     
     lean::name native__ir_compiler__79 = lean::name({"char", "decidable_eq"});
     
     env = add_native(env, native__ir_compiler__79, char_decidable_eq);
     
     lean::name native__ir_compiler__78 = lean::name({"fin", "decidable_eq", "_main"});
     
     env = add_native(env, native__ir_compiler__78, fin_decidable_eq__main);
     
     lean::name native__ir_compiler__77 = lean::name({"fin", "decidable_eq", "_match_1"});
     
     env = add_native(env, native__ir_compiler__77, fin_decidable_eq__match_1);
     
     lean::name native__ir_compiler__76 = lean::name({"fin", "decidable_eq", "_match_1", "_lambda_2"});
     
     env = add_native(env, native__ir_compiler__76, fin_decidable_eq__match_1__lambda_2);
     
     lean::name native__ir_compiler__75 = lean::name({"char", "quote_core", "_val_18"});
     
     env = add_native(env, native__ir_compiler__75, char_quote_core__val_18);
     
     lean::name native__ir_compiler__74 = lean::name({"char", "quote_core", "_val_17"});
     
     env = add_native(env, native__ir_compiler__74, char_quote_core__val_17);
     
     lean::name native__ir_compiler__73 = lean::name({"char", "quote_core", "_val_16"});
     
     env = add_native(env, native__ir_compiler__73, char_quote_core__val_16);
     
     lean::name native__ir_compiler__72 = lean::name({"char", "quote_core", "_val_15"});
     
     env = add_native(env, native__ir_compiler__72, char_quote_core__val_15);
     
     lean::name native__ir_compiler__71 = lean::name({"char", "quote_core", "_val_14"});
     
     env = add_native(env, native__ir_compiler__71, char_quote_core__val_14);
     
     lean::name native__ir_compiler__70 = lean::name({"char", "quote_core", "_val_13"});
     
     env = add_native(env, native__ir_compiler__70, char_quote_core__val_13);
     
     lean::name native__ir_compiler__69 = lean::name({"char", "quote_core", "_val_12"});
     
     env = add_native(env, native__ir_compiler__69, char_quote_core__val_12);
     
     lean::name native__ir_compiler__68 = lean::name({"char", "quote_core", "_val_11"});
     
     env = add_native(env, native__ir_compiler__68, char_quote_core__val_11);
     
     lean::name native__ir_compiler__67 = lean::name({"char", "quote_core", "_val_10"});
     
     env = add_native(env, native__ir_compiler__67, char_quote_core__val_10);
     
     lean::name native__ir_compiler__66 = lean::name({"list", "append", "_main"});
     
     env = add_native(env, native__ir_compiler__66, list_append__main);
     
     lean::name native__ir_compiler__65 = lean::name({"list", "append", "_main", "_rec_2"});
     
     env = add_native(env, native__ir_compiler__65, list_append__main__rec_2);
     
     lean::name native__ir_compiler__64 = lean::name({"string", "quote", "_main", "_val_4"});
     
     env = add_native(env, native__ir_compiler__64, string_quote__main__val_4);
     
     lean::name native__ir_compiler__63 = lean::name({"string", "quote", "_main", "_val_3"});
     
     env = add_native(env, native__ir_compiler__63, string_quote__main__val_3);
     
     lean::name native__ir_compiler__62 = lean::name({"put_str_ln"});
     
     env = add_native(env, native__ir_compiler__62, put_str_ln);
     
     lean::name native__ir_compiler__61 = lean::name({"put_str_ln", "_val_2"});
     
     env = add_native(env, native__ir_compiler__61, put_str_ln__val_2);
     
     lean::name native__ir_compiler__60 = lean::name({"main"});
     
     env = add_native(env, native__ir_compiler__60, ___lean__main);
     
     lean::name native__ir_compiler__59 = lean::name({"string", "empty"});
     
     env = add_native(env, native__ir_compiler__59, string_empty);
     
     lean::name native__ir_compiler__58 = lean::name({"char", "of_nat"});
     
     env = add_native(env, native__ir_compiler__58, char_of_nat);
     
     lean::name native__ir_compiler__57 = lean::name({"char_sz"});
     
     env = add_native(env, native__ir_compiler__57, char_sz);
     
     lean::name native__ir_compiler__56 = lean::name({"string", "str"});
     
     env = add_native(env, native__ir_compiler__56, string_str);
     
     lean::name native__ir_compiler__55 = lean::name({"main", "_val_2"});
     
     env = add_native(env, native__ir_compiler__55, main__val_2);
     
     lean::io_state ios = lean::get_global_ios();
     ;
     lean::options opts = lean::get_options_from_ios(ios);
     ;
     lean::vm_state S(env, opts);
     
     lean::scope_vm_state scoped(S);
     
     g_env = & env;;
     lean::vm_obj native__ir_compiler__94 = lean::mk_vm_simple(0);
     ;
     {
          lean::vm_obj _$local$__native__ir_compiler__95 = ___lean__main();
          ;
          lean::invoke(_$local$__native__ir_compiler__95, native__ir_compiler__94);
          
      };
     
 }lean::vm_obj  string_has_to_string() {
     {
          return string_quote();
      };
 }

lean::vm_obj  string_quote() {
     {
          return lean::mk_native_closure(*g_env, lean::name({"string", "quote", "_main"}),{});
      };
 }

lean::vm_obj  string_quote__main(lean::vm_obj  const &  _$local$__native__ir_compiler__51) {
     {
          lean::vm_obj native__ir_compiler__52 = _$local$__native__ir_compiler__51;
          lean::buffer<lean::vm_obj> buffer;
          
          int ctor_index = lean::list_cases_on(native__ir_compiler__52, buffer);
          ;
          switch (ctor_index){
               
               case 0:{
                    {
                         return string_quote__main__val_3();
                     };
                    break;
                    
                }case 1:{
                    lean::vm_obj _$local$__native__ir_compiler__53 = cfield(native__ir_compiler__52, 0);
                    lean::vm_obj _$local$__native__ir_compiler__54 = cfield(native__ir_compiler__52, 1);
                    lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main"}),{});
                    lean::vm_obj _$local$___anf__4 = lean::mk_vm_simple(0);
                    lean::vm_obj _$local$___anf__5 = string_quote__main__val_4();
                    lean::vm_obj _$local$___anf__6 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main"}),{});
                    lean::vm_obj _$local$___anf__7 = lean::mk_vm_simple(0);
                    lean::vm_obj _$local$___anf__8 = lean::mk_native_closure(*g_env, lean::name({"string", "quote_aux", "_main"}),{});
                    lean::vm_obj _$local$___anf__9 = _$local$__native__ir_compiler__53;
                    lean::vm_obj _$local$___anf__10 = _$local$__native__ir_compiler__54;
                    lean::vm_obj _$local$___anf__11 = lean::mk_vm_constructor(1,{_$local$___anf__9, _$local$___anf__10});
                    lean::vm_obj _$local$___anf__12 = lean::invoke(_$local$___anf__8, _$local$___anf__11);
                    lean::vm_obj _$local$___anf__13 = string_quote__main__val_4();
                    lean::vm_obj _$local$___anf__14 = lean::invoke(_$local$___anf__6, _$local$___anf__7, _$local$___anf__12, _$local$___anf__13);
                    {
                         return lean::invoke(_$local$___anf__3, _$local$___anf__4, _$local$___anf__5, _$local$___anf__14);
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  string_quote_aux__main(lean::vm_obj  const &  _$local$__native__ir_compiler__50) {
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"string", "quote_aux", "_main", "_rec_2"}),{});
     lean::vm_obj _$local$___anf__2 = _$local$__native__ir_compiler__50;
     {
          return lean::invoke(_$local$___anf__1, _$local$___anf__2);
      };
 }

lean::vm_obj  string_quote_aux__main__rec_2(lean::vm_obj  const &  _$local$__native__ir_compiler__46) {
     {
          lean::vm_obj native__ir_compiler__47 = _$local$__native__ir_compiler__46;
          lean::buffer<lean::vm_obj> buffer;
          
          int ctor_index = lean::list_cases_on(native__ir_compiler__47, buffer);
          ;
          switch (ctor_index){
               
               case 0:{
                    {
                         return string_empty();
                     };
                    break;
                    
                }case 1:{
                    lean::vm_obj _$local$__native__ir_compiler__48 = cfield(native__ir_compiler__47, 0);
                    lean::vm_obj _$local$__native__ir_compiler__49 = cfield(native__ir_compiler__47, 1);
                    lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main"}),{});
                    lean::vm_obj _$local$___anf__4 = lean::mk_vm_simple(0);
                    lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "quote_core"}),{});
                    lean::vm_obj _$local$___anf__6 = _$local$__native__ir_compiler__48;
                    lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
                    lean::vm_obj _$local$___anf__8 = lean::mk_native_closure(*g_env, lean::name({"string", "quote_aux", "_main", "_rec_2"}),{});
                    lean::vm_obj _$local$___anf__9 = _$local$__native__ir_compiler__49;
                    lean::vm_obj _$local$___anf__10 = lean::invoke(_$local$___anf__8, _$local$___anf__9);
                    {
                         return lean::invoke(_$local$___anf__3, _$local$___anf__4, _$local$___anf__7, _$local$___anf__10);
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  char_quote_core(lean::vm_obj  const &  _$local$__native__ir_compiler__40) {
     lean::vm_obj _$local$___anf__1 = char_decidable_eq();
     lean::vm_obj _$local$___anf__2 = _$local$__native__ir_compiler__40;
     lean::vm_obj _$local$___anf__3 = char_quote_core__val_10();
     {
          lean::vm_obj native__ir_compiler__41 = lean::invoke(_$local$___anf__1, _$local$___anf__2, _$local$___anf__3);
          int ctor_index = cidx(native__ir_compiler__41);
          ;
          switch (ctor_index){
               
               case 0:{
                    lean::vm_obj _$local$___anf__4 = char_decidable_eq();
                    lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__40;
                    lean::vm_obj _$local$___anf__6 = char_quote_core__val_11();
                    {
                         lean::vm_obj native__ir_compiler__42 = lean::invoke(_$local$___anf__4, _$local$___anf__5, _$local$___anf__6);
                         int ctor_index = cidx(native__ir_compiler__42);
                         ;
                         switch (ctor_index){
                              
                              case 0:{
                                   lean::vm_obj _$local$___anf__7 = char_decidable_eq();
                                   lean::vm_obj _$local$___anf__8 = _$local$__native__ir_compiler__40;
                                   lean::vm_obj _$local$___anf__9 = char_quote_core__val_12();
                                   {
                                        lean::vm_obj native__ir_compiler__43 = lean::invoke(_$local$___anf__7, _$local$___anf__8, _$local$___anf__9);
                                        int ctor_index = cidx(native__ir_compiler__43);
                                        ;
                                        switch (ctor_index){
                                             
                                             case 0:{
                                                  lean::vm_obj _$local$___anf__10 = char_decidable_eq();
                                                  lean::vm_obj _$local$___anf__11 = _$local$__native__ir_compiler__40;
                                                  lean::vm_obj _$local$___anf__12 = char_quote_core__val_13();
                                                  {
                                                       lean::vm_obj native__ir_compiler__44 = lean::invoke(_$local$___anf__10, _$local$___anf__11, _$local$___anf__12);
                                                       int ctor_index = cidx(native__ir_compiler__44);
                                                       ;
                                                       switch (ctor_index){
                                                            
                                                            case 0:{
                                                                 lean::vm_obj _$local$___anf__13 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_le"}),{});
                                                                 lean::vm_obj _$local$___anf__14 = _$local$__native__ir_compiler__40;
                                                                 lean::vm_obj _$local$___anf__15 = lean::mk_vm_nat(31);
                                                                 {
                                                                      lean::vm_obj native__ir_compiler__45 = lean::invoke(_$local$___anf__13, _$local$___anf__14, _$local$___anf__15);
                                                                      int ctor_index = cidx(native__ir_compiler__45);
                                                                      ;
                                                                      switch (ctor_index){
                                                                           
                                                                           case 0:{
                                                                                lean::vm_obj _$local$___anf__16 = _$local$__native__ir_compiler__40;
                                                                                lean::vm_obj _$local$___anf__17 = lean::mk_vm_simple(0);
                                                                                {
                                                                                     return lean::mk_vm_constructor(1,{_$local$___anf__16, _$local$___anf__17});
                                                                                 };
                                                                                break;
                                                                                
                                                                            }case 1:{
                                                                                lean::vm_obj _$local$___anf__16 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main"}),{});
                                                                                lean::vm_obj _$local$___anf__17 = lean::mk_vm_simple(0);
                                                                                lean::vm_obj _$local$___anf__18 = lean::mk_native_closure(*g_env, lean::name({"char_to_hex"}),{});
                                                                                lean::vm_obj _$local$___anf__19 = _$local$__native__ir_compiler__40;
                                                                                lean::vm_obj _$local$___anf__20 = lean::invoke(_$local$___anf__18, _$local$___anf__19);
                                                                                lean::vm_obj _$local$___anf__21 = char_quote_core__val_14();
                                                                                {
                                                                                     return lean::invoke(_$local$___anf__16, _$local$___anf__17, _$local$___anf__20, _$local$___anf__21);
                                                                                 };
                                                                                break;
                                                                                
                                                                            }default:{
                                                                                throw std::runtime_error("default case should never be reached");;
                                                                            }
                                                                       }
                                                                      
                                                                  };
                                                                 break;
                                                                 
                                                             }case 1:{
                                                                 {
                                                                      return char_quote_core__val_15();
                                                                  };
                                                                 break;
                                                                 
                                                             }default:{
                                                                 throw std::runtime_error("default case should never be reached");;
                                                             }
                                                        }
                                                       
                                                   };
                                                  break;
                                                  
                                              }case 1:{
                                                  {
                                                       return char_quote_core__val_16();
                                                   };
                                                  break;
                                                  
                                              }default:{
                                                  throw std::runtime_error("default case should never be reached");;
                                              }
                                         }
                                        
                                    };
                                   break;
                                   
                               }case 1:{
                                   {
                                        return char_quote_core__val_17();
                                    };
                                   break;
                                   
                               }default:{
                                   throw std::runtime_error("default case should never be reached");;
                               }
                          }
                         
                     };
                    break;
                    
                }case 1:{
                    {
                         return char_quote_core__val_18();
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  char_to_hex(lean::vm_obj  const &  _$local$__native__ir_compiler__39) {
     lean::vm_obj _$local$___anf__1 = _$local$__native__ir_compiler__39;
     lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"nat", "div"}),{});
     lean::vm_obj _$local$___anf__4 = _$local$___anf__1;
     lean::vm_obj _$local$___anf__5 = lean::mk_vm_nat(16);
     lean::vm_obj _$local$___anf__2 = lean::invoke(_$local$___anf__3, _$local$___anf__4, _$local$___anf__5);
     lean::vm_obj _$local$___anf__7 = lean::mk_native_closure(*g_env, lean::name({"nat", "mod"}),{});
     lean::vm_obj _$local$___anf__8 = _$local$___anf__1;
     lean::vm_obj _$local$___anf__9 = lean::mk_vm_nat(16);
     lean::vm_obj _$local$___anf__6 = lean::invoke(_$local$___anf__7, _$local$___anf__8, _$local$___anf__9);
     lean::vm_obj _$local$___anf__10 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main"}),{});
     lean::vm_obj _$local$___anf__11 = lean::mk_vm_simple(0);
     lean::vm_obj _$local$___anf__12 = lean::mk_native_closure(*g_env, lean::name({"hex_digit_to_string"}),{});
     lean::vm_obj _$local$___anf__13 = _$local$___anf__6;
     lean::vm_obj _$local$___anf__14 = lean::invoke(_$local$___anf__12, _$local$___anf__13);
     lean::vm_obj _$local$___anf__15 = lean::mk_native_closure(*g_env, lean::name({"hex_digit_to_string"}),{});
     lean::vm_obj _$local$___anf__16 = _$local$___anf__2;
     lean::vm_obj _$local$___anf__17 = lean::invoke(_$local$___anf__15, _$local$___anf__16);
     {
          return lean::invoke(_$local$___anf__10, _$local$___anf__11, _$local$___anf__14, _$local$___anf__17);
      };
 }

lean::vm_obj  hex_digit_to_string(lean::vm_obj  const &  _$local$__native__ir_compiler__32) {
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_le"}),{});
     lean::vm_obj _$local$___anf__2 = _$local$__native__ir_compiler__32;
     lean::vm_obj _$local$___anf__3 = lean::mk_vm_nat(9);
     {
          lean::vm_obj native__ir_compiler__33 = lean::invoke(_$local$___anf__1, _$local$___anf__2, _$local$___anf__3);
          int ctor_index = cidx(native__ir_compiler__33);
          ;
          switch (ctor_index){
               
               case 0:{
                    lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
                    lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__32;
                    lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(10);
                    {
                         lean::vm_obj native__ir_compiler__34 = lean::invoke(_$local$___anf__4, _$local$___anf__5, _$local$___anf__6);
                         int ctor_index = cidx(native__ir_compiler__34);
                         ;
                         switch (ctor_index){
                              
                              case 0:{
                                   lean::vm_obj _$local$___anf__7 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
                                   lean::vm_obj _$local$___anf__8 = _$local$__native__ir_compiler__32;
                                   lean::vm_obj _$local$___anf__9 = lean::mk_vm_nat(11);
                                   {
                                        lean::vm_obj native__ir_compiler__35 = lean::invoke(_$local$___anf__7, _$local$___anf__8, _$local$___anf__9);
                                        int ctor_index = cidx(native__ir_compiler__35);
                                        ;
                                        switch (ctor_index){
                                             
                                             case 0:{
                                                  lean::vm_obj _$local$___anf__10 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
                                                  lean::vm_obj _$local$___anf__11 = _$local$__native__ir_compiler__32;
                                                  lean::vm_obj _$local$___anf__12 = lean::mk_vm_nat(12);
                                                  {
                                                       lean::vm_obj native__ir_compiler__36 = lean::invoke(_$local$___anf__10, _$local$___anf__11, _$local$___anf__12);
                                                       int ctor_index = cidx(native__ir_compiler__36);
                                                       ;
                                                       switch (ctor_index){
                                                            
                                                            case 0:{
                                                                 lean::vm_obj _$local$___anf__13 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
                                                                 lean::vm_obj _$local$___anf__14 = _$local$__native__ir_compiler__32;
                                                                 lean::vm_obj _$local$___anf__15 = lean::mk_vm_nat(13);
                                                                 {
                                                                      lean::vm_obj native__ir_compiler__37 = lean::invoke(_$local$___anf__13, _$local$___anf__14, _$local$___anf__15);
                                                                      int ctor_index = cidx(native__ir_compiler__37);
                                                                      ;
                                                                      switch (ctor_index){
                                                                           
                                                                           case 0:{
                                                                                lean::vm_obj _$local$___anf__16 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
                                                                                lean::vm_obj _$local$___anf__17 = _$local$__native__ir_compiler__32;
                                                                                lean::vm_obj _$local$___anf__18 = lean::mk_vm_nat(14);
                                                                                {
                                                                                     lean::vm_obj native__ir_compiler__38 = lean::invoke(_$local$___anf__16, _$local$___anf__17, _$local$___anf__18);
                                                                                     int ctor_index = cidx(native__ir_compiler__38);
                                                                                     ;
                                                                                     switch (ctor_index){
                                                                                          
                                                                                          case 0:{
                                                                                               {
                                                                                                    return hex_digit_to_string__val_7();
                                                                                                };
                                                                                               break;
                                                                                               
                                                                                           }case 1:{
                                                                                               {
                                                                                                    return hex_digit_to_string__val_8();
                                                                                                };
                                                                                               break;
                                                                                               
                                                                                           }default:{
                                                                                               throw std::runtime_error("default case should never be reached");;
                                                                                           }
                                                                                      }
                                                                                     
                                                                                 };
                                                                                break;
                                                                                
                                                                            }case 1:{
                                                                                {
                                                                                     return hex_digit_to_string__val_9();
                                                                                 };
                                                                                break;
                                                                                
                                                                            }default:{
                                                                                throw std::runtime_error("default case should never be reached");;
                                                                            }
                                                                       }
                                                                      
                                                                  };
                                                                 break;
                                                                 
                                                             }case 1:{
                                                                 {
                                                                      return hex_digit_to_string__val_10();
                                                                  };
                                                                 break;
                                                                 
                                                             }default:{
                                                                 throw std::runtime_error("default case should never be reached");;
                                                             }
                                                        }
                                                       
                                                   };
                                                  break;
                                                  
                                              }case 1:{
                                                  {
                                                       return hex_digit_to_string__val_11();
                                                   };
                                                  break;
                                                  
                                              }default:{
                                                  throw std::runtime_error("default case should never be reached");;
                                              }
                                         }
                                        
                                    };
                                   break;
                                   
                               }case 1:{
                                   {
                                        return hex_digit_to_string__val_12();
                                    };
                                   break;
                                   
                               }default:{
                                   throw std::runtime_error("default case should never be reached");;
                               }
                          }
                         
                     };
                    break;
                    
                }case 1:{
                    lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"nat", "to_string"}),{});
                    lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__32;
                    {
                         return lean::invoke(_$local$___anf__4, _$local$___anf__5);
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  hex_digit_to_string__val_12() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(97);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  hex_digit_to_string__val_11() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(98);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  hex_digit_to_string__val_10() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(99);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  hex_digit_to_string__val_9() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(100);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  hex_digit_to_string__val_8() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(101);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  hex_digit_to_string__val_7() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(102);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  char_decidable_eq() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"fin", "decidable_eq", "_main"}),{});
     lean::vm_obj _$local$___anf__1 = char_sz();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  fin_decidable_eq__main(lean::vm_obj  const &  _$local$__native__ir_compiler__29, lean::vm_obj  const &  _$local$__native__ir_compiler__30, lean::vm_obj  const &  _$local$__native__ir_compiler__31) {
     lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"fin", "decidable_eq", "_match_1"}),{});
     lean::vm_obj _$local$___anf__4 = _$local$__native__ir_compiler__29;
     lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__30;
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_simple(0);
     lean::vm_obj _$local$___anf__7 = _$local$__native__ir_compiler__31;
     lean::vm_obj _$local$___anf__8 = lean::mk_vm_simple(0);
     lean::vm_obj _$local$___anf__9 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_eq"}),{});
     lean::vm_obj _$local$___anf__10 = _$local$__native__ir_compiler__30;
     lean::vm_obj _$local$___anf__11 = _$local$__native__ir_compiler__31;
     lean::vm_obj _$local$___anf__12 = lean::invoke(_$local$___anf__9, _$local$___anf__10, _$local$___anf__11);
     {
          return lean::invoke(_$local$___anf__3, _$local$___anf__4, _$local$___anf__5, _$local$___anf__6, _$local$___anf__7, _$local$___anf__8, _$local$___anf__12);
      };
 }

lean::vm_obj  fin_decidable_eq__match_1(lean::vm_obj  const &  _$local$__native__ir_compiler__22, lean::vm_obj  const &  _$local$__native__ir_compiler__23, lean::vm_obj  const &  _$local$__native__ir_compiler__24, lean::vm_obj  const &  _$local$__native__ir_compiler__25, lean::vm_obj  const &  _$local$__native__ir_compiler__26, lean::vm_obj  const &  _$local$__native__ir_compiler__27) {
     {
          lean::vm_obj native__ir_compiler__28 = _$local$__native__ir_compiler__27;
          int ctor_index = cidx(native__ir_compiler__28);
          ;
          switch (ctor_index){
               
               case 0:{
                    {
                         return lean::mk_vm_simple(0);
                     };
                    break;
                    
                }case 1:{
                    {
                         return lean::mk_vm_constructor(1,{});
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  fin_decidable_eq__match_1__lambda_2(lean::vm_obj  const &  _$local$__native__ir_compiler__16, lean::vm_obj  const &  _$local$__native__ir_compiler__17, lean::vm_obj  const &  _$local$__native__ir_compiler__18, lean::vm_obj  const &  _$local$__native__ir_compiler__19, lean::vm_obj  const &  _$local$__native__ir_compiler__20, lean::vm_obj  const &  _$local$__native__ir_compiler__21) {
     {
          return lean::mk_vm_simple(0);
      };
 }

lean::vm_obj  char_quote_core__val_18() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(110);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  char_quote_core__val_17() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(116);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  char_quote_core__val_16() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  char_quote_core__val_15() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(34);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  char_quote_core__val_14() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(120);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(92);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  char_quote_core__val_13() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(34);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  char_quote_core__val_12() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(92);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  char_quote_core__val_11() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(9);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  char_quote_core__val_10() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(10);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  list_append__main(lean::vm_obj  const &  _$local$__native__ir_compiler__13, lean::vm_obj  const &  _$local$__native__ir_compiler__14, lean::vm_obj  const &  _$local$__native__ir_compiler__15) {
     lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main", "_rec_2"}),{});
     lean::vm_obj _$local$___anf__4 = lean::mk_vm_simple(0);
     lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__14;
     lean::vm_obj _$local$___anf__6 = _$local$__native__ir_compiler__15;
     {
          return lean::invoke(_$local$___anf__3, _$local$___anf__4, _$local$___anf__5, _$local$___anf__6);
      };
 }

lean::vm_obj  list_append__main__rec_2(lean::vm_obj  const &  _$local$__native__ir_compiler__7, lean::vm_obj  const &  _$local$__native__ir_compiler__8, lean::vm_obj  const &  _$local$__native__ir_compiler__9) {
     {
          lean::vm_obj native__ir_compiler__10 = _$local$__native__ir_compiler__8;
          lean::buffer<lean::vm_obj> buffer;
          
          int ctor_index = lean::list_cases_on(native__ir_compiler__10, buffer);
          ;
          switch (ctor_index){
               
               case 0:{
                    {
                         return _$local$__native__ir_compiler__9;
                     };
                    break;
                    
                }case 1:{
                    lean::vm_obj _$local$__native__ir_compiler__11 = cfield(native__ir_compiler__10, 0);
                    lean::vm_obj _$local$__native__ir_compiler__12 = cfield(native__ir_compiler__10, 1);
                    lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__11;
                    lean::vm_obj _$local$___anf__6 = lean::mk_native_closure(*g_env, lean::name({"list", "append", "_main", "_rec_2"}),{});
                    lean::vm_obj _$local$___anf__7 = lean::mk_vm_simple(0);
                    lean::vm_obj _$local$___anf__8 = _$local$__native__ir_compiler__12;
                    lean::vm_obj _$local$___anf__9 = _$local$__native__ir_compiler__9;
                    lean::vm_obj _$local$___anf__10 = lean::invoke(_$local$___anf__6, _$local$___anf__7, _$local$___anf__8, _$local$___anf__9);
                    {
                         return lean::mk_vm_constructor(1,{_$local$___anf__5, _$local$___anf__10});
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  string_quote__main__val_4() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(34);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = string_empty();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__4);
      };
 }

lean::vm_obj  string_quote__main__val_3() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(34);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(34);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = string_empty();
     lean::vm_obj _$local$___anf__9 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__8);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__9);
      };
 }

lean::vm_obj  put_str_ln(lean::vm_obj  const &  _$local$__native__ir_compiler__4, lean::vm_obj  const &  _$local$__native__ir_compiler__5, lean::vm_obj  const &  _$local$__native__ir_compiler__6) {
     lean::vm_obj _$local$___anf__3 = lean::mk_native_closure(*g_env, lean::name({"put_str"}),{});
     lean::vm_obj _$local$___anf__4 = put_str_ln__val_2();
     lean::vm_obj _$local$___anf__5 = _$local$__native__ir_compiler__5;
     lean::vm_obj _$local$___anf__6 = _$local$__native__ir_compiler__6;
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = lean::mk_vm_constructor(1,{_$local$___anf__4, _$local$___anf__7});
     {
          return lean::invoke(_$local$___anf__3, _$local$___anf__8);
      };
 }

lean::vm_obj  put_str_ln__val_2() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(10);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  ___lean__main() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"put_str_ln"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_simple(0);
     lean::vm_obj _$local$___anf__2 = string_has_to_string();
     lean::vm_obj _$local$___anf__3 = main__val_2();
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1, _$local$___anf__2, _$local$___anf__3);
      };
 }

lean::vm_obj  string_empty() {
     {
          return lean::mk_vm_simple(0);
      };
 }

lean::vm_obj  char_of_nat(lean::vm_obj  const &  _$local$__native__ir_compiler__2) {
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"nat", "decidable_lt"}),{});
     lean::vm_obj _$local$___anf__2 = _$local$__native__ir_compiler__2;
     lean::vm_obj _$local$___anf__3 = char_sz();
     {
          lean::vm_obj native__ir_compiler__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2, _$local$___anf__3);
          int ctor_index = cidx(native__ir_compiler__3);
          ;
          switch (ctor_index){
               
               case 0:{
                    {
                         return lean::mk_vm_simple(0);
                     };
                    break;
                    
                }case 1:{
                    {
                         return _$local$__native__ir_compiler__2;
                     };
                    break;
                    
                }default:{
                    throw std::runtime_error("default case should never be reached");;
                }
           }
          
      };
 }

lean::vm_obj  char_sz() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"nat", "succ"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_vm_nat(255);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__1);
      };
 }

lean::vm_obj  string_str(lean::vm_obj  const &  _$local$__native__ir_compiler__0, lean::vm_obj  const &  _$local$__native__ir_compiler__1) {
     lean::vm_obj _$local$___anf__2 = _$local$__native__ir_compiler__0;
     lean::vm_obj _$local$___anf__3 = _$local$__native__ir_compiler__1;
     {
          return lean::mk_vm_constructor(1,{_$local$___anf__2, _$local$___anf__3});
      };
 }

lean::vm_obj  main__val_2() {
     lean::vm_obj _$local$___anf__0 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__1 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__2 = lean::mk_vm_nat(33);
     lean::vm_obj _$local$___anf__3 = lean::invoke(_$local$___anf__1, _$local$___anf__2);
     lean::vm_obj _$local$___anf__4 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__5 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__6 = lean::mk_vm_nat(110);
     lean::vm_obj _$local$___anf__7 = lean::invoke(_$local$___anf__5, _$local$___anf__6);
     lean::vm_obj _$local$___anf__8 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__9 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__10 = lean::mk_vm_nat(97);
     lean::vm_obj _$local$___anf__11 = lean::invoke(_$local$___anf__9, _$local$___anf__10);
     lean::vm_obj _$local$___anf__12 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__13 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__14 = lean::mk_vm_nat(101);
     lean::vm_obj _$local$___anf__15 = lean::invoke(_$local$___anf__13, _$local$___anf__14);
     lean::vm_obj _$local$___anf__16 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__17 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__18 = lean::mk_vm_nat(76);
     lean::vm_obj _$local$___anf__19 = lean::invoke(_$local$___anf__17, _$local$___anf__18);
     lean::vm_obj _$local$___anf__20 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__21 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__22 = lean::mk_vm_nat(32);
     lean::vm_obj _$local$___anf__23 = lean::invoke(_$local$___anf__21, _$local$___anf__22);
     lean::vm_obj _$local$___anf__24 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__25 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__26 = lean::mk_vm_nat(111);
     lean::vm_obj _$local$___anf__27 = lean::invoke(_$local$___anf__25, _$local$___anf__26);
     lean::vm_obj _$local$___anf__28 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__29 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__30 = lean::mk_vm_nat(108);
     lean::vm_obj _$local$___anf__31 = lean::invoke(_$local$___anf__29, _$local$___anf__30);
     lean::vm_obj _$local$___anf__32 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__33 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__34 = lean::mk_vm_nat(108);
     lean::vm_obj _$local$___anf__35 = lean::invoke(_$local$___anf__33, _$local$___anf__34);
     lean::vm_obj _$local$___anf__36 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__37 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__38 = lean::mk_vm_nat(101);
     lean::vm_obj _$local$___anf__39 = lean::invoke(_$local$___anf__37, _$local$___anf__38);
     lean::vm_obj _$local$___anf__40 = lean::mk_native_closure(*g_env, lean::name({"string", "str"}),{});
     lean::vm_obj _$local$___anf__41 = lean::mk_native_closure(*g_env, lean::name({"char", "of_nat"}),{});
     lean::vm_obj _$local$___anf__42 = lean::mk_vm_nat(72);
     lean::vm_obj _$local$___anf__43 = lean::invoke(_$local$___anf__41, _$local$___anf__42);
     lean::vm_obj _$local$___anf__44 = string_empty();
     lean::vm_obj _$local$___anf__45 = lean::invoke(_$local$___anf__40, _$local$___anf__43, _$local$___anf__44);
     lean::vm_obj _$local$___anf__46 = lean::invoke(_$local$___anf__36, _$local$___anf__39, _$local$___anf__45);
     lean::vm_obj _$local$___anf__47 = lean::invoke(_$local$___anf__32, _$local$___anf__35, _$local$___anf__46);
     lean::vm_obj _$local$___anf__48 = lean::invoke(_$local$___anf__28, _$local$___anf__31, _$local$___anf__47);
     lean::vm_obj _$local$___anf__49 = lean::invoke(_$local$___anf__24, _$local$___anf__27, _$local$___anf__48);
     lean::vm_obj _$local$___anf__50 = lean::invoke(_$local$___anf__20, _$local$___anf__23, _$local$___anf__49);
     lean::vm_obj _$local$___anf__51 = lean::invoke(_$local$___anf__16, _$local$___anf__19, _$local$___anf__50);
     lean::vm_obj _$local$___anf__52 = lean::invoke(_$local$___anf__12, _$local$___anf__15, _$local$___anf__51);
     lean::vm_obj _$local$___anf__53 = lean::invoke(_$local$___anf__8, _$local$___anf__11, _$local$___anf__52);
     lean::vm_obj _$local$___anf__54 = lean::invoke(_$local$___anf__4, _$local$___anf__7, _$local$___anf__53);
     {
          return lean::invoke(_$local$___anf__0, _$local$___anf__3, _$local$___anf__54);
      };
 }



