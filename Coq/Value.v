Section Cost.

Require Export System.

  Context {sys_type : SystemType}.

  (** Convenience Aliasing *)
  Definition valueType := ValueType sys_type.
  Inductive Value := mk_value { value_cost: valueType; value_benefit: valueType }.

End Cost.


  
