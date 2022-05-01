
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro h,
  intro hnp,
  contradiction,

end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_contradiction hboom,
  contradiction,


end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  {
    intro h,
    by_contradiction hboom,
    contradiction,
  },
  {
    intro h,
    intro hnp,
    contradiction,
  }
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hpq,
  cases hpq with hp hq,
  {
    right,
    assumption

  },
  {
    left,
    assumption,
  }


end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  split,
  {
    cases h,
    assumption
  },
  {
    cases h,
    assumption
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro hp,
  cases h with hnp hq,
  {
    contradiction,  
  },
  {
    assumption,
  }
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro hnp,
  cases h with hp hq,
  {
    contradiction,
  },
  {
    assumption,
  }
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro h,
  intro hq,
  by_cases r : P,
  {
    have hq: Q := h r,
    contradiction,
  },
  {
    assumption,
  }
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro p,
  by_cases r : Q,
  {
    assumption,
  },
  {
    have hnp:¬P := h r,
    contradiction,
  }
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  {
    intro h,
    intro hnq,
    by_contradiction hboom,
    have hq:Q := h hboom,
    contradiction, 
  },
  {
    intro h,
    intro hp,
    by_cases r: Q,
    {
      assumption,
    },
    {
      have hnp:¬P := h r,
      contradiction,
    }
  }
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  by_cases x:P,
  {
    apply h,
    left,
    assumption
  },
  {
    apply h,
    right,
    assumption,
  }

end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  apply np,
  apply h,
  intro p,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hpq,
  intro npq,
  cases npq with np nq,
  cases hpq with hp hq,
  {
    contradiction,
  },
  {
    contradiction,
  }
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hpq,
  intro norpq,
  cases hpq with p q,
  cases norpq with np nq,
  {
    contradiction,
  },
  {
    contradiction,
  }
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro nhpq,
  split,
  {
    intro np,
    apply nhpq,
    left,
    assumption
  },
  {
    intro nq,
    apply nhpq,
    right,
    assumption,

  }
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro cnpq,
  intro porq,
  cases cnpq with np nq,
  cases porq with hp hq,
  {
    contradiction,
  },
  {
    contradiction,
  }
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro nepq,
  by_cases h:P,
  {
    left,
    intro q,
    apply nepq,
    split,
    {
      assumption,
    },
    {
      assumption,
    }
  },
  {
    right,
    assumption,
  }
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nopq,
  intro peq,
  cases peq with p q,
  cases nopq with nq np,
  {
    contradiction,
  },
  {
    contradiction,
  }
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  {
    intro npeq,
    by_cases h:P,
    {
      left,
      intro q,
      apply npeq,
      split,
      {
        assumption,
      },
      {
        assumption,
      }
    },
    {
      right,
      assumption,
    },
    
    
  },
  {
    intro norpq,
    intro peq,
    cases peq with p q,
    cases norpq with np nq,
    {
      contradiction,
    },
    {
      contradiction,
    }
  }
  
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  {
    intro nopq,
    split,
    {
      intro p,
      apply nopq,
      left,
      assumption,
    },
    {
      intro q,
      apply nopq,
      right,
      assumption,
    },
  },
  {
    intro nepq,
    intro pouq,
    cases nepq with np nq,
    cases pouq with p q,
    {
      contradiction,
    },
    {
      contradiction,
    }
  }
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro peqor,
  cases peqor with p qr,
  cases qr with q r,
  {
    left,
    split,
    {
      assumption
    },
    {
      assumption,
    },
  },
  {
    right,
    split,
    {
      assumption,
    },
    {
      assumption,
    }
  }
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peqoper,
  split,
  {
    cases peqoper with peq per,
    {
      cases peq with p q,
      assumption,
    },
    {
      cases per with p r,
      assumption,
    },
  },
  {
    cases peqoper with peq per,
    {
      cases peq with p q,
      left,
      assumption,
    },
    {
      cases per with p r,
      right,
      assumption,

    }
  }
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro poqer,
  split,
  {
    cases poqer with p qer,
    {
      left,
      assumption,
    },
    {
      cases qer with q r,
      right,
      assumption,
    },
  },
  {
    cases poqer with p qer,
    {
      left,
      assumption,
    },
    {
      cases qer with q r,
      right,
      assumption,
    }
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hpoqepor,
  cases hpoqepor with hpoq por,
  cases hpoq with p q,
  {
    left,
    assumption,
  },
  {
    cases por with p r,
    {
      left,
      assumption,
    },
    {
      right,
      split,
      {
        assumption,
      },
      {
        assumption,
      },
    }
  }

end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro peq_tor,
  intro p,
  intro q,
  apply peq_tor,
  split,
  {
    assumption,
  },
  {
    assumption,
  }

end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro p_to_q_to_r,
  intro peq,
  cases peq with p q,
  apply p_to_q_to_r,
  {
    assumption,
  },
  {
    assumption,
  },

end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq with p q,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  {
    intro pep,
    cases pep with p p',
    {
      assumption,
    },
  },
  {
    intro p,
    split,
    {
      assumption,
    },
    {
      assumption,
    },
  }
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  {
    intro pop,
    cases pop with p p',
    {
      assumption
    },
    {
      assumption,
    },
  },
  {
    intro p,
    left,
    assumption,
  }
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro epx,
  intro x,
  by_contradiction hboom,
  apply epx,
  existsi x,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro napx,
  intro nepx,
  cases nepx with t ht,
  exact(napx t) ht,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro epx,
  intro x,
  by_contradiction nPx,
  apply epx,
  existsi x,
  exact nPx,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro epx,
  intro apx,
  cases epx with x npx,
  apply npx,
  apply apx,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  {
  rw contrapositive_law,
  rw doubleneg_law,
  intro epx,
  intro x,
  by_contradiction nPx,
  apply epx,
  existsi x,
  exact nPx,
  },
  {
    intro epx,
    intro apx,
    cases epx with x npx,
    apply npx,
    apply apx,
  }
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  {
    intro epx,
  intro x,
  by_contradiction hboom,
  apply epx,
  existsi x,
  assumption,
  },
  {
    intro napx,
  intro nepx,
  cases nepx with t ht,
  exact(napx t) ht,
  }
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro epx,
  intro apx,
  cases epx with x Px,
  exact(apx x) Px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro apx,
  intro nepx,
  cases nepx with x npx,
  apply npx,
  apply apx,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro nepx,
  intro x,
  by_contradiction hboom,
  apply nepx,
  existsi x,
  exact hboom,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro nepx,
  intro x,
  by_contradiction pboom,
  apply nepx,
  existsi x,
  exact pboom,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  {
    intro apx,
  intro nepx,
  cases nepx with x npx,
  apply npx,
  apply apx,
  },
  {
    intro nepx,
  intro x,
  by_contradiction hboom,
  apply nepx,
  existsi x,
  exact hboom,
  }
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  {
    intro epx,
    intro apx,
    cases epx with x Px,
    exact(apx x) Px,
  },
  {
    rw contrapositive_law,
    rw doubleneg_law,
    intro nepx,
    intro x,
    by_contradiction pboom,
    apply nepx,
    existsi x,
    exact pboom,
  }
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro epq,
  split,
  {
    sorry,
  }
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
