module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
import StacksCore.Tactic.EgaSgaAttribute

/-! # Comparing topologies through their sheaves

## Main results

* `isSheaf_sup_of_isSheaf`: a presheaf that is a sheaf for `J` and for `J'` is a sheaf for
  `J ⊔ J'`.
* `le_of_sheaves`: if every `J'`-sheaf is a `J`-sheaf then `J ≤ J'`.
* `le_iff_isSheaf_imp_isSheaf`: `J ≤ J'` if and only if every `J'`-sheaf is a `J`-sheaf
  (Stacks 00ZQ).

Tags covered: 00ZQ.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J J' : GrothendieckTopology C)

/-- A presheaf that is a sheaf for both `J` and `J'` is a sheaf for the join `J ⊔ J'`. -/
@[sga "4 IV 9.1.2" "Binary case of d)"]
lemma isSheaf_sup_of_isSheaf (P : Cᵒᵖ ⥤ Type (max u v))
    (hJ : Presieve.IsSheaf J P) (hJ' : Presieve.IsSheaf J' P) :
    Presieve.IsSheaf (J ⊔ J') P := by
  rw [show J ⊔ J' = (J.toCoverage ⊔ J'.toCoverage).toGrothendieck from
        ((Coverage.gi C).l_sup_u _ _).symm, Presieve.isSheaf_sup]
  refine ⟨?_, ?_⟩ <;> rw [(Coverage.gi C).l_u_eq] <;> assumption

/-- If every `J'`-sheaf is a `J`-sheaf, then `J ≤ J'`: indeed `J ⊔ J'` then has the same
sheaves as `J'`, hence equals `J'`. -/
@[sga "4 II 4.4.4" "T = T′", sga "4 IV 9.1.2" "partial"]
lemma le_of_sheaves
    (h : ∀ (P : Cᵒᵖ ⥤ Type (max u v)),
      Presheaf.IsSheaf J' P → Presheaf.IsSheaf J P) :
    J ≤ J' := by
  have key : J ⊔ J' = J' := by
    rw [topology_eq_iff_same_sheaves]
    refine fun P ↦ ⟨fun hP ↦ Presieve.isSheaf_of_le P le_sup_right hP, fun hP ↦ ?_⟩
    exact isSheaf_sup_of_isSheaf J J' P
      ((isSheaf_iff_isSheaf_of_type J P).mp <| h P <| (isSheaf_iff_isSheaf_of_type J' P).mpr hP) hP
  exact key ▸ le_sup_left

/-- **Stacks 00ZQ.** For Grothendieck topologies `J`, `J'` on a category `C`, we have `J ≤ J'`
(every `J`-covering sieve is `J'`-covering) if and only if every sheaf for `J'` is a sheaf
for `J`. -/
@[stacks 00ZQ]
theorem le_iff_isSheaf_imp_isSheaf :
    J ≤ J' ↔
      ∀ (P : Cᵒᵖ ⥤ Type (max u v)),
        Presheaf.IsSheaf J' P → Presheaf.IsSheaf J P :=
  ⟨fun hJJ' _ hP _ _ _ hS ↦ hP _ _ (hJJ' _ hS), le_of_sheaves J J'⟩
