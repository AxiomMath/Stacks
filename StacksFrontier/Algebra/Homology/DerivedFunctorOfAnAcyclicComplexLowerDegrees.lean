module

public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex

/-!
# A left exact functor and the cohomology of an acyclic complex, one degree at a time

`Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic`
(`StacksFrontier/Algebra/Homology/DerivedFunctorOfAnAcyclicComplex.lean`) says that a left exact
functor `T` commutes with the cohomology of a complex `K` of `T`-acyclic objects whose
cohomology is `T`-acyclic in every degree.  An induction on the degree cannot use that form: at
stage `n` the acyclicity of `Hⁿ K` is the very thing being proved.  This file proves the
comparison in degree `n` from the acyclicity of the cohomology in the degrees strictly below
`n`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.shortExact_map_of_acyclic_X₁`: a short exact sequence
  stays short exact under `T` as soon as its first term is `T`-acyclic.
* `Stacks.Cohomology.RightDerivedCoEdge.acyclic_cycles_of_le` and
  `Stacks.Cohomology.RightDerivedCoEdge.acyclic_boundaries_of_le`: the cycles in degree `n` and
  the boundaries out of degree `n` are `T`-acyclic as soon as the cohomology is `T`-acyclic in
  every degree `≤ n`.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic_lt` and
  `Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclicLt`: **a left exact
  functor commutes with the cohomology of a complex of acyclic objects in degree `n` as soon as
  the cohomology is acyclic in the degrees strictly below `n`.**
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Stacks.RightDerivedComp

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E]

variable [EnoughInjectives D] (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T]

variable (K : CochainComplex D ℕ) (hX : ∀ q, acyclic T (K.X q))

/-- **A short exact sequence stays short exact under a left exact functor as soon as its first
term is acyclic.**  Only `T`-acyclicity of `S.X₁` is used: left exactness supplies the
monomorphism and the exactness in the middle, and the vanishing of `R¹T` on `S.X₁` supplies the
epimorphism.

`Stacks.RightDerivedComp.acyclic_shortExact_X₂` has the same short-exactness in its conclusion
but asks for two of the three terms to be acyclic, because it also concludes that the middle
term is.  That extra hypothesis is what makes the degeneration below need the cohomology in the
degree it is read at, and dropping it is what lets an induction on the degree close. -/
lemma shortExact_map_of_acyclic_X₁ (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : acyclic T S.X₁) : (S.map T).ShortExact := by
  let _ := HasDerivedCategory.standard D
  let _ := HasDerivedCategory.standard E
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono T).1 inferInstance S hS
  exact
    { exact := h.1
      mono_f := h.2
      epi_g := Functor.epi_map_g T hS
        (((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus T S.X₁).2
          inferInstance).1 ((rightAcyclic_iff_acyclic T S.X₁).2 h₁) 1 one_pos) }

include hX in
/-- **The cycles in degree `n` are `T`-acyclic as soon as the cohomology is `T`-acyclic in every
degree `≤ n`.**  This is `Stacks.Cohomology.RightDerivedCoEdge.acyclic_cycles` with the
cohomology hypothesis restricted to the degrees that the induction actually consumes. -/
lemma acyclic_cycles_of_le :
    ∀ (n : ℕ), (∀ q ≤ n, acyclic T (K.homology q)) → acyclic T (K.cycles n)
  | 0, hH' => acyclic_of_iso T (CochainComplex.isoHomologyπ₀ K).symm (hH' 0 le_rfl)
  | n + 1, hH' =>
    (acyclic_shortExact_X₂ T _ (shortExact_boundaries K n (n + 1) rfl)
      (acyclic_shortExact T _ (shortExact_cycles K n)
        (acyclic_cycles_of_le n fun q hq => hH' q (hq.trans (Nat.le_succ n))) (hX n)).1
      (hH' (n + 1) le_rfl)).1

include hX in
/-- **The boundaries out of degree `n` are `T`-acyclic as soon as the cohomology is `T`-acyclic
in every degree `≤ n`**, and `T` keeps their presentation as a quotient of `Kⁿ` exact. -/
lemma acyclic_boundaries_of_le (n : ℕ) (hH' : ∀ q ≤ n, acyclic T (K.homology q)) :
    acyclic T (cokernel (K.iCycles n)) ∧ Epi (T.map (cokernel.π (K.iCycles n))) :=
  have h := acyclic_shortExact T _ (shortExact_cycles K n)
    (acyclic_cycles_of_le T K hX n hH') (hX n)
  ⟨h.1, h.2.epi_g⟩

include hX in
/-- **A left exact functor commutes with the cohomology of a complex of acyclic objects in
degree `n` as soon as the cohomology is acyclic in the degrees strictly below `n`.**

The cohomology in degree `n` itself is *not* assumed, and in degree zero nothing is.  What the
comparison needs is that `T` keep `0 ⟶ Bⁿ ⟶ Zⁿ ⟶ Hⁿ ⟶ 0` short exact, and by
`Stacks.Cohomology.RightDerivedCoEdge.shortExact_map_of_acyclic_X₁` that is the acyclicity of
`Bⁿ` alone, which `Stacks.Cohomology.RightDerivedCoEdge.acyclic_boundaries_of_le` gets from the
cohomology in degrees `< n`.

This is the form the degeneration has to take to be usable in an induction on the degree, where
acyclicity of `Hⁿ` is the very thing being proved at stage `n`. -/
theorem isIso_homologyToMapHomology_of_acyclic_lt (n : ℕ)
    (hH' : ∀ q < n, acyclic T (K.homology q)) :
    IsIso (homologyToMapHomology T K n) := by
  obtain _ | n := n
  · exact isIso_homologyToMapHomology_zero T K
  · obtain ⟨hB, hepi⟩ :=
      acyclic_boundaries_of_le T K hX n fun q hq => hH' q (Nat.lt_succ_of_le hq)
    have hTH : IsColimit (CokernelCofork.ofπ (T.map (K.homologyπ (n + 1)))
        (show T.map (boundariesToCycles K n (n + 1)) ≫ T.map (K.homologyπ (n + 1)) = 0 by
          rw [← T.map_comp, boundariesToCycles_comp_homologyπ, T.map_zero])) :=
      (shortExact_map_of_acyclic_X₁ T _ (shortExact_boundaries K n (n + 1) rfl) hB).gIsCokernel
    exact isIso_homologyToMapHomology_of_isColimit T K (n + 1) n
      (isCokernelEpiComp hTH (T.map (cokernel.π (K.iCycles n)))
        (by rw [← T.map_comp, π_comp_boundariesToCycles]))

include hX in
/-- `isIso_homologyToMapHomology_of_acyclic_lt` as an isomorphism `Hⁿ (T K) ≅ T (Hⁿ K)`. -/
def homologyIsoMapHomologyOfAcyclicLt (n : ℕ)
    (hH' : ∀ q < n, acyclic T (K.homology q)) :
    ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      T.obj (K.homology n) :=
  have := isIso_homologyToMapHomology_of_acyclic_lt T K hX n hH'
  asIso (homologyToMapHomology T K n)

end Stacks.Cohomology.RightDerivedCoEdge

end
