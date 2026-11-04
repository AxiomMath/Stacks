module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalUniversal
public import StacksFrontier.Algebra.Module.CharacterModule.Finite

/-!
# The dual of a cohomological δ-functor is a homological δ-functor

Let `A`, `A'` be abelian categories, `D : Aᵒᵖ ⥤ A'` an exact contravariant functor, `R` a ring
(not necessarily commutative) and `E = (Eⁿ, δ)` a cohomological δ-functor from `A'` to left
`Rᵐᵒᵖ`-modules. Then `Hₙ(X) = (Eⁿ(D X))^∨`, where `(-)^∨ = Hom_ℤ(-, ℚ/ℤ)` is character duality
(which turns left `Rᵐᵒᵖ`-modules into left `R`-modules), is a homological δ-functor from `A` to
left `R`-modules: a short exact sequence `0 → X₁ → X₂ → X₃ → 0` goes to the short exact sequence
`0 → D X₃ → D X₂ → D X₁ → 0`, and dualizing its long exact `E`-sequence (character duality is
exact) gives the long exact `H`-sequence, with connecting maps the duals of those of `E`.

If moreover `D` is an anti-equivalence and every object can be embedded by a monomorphism that
kills `Eⁿ⁺¹`, then `H` is coeffaceable, hence universal. The homology of a profinite group with
finite coefficients is defined this way in the source of 03VM (Section 03VI, "Trivial duality").

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.ofDeltaFunctorDual`: the homological
  δ-functor `Hₙ(X) = (Eⁿ(D X))^∨`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffacementOfDual`: the coeffacement of `X`
  for `Hₙ₊₁` given by the dual of a monomorphism out of `D X` killed by `Eⁿ⁺¹`.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffaceable_ofDeltaFunctorDual`: if `D` is
  an anti-equivalence and every object embeds by a monomorphism killed by `Eⁿ⁺¹`, then the dual
  δ-functor is coeffaceable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped CharacterModule.MulOppositeAction

universe v u u' w

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type u} [Category.{v} A] [Abelian A] {A' : Type*} [Category A'] [Abelian A']
  {R : Type u'} [Ring R]
  (E : CategoryTheory.DeltaFunctor A' (ModuleCat.{w} Rᵐᵒᵖ)) (D : Aᵒᵖ ⥤ A') [D.Additive]
  [PreservesFiniteLimits D] [PreservesFiniteColimits D]

/-- The image under `D` of the opposite of a short complex: `D X₃ → D X₂ → D X₁`. -/
abbrev dualShortComplex (S : ShortComplex A) : ShortComplex A' := S.op.map D

/-- The image under `D` of the opposite of a short exact sequence is short exact. -/
lemma shortExact_dualShortComplex {S : ShortComplex A} (hS : S.ShortExact) :
    (dualShortComplex D S).ShortExact :=
  hS.op.map_of_exact D

/-- A contravariant functor carries a commutative square to a commutative square. -/
lemma map_op_comp_map_op_eq {C C' : Type*} [Category C] [Category C'] (F : Cᵒᵖ ⥤ C')
    {X Y Z W : C} (a : Y ⟶ Z) (b : X ⟶ Y) (c : W ⟶ Z) (d : X ⟶ W) (h : b ≫ a = d ≫ c) :
    F.map a.op ≫ F.map b.op = F.map c.op ≫ F.map d.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]

/-- **The dual homological δ-functor** `Hₙ(X) = (Eⁿ(D X))^∨`. -/
def ofDeltaFunctorDual : HomologicalDeltaFunctor A (ModuleCat.{w} R) where
  functor n := (D ⋙ E.functor n).rightOp ⋙ CharacterModule.moduleCatDualOfMulOppositeFunctor R
  additive n := by
    have := E.additive n
    infer_instance
  δ {S} hS n := (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
    (E.δ (shortExact_dualShortComplex D hS) n).op
  map_g_δ {S} hS n := by
    change (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
        ((E.functor (n + 1)).map (dualShortComplex D S).f).op ≫
      (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
        (E.δ (shortExact_dualShortComplex D hS) n).op = 0
    rw [← Functor.map_comp, ← op_comp, E.δ_map_f, op_zero, Functor.map_zero]
  δ_map_f {S} hS n := by
    change (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
        (E.δ (shortExact_dualShortComplex D hS) n).op ≫
      (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
        ((E.functor n).map (dualShortComplex D S).g).op = 0
    rw [← Functor.map_comp, ← op_comp, E.map_g_δ, op_zero, Functor.map_zero]
  epi_map_g {S} hS := by
    have := E.mono_map_f (shortExact_dualShortComplex D hS)
    exact CharacterModule.epi_moduleCatDualOfMulOppositeFunctor_map R
      ((E.functor 0).map (dualShortComplex D S).f)
  exact_map {S} hS n :=
    CharacterModule.exact_moduleCatDualOfMulOppositeFunctor_map R
      (E.exact_map (shortExact_dualShortComplex D hS) n)
  exact_δ₁ {S} hS n :=
    CharacterModule.exact_moduleCatDualOfMulOppositeFunctor_map R
      (E.exact_δ₂ (shortExact_dualShortComplex D hS) n)
  exact_δ₂ {S} hS n :=
    CharacterModule.exact_moduleCatDualOfMulOppositeFunctor_map R
      (E.exact_δ₁ (shortExact_dualShortComplex D hS) n)
  δ_naturality {S T} hS hT φ n :=
    map_op_comp_map_op_eq (CharacterModule.moduleCatDualOfMulOppositeFunctor R)
      ((E.functor (n + 1)).map (D.map φ.τ₃.op)) (E.δ (shortExact_dualShortComplex D hT) n)
      (E.δ (shortExact_dualShortComplex D hS) n) ((E.functor n).map (D.map φ.τ₁.op))
      (E.δ_naturality (shortExact_dualShortComplex D hT) (shortExact_dualShortComplex D hS)
        (D.mapShortComplex.map (ShortComplex.opMap φ)) n).symm

/-- The value of the dual δ-functor on an object: `Hₙ(X) = (Eⁿ(D X))^∨`. -/
lemma ofDeltaFunctorDual_functor_obj (n : ℕ) (X : A) :
    ((ofDeltaFunctorDual E D).functor n).obj X =
      ModuleCat.of R (CharacterModule ((E.functor n).obj (D.obj (Opposite.op X)))) :=
  rfl

/-- The value of the dual δ-functor on a morphism `f` is the dual of `Eⁿ(D f)`. -/
lemma ofDeltaFunctorDual_functor_map (n : ℕ) {X Y : A} (f : X ⟶ Y) :
    ((ofDeltaFunctorDual E D).functor n).map f =
      (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
        ((E.functor n).map (D.map f.op)).op :=
  rfl

/-- The connecting map of the dual δ-functor is the dual of the connecting map of `E` on the
image under `D` of the opposite short exact sequence. -/
lemma ofDeltaFunctorDual_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (ofDeltaFunctorDual E D).δ hS n = (CharacterModule.moduleCatDualOfMulOppositeFunctor R).map
      (E.δ (shortExact_dualShortComplex D hS) n).op :=
  rfl

/-- **A coeffacement of the dual δ-functor from an effacement.** If `D` is an anti-equivalence
and `ι : D X ⟶ I` is a monomorphism killed by `Eⁿ⁺¹`, the dual of `ι` coeffaces `X` for
`Hₙ₊₁ = (Eⁿ⁺¹ ∘ D)^∨`. -/
def coeffacementOfDual (e : Aᵒᵖ ≌ A') [e.functor.Additive] (X : A) (n : ℕ) {I : A'}
    (ι : e.functor.obj (Opposite.op X) ⟶ I) (hι : Mono ι) (hE : (E.functor (n + 1)).map ι = 0) :
    (ofDeltaFunctorDual E e.functor).Coeffacement X n :=
  haveI := hι
  let πop : Opposite.op X ⟶ e.inverse.obj I := e.unit.app (Opposite.op X) ≫ e.inverse.map ι
  haveI : Mono πop := mono_comp _ _
  haveI : Epi πop.unop := unop_epi_of_mono πop
  { P := (e.inverse.obj I).unop
    π := πop.unop
    map_π := by
      rw [ofDeltaFunctorDual_functor_map, Quiver.Hom.op_unop]
      have hD : e.functor.map πop = ι ≫ e.counitInv.app I := by
        simp only [πop, Functor.map_comp, Equivalence.fun_inv_map]
        rw [← Category.assoc, Equivalence.functor_unit_comp, Category.id_comp]
      rw [hD, Functor.map_comp, hE, zero_comp, op_zero, Functor.map_zero]
      rfl }

/-- **Coeffaceability of the dual δ-functor.** If `D` is an anti-equivalence and every object
`Y` has a monomorphism `Y ⟶ I` killed by `Eⁿ⁺¹`, then `Hₙ(X) = (Eⁿ(D X))^∨` is coeffaceable:
the coeffacing epimorphism of `X` is the dual of the effacing monomorphism of `D X`. -/
theorem coeffaceable_ofDeltaFunctorDual (e : Aᵒᵖ ≌ A') [e.functor.Additive]
    (heff : ∀ (Y : A') (n : ℕ), ∃ (I : A') (ι : Y ⟶ I), Mono ι ∧ (E.functor (n + 1)).map ι = 0) :
    (ofDeltaFunctorDual E e.functor).Coeffaceable where
  nonempty X n := by
    obtain ⟨I, ι, hι, hE⟩ := heff (e.functor.obj (Opposite.op X)) n
    exact ⟨coeffacementOfDual E e X n ι hι hE⟩

end Stacks.CategoryHomology.HomologicalDeltaFunctor

end
