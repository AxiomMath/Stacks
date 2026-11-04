module

public import StacksFrontier.RingTheory.Flat.FlatteningStageTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatAtPointFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatAtPointFlatBaseChange

/-!
# Flatness at the primes above a point under a flat change of the algebra

Let `C₀ → C` be a flat map of `A`-algebras, `q` a prime of `C` lying over the maximal ideal of the
local ring `A`, `q₀` its contraction to `C₀`, and `N` the base change to `C` of a `C₀`-module
`N₀`. Then for every local `A`-algebra `R` the condition `Module.IsFlatAtPrimesAbove` holds for
`(C₀, q₀, N₀)` exactly when it holds for `(C, q, N)`. This is Stacks Tag 05P5 for the flat local
map `(C₀)_{q₀} → C_q`, read on `C₀` and `C` through the dictionary
`Module.FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove`; it is the step of the proof of
Stacks Tag 05PG which replaces the algebra by an étale neighbourhood carrying a complete
dévissage.

## Main results

* `Module.isFlatAtPrimesAbove_iff_of_flat`: the comparison.

## References

* [Stacks Project, Tag 05P5](https://stacks.math.columbia.edu/tag/05P5)
* [Stacks Project, Tag 05P4](https://stacks.math.columbia.edu/tag/05P4)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing CategoryTheory

open scoped TensorProduct

universe u v w v' w' x

namespace Module

/-- Propositions whose liftings are equal types are equivalent. -/
theorem iff_of_plift_eq {P Q : Prop} (e : PLift P = PLift Q) : P ↔ Q :=
  ⟨fun p => (cast e ⟨p⟩).down, fun q => (cast e.symm ⟨q⟩).down⟩

/-- **Stacks Tag 05P5, read on non-local algebras.** For a flat map `C₀ → C` of `A`-algebras, a
prime `q` of `C` over the maximal ideal of `A` and the base change `N` to `C` of a `C₀`-module
`N₀`, flatness at the primes above `q` of the base changes of `N` is flatness at the primes above
the contraction of `q` of the base changes of `N₀`. -/
theorem isFlatAtPrimesAbove_iff_of_flat {A : Type u} [CommRing A] [IsLocalRing A]
    {C₀ : Type v} [CommRing C₀] [Algebra A C₀] {C : Type v'} [CommRing C] [Algebra A C]
    [Algebra C₀ C] [IsScalarTower A C₀ C] [Module.Flat C₀ C]
    (q : Ideal C) [q.IsPrime] (hq : q.comap (algebraMap A C) = maximalIdeal A)
    {N₀ : Type w} [AddCommGroup N₀] [Module C₀ N₀] {N : Type w'} [AddCommGroup N]
    [Module C₀ N] [Module C N] [IsScalarTower C₀ C N] (h : N₀ →ₗ[C₀] N) (hh : IsBaseChange C h)
    (R : Type x) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalHom (algebraMap A R)] :
    IsFlatAtPrimesAbove A C₀ (q.comap (algebraMap C₀ C)) N₀ R ↔
      IsFlatAtPrimesAbove A C q N R := by
  set q₀ := q.comap (algebraMap C₀ C) with hq₀def
  have hq₀ : q₀.comap (algebraMap A C₀) = maximalIdeal A := by
    rwa [hq₀def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have : q.LiesOver q₀ := ⟨rfl⟩
  let T₀ := flatAtPointSituationAtPrime A C₀ q₀ hq₀ N₀
  let T := flatAtPointSituationAtPrime A C q hq N
  let : Algebra (Localization.AtPrime q₀) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver q₀ q
  have : IsLocalHom (algebraMap (Localization.AtPrime q₀) (Localization.AtPrime q)) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q₀ q (algebraMap C₀ C) rfl))
  have : Module.Flat (Localization.AtPrime q₀) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q₀) q₀.primeCompl
      (Localization.AtPrime q)).mpr (Module.Flat.trans C₀ C (Localization.AtPrime q))
  -- the two outer translations
  have e₁ : T₀.ConditionOn R ↔ IsFlatAtPrimesAbove A C₀ q₀ N₀ R :=
    FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove (S := T₀) q₀
      (LocalizedModule.mkLinearMap q₀.primeCompl N₀) R
  have e₄ : T.ConditionOn R ↔ IsFlatAtPrimesAbove A C q N R :=
    FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove (S := T) q
      (LocalizedModule.mkLinearMap q.primeCompl N) R
  -- Stacks 05P5
  let R' : LocalAlgCat.{u, x} A := { carrier := R }
  have e₂ : T₀.ConditionOn R ↔
      (T₀.baseChange (Localization.AtPrime q)).ConditionOn R :=
    iff_of_plift_eq (Functor.congr_obj
      (FlatAtPointSituation.flatAtPointFunctor_baseChange.{u, v, max v w, x, v'} T₀
        (Localization.AtPrime q)) R')
  -- Stacks 05P4 along the identity, to change the module and the `A`-algebra structure
  let f : @AlgHom A (Localization.AtPrime q) (Localization.AtPrime q) _ _ _
      (T₀.baseChange (Localization.AtPrime q)).algebraAB inferInstance :=
    @AlgHom.mk A (Localization.AtPrime q) (Localization.AtPrime q) _ _ _
      (T₀.baseChange (Localization.AtPrime q)).algebraAB inferInstance
      (RingHom.id (Localization.AtPrime q)) (fun a =>
        (IsScalarTower.algebraMap_apply A (Localization.AtPrime q₀)
          (Localization.AtPrime q) a).symm)
  have hX : IsBaseChange (Localization.AtPrime q₀)
      (LocalizedModule.mkLinearMap q₀.primeCompl N₀) :=
    IsLocalizedModule.isBaseChange q₀.primeCompl (Localization.AtPrime q₀) _
  have hY : IsBaseChange (Localization.AtPrime q)
      (((LocalizedModule.mkLinearMap q.primeCompl N).restrictScalars C₀).comp h) :=
    hh.comp (IsLocalizedModule.isBaseChange q.primeCompl (Localization.AtPrime q) _)
  let e₀ : Localization.AtPrime q ⊗[Localization.AtPrime q₀]
      LocalizedModule q₀.primeCompl N₀ ≃ₗ[Localization.AtPrime q]
        LocalizedModule q.primeCompl N :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Localization.AtPrime q) _)
      hX.equiv.symm).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C₀ (Localization.AtPrime q₀)
        (Localization.AtPrime q) (Localization.AtPrime q) N₀).trans hY.equiv)
  have e₃ : (T₀.baseChange (Localization.AtPrime q)).ConditionOn R ↔ T.ConditionOn R :=
    iff_of_plift_eq (Functor.congr_obj
      (@FlatAtPointSituation.flatAtPointFunctor_eq_of_finite
        (T₀.baseChange (Localization.AtPrime q)) (Localization.AtPrime q) _ _ inferInstance
        (isLocalHom_algebraMap_localizationAtPrime q hq) _ _ _ f
        (inferInstanceAs (IsLocalHom (RingHom.id (Localization.AtPrime q))))
        (RingHom.Finite.id _) e₀) R')
  exact e₁.symm.trans (e₂.trans (e₃.trans e₄))

end Module

end
