module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# Naturality of the canonical Frobenius on `RΓ_c(X_k̄, K)`

`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` is the endomorphism `π_X^*` of
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` attached to a bounded below complex `K` on `X_étale`.
This file makes `RΓ_c(X_k̄, -)` a functor of `K` and shows that `π_X^*` is natural in `K`: every
ingredient of its construction — the base change twist of the Frobenius descent isomorphism of
Tag 03SR, the unit comparing degreewise and derived direct image, and the composition
comparison of derived direct images — is a natural transformation; the first two are
`Stacks.EtaleCohomology.frobeniusRestrictionDerivedMap_naturality`.  Naturality is what lets
`π_X^*` act on an inverse system `n ↦ RΓ_c(X_k̄, Kₙ)`, hence on ℓ-adic cohomology.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`: `K ↦ RΓ_c(X_k̄, K)`, whose value is
  `Stacks.EtaleCohomology.compactSupportFrobeniusCohomology` by definition.
* `Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans`: `π_X^*` as a natural
  endomorphism of that functor; its component is `canonicalCompactSupportFrobenius`, by `rfl`.

## Main results

* `Stacks.EtaleCohomology.isGE_compactSupportFrobeniusFunctor_obj`: `RΓ_c(X_k̄, -)` carries a
  complex lying in degrees `≥ a` to an object of `D⁺` that is `≥ a`.

## References

* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Frobenius

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The restriction `C ↦ C|_{Y_k̄}` to the base change, as a functor into `D⁺(Y_k̄)`.  Its value
is `Stacks.EtaleCohomology.fieldBaseChangeRestriction` by definition. -/
public abbrev fieldBaseChangeRestrictionFunctor :
    CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ (fieldBaseChange Y kbar)) :=
  (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus ⋙
    DerivedCategory.Plus.Q

end Frobenius

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`RΓ_c(X_k̄, -)` as a functor** of the bounded below complex on `X_étale`: extension by zero
to `X̄`, restriction to `X̄_k̄`, derived direct image to `Spec k̄` and derived global sections. -/
public def compactSupportFrobeniusFunctor :
    CochainComplex.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus ⋙
    fieldBaseChangeRestrictionFunctor.{u, r} Λ (Over.mk j.toBase) kbar ⋙
    etaleModuleDerivedDirectImage.{u, r} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) ⋙
    etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))

omit [Fintype k] in
/-- The value of the functor is `RΓ_c(X_k̄, K)` of `compactSupportFrobeniusCohomology`. -/
public theorem compactSupportFrobeniusFunctor_obj
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).obj K =
      compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K :=
  rfl

/-- **`π_X^*` is a natural endomorphism of `RΓ_c(X_k̄, -)`.**  Its component at `K` is the
canonical endomorphism `canonicalCompactSupportFrobenius` of `RΓ_c(X_k̄, K)`. -/
public def canonicalCompactSupportFrobeniusNatTrans :
    compactSupportFrobeniusFunctor.{u, r} Λ f j kbar ⟶
      compactSupportFrobeniusFunctor.{u, r} Λ f j kbar where
  app K := canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K
  naturality K K' g := by
    have hn := frobeniusRestrictionDerivedMap_naturality.{u, r} Λ (Over.mk j.toBase) kbar p q
      hcard ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map g)
    have hc := (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard)).inv.naturality
        ((fieldBaseChangeRestrictionFunctor.{u, r} Λ (Over.mk j.toBase) kbar).map
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map g))
    dsimp only [fieldBaseChangeRestrictionFunctor, Functor.comp_map, Functor.comp_obj] at hn hc
    dsimp only [compactSupportFrobeniusFunctor, canonicalCompactSupportFrobenius,
      frobeniusRestrictionCohomologyEndo, Functor.comp_map, Functor.comp_obj]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp, Category.assoc,
      Category.assoc, hc]

/-- The component of `canonicalCompactSupportFrobeniusNatTrans` at `K` is the canonical
endomorphism `π_X^*` of `RΓ_c(X_k̄, K)`. -/
@[simp]
public theorem canonicalCompactSupportFrobeniusNatTrans_app
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard).app K =
      canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K :=
  rfl

omit [Fintype k] in
/-- `RΓ_c(X_k̄, -)` carries a complex lying in degrees `≥ a` to an object `≥ a` of `D⁺`. -/
public theorem isGE_compactSupportFrobeniusFunctor_obj
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).obj K).IsGE a := by
  let E := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus
  let Y := Over.mk j.toBase
  let I := (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus
  have h₀ : (I.obj (E.obj K)).obj.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map_isZero
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE K.obj a i hi))
  have h₁ : (DerivedCategory.Plus.Q.obj (I.obj (E.obj K))).IsGE a := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj (I.obj (E.obj K)).obj).IsGE a
    infer_instance
  have h₂ := (etaleModuleDirectImage.{u, r} Λ
    (pullback.snd Y.hom (specAlgebraMap k kbar))).isGE_rightDerivedFunctorPlus_obj
      (DerivedCategory.Plus.Q.obj (I.obj (E.obj K))) a
  exact (etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar))).isGE_rightDerivedFunctorPlus_obj
    ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
      (DerivedCategory.Plus.Q.obj (I.obj (E.obj K)))) a

end CompactSupport

end Stacks.EtaleCohomology
