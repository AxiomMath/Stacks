module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Homology.PseudoCoherent.Relative.Locality
public import StacksFrontier.Homology.PseudoCoherent.Relative.Tower

@[expose] public section

/-!
# Relative pseudo-coherence of a module after flat extension of scalars

Let `R → A → B` be finite-type maps of commutative rings with `B` flat over `A` and, as a
`B`-module, pseudo-coherent relative to `A`. Then tensoring an `A`-module with `B` preserves
relative `m`-pseudo-coherence and relative pseudo-coherence over `R`.

## Main definitions

* `PseudoCoherence.derivedExtensionScalarsSingleIsoOfFlat`: for a flat extension, derived
  extension of scalars of a module placed in degree zero is its ordinary tensor product, again
  in degree zero.

## Main results

* `PseudoCoherence.tensorProduct_preserves_relativelyPseudoCoherent_of_flat`: flat extension of
  scalars preserves relative `m`-pseudo-coherence and relative pseudo-coherence of modules.
* `PseudoCoherence.moduleRelativelyPseudoCoherentFrom_of_span_eq_top`: if finitely many elements
  of `A` generate the unit ideal and each localization `A_{aᵢ}` is `m`-pseudo-coherent relative to
  `R` as a module over itself, then so is `A`.

## Implementation notes

The extension of scalars of `M` is written `TensorProduct A B M`; it is identified with
`M ⊗[A] B` by `TensorProduct.comm`.

## References

* [The Stacks Project, Lemma 15.82.10 (067C)](https://stacks.math.columbia.edu/tag/067C)
* [The Stacks Project, Lemma 15.82.12 (067E)](https://stacks.math.columbia.edu/tag/067E)
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CochainComplex.DerivedExtensionScalars

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- When extension of scalars along `f` is exact, the derived extension of scalars along `f` is
isomorphic to the functor that `ModuleCat.extendScalars f` induces on derived categories. -/
public noncomputable def derivedExtensionIsoOfExact
    {S B : Type u} [CommRing S] [CommRing B] (f : S →+* B)
    [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)]
    [PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f)] :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  let D := derivedExtensionScalarsGeneral.{u, u, u} f
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{u} S) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

/-- Flat derived extension agrees with the ordinary tensor product on a degree-zero module. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[no_expose]
public noncomputable def derivedExtensionScalarsSingleIsoOfFlat {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Module.Flat A B]
    (hB : IsModuleRelativelyPseudoCoherent (R := A) (A := B) B)
    (M : Type u) [AddCommGroup M] [Module A M] :
    (derivedExtensionScalars hB).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
      (ModuleCat.of B (TensorProduct A B M)) := by
  let f := algebraMap A B
  let F := ModuleCat.extendScalars.{u, u, u} f
  let eTensor := extendScalarsAlgebraMapObjIso (S := B) (ModuleCat.of A M)
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  letI : Algebra A B := ((algebraMap B B).comp f).toAlgebra
  have : Module.Flat A B := hf
  have : F.Additive :=
    ⟨fun {_ _ g h} ↦
      ModuleCat.hom_ext (LinearMap.baseChange_add (A := B) (f := g.hom) (g := h.hom))⟩
  have hexact : ∀ T : ShortComplex (ModuleCat.{u} A), T.Exact → (T.map F).Exact := by
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact B hT
  have hlimits := ((Functor.exact_tfae F).out 2 4).mp hexact
  have : PreservesFiniteLimits F := hlimits.1
  have : PreservesFiniteColimits F := hlimits.2
  exact (derivedExtensionIsoOfExact f).app _ ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso eTensor

/-- Relative `m`-pseudo-coherence transports along an isomorphism of objects of the derived
category. -/
lemma relativelyPseudoCoherentFrom_of_iso
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] {K L : DerivedCategory (ModuleCat.{u} B)} {m : ℤ}
    (e : K ≅ L) (h : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := R) L m := by
  intro n f hf
  obtain ⟨E, hE, a, ha, ha'⟩ := h n f hf
  let j := (ModuleCat.restrictScalars f.toRingHom).mapDerivedCategory.mapIso e
  refine ⟨E, hE, a ≫ j.hom, ?_, ?_⟩
  · intro i hi
    have := ha i hi
    simp only [Functor.map_comp]
    infer_instance
  · have := ha'
    simp only [Functor.map_comp]
    infer_instance

/-- Flat extension of scalars preserves relative `m`-pseudo-coherence and relative
pseudo-coherence for modules. -/
@[stacks 067C]
public theorem tensorProduct_preserves_relativelyPseudoCoherent_of_flat
    {R : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Flat A B] (m : ℤ)
    (hB : IsModuleRelativelyPseudoCoherent (R := A) (A := B) B) :
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
    (IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M m →
      IsModuleRelativelyPseudoCoherentFrom (R := R) (A := B)
        (TensorProduct A B M) m) ∧
    (IsModuleRelativelyPseudoCoherent (R := R) (A := A) M →
      IsModuleRelativelyPseudoCoherent (R := R) (A := B)
        (TensorProduct A B M)) := by
  let : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans (R := R) (S := A) (A := B) inferInstance inferInstance
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  have h := derivedExtensionScalars_preserves_relativelyPseudoCoherent
    (R := R) K m hB
  let e := derivedExtensionScalarsSingleIsoOfFlat hB M
  exact ⟨fun hM ↦ relativelyPseudoCoherentFrom_of_iso e (h.1 hM),
    fun hM n ↦ relativelyPseudoCoherentFrom_of_iso e (h.2 hM n)⟩

/-! ### Relative pseudo-coherence of an algebra is local on a finite principal cover

For the algebra itself in degree zero, the derived localization of `A` away from `a` is the
localized algebra `A_a` in degree zero. -/

/-- Derived localization away from `a` of `A` placed in degree zero is `A_a` placed in degree
zero. -/
-- The body names a `private` helper, so it must not be exposed to importers.
@[no_expose]
private noncomputable def localizationAwaySingleIso {A : Type u} [CommRing A] (a : A) :
    (StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} a).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away a)) 0).obj
        (ModuleCat.of (Localization.Away a) (Localization.Away a)) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away a))
  letI : F.Additive := extendScalars_additive.{u, u} _
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away a) (Submonoid.powers a)))
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap A (Localization.Away a))).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away a)) 0).mapIso
      (extendScalarsAlgebraMapObjIso (S := Localization.Away a) (ModuleCat.of A A) ≪≫
        (Algebra.TensorProduct.rid A (Localization.Away a)
          (Localization.Away a)).toLinearEquiv.toModuleIso)

/-- If finitely many elements of a finite-type `R`-algebra `A` generate the unit ideal and each
localization `A_{aᵢ}` is `m`-pseudo-coherent relative to `R` as a module over itself, then so is
`A`. -/
public theorem moduleRelativelyPseudoCoherentFrom_of_span_eq_top
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {ι : Type*} [Finite ι] (a : ι → A) (ha : Ideal.span (Set.range a) = ⊤) (m : ℤ)
    (h : ∀ i,
      letI : Algebra.FiniteType A (Localization.Away (a i)) :=
        IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (a i)) _
      letI : Algebra.FiniteType R (Localization.Away (a i)) :=
        Algebra.FiniteType.trans (R := R) (S := A)
          (A := Localization.Away (a i)) inferInstance inferInstance
      IsModuleRelativelyPseudoCoherentFrom (R := R) (A := Localization.Away (a i))
        (Localization.Away (a i)) m) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) A m := by
  refine (relativelyPseudoCoherent_iff_localizationAway_of_span_eq_top a ha
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) m).1.mp
    fun i ↦ ?_
  let : Algebra.FiniteType A (Localization.Away (a i)) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (a i)) _
  let : Algebra.FiniteType R (Localization.Away (a i)) :=
    Algebra.FiniteType.trans (R := R) (S := A)
      (A := Localization.Away (a i)) inferInstance inferInstance
  exact relativelyPseudoCoherentFrom_of_iso (localizationAwaySingleIso (a i)).symm (h i)
end PseudoCoherence
