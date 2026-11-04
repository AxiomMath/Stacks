module

public import Mathlib.Algebra.Homology.SingleHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleLocalization
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.RingTheory.Dualizing.DerivedHomCorepresentability
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionFiniteType
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatEpimorphism
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Finite
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor

/-!
# The dualizing module of a quasi-finite ring map is `H⁰` of its relative dualizing complex

Let `A → B` be a quasi-finite homomorphism of Noetherian rings.  Zariski's main theorem factors it
as `A → B' → B` with `A → B'` finite and `Spec(B) → Spec(B')` an open immersion, and the relative
dualizing module is `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B`.  On the other side stands the algebraic
relative dualizing complex `ω•_{B/A} = φ^!(A)` of [Stacks, Tag 0E9M].  The two are related by a
`B`-linear isomorphism `ω_{B/A} ≅ H⁰(ω•_{B/A})`.

## Main definitions

* `Dualizing.PolynomialPresentation.relativeDualizingComplex` — `ω•_{B/A} = φ^!(A)`, at a
  polynomial presentation of `φ`.
* `Dualizing.dualToSingleHom` — `Hom_R(S, R) → Hom_{D(R)}(S[0], R[0])`, `S`-linearly.

## Main results

* `Dualizing.nonempty_homologyZero_derivedHom_linearEquiv_dual` — `H⁰(RHom_R(S, R)) ≅ Hom_R(S, R)`
  as `S`-modules.
* `Dualizing.nonempty_derivedTensorProductOver_unitObject_iso_mapDerivedCategory` — for a flat
  `R → S`, `- ⊗_R^L S` is derived extension of scalars.
* `Dualizing.nonempty_dualizingModule_linearEquiv_homologyZero_relativeDualizingComplex` —
  **[Stacks, Tag 0C0I]**: `ω_{B/A} ≅ H⁰(ω•_{B/A})`.

## Implementation notes

The source calls the isomorphism *nonunique*, so the faithful conclusion is an existence
statement, `Nonempty (ω_{B/A} ≃ₗ[B] H⁰(ω•_{B/A}))`: there is no canonical map in either
direction to assert is an isomorphism.  For the same reason `ω•_{B/A}` is taken at an arbitrary
polynomial presentation, and `ω_{B/A}` at an arbitrary finite-open factorization, rather than at
ones chosen by `Classical.choice`.

The proof follows the source.  For the factorization `A → B' → B`, [Stacks, Tag 0BZT]
(`Dualizing.PolynomialPresentation.exists_upperShriekComp_of_finiteType`) identifies `ω•_{B/A}`
with the upper shriek along `B' → B` of `ω•_{B'/A}`; by [Stacks, Tag 0C0H]
(`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`) that upper
shriek is `- ⊗_{B'}^L B`, which `B` being flat over `B'` makes derived extension of scalars, so
that `H⁰` commutes with it.  By [Stacks, Tag 0C0G]
(`Dualizing.upperShriekFunctor_iso_derivedHom_of_finite`) `ω•_{B'/A} = RHom_A(B', A)`, whose
`H⁰` is `Hom_A(B', A)`.  This last identification has to be `B'`-linear, to be transported along
`B' → B`: it is read off the corepresentability of the cohomology of `RHom_A(B', -)` by `B'[0]`
(`Dualizing.derivedHomHomologyLinearEquiv`), followed by the full faithfulness of
`D(A)`'s embedding of `A`-modules in degree zero.

## References

* [Stacks Project, Tag 0C0I](https://stacks.math.columbia.edu/tag/0C0I)
* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0E9M](https://stacks.math.columbia.edu/tag/0E9M)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0C0H](https://stacks.math.columbia.edu/tag/0C0H)
* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
-/

@[expose] public section

open CategoryTheory Stacks.Discriminant
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Discriminant.algebraDualModule

universe u

namespace Dualizing

namespace PolynomialPresentation

/-- The algebraic relative dualizing complex `ω•_{B/A} = φ^!(A)` of [Stacks, Tag 0E9M], at a
polynomial presentation `p` of a finite type homomorphism `φ : A →+* B`: upper shriek of `p`
applied to the base ring placed in cohomological degree zero. -/
public noncomputable abbrev relativeDualizingComplex {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (p : PolynomialPresentation f) : DerivedCategory (ModuleCat.{u} B) :=
  p.upperShriekFunctor.{u, u}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (ULift.{u} A)))

end PolynomialPresentation

/-- The relative dualizing module of a finite-open factorization is `Hom_A(B', A) ⊗_{B'} B`; this
is the same tensor product with its factors exchanged, so that the `B`-action is the one on the
left-hand factor and base change along `B' → B` applies to it. -/
private noncomputable def dualizingModuleSwapEquiv {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (F : FiniteOpenFactorization.{u, u, u} A B) :
    dualizingModule F ≃ₗ[B] B ⊗[F.middle] Module.Dual A F.middle := by
  let C := F.middle
  let M := Module.Dual A C
  let es := TensorProduct.comm C M B
  letI : AddCommGroup (M ⊗[C] B) := by
    change AddCommGroup (dualizingModule F)
    exact dualizingModule.instAddCommGroup F
  letI : Module B (M ⊗[C] B) := dualizingModule.instModule F
  letI : Module B (B ⊗[C] M) := TensorProduct.leftModule
  let eSwapRaw : (M ⊗[C] B) ≃ₗ[B] B ⊗[C] M :=
    es.toAddEquiv.toLinearEquiv (by
      intro b z
      change es.toAddEquiv (es.toAddEquiv.symm (b • es.toAddEquiv z)) = _
      exact es.toAddEquiv.apply_symm_apply _)
  exact (dualizingModuleTensorEquiv F).trans eSwapRaw

/-- `S`, viewed as an `R`-module through `algebraMap R S` by restriction of scalars, is `S` with
its algebra module structure. -/
noncomputable def restrictScalarsSelfLinearEquiv (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] :
    ((ModuleCat.restrictScalars.{u} (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[R] S where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (Algebra.smul_def r (show S from x)).symm
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

/-- An `R`-linear form on `S`, read as a morphism from `S|_R` to the universe lift of `R`. -/
noncomputable def dualToULiftHom {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (φ : Module.Dual R S) :
    (ModuleCat.restrictScalars.{u} (algebraMap R S)).obj (ModuleCat.of S S) ⟶
      ModuleCat.of R (ULift.{u} R) :=
  (restrictScalarsSelfLinearEquiv R S).toModuleIso.hom ≫
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap ∘ₗ φ)

/-- The `S`-linear map `Hom_R(S, R) → Hom_{D(R)}(S[0], R[0])`, `S` acting on the left by
precomposition with multiplication on `S` and on the right through the source. -/
noncomputable def dualToSingleHom (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    letI := smulHomRestrictedUnitSingle (algebraMap R S) 0
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (ULift.{u} R))))
    Module.Dual R S →ₗ[S] (restrictedUnitSingle (algebraMap R S) 0 ⟶
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (ULift.{u} R)))) :=
  letI := smulHomRestrictedUnitSingle (algebraMap R S) 0
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (ULift.{u} R))))
  { toFun φ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (dualToULiftHom φ) ≫
      (CategoryTheory.shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).inv.app _
    map_add' φ ψ := by
      have : dualToULiftHom (φ + ψ) = dualToULiftHom φ + dualToULiftHom ψ := by
        ext x
        rfl
      rw [this, Functor.map_add, Preadditive.add_comp]
    map_smul' s φ := by
      change _ = smulRestrictedUnitSingle (algebraMap R S) s 0 ≫ _
      have : dualToULiftHom (s • φ) =
          (ModuleCat.restrictScalars.{u} (algebraMap R S)).map (s • 𝟙 (ModuleCat.of S S)) ≫
            dualToULiftHom φ := by
        ext x
        rfl
      rw [this, Functor.map_comp, Category.assoc]
      rfl }

/-- `Dualizing.dualToSingleHom` is bijective: `S[0] → R[0]` in `D(R)` are the `R`-linear maps
`S → R`, the embedding of `R`-modules in degree zero being fully faithful. -/
theorem dualToSingleHom_bijective (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Function.Bijective (dualToSingleHom R S) := by
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (ULift.{u} R))
  let e := (CategoryTheory.shiftFunctorZero (DerivedCategory (ModuleCat.{u} R)) ℤ).app Y
  refine ⟨fun φ ψ h => ?_, fun x => ?_⟩
  · have h' : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (dualToULiftHom φ) =
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (dualToULiftHom ψ) :=
      (cancel_mono e.inv).mp h
    have h'' := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_injective h'
    ext x
    exact congrArg (fun k => (k.hom x).down) h''
  · let g := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).preimage (x ≫ e.hom)
    refine ⟨(ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap ∘ₗ g.hom ∘ₗ
      (restrictScalarsSelfLinearEquiv R S).symm.toLinearMap, ?_⟩
    have hg : dualToULiftHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap ∘ₗ g.hom ∘ₗ
        (restrictScalarsSelfLinearEquiv R S).symm.toLinearMap) = g := by
      ext y
      rfl
    show (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map _ ≫ e.inv = x
    rw [hg, Functor.map_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **The zeroth cohomology of `RHom_R(S, R)` is the `R`-dual of `S`, `S`-linearly.**  For an
`R`-algebra `S`, `H⁰(RHom_R(S, R)) ≅ Hom_R(S, R)` as `S`-modules, `S` acting on `Hom_R(S, R)`
through its argument. -/
theorem nonempty_homologyZero_derivedHom_linearEquiv_dual (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] :
    Nonempty (↥((DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0).obj
        ((derivedHom.{u, u, u} (algebraMap R S)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (ULift.{u} R))))) ≃ₗ[S] Module.Dual R S) := by
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (ULift.{u} R))
  let := smulHomRestrictedUnitSingle (algebraMap R S) 0
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).obj Y)
  obtain ⟨e⟩ := nonempty_derivedHomHomologyLinearEquiv (algebraMap R S) Y 0
  exact ⟨e.trans (LinearEquiv.ofBijective (dualToSingleHom R S)
    (dualToSingleHom_bijective R S)).symm⟩

/-- For a flat `f : R → S`, derived tensor product over `R` with `S` is derived extension of
scalars along `f`. -/
theorem nonempty_derivedTensorProductOver_unitObject_iso_mapDerivedCategory {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' f hf
    Nonempty (derivedTensorProductOver.{u, u} f (Stacks0BZE.unitObject.{u, u} S) ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory) := by
  let : MonoidalCategoryStruct (ModuleCat.{u} S) := ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} S) := ModuleCat.liftedModuleMonoidal.{u, u}
  let N := HomologicalComplex.tensorUnit (ModuleCat.{u} S) (ComplexShape.up ℤ)
  obtain ⟨eRep⟩ := derivedTensorRepresentativeIso.{u, u} f N
  let eUnit : DerivedCategory.Q.obj N ≅ Stacks0BZE.unitObject.{u, u} S :=
    (Stacks0BZE.unitObjectIso.{u, u} S).symm
  exact ⟨(derivedTensorProductOverIsoCongr.{u, u} f eUnit).symm ≪≫ eRep.symm ≪≫
    canonicalTensorUnitIsoMapDerivedCategory.{u, u} f hf⟩

/-- **Stacks Project, Tag 0C0I.**  Let `A → B` be a quasi-finite homomorphism of Noetherian rings
and let `ω•_{B/A}` be its algebraic relative dualizing complex.  Then the relative dualizing
module `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` of a finite-open factorization `A → B' → B` is
isomorphic to `H⁰(ω•_{B/A})` as a `B`-module.

The source's isomorphism is *nonunique*, so the conclusion is the existence of a `B`-linear
equivalence rather than the invertibility of a named map. -/
@[stacks 0C0I "ω_{B/A} = H⁰(ω•_{B/A}), the source's isomorphism being nonunique"]
public theorem nonempty_dualizingModule_linearEquiv_homologyZero_relativeDualizingComplex
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, u, u} A B)
    (p : PolynomialPresentation (algebraMap A B)) :
    Nonempty (dualizingModule F ≃ₗ[B]
      ↥((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj
        p.relativeDualizingComplex)) := by
  let C := F.middle
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  let a : A →+* C := algebraMap A C
  let b : C →+* B := algebraMap C B
  have hfin : a.Finite := RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨q⟩ := nonempty_polynomialPresentation a hfin.finiteType
  -- `Spec(B) → Spec(B')` is an open immersion
  have hOpen : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom b)) := by
    have hU := specMap_ulift_isOpenImmersion b F.isOpenEmbedding_comap F.awayMap_bijective
    let uC : ULift.{u} C ≃+* C := ULift.ringEquiv
    let uB : ULift.{u} B ≃+* B := ULift.ringEquiv
    have : IsIso (CommRingCat.ofHom uC.symm.toRingHom) := uC.symm.toCommRingCatIso.isIso_hom
    have : IsIso (CommRingCat.ofHom uB.toRingHom) := uB.toCommRingCatIso.isIso_hom
    have heq : b = uB.toRingHom.comp ((RingHom.ulift.{u, u} b).comp uC.symm.toRingHom) := by
      ext x
      rfl
    rw [heq, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp, CommRingCat.ofHom_comp,
      AlgebraicGeometry.Spec.map_comp]
    infer_instance
  have hflat : b.Flat :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)
      (φ := CommRingCat.ofHom b)).mp inferInstance
  obtain ⟨⟨q'⟩, hq'⟩ :=
    nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion.{u, u} b hOpen
  obtain ⟨eOpen⟩ := hq' q'
  -- the presentation `p`, read as one of the composite `B' → B` after `A → B'`
  have hcomp : b.comp a = algebraMap A B := (IsScalarTower.algebraMap_eq A C B).symm
  let r : PolynomialPresentation (b.comp a) :=
    { variableCount := p.variableCount
      toRingHom := p.toRingHom
      commutes := p.commutes.trans hcomp.symm
      surjective := p.surjective }
  obtain ⟨τ, hτ⟩ := PolynomialPresentation.exists_upperShriekComp_of_finiteType.{u, u} q q' r
  let A0 := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (ULift.{u} A))
  have hA0 : DerivedCategoryB.IsBoundedBelow A0 := ⟨0, fun n hn => A0.isZero_of_isGE 0 n hn⟩
  have := hτ A0 hA0
  obtain ⟨eFin⟩ := upperShriekFunctor_iso_derivedHom_of_finite a hfin q
  obtain ⟨eExt⟩ := nonempty_derivedTensorProductOver_unitObject_iso_mapDerivedCategory b hflat
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} b) :=
    extendScalars_preservesFiniteLimits_of_flat' b hflat
  let K := (derivedHom.{u, u, u} a).obj A0
  -- `ω•_{B/A} ≅ RHom_A(B', A) ⊗_{B'}^L B`
  let eComplex : p.relativeDualizingComplex ≅
      (ModuleCat.extendScalars.{u, u, u} b).mapDerivedCategory.obj K :=
    (asIso (τ.app A0)).symm ≪≫ (eOpen ≪≫ eExt).app _ ≪≫
      (ModuleCat.extendScalars.{u, u, u} b).mapDerivedCategory.mapIso (eFin.app A0)
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj p.relativeDualizingComplex ≅
      (ModuleCat.extendScalars.{u, u, u} b).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) 0).obj K) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).mapIso eComplex ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (ModuleCat.extendScalars.{u, u, u} b) 0).app K
  let eT := extendScalarsTensorIsoUnit.{u, u} (A := B)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) 0).obj K)
  obtain ⟨eDual⟩ := nonempty_homologyZero_derivedHom_linearEquiv_dual A C
  exact ⟨(dualizingModuleSwapEquiv F).trans
    ((eDual.symm.baseChange C B).trans (eH ≪≫ eT).toLinearEquiv.symm)⟩

end Dualizing

end
