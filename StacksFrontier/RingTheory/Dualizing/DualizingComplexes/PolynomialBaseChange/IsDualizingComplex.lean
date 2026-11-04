module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.RingTheory.Dualizing.Complex
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange.FiniteInjectiveDimension
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange.Homothety
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange.EndomorphismUnit

/-!
# Dualizing complexes over polynomial rings

A dualizing complex over a Noetherian ring remains dualizing after extension of scalars to the
polynomial ring in one variable.

## Main definitions

* `Dualizing.polynomialBaseChange` is extension of scalars from `A` to `A[X]` on derived
  categories.

## Main results

* `Dualizing.polynomialBaseChange_isDualizingComplex` states that polynomial base change of a
  dualizing complex is dualizing.

## Implementation notes

Since `A[X]` is free, hence flat, over `A`, ordinary extension of scalars is exact and thus
induces a functor on derived categories. For an independently universe-polymorphic module
category, `polynomialBaseChange` first lifts module carriers and changes coefficients from `A`
to `ULift A`. Extension of scalars can then be formed in one universe, after which restriction
along the polynomial ring equivalence returns the coefficients to `A[X]`. Thus its target is
`DerivedCategory (ModuleCat.{max u v} (Polynomial A))`, and the construction realizes the
source's tensor product with `A[X]` without identifying the ring and module universes.

The homothety condition is handled through the canonical map `R → End K` in the derived
category: `isIso_canonicalHomothety_of_endomorphism_iso_unit` shows that an isomorphism of the
derived endomorphism object with the tensor unit makes that map invertible, and base change of
the derived internal Hom along the flat map `A' → A'[X]` transports it.

## References

* [Stacks Project, Tag 0A7J](https://stacks.math.columbia.edu/tag/0A7J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Dualizing

universe u v w x

/-- Extension of scalars from `A` to `A[X]`, applied to an object of the derived category.
The module carrier is first universe-lifted, and the coefficient ring is temporarily changed to
`ULift A`, so that exactness of tensoring can be invoked in a common universe. -/
noncomputable def polynomialBaseChange {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) :
    DerivedCategory (ModuleCat.{max u v} (Polynomial A)) := by
  let A' := ULift.{v} A
  let e : A' ≃+* A := ULift.ringEquiv
  let p : Polynomial A ≃+* Polynomial A' := Polynomial.mapEquiv e.symm
  let U := ModuleCat.uliftFunctor.{u, v} A
  let C := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let f : A' →+* Polynomial A' := Polynomial.C
  let E := ModuleCat.extendScalars.{max u v, max u v, max u v} f
  let R := ModuleCat.restrictScalars.{max u v} p.toRingHom
  letI : PreservesFiniteLimits E :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by
      rw [show f = algebraMap A' (Polynomial A') from rfl, RingHom.flat_algebraMap_iff]
      infer_instance)
  letI : E.Additive := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) E := inferInstance
    have : PreservesBinaryBiproducts E :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  exact R.mapDerivedCategory.obj
    (E.mapDerivedCategory.obj (C.mapDerivedCategory.obj (U.mapDerivedCategory.obj K)))

/-- A functor preserving injective objects sends injective objects to objects of finite
injective dimension. -/
private theorem exists_hasInjectiveDimensionLE_of_preservesInjectiveObjects
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (F : ModuleCat.{w} R ⥤ ModuleCat.{x} S) [F.PreservesInjectiveObjects]
    (M : ModuleCat.{w} R) (hM : Injective M) : ∃ n : ℕ, HasInjectiveDimensionLE (F.obj M) n :=
  ⟨0, (injective_iff_hasInjectiveDimensionLE_zero (F.obj M)).mp (F.injective_obj_of_injective hM)⟩

/-- A dualizing complex over a Noetherian ring remains dualizing after tensoring with the
polynomial ring in one variable. -/
@[stacks 0A7J]
public theorem polynomialBaseChange_isDualizingComplex {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex (polynomialBaseChange K) := by
  let A' := ULift.{v} A
  let e : A' ≃+* A := ULift.ringEquiv
  let p : Polynomial A ≃+* Polynomial A' := Polynomial.mapEquiv e.symm
  let U := ModuleCat.uliftFunctor.{u, v} A
  let C := ModuleCat.restrictScalars.{max u v} e.toRingHom
  let f : A' →+* Polynomial A' := Polynomial.C
  let E := ModuleCat.extendScalars.{max u v, max u v, max u v} f
  let R := ModuleCat.restrictScalars.{max u v} p.toRingHom
  let K₁ := U.mapDerivedCategory.obj K
  let K₂ := C.mapDerivedCategory.obj K₁
  let : Small.{v} A := small_base_from_dualizing K hK
  let : Small.{max u v} A := small_lift.{u, max u v, v} A
  let : IsNoetherianRing A' := isNoetherianRing_of_ringEquiv (R := A) e.symm
  let : IsNoetherianRing (Polynomial A') := inferInstance
  let : U.PreservesInjectiveObjects := inferInstance
  let : C.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let : C.PreservesInjectiveObjects := inferInstance
  let : PreservesFiniteLimits E := by
    apply ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    rw [show f = algebraMap A' (Polynomial A') from rfl, RingHom.flat_algebraMap_iff]
    infer_instance
  let : PreservesFiniteColimits E := inferInstance
  let : E.Additive := by
    have : PreservesColimitsOfShape (Discrete WalkingPair) E := inferInstance
    have : PreservesBinaryBiproducts E :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  let K₃ := E.mapDerivedCategory.obj K₂
  let : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv p
  let : R.PreservesInjectiveObjects := inferInstance
  have hUinj : ∀ M : ModuleCat.{v} A, Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (U.obj M) n :=
    exists_hasInjectiveDimensionLE_of_preservesInjectiveObjects U
  have hK₁ : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K₁ :=
    finiteInjectiveDimension_mapDerivedCategory U hUinj K hK.finiteInjectiveDimension
  have hCinj : ∀ M : ModuleCat.{max u v} A, Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (C.obj M) n :=
    exists_hasInjectiveDimensionLE_of_preservesInjectiveObjects C
  have hK₂ : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K₂ :=
    finiteInjectiveDimension_mapDerivedCategory C hCinj K₁ hK₁
  have hEinj : ∀ M : ModuleCat.{max u v} A', Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (E.obj M) n := by
    intro M hM
    let : Module.Injective A' M := Module.injective_module_of_injective_object A' M
    refine ⟨1, ?_⟩
    exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv
      (polynomialExtensionModuleEquiv M) 1).mpr
        (Module.tensorProduct_polynomial_hasInjectiveDimensionLE
          (A := A') (E := (M : Type (max u v))))
  have hK₃ : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K₃ :=
    finiteInjectiveDimension_mapDerivedCategory E hEinj K₂ hK₂
  have hRinj : ∀ M : ModuleCat.{max u v} (Polynomial A'), Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE (R.obj M) n :=
    exists_hasInjectiveDimensionLE_of_preservesInjectiveObjects R
  have hfiniteInjectiveDimension :
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension (polynomialBaseChange K) := by
    show StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (R.mapDerivedCategory.obj K₃)
    exact finiteInjectiveDimension_mapDerivedCategory R hRinj K₃ hK₃
  have hUfin : ∀ M : ModuleCat.{v} A, Module.Finite A M →
      Module.Finite A (U.obj M) := by
    intro M hM
    exact (Module.Finite.equiv_iff
      (ULift.moduleEquiv : U.obj M ≃ₗ[A] M)).mpr hM
  have hK₁fin : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K₁) :=
    finiteCohomology_mapDerivedCategory U hUfin K hK.finiteCohomology
  have hCfin : ∀ M : ModuleCat.{max u v} A, Module.Finite A M →
      Module.Finite A' (C.obj M) := by
    intro M hM
    let : Module.Finite A M := hM
    exact finite_restrictScalars_of_ringEquiv e M
  have hK₂fin : ∀ i : ℤ,
      Module.Finite A' ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A') i).obj K₂) :=
    finiteCohomology_mapDerivedCategory C hCfin K₁ hK₁fin
  have hK₂pseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K₂ :=
    pseudoCoherent_of_finiteInjectiveDimension_finiteCohomology K₂ hK₂ hK₂fin
  have hK₂boundedBelow : ∃ a : ℤ, K₂.IsGE a :=
    isGE_of_finiteInjectiveDimension K₂ hK₂
  have hK₂homothety : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A').homZeroEquiv
        K₂ K₂).symm (𝟙 K₂)) :=
    isIso_canonicalHomothety_ulift_change K hK
  have hK₂dualizing : IsDualizingComplex K₂ :=
    isDualizingComplex_of_canonicalHomothety K₂ hK₂ hK₂fin hK₂homothety
  have hEfin : ∀ M : ModuleCat.{max u v} A', Module.Finite A' M →
      Module.Finite (Polynomial A') (E.obj M) := by
    intro M hM
    exact (Module.Finite.equiv_iff (polynomialExtensionModuleEquiv M)).mpr
      (finite_tensorProduct_left (R := A') (S := Polynomial A') M hM)
  have hK₃fin : ∀ i : ℤ,
      Module.Finite (Polynomial A')
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Polynomial A')) i).obj K₃) :=
    finiteCohomology_mapDerivedCategory E hEfin K₂ hK₂fin
  have hfiniteCohomology : ∀ i : ℤ,
      Module.Finite (Polynomial A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Polynomial A)) i).obj
          (polynomialBaseChange K)) := by
    have hRfin : ∀ M : ModuleCat.{max u v} (Polynomial A'),
        Module.Finite (Polynomial A') M →
          Module.Finite (Polynomial A) (R.obj M) := by
      intro M hM
      let : Module.Finite (Polynomial A') M := hM
      exact finite_restrictScalars_of_ringEquiv p M
    have hK₄fin : ∀ i : ℤ,
        Module.Finite (Polynomial A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Polynomial A)) i).obj
            (R.mapDerivedCategory.obj K₃)) :=
      finiteCohomology_mapDerivedCategory R hRfin K₃ hK₃fin
    intro i
    show Module.Finite (Polynomial A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Polynomial A)) i).obj
        (R.mapDerivedCategory.obj K₃))
    exact hK₄fin i
  let : E.mapDerivedCategory.IsLeftDerivedFunctor E.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A') (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ E.mapDerivedCategoryFactors
  have hRHomBaseChange :
      IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange f E.mapDerivedCategory
        E.mapDerivedCategoryFactors.hom K₂ K₂) :=
    Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange f E.mapDerivedCategory
      E.mapDerivedCategoryFactors.hom K₂ K₂
      (Or.inr (Or.inr (Or.inl ⟨by
        rw [show f = algebraMap A' (Polynomial A') from rfl,
          RingHom.flat_algebraMap_iff]
        infer_instance, hK₂pseudo, hK₂boundedBelow⟩)))
  let hHA :
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{max u v, max u v} A').obj
        (Opposite.op K₂, K₂) ≅
      DerivedCategory.Q.obj
        (𝟙_ (CochainComplex (ModuleCat.{max u v} A') ℤ)) :=
    transportedEndomorphismIsoUnit K₂ hK₂ hK₂homothety
  let hHB :
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{max u v, max u v} (Polynomial A')).obj
        (Opposite.op K₃, K₃) ≅
      DerivedCategory.Q.obj
        (𝟙_ (CochainComplex (ModuleCat.{max u v} (Polynomial A')) ℤ)) :=
    (asIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange f E.mapDerivedCategory
      E.mapDerivedCategoryFactors.hom K₂ K₂)).symm ≪≫
      E.mapDerivedCategory.mapIso hHA ≪≫ (polynomialExtensionUnitIso).symm
  let hHBlift := liftedEndomorphismIsoUnitOfTransported K₃ hHB
  have hK₃canon : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (Polynomial A')).homZeroEquiv
        K₃ K₃).symm (𝟙 K₃)) := by
    let B := Polynomial A'
    let B' := ULift.{max u v} B
    let eB : B' ≃+* B := ULift.ringEquiv
    let F := ModuleCat.restrictScalars.{max u v} eB.toRingHom
    let G := ModuleCat.restrictScalars.{max u v} eB.symm.toRingHom
    let K' := F.mapDerivedCategory.obj K₃
    let : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eB
    let : F.PreservesInjectiveObjects := inferInstance
    have hFinObj : ∀ M : ModuleCat.{max u v} B, Injective M →
        ∃ n : ℕ, HasInjectiveDimensionLE (F.obj M) n :=
      exists_hasInjectiveDimensionLE_of_preservesInjectiveObjects F
    have hK'fin : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K' :=
      finiteInjectiveDimension_mapDerivedCategory F hFinObj K₃ hK₃
    have hK'canon : IsIso
        (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction B').homZeroEquiv
          K' K').symm (𝟙 K')) := by
      show IsIso
        (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction B').homZeroEquiv
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{max u v, max u v}
            B).functor.obj K₃)
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{max u v,
            max u v} B).functor.obj K₃)).symm
          (𝟙 ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{max u v,
            max u v} B).functor.obj K₃)))
      exact isIso_canonicalHomothety_of_endomorphism_iso_unit _ hHBlift
    have hLcanon : IsIso
        (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction B).homZeroEquiv
          (G.mapDerivedCategory.obj K') (G.mapDerivedCategory.obj K')).symm
            (𝟙 (G.mapDerivedCategory.obj K'))) :=
      isIso_canonicalHomothety_restrictScalars eB.symm K' hK'fin hK'canon
    exact isIso_canonicalHomothety_of_iso
      (derivedRestrictScalarsUnitIso eB K₃) hLcanon
  have hK₃dualizing : IsDualizingComplex K₃ :=
    isDualizingComplex_of_canonicalHomothety K₃ hK₃ hK₃fin hK₃canon
  refine ⟨hfiniteInjectiveDimension, hfiniteCohomology, ?_⟩
  intro I hrep hinj hbound
  obtain ⟨eI⟩ := hrep
  obtain ⟨a, b, hge, hle⟩ := hbound
  let G := ModuleCat.restrictScalars.{max u v} p.symm.toRingHom
  let J : CochainComplex (ModuleCat.{max u v} (Polynomial A')) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let : G.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv p.symm
  let : G.PreservesInjectiveObjects := inferInstance
  have hinjJ (i : ℤ) : Injective (J.X i) :=
    G.injective_obj_of_injective (hinj i)
  have hgeJ : J.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact G.map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp hge i hi)
  have hleJ : J.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact G.map_isZero ((CochainComplex.isStrictlyLE_iff I b).mp hle i hi)
  let eJ : DerivedCategory.Q.obj J ≅ K₃ :=
    (G.mapDerivedCategoryFactors.app I).symm ≪≫
      G.mapDerivedCategory.mapIso eI ≪≫ derivedRestrictScalarsUnitIso p K₃
  have hJ : QuasiIso (homothety J) :=
    hK₃dualizing.homothetyQuasiIso J ⟨eJ⟩ hinjJ ⟨a, b, hgeJ, hleJ⟩
  exact homothetyQuasiIso_of_restrictScalars_general p.symm I hJ

end Dualizing
