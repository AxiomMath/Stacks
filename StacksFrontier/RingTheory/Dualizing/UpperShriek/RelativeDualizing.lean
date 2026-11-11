module

public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionDuality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionHomothety
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.HomothetyOverRing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Bounded
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative dualizing complex of a perfect homomorphism

Let `φ : R →+* A` be a homomorphism of finite type of Noetherian rings, presented by `p` with
polynomial algebra `P`. The relative dualizing complex of `φ` is `ω_{A/R} = φ^!(R)`, the value of
the upper shriek functor of `p` at `R` placed in cohomological degree zero. When `φ` is perfect,
`ω_{A/R}` lies in `Dᵇ_Coh(A)`, hence is pseudo-coherent over `A`, and the canonical map
`A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` is an isomorphism. A flat `φ` is perfect, so the first two
statements also hold for flat `φ` with no further hypothesis.

## Main definitions

* `Dualizing.extendScalarsULiftTensorUnitModuleIso`: extension of scalars along `S →+* T` carries
  the universe-lifted `S` to the universe-lifted `T`.
* `Dualizing.PolynomialPresentation.derivedExtensionTensorUnitIso`: derived base change along the
  presentation carries the unit of `D(R)` to the unit of `D(P)`.

## Main results

* `Dualizing.derivedCategoryBBounded_singleFunctor_obj`: a finite module placed in degree zero
  lies in `Dᵇ_Coh(R)`.
* `Dualizing.isPseudoCoherent_of_derivedCategoryBMinus`: over a Noetherian ring, a
  cohomologically bounded-above object with finite cohomology is pseudo-coherent.
* `Dualizing.PolynomialPresentation.upperShriekFunctor_unit_derivedCategoryBBounded`: if `A` is a
  perfect `P`-module, then `ω_{A/R}` lies in `Dᵇ_Coh(A)`.
* `Dualizing.upperShriekFunctor_unit_derivedCategoryBBounded_of_perfect`: for a perfect
  `φ`, `ω_{A/R}` lies in `Dᵇ_Coh(A)`.
* `Dualizing.upperShriekFunctor_unit_isPseudoCoherent_of_perfect`: for a perfect `φ`,
  `ω_{A/R}` is pseudo-coherent over `A`.
* `Dualizing.upperShriekFunctor_unit_derivedCategoryBBounded_of_flat`: for a flat `φ`, `ω_{A/R}`
  lies in `Dᵇ_Coh(A)`.
* `Dualizing.upperShriekFunctor_unit_isPseudoCoherent_of_flat`: for a flat `φ`, `ω_{A/R}` is
  pseudo-coherent over `A`.
* `Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule`: if `A` is a
  perfect `P`-module, the derived homothety `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` is an isomorphism.
* `Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isDualizingComplex`: the derived
  homothety `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` is an isomorphism when `P` is its own dualizing
  complex.
* `Dualizing.nonempty_presentationDerivedHom_self_iso_doubleDual`: the derived endomorphisms of
  `RHom_P(A, M)`, read in `D(P)`, are the double dual `RHom_P(RHom_P(A, M), M)`.

## Implementation notes

The module universe `max v u` is independent of the ring universe `u`, so the ring `R`, regarded
as a module over itself in that universe, is `ULift.{v} R`. Every statement is made for an
arbitrary polynomial presentation `p` of `φ`.

## References

* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0DHS](https://stacks.math.columbia.edu/tag/0DHS)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- A finite `R`-module placed in cohomological degree zero lies in `Dᵇ_Coh(R)`. -/
theorem derivedCategoryBBounded_singleFunctor_obj (M : ModuleCat.{max v u} R)
    (hM : Module.Finite R M) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{max v u} R ↦ Module.Finite R N)
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M) := by
  have e : ∀ i : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M) ≅
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) 0).obj M).homology i :=
    fun i ↦ (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} R) i).app
      ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) 0).obj M)
  have hzero : ∀ i : ℤ, i ≠ 0 → Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj M)) :=
    fun i hi ↦ (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso (e i)
  refine ⟨⟨⟨0, fun n hn ↦ hzero n (by omega)⟩, ⟨0, fun n hn ↦ hzero n (by omega)⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact Module.Finite.equiv
      (e 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).toLinearEquiv.symm
  · let := ModuleCat.subsingleton_of_isZero (hzero n hn)
    infer_instance

/-- The unit `R`, lifted to the module universe and placed in degree zero, lies in `Dᵇ_Coh(R)`. -/
private theorem derivedCategoryBBounded_singleFunctor_obj_ulift :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{max v u} R ↦ Module.Finite R N)
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (ULift.{v} R))) :=
  derivedCategoryBBounded_singleFunctor_obj.{u, v} (ModuleCat.of R (ULift.{v} R))
    (Module.Finite.equiv (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).symm)

/-- Over a Noetherian ring `A`, a cohomologically bounded-above object of `D(A)` whose
cohomology modules are finite is pseudo-coherent. -/
@[sga "6 I 5.0" "more general"]
theorem isPseudoCoherent_of_derivedCategoryBMinus [IsNoetherianRing A]
    {X : DerivedCategory (ModuleCat.{max v u} A)}
    (hX : DerivedCategoryB.derivedCategoryBMinus
      (fun N : ModuleCat.{max v u} A ↦ Module.Finite A N) X) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent X := by
  let : Small.{max v u} A := small_max.{v} A
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    X 0 (ULift.{v} A)).2.1.mpr ⟨hX.1, hX.2⟩

namespace PolynomialPresentation

/-- The relative dualizing complex `ω_{A/R} = φ^!(R)` lies in `Dᵇ_Coh(A)` when `A` is a perfect
module over the polynomial algebra of the presentation `p`. -/
theorem upperShriekFunctor_unit_derivedCategoryBBounded [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly A := Module.compHom A p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) A) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{max v u} A ↦ Module.Finite A N)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R)))) :=
  p.upperShriekFunctor_derivedCategoryBBounded.{u, v} hperf
    derivedCategoryBBounded_singleFunctor_obj_ulift.{u, v}

end PolynomialPresentation

/-- Let `φ : R →+* A` be a perfect homomorphism of finite type of Noetherian rings. Then the
relative dualizing complex `ω_{A/R} = φ^!(R)` lies in `Dᵇ_Coh(A)`. -/
@[stacks 0BZW "(1)(a)", sga "5 III 6.2" "partial"]
theorem upperShriekFunctor_unit_derivedCategoryBBounded_of_perfect
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f) (hf : f.Perfect) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{max v u} A ↦ Module.Finite A N)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R)))) :=
  upperShriekFunctor_derivedCategoryBBounded_of_perfect.{u, v} p hf
    derivedCategoryBBounded_singleFunctor_obj_ulift.{u, v}

/-- The relative dualizing complex `ω_{A/R} = φ^!(R)` of a perfect homomorphism of finite type of
Noetherian rings is pseudo-coherent over `A`. -/
theorem upperShriekFunctor_unit_isPseudoCoherent_of_perfect
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f) (hf : f.Perfect) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R)))) :=
  have h := upperShriekFunctor_unit_derivedCategoryBBounded_of_perfect.{u, v} p hf
  isPseudoCoherent_of_derivedCategoryBMinus.{u, v} ⟨h.1.2, h.2⟩

/-- For a flat homomorphism `φ : R →+* A` of finite type of Noetherian rings, the relative
dualizing complex `ω_{A/R} = φ^!(R)` lies in `Dᵇ_Coh(A)`. -/
theorem upperShriekFunctor_unit_derivedCategoryBBounded_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f) (hflat : f.Flat) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{max v u} A ↦ Module.Finite A N)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R)))) := by
  let : Algebra R A := f.toAlgebra
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact upperShriekFunctor_unit_derivedCategoryBBounded_of_perfect.{u, v} p
    (RingHom.perfect_algebraMap.mpr (Algebra.Perfect.of_flat_of_finitePresentation R A))

/-- The relative dualizing complex `ω_{A/R} = φ^!(R)` of a flat homomorphism of finite type of
Noetherian rings is pseudo-coherent over `A`. -/
@[sga "5 III 6.2" "partial"]
theorem upperShriekFunctor_unit_isPseudoCoherent_of_flat
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f) (hflat : f.Flat) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R)))) :=
  have h := upperShriekFunctor_unit_derivedCategoryBBounded_of_flat.{u, v} p hflat
  isPseudoCoherent_of_derivedCategoryBMinus.{u, v} ⟨h.1.2, h.2⟩

/-- Suppose the derived base change of `R`, placed in degree zero, to the polynomial algebra `P`
of the presentation is a dualizing complex over `P`, that is, `P` is its own dualizing complex.
Then the derived homothety `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` of the derived Hom adjunction over `A`
is an isomorphism. Perfectness of `φ` is not assumed. -/
theorem upperShriekFunctor_unit_isIso_derivedHomothety_of_isDualizingComplex
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation f)
    (hP : IsDualizingComplex
      (p.derivedExtension.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) :
    IsIso (derivedHomothety (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v} A)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  have hdual : IsDualizingComplex
      ((derivedHom.{u, v, u} p.toRingHom).obj
        (p.derivedExtension.{u, v}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
            (ModuleCat.of R (ULift.{v} R))))) :=
    isDualizingComplex_derivedHom_of_finite.{u, v} p.toRingHom p.finite_toRingHom _ hP
  exact isIso_derivedHomothety_overRing_of_isDualizingComplex.{u, v} A _
    (isDualizingComplex_shift _ hdual (p.variableCount : ℤ))


/-- Extension of scalars along `g : S →+* T` carries `S`, lifted to the module universe
`max v u`, to the lifted `T`; the isomorphism is the right unitor of the tensor product read
through the two universe lifts. -/
noncomputable def extendScalarsULiftTensorUnitModuleIso {S T : Type u} [CommRing S] [CommRing T]
    (g : S →+* T) :
    (ModuleCat.extendScalars.{u, u, max v u} g).obj (ModuleCat.of S (ULift.{v} S)) ≅
      derivedTensorUnitModule.{u, v} T := by
  letI := g.toAlgebra
  exact LinearEquiv.toModuleIso
    (((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T)
          (ULift.moduleEquiv (R := S) (M := S))).trans
        (TensorProduct.AlgebraTensorModule.rid S T T)).trans
      (show T ≃ₗ[T] ULift.{max v u} T from
        { toFun := fun a => ULift.up a
          invFun := fun x => x.down
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }))

/-- Derived base change along the presentation carries the unit of `D(R)` to the unit of `D(P)`:
the identification `R ⊗_R^L P ≅ P` in degree zero. -/
noncomputable def PolynomialPresentation.derivedExtensionTensorUnitIso
    (p : PolynomialPresentation f) :
    p.derivedExtension.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))) ≅
      StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} p.Poly := by
  letI : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  exact ((ModuleCat.extendScalars.{u, u, max v u}
        (MvPolynomial.C : R →+* p.Poly)).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of R (ULift.{v} R)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} p.Poly) 0).mapIso
      (extendScalarsULiftTensorUnitModuleIso.{u, v} (MvPolynomial.C : R →+* p.Poly)) ≪≫
    (derivedTensorUnitIsoSingle.{u, v} p.Poly).symm

/-- Let `R` be Noetherian and `φ : R →+* A` presented by `p`, and suppose `A` is a perfect module
over the polynomial algebra `P` of the presentation. Then the derived homothety
`A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` of the derived Hom adjunction over `A` is an isomorphism.

The perfectness hypothesis is stated for `A` lifted to the module universe `max v u` in which
upper shriek is formed. -/
@[sga "5 III 6.2" "special case", sga "6 III 4.9.2" "special case"]
theorem upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule [IsNoetherianRing R]
    (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly (ULift.{max v u} A) :=
        Module.compHom (ULift.{max v u} A) p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{max v u} A)) :
    IsIso (derivedHomothety (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, v} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v} A)
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  set ωP := p.derivedExtension.{u, v}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (ModuleCat.of R (ULift.{v} R)))
  set eU := PolynomialPresentation.derivedExtensionTensorUnitIso.{u, v} p
  have : ωP.IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (eU ≪≫ derivedTensorUnitIsoSingle.{u, v} p.Poly).symm 0
  obtain ⟨I, hIge, hIinj, ⟨eI⟩⟩ := exists_injectiveRepresentative ωP 0
  have hbid : IsIso (dualizingBidualityMor.{u, max v u} p.Poly ωP
      (targetSingle.{u, v} p.toRingHom)) := by
    change IsIso (bidualityMor
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} p.Poly) ωP
      (targetSingle.{u, v} p.toRingHom))
    refine isIso_bidualityMor_of_iso_dualizing _ eU.symm _ ?_
    exact isIso_dualizingBidualityMor_derivedTensorUnit_of_isPerfect.{u, v}
      (targetSingle.{u, v} p.toRingHom)
      (isPerfect_scalarPreimage_targetSingle.{u, v} p.toRingHom hperf)
  exact isIso_derivedHomothety_overRing_derivedHom_shift.{u, v} p.toRingHom I 0 hIge hIinj eI
    hbid (p.variableCount : ℤ) (Iso.refl _)

/-- For an object `M` of `D(P)`, where `P` is the polynomial algebra of a presentation `p` of `φ`,
the internal derived Hom from `RHom_P(A, M)` to itself, formed over `A` and read in `D(P)` by
restriction of scalars along the presentation's surjection, is `RHom_P(RHom_P(A, M), M)`. -/
theorem nonempty_presentationDerivedHom_self_iso_doubleDual (p : PolynomialPresentation f)
    (M : DerivedCategory (ModuleCat.{u} p.Poly)) :
    Nonempty
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
            (Opposite.op ((derivedHom.{u, u, u} p.toRingHom).obj M),
              (derivedHom.{u, u, u} p.toRingHom).obj M)) ≅
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom p.Poly).obj
          (Opposite.op ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom p.Poly).obj
            (Opposite.op (targetSingleModel.{u} p.toRingHom), M)), M)) :=
  nonempty_modelHom_derivedHom_self_iso_doubleDual.{u} p.toRingHom M

end Dualizing

end
