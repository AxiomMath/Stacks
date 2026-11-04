module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedModuleCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedQuasicoherentDerived
import StacksCore.Tactic.StacksAttribute

/-!
# `D_{QCoh,T}(𝒪_X)` as a module category

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let
`T ⊆ |X|` be a closed subset such that `|X| ∖ T` is quasi-compact. Stacks 0DK8 says that the
analogue of Stacks 09MC holds for `D_{QCoh,T}(𝒪_X)`: there is a differential graded algebra
`(E, d)` with only finitely many nonzero cohomology groups `H^i(E)` such that
`D_{QCoh,T}(𝒪_X)` is equivalent to `D(E, d)`. For `T = |X|` the category `D_{QCoh,T}(𝒪_X)` is
`D_QCoh(𝒪_X)` and this is Stacks 09MC itself.

## The proof

This is the source's: the argument of 09MC with 0AEC and 0AED in place of 09IY and 09M8, and
the variant of 09MA with supports. As for 09MC
(`AlgebraicGeometry.Space.exists_differentialGradedAlgebra_equivalence`) it is run on the
equi-universe model `Y` of the small étale ringed site of `X`, through the equivalence
`D(𝒪_X) ≌ D(𝒪_Y)` of `AlgebraicGeometry.Space.modelEquivalence`, so that `D(E, d)` is a category
of the right size.

* The image `𝒬_T` of `D_{QCoh,T}(𝒪_X)` in `D(𝒪_Y)` is a triangulated subcategory: so are
  `D_QCoh` and the objects whose cohomology sheaves are supported on `T`
  (`AlgebraicGeometry.Space.isTriangulated_cohomologySupportedOn`).
  It is closed under the direct sums of `D(𝒪_Y)`, because `D_QCoh` and support on a closed `T`
  are closed under the direct sums of `D(𝒪_X)`
  (`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_cohomologySupportedOn`).
* Stacks 0AEC gives a perfect generator `P` of `D_{QCoh,T}(𝒪_X)` lying in `D_{QCoh,T}`; let `K`
  be a K-injective complex on `Y` representing its image. Perfect objects are compact relative
  to `D_QCoh` (Stacks 09M8, as in the proof of 0AED), hence relative to the smaller `𝒬_T`.
* `- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒬_T` is then an equivalence for `E = Hom^•(K, K)`
  (`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalence`): its values lie in `𝒬_T`
  because `𝒬_T` is triangulated, closed under sums and contains `K` (the variant of 09MA with
  supports, `AlgebraicGeometry.RingedSite.prop_tensorWithComplexDerived_obj`), it is fully
  faithful by the compactness of `K` and 09MD, and its right adjoint has zero kernel on `𝒬_T`
  because `P` generates (Stacks 09J1).
* `H^i(E) = Hom(K, K[i]) = Hom(P, P[i])` (09MD) vanishes for `|i|` large
  (`AlgebraicGeometry.Space.exists_hom_shift_eq_zero_of_isPerfect`, half of Stacks 09MB).

## Main results

* `AlgebraicGeometry.Space.exists_differentialGradedAlgebra_equivalence_of_supported`:
  **Stacks 0DK8**.

## References

* [Stacks Project, Tag 0DK8](https://stacks.math.columbia.edu/tag/0DK8)
* [Stacks Project, Tag 09MC](https://stacks.math.columbia.edu/tag/09MC)
* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 0AED](https://stacks.math.columbia.edu/tag/0AED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- The derived categories here are the standard models, on which 09MC, 0AEC and `D_QCoh` are
-- stated; the locally small model of `D(𝒪_Y)`, whose morphisms are one universe lower, is not.

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section

variable (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))

/-- The image of `D_{QCoh,T}(𝒪_X)` in `D(𝒪_Y)`, for `Y` the equi-universe model of the small
étale ringed site of `X`: the objects whose image in `D(𝒪_X)` has quasi-coherent cohomology
sheaves supported on `T`. -/
abbrev modelQcohDerivedSupportedOn :
    ObjectProperty (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))) :=
  modelQcohDerived X ⊓
    ObjectProperty.inverseImage (CohomologySupportedOn B S hS X.1 X.2 T)
      (modelEquivalence X).inverse

/-- `D_{QCoh,T}(𝒪_X)` is equivalent to its image in `D(𝒪_Y)`. -/
def quasicoherentDerivedSupportedOnEquivModel :
    (quasicoherentDerivedSupportedOn X T).FullSubcategory ≌
      (modelQcohDerivedSupportedOn X T).FullSubcategory := by
  let e := modelEquivalence X
  let G := (quasicoherentDerivedSupportedOn X T).ι ⋙ (QcohDerived B S hS X).ι ⋙ e.functor
  have hF : ∀ M : (quasicoherentDerivedSupportedOn X T).FullSubcategory,
      modelQcohDerivedSupportedOn X T (G.obj M) := fun M =>
    ⟨(QcohDerived B S hS X).prop_of_iso (e.unitIso.app M.obj.obj) M.obj.property,
      cohomologySupportedOn_of_iso' B S hS (e.unitIso.app M.obj.obj) M.property⟩
  have : G.Faithful := inferInstanceAs (_ ⋙ _ ⋙ _).Faithful
  have : G.Full := inferInstanceAs (_ ⋙ _ ⋙ _).Full
  have : ((modelQcohDerivedSupportedOn X T).lift G hF).EssSurj :=
    ⟨fun L => ⟨⟨⟨e.inverse.obj L.obj, L.property.1⟩, L.property.2⟩,
      ⟨ObjectProperty.isoMk _ (e.counitIso.app L.obj)⟩⟩⟩
  have : ((modelQcohDerivedSupportedOn X T).lift G hF).IsEquivalence := { }
  exact ((modelQcohDerivedSupportedOn X T).lift G hF).asEquivalence

variable {X T}

/-- `D_{QCoh,T}(𝒪_X)`, read in the model, is closed under the direct sums of `D(𝒪_Y)`, for `T`
closed. -/
theorem modelQcohDerivedSupportedOn_prop_of_isColimit (hT : IsClosed T) {ι : Type u}
    (Z : ι → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)))
    (c : Cofan Z) (hc : IsColimit c) (hZ : ∀ i, modelQcohDerivedSupportedOn X T (Z i)) :
    modelQcohDerivedSupportedOn X T c.pt := by
  have hq : modelQcohDerived X c.pt :=
    modelQcohDerived_prop_of_isColimit X Z c hc fun i => (hZ i).1
  have hs : CohomologySupportedOn B S hS X.1 X.2 T ((modelEquivalence X).inverse.obj c.pt) := by
    have := isClosedUnderColimitsOfShape_cohomologySupportedOn X T hT ι
    have hc' : IsColimit ((modelEquivalence X).inverse.mapCocone c) :=
      isColimitOfPreserves (modelEquivalence X).inverse hc
    have hF : ∀ j : Discrete ι, CohomologySupportedOn B S hS X.1 X.2 T
        ((Discrete.functor Z ⋙ (modelEquivalence X).inverse).obj j) := fun j => (hZ j.as).2
    have h := @ObjectProperty.prop_of_isColimit _ _ (CohomologySupportedOn B S hS X.1 X.2 T)
      (Discrete ι) _ this (Discrete.functor Z ⋙ (modelEquivalence X).inverse) _ hc' hF
    rw [Functor.mapCocone_pt] at h
    exact h
  exact ⟨hq, hs⟩

/-- A complex on the equi-universe model whose lift is K-injective and which represents the image
of a given object of `D(𝒪_X)`. -/
theorem exists_kInjective_modelComplex_iso
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    ∃ K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ,
      (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K).IsKInjective ∧
      Nonempty ((modelEquivalence X).inverse.obj
        (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) ≅ P) := by
  let : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, u, u, u} (modelSite X).J
      (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)
  let P' := (modelEquivalence X).functor.obj P
  let M := DerivedCategory.Q.objPreimage P'
  let K := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))).obj M
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))).app M
  exact ⟨K, CochainComplex.isKInjective_of_iso (modelLiftComplexIso X K).symm,
    ⟨(modelEquivalence X).inverse.mapIso
      (DerivedCategory.Q.mapIso (modelLiftComplexIso X K) ≪≫
        (asIso (DerivedCategory.Q.map ι)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso P') ≪≫
      ((modelEquivalence X).unitIso.app P).symm⟩⟩

/-- The image in the model of a generator of `D_{QCoh,T}(𝒪_X)` generates the image of
`D_{QCoh,T}(𝒪_X)`. -/
theorem isZero_of_modelQcohDerivedSupportedOn
    (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      CohomologySupportedOn B S hS X.1 X.2 T E.obj →
        (IsZero E.obj ↔ ∀ (n : ℤ) (g : P⟦n⟧ ⟶ E.obj), g = 0))
    (eP : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) ≅ P)
    (L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)))
    (hL : modelQcohDerivedSupportedOn X T L)
    (h : ∀ (n : ℤ) (f : (DerivedCategory.Q.obj
      (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K))⟦n⟧ ⟶ L), f = 0) : IsZero L := by
  let e := modelEquivalence X
  have hz : IsZero (e.inverse.obj L) := (hgen ⟨e.inverse.obj L, hL.1⟩ hL.2).2 fun n g => by
    let eS := (e.inverse.commShiftIso n).app _ ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso eP
    have h0 := h n (e.inverse.preimage (eS.hom ≫ g))
    rw [← cancel_epi eS.hom, comp_zero, ← e.inverse.map_preimage (eS.hom ≫ g), h0,
      Functor.map_zero]
  exact (e.functor.map_isZero hz).of_iso (e.counitIso.app L).symm

variable (X T)

/-- **Stacks 0DK8.** *Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S` and let `T ⊆ |X|` be a closed subset such that `|X| ∖ T` is
quasi-compact. Then there exists a differential graded algebra `(E, d)` with only a finite number
of nonzero cohomology groups `H^i(E)` such that `D_{QCoh,T}(𝒪_X)` is equivalent to `D(E, d)`.*

This is the analogue of Stacks 09MC for `D_{QCoh,T}(𝒪_X)`, the full subcategory
`(AlgebraicGeometry.Space.quasicoherentDerivedSupportedOn X T).FullSubcategory` of `D_QCoh(𝒪_X)`
of the objects whose cohomology sheaves are supported on `T`; for `T = |X|` it is Stacks 09MC.
`E` is the endomorphism differential graded algebra of a K-injective complex representing a
perfect generator of `D_{QCoh,T}(𝒪_X)` (Stacks 0AEC), formed on the equi-universe model of the
small étale ringed site of `X`, so that its carrier and `D(E, d)` live in the universe of `X`. -/
@[stacks 0DK8]
theorem exists_differentialGradedAlgebra_equivalence_of_supported
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ E : DifferentialGradedAlgebra.{0, u} ℤ, {i : ℤ | Nontrivial (E.Cohomology i)}.Finite ∧
      Nonempty ((quasicoherentDerivedSupportedOn X T).FullSubcategory ≌
        DifferentialGradedModule.derivedCategory.{0, u, u} E) := by
  obtain ⟨P, hP, hPq, hPT, hgen⟩ :=
    exists_isPerfect_generator_of_supported B S hS X hqc hqs T hT hTc
  obtain ⟨K, hKinj, ⟨eP⟩⟩ := exists_kInjective_modelComplex_iso (X := X) P
  have hK : modelQcohDerivedSupportedOn X T
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) :=
    ⟨(QcohDerived B S hS X).prop_of_iso eP.symm hPq,
      cohomologySupportedOn_of_iso' B S hS eP.symm hPT⟩
  have hcompact : RingedSite.IsRelativelyCompactShifts.{u, u, u, u, u} (modelSite X) K
      (modelQcohDerivedSupportedOn X T) := fun A hA ι _ Z hZ T' j hj =>
    isRelativelyCompactShifts_model hqc hqs K P hP eP A hA Z (fun i => (hZ i).1) j hj
  refine ⟨(RingedSite.Rep.{u, u, u, u, u, 0} (modelSite X) ℤ K).algebra, ?_,
    ⟨(quasicoherentDerivedSupportedOnEquivModel X T).trans
      (RingedSite.tensorWithComplexDerivedEquivalence.{u, u, u, u, u} (modelSite X) K
        (modelQcohDerivedSupportedOn X T)
        (fun Z c hc hZ => modelQcohDerivedSupportedOn_prop_of_isColimit hT Z c hc hZ) hK
        hcompact (isZero_of_modelQcohDerivedSupportedOn K P hgen eP)).symm⟩⟩
  obtain ⟨lo, hi, hvan⟩ := exists_hom_shift_eq_zero_of_isPerfect X hqc hqs P hP
  refine (Set.finite_Icc lo hi).subset fun i (hne : Nontrivial _) => ?_
  by_contra hout
  have hi' : i < lo ∨ hi < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hout
  let e := modelEquivalence X
  let A := DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)
  have h0 : ∀ f : A ⟶ A⟦i⟧, f = 0 := fun f => by
    apply e.inverse.map_injective
    rw [Functor.map_zero, ← cancel_epi eP.inv, comp_zero,
      ← cancel_mono ((e.inverse.commShiftIso i).hom.app A ≫
        (CategoryTheory.shiftFunctor _ i).map eP.hom), zero_comp]
    exact hvan i hi' _
  exact not_subsingleton _ ((RingedSite.repCohomologyEquivDerivedHom.{u, u, u, u, u}
    (modelSite X) K i).subsingleton_congr.2 ⟨fun f₁ f₂ => by rw [h0 f₁, h0 f₂]⟩)

end

end AlgebraicGeometry.Space

end
