module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineLiftStep
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The lifting property of the step of Stacks 08HN, and its invariance under isomorphism

For an étale morphism `j : Z ⟶ Y` of algebraic spaces and a set `Zs` of points of `Y`, the
*supported lifting property* says: every perfect `P` on `Z` supported over `Zs`, together with a
morphism `α : P ⟶ j^*G` to the restriction of an object `G` of `D_QCoh(𝒪_Y)`, extends to a
perfect `Q` on `Y` supported on `Zs` with an isomorphism `c : P ⊕ P[1] ≅ j^*Q` and a morphism
`b : Q ⟶ G` restricting to `α ∘ pr₁`.  This is what the step of the proof of Stacks 08HN uses on
the affine member `V` of an elementary distinguished square, for `j` the inclusion of
`U ×_X V`.

The property holds for the inclusion of a quasi-compact open into an affine represented
algebraic space (`AlgebraicGeometry.Space.exists_represented_supported_lift_biprod_shift_hom`,
Stacks 08EK and 08EH carried across `ε^*`), and this file shows that it only depends on `j` up to
isomorphism: étale restriction along an isomorphism of algebraic spaces is an equivalence which
preserves perfectness, quasi-coherence and supports.

## Main definitions

* `AlgebraicGeometry.Space.SupportedLiftProperty`

## Main results

* `AlgebraicGeometry.Space.supportedLiftProperty_of_iso`: invariance under isomorphism.
* `AlgebraicGeometry.Space.supportedLiftProperty_representedOpen`: the property for the
  inclusion of a quasi-compact open into an affine represented algebraic space.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

/-- **The supported lifting property of an étale morphism `j : Z ⟶ Y` at a set `Zs` of points of
`Y`**: every perfect `P` on `Z` supported over `Zs` with a morphism `α : P ⟶ j^*G`, for `G` in
`D_QCoh(𝒪_Y)`, extends to a perfect `Q` on `Y` supported on `Zs` with an isomorphism
`c : P ⊕ P[1] ≅ j^*Q` and `b : Q ⟶ G` such that `c ≫ j^*b = pr₁ ≫ α`. -/
def SupportedLiftProperty {Y Z : AlgebraicSpaces B S hS} (j : Z ⟶ Y) (hj : IsEtale B S hS j.hom)
    (Zs : Set (points B S hS Y.1)) : Prop :=
  ∀ (P : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)),
    (smallEtaleRingedSite B S hS Z.1 Z.2).IsPerfect P →
    CohomologySupportedOn B S hS Z.1 Z.2 (pointsMap B S hS Z.1 j.hom ⁻¹' Zs) P →
    ∀ (G : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)),
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) G →
    ∀ (α : P ⟶ (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj G),
    ∃ Q : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect Q ∧
      CohomologySupportedOn B S hS Y.1 Y.2 Zs Q ∧
      ∃ (c : P ⊞ P⟦(1 : ℤ)⟧ ≅ (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj Q)
        (b : Q ⟶ G),
        c.hom ≫ (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.map b =
          biprod.fst ≫ α

/-- **Supports pull back along étale restriction**: if `E` is supported on `T`, then `E|_Y` is
supported on the inverse image of `T`. -/
theorem cohomologySupportedOn_etaleModulePullback {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (T : Set (points B S hS X.1))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2 T E) :
    CohomologySupportedOn B S hS Y.1 Y.2 (pointsMap B S hS Y.1 g.hom ⁻¹' T)
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) := fun i p hp => by
  have hp' : p ∈ supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
      ((etaleModulePullback.{u, u} B S hS g hg).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) :=
    (supportOfSheaf_eq_of_iso B S hS Y
      (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso i).app E)).le hp
  rw [supportOfSheaf_toSheaf_etaleModulePullback] at hp'
  exact hE i hp'

/-- Étale restriction along an isomorphism of algebraic spaces is an equivalence of the module
categories, with quasi-inverse the restriction along the inverse. -/
def etaleModulePullbackEquivalence {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    Modules.{u, u} B S hS Y'.1 Y'.2 ≌ Modules.{u, u} B S hS Y.1 Y.2 :=
  CategoryTheory.Equivalence.mk
    (etaleModulePullback.{u, u} B S hS e.hom (isEtale_of_isIso B S hS e.hom.hom))
    (etaleModulePullback.{u, u} B S hS e.inv (isEtale_of_isIso B S hS e.inv.hom))
    ((etaleModulePullbackIdIso B S hS (isEtale_of_isIso B S hS (𝟙 Y'.1))).symm ≪≫
      etaleModulePullbackCongr B S hS (isEtale_of_isIso B S hS (𝟙 Y'.1))
        (isEtale_of_isIso B S hS (e.inv ≫ e.hom).hom) e.inv_hom_id.symm ≪≫
      (etaleModulePullbackCompIso B S hS e.inv e.hom (isEtale_of_isIso B S hS e.inv.hom)
        (isEtale_of_isIso B S hS e.hom.hom) (isEtale_of_isIso B S hS (e.inv ≫ e.hom).hom)).symm)
    (etaleModulePullbackCompIso B S hS e.hom e.inv (isEtale_of_isIso B S hS e.hom.hom)
        (isEtale_of_isIso B S hS e.inv.hom) (isEtale_of_isIso B S hS (e.hom ≫ e.inv).hom) ≪≫
      etaleModulePullbackCongr B S hS (isEtale_of_isIso B S hS (e.hom ≫ e.inv).hom)
        (isEtale_of_isIso B S hS (𝟙 Y.1)) e.hom_inv_id ≪≫
      etaleModulePullbackIdIso B S hS (isEtale_of_isIso B S hS (𝟙 Y.1)))

instance etaleModulePullbackEquivalence_functor_additive {Y Y' : AlgebraicSpaces B S hS}
    (e : Y ≅ Y') : (etaleModulePullbackEquivalence B S hS e).functor.Additive :=
  etaleModulePullback_additive B S hS e.hom (isEtale_of_isIso B S hS e.hom.hom)

instance etaleModulePullbackEquivalence_functor_preservesFiniteLimits
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    PreservesFiniteLimits (etaleModulePullbackEquivalence B S hS e).functor :=
  preservesFiniteLimits_etaleModulePullback B S hS e.hom (isEtale_of_isIso B S hS e.hom.hom)

instance etaleModulePullbackEquivalence_functor_preservesFiniteColimits
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    PreservesFiniteColimits (etaleModulePullbackEquivalence B S hS e).functor :=
  preservesFiniteColimits_etaleModulePullback B S hS e.hom (isEtale_of_isIso B S hS e.hom.hom)

instance etaleModulePullbackEquivalence_inverse_additive {Y Y' : AlgebraicSpaces B S hS}
    (e : Y ≅ Y') : (etaleModulePullbackEquivalence B S hS e).inverse.Additive :=
  etaleModulePullback_additive B S hS e.inv (isEtale_of_isIso B S hS e.inv.hom)

instance etaleModulePullbackEquivalence_inverse_preservesFiniteLimits
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    PreservesFiniteLimits (etaleModulePullbackEquivalence B S hS e).inverse :=
  preservesFiniteLimits_etaleModulePullback B S hS e.inv (isEtale_of_isIso B S hS e.inv.hom)

instance etaleModulePullbackEquivalence_inverse_preservesFiniteColimits
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    PreservesFiniteColimits (etaleModulePullbackEquivalence B S hS e).inverse :=
  preservesFiniteColimits_etaleModulePullback B S hS e.inv (isEtale_of_isIso B S hS e.inv.hom)

instance etaleModulePullbackEquivalence_mapDerivedCategory_functor_additive
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
      (etaleModulePullbackEquivalence B S hS e)).functor.Additive :=
  inferInstanceAs ((etaleModulePullbackEquivalence B S hS e).functor.mapDerivedCategory).Additive

noncomputable instance etaleModulePullbackEquivalence_mapDerivedCategory_functor_commShift
    {Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y') :
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
      (etaleModulePullbackEquivalence B S hS e)).functor.CommShift ℤ :=
  inferInstanceAs ((etaleModulePullbackEquivalence B S hS e).functor.mapDerivedCategory.CommShift ℤ)

/-- **The supported lifting property is invariant under isomorphism.**  Given a square
`eZ ≫ j' = j ≫ eY` with `eZ`, `eY` isomorphisms, the property of `j'` at `Zs'` gives the
property of `j` at the inverse image of `Zs'`.  Restriction along `eZ` and `eY` is an equivalence
(`AlgebraicGeometry.Space.etaleModulePullbackEquivalence`), so the data on `Z` and `Y` are
carried to `Z'` and `Y'`, lifted there, and carried back by
`CategoryTheory.exists_biprod_shift_iso_comp_map_eq`. -/
theorem supportedLiftProperty_of_iso {Y Z Y' Z' : AlgebraicSpaces B S hS} (j : Z ⟶ Y)
    (hj : IsEtale B S hS j.hom) (j' : Z' ⟶ Y') (hj' : IsEtale B S hS j'.hom) (eZ : Z ≅ Z')
    (eY : Y ≅ Y') (hcomm : eZ.hom ≫ j' = j ≫ eY.hom) (Zs' : Set (points B S hS Y'.1))
    (h : SupportedLiftProperty B S hS j' hj' Zs') :
    SupportedLiftProperty B S hS j hj (pointsMap B S hS Y.1 eY.hom.hom ⁻¹' Zs') := by
  intro P hP hPZ G hG α
  let EZ := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalence B S hS eZ)
  let EY := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalence B S hS eY)
  have hE := fun {A A' : AlgebraicSpaces B S hS} (e : A ⟶ A') [IsIso e] =>
    isEtale_of_isIso B S hS e.hom
  let R₀ := (etaleModulePullback.{u, u} B S hS j' hj').mapDerivedCategory
  let R := (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
  have hjj := isEtale_comp B S hS hj (hE eY.hom)
  let FZ := (etaleModulePullbackEquivalence B S hS eZ).functor
  let FY := (etaleModulePullbackEquivalence B S hS eY).functor
  let ι : etaleModulePullback.{u, u} B S hS j' hj' ⋙ FZ ≅
      FY ⋙ etaleModulePullback.{u, u} B S hS j hj :=
    etaleModulePullbackCompIso B S hS eZ.hom j' (hE _) hj' (hcomm ▸ hjj) ≪≫
      etaleModulePullbackCongr B S hS (hcomm ▸ hjj) hjj hcomm ≪≫
      (etaleModulePullbackCompIso B S hS j eY.hom hj (hE _) _).symm
  let σ : R₀ ⋙ EZ.functor ≅ EY.functor ⋙ R :=
    (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS j' hj') FZ).symm ≪≫
      Stacks.DerivedGlueing.mapDerivedCategoryCongr ι ≪≫
      Functor.mapDerivedCategoryComp FY (etaleModulePullback.{u, u} B S hS j hj)
  let P₁ := EZ.inverse.obj P
  let G₁ := EY.inverse.obj G
  let eP : EZ.functor.obj P₁ ≅ P := EZ.counitIso.app P
  let eG : EY.functor.obj G₁ ≅ G := EY.counitIso.app G
  let α₁ : P₁ ⟶ R₀.obj G₁ :=
    EZ.fullyFaithfulFunctor.preimage (eP.hom ≫ α ≫ R.map eG.inv ≫ σ.inv.app G₁)
  have hα₁ : EZ.functor.map α₁ = eP.hom ≫ α ≫ R.map eG.inv ≫ σ.inv.app G₁ :=
    EZ.fullyFaithfulFunctor.map_preimage _
  have hP₁ : (smallEtaleRingedSite B S hS Z'.1 Z'.2).IsPerfect P₁ :=
    isPerfect_etaleModulePullback_standard B S hS eZ.inv (hE _) P hP
  have hP₁Z : CohomologySupportedOn B S hS Z'.1 Z'.2 (pointsMap B S hS Z'.1 j'.hom ⁻¹' Zs') P₁ := by
    refine (cohomologySupportedOn_etaleModulePullback B S hS eZ.inv (hE _) _ P hPZ).mono B S hS _ _
      fun p hp => ?_
    simp only [Set.mem_preimage] at hp ⊢
    have hc : eZ.inv ≫ j ≫ eY.hom = j' := by rw [← hcomm, Iso.inv_hom_id_assoc]
    rw [← hc]
    simpa only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply]
      using hp
  have hG₁ := derivedQuasicoherent_etaleModulePullback B S hS eY.inv (hE _) G hG
  obtain ⟨Q₁, hQ₁, hQ₁Z, c₀, b₀, hc₀⟩ := h P₁ hP₁ hP₁Z G₁ hG₁ α₁
  obtain ⟨c, hc⟩ := CategoryTheory.exists_biprod_shift_iso_comp_map_eq
    (hε' := etaleModulePullbackEquivalence_mapDerivedCategory_functor_commShift B S hS eZ)
    EY.functor EZ.functor R₀ R
    σ eP eG α α₁ hα₁ c₀ b₀ hc₀
  exact ⟨EY.functor.obj Q₁,
    isPerfect_etaleModulePullback_standard B S hS eY.hom (hE _) Q₁ hQ₁,
    cohomologySupportedOn_etaleModulePullback B S hS eY.hom (hE _) _ Q₁ hQ₁Z, c,
    EY.functor.map b₀ ≫ eG.hom, hc⟩

/-- **The supported lifting property for a quasi-compact open of an affine represented algebraic
space** (Stacks 08EK and 08EH, carried across `ε^*`). -/
theorem supportedLiftProperty_representedOpen (V₀ : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    (O : ((BigFppfOver.toScheme B S hS).obj V₀).Opens)
    (hO : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj V₀)))
    (Z : Set ((BigFppfOver.toScheme B S hS).obj V₀)) (hZ : IsClosed Z) (hZc : IsCompact Zᶜ) :
    SupportedLiftProperty B S hS (representedSpaceMap B S hS (openIncl B S hS V₀ O))
      (isEtale_representedSpaceMap_openIncl B S hS V₀ O) ((pointsEquivScheme B S hS V₀) ⁻¹' Z) :=
  fun P hP hPZ G hG α =>
    exists_represented_supported_lift_biprod_shift_hom B S hS V₀ O hO Z hZ hZc P hP hPZ G hG α

end AlgebraicGeometry.Space
