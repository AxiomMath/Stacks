module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionSupportedDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.KInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

/-!
# `Rj_*` computes `F ↦ j_*(F|_U)` on the unbounded derived category

Let `i : Z ⟶ X` be a closed immersion of schemes in a big étale site and let `j : U ⟶ X` be the
inclusion of the open complement.  Restriction to the open complement
`j^{-1} : Ab(X_étale) ⥤ Ab(U_étale)` is exact, so it descends to the unbounded derived
categories as `j^{-1} : D(X_étale) ⥤ D(U_étale)`, and the composite with the right derived
functor `Rj_* : D(U_étale) ⥤ D(X_étale)` of direct image is a right derived functor of the left
exact functor `F ↦ j_*(F|_U)` of `AlgebraicGeometry.complementRestrictPush`.

This is the derived half of the short exact sequence
`0 ⟶ i_*ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` of
`AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective`:
it says that the third term of
that sequence of functors is computed on the derived category by `Rj_* ∘ j^{-1}`.

## Main results

* `CochainComplex.isKInjective_mapHomologicalComplex_of_natIso` and
  `CochainComplex.isKInjective_mapHomologicalComplex_inverse` — two transfer lemmas for the
  property of carrying K-injective cochain complexes to K-injective cochain complexes: it is
  invariant under a natural isomorphism of the functor, and the quasi-inverse of an equivalence
  has it.
* `AlgebraicGeometry.isKInjective_complementPullback` — [Stacks, Tag 08FI] for restriction to
  the open complement of a closed immersion: it carries K-injective complexes of abelian
  sheaves to K-injective complexes.
* `AlgebraicGeometry.complementRestrictPushDerivedUnit` — the comparison map exhibiting
  `j^{-1} ⋙ Rj_*` as a candidate right derived functor of `F ↦ j_*(F|_U)`.
* `AlgebraicGeometry.isRightDerivedFunctor_complementRestrictPush` — that comparison exhibits
  it as the right derived functor.
* `AlgebraicGeometry.exists_distTriang_supportedSections_derivedPushforward` — the
  distinguished triangle of [Stacks, Tag 0A45] with its third vertex the honest
  `Rj_*(K|_U)`.

## Implementation notes

K-injectivity is transported from the localized site rather than proved again.  Restriction to
the open complement is, up to the isomorphism
`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose` and the equality
`AlgebraicGeometry.overPullback_comp_sheafCongr_inverse`, the composite of restriction to the
localization of the small étale site of `X` at the open complement with the quasi-inverse of
the slice equivalence of [Stacks, Tag 03S3].  The first factor carries K-injective complexes to
K-injective complexes because its left adjoint, extension by zero, is exact — that is
`CategoryTheory.SemiRepresentable.isKInjective_overPullback_mapHomologicalComplex_obj`, the
one-object case of [Stacks, Tag 0D88] — and the second does because it is the quasi-inverse of
an equivalence; both are instances of the adjoint criterion
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, [Stacks, Tag 08BJ].

That the comparison map exhibits a right derived functor is then
`isRightDerivedFunctor_of_isIso_app_isKInjective`: the comparison is built from the unit of
`Rj_*`, and at a K-injective complex `I` of `Ab(X_étale)` that unit is evaluated at the complex
`I|_U`, which is K-injective, so it is invertible there.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (isRightDerivedFunctor_of_isIso_app_isKInjective)

universe v₁ v₂ u₁ u₂ u

namespace CochainComplex

/-- **Carrying K-injective complexes to K-injective complexes is invariant under a natural
isomorphism.** If `F ≅ G` are additive functors of abelian categories and `F` carries the
cochain complex `I` to a K-injective complex, then so does `G`: the two images are isomorphic
complexes, and K-injectivity is invariant under an isomorphism of complexes. -/
public theorem isKInjective_mapHomologicalComplex_of_natIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {F G : A ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (I : CochainComplex A ℤ)
    (h : IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := h
  isKInjective_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app I)

/-- **The quasi-inverse of an equivalence of abelian categories carries K-injective complexes to
K-injective complexes.** It is a right adjoint whose left adjoint, the functor of the
equivalence, is exact, so this is the adjoint criterion [Stacks, Tag 08BJ]. -/
public theorem isKInjective_mapHomologicalComplex_inverse
    {A : Type u₁} [Category.{v₁} A] [Abelian A] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (e : A ≌ D) (I : CochainComplex D ℤ) [I.IsKInjective] :
    IsKInjective ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  isKInjective_mapHomologicalComplex_of_exact e.inverse e.functor e.toAdjunction I

end CochainComplex

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- **[Stacks, Tag 08FI] for the open complement of a closed immersion.** Restriction to the
open complement carries a K-injective cochain complex of abelian sheaves on the small étale site
of `X` to a K-injective complex of abelian sheaves on the small étale site of the complement.

Restriction to the open complement is restriction to the localization of the small étale site of
`X` at the complement, read through the slice equivalence of [Stacks, Tag 03S3]; the first of
those two functors has an exact left adjoint, namely extension by zero, and the second is the
quasi-inverse of an equivalence. -/
public theorem isKInjective_complementPullback
    (I : CochainComplex (SmallEtaleAbelianSheaf B X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  set V := complementEtaleObj B i with hV
  set P := (SmallEtale.topology B X.obj X.property).overPullback AddCommGrpCat.{u + 1} V with hP
  set E := (smallEtaleEquivalenceOver B X.obj X.property V).sheafCongr
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    ((SmallEtale.topology B X.obj X.property).over V) AddCommGrpCat.{u + 1} with hE
  have h1 : CochainComplex.IsKInjective ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CategoryTheory.SemiRepresentable.isKInjective_overPullback_mapHomologicalComplex_obj.{u + 1,
      u, u + 1} _ _ I
  have := h1
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have h2 : CochainComplex.IsKInjective ((E.inverse.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    CochainComplex.isKInjective_mapHomologicalComplex_inverse E _
  have : (P ⋙ E.inverse).Additive := inferInstance
  have h3 : CochainComplex.IsKInjective
      (((P ⋙ E.inverse).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
    have : CochainComplex.IsKInjective
        ((P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := h2
    exact CochainComplex.isKInjective_of_iso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ E.inverse))
        (ComplexShape.up ℤ)).app I)
  have key := smallEtaleSheafPullbackIsoPostcompose B X.obj X.property V AddCommGrpCat.{u + 1} ≪≫
    eqToIso (overPullback_comp_sheafCongr_inverse B X.obj X.property V
      AddCommGrpCat.{u + 1}).symm
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_natIso key.symm I h3

section Derived

variable [HasDerivedCategory.{u + 1} (SmallEtaleAbelianSheaf B X)]
  [HasDerivedCategory.{u + 1} (SmallEtaleAbelianSheaf B (closedComplement B i))]

/-- Direct image along the inclusion of the open complement has a right derived functor on the
unbounded derived category, computed by K-injective resolutions: abelian sheaves on a small
étale site form a Grothendieck abelian category, so every complex of them receives a
quasi-isomorphism into a K-injective complex. -/
public instance hasPointwiseRightDerivedFunctor_complementPushforward :
    Functor.HasPointwiseRightDerivedFunctor
      ((Stacks.HigherDirectImage.pushforward.{u, u + 1} B
        (closedComplementInclusion B i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B (closedComplement B i))
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0} _
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B (closedComplement B i))).1

/-- `Rj_* : D(U_étale) ⥤ D(X_étale)`, the total right derived functor of direct image along the
inclusion of the open complement. -/
public abbrev complementDerivedPushforward :
    DerivedCategory (SmallEtaleAbelianSheaf B (closedComplement B i)) ⥤
      DerivedCategory (SmallEtaleAbelianSheaf B X) :=
  ((Stacks.HigherDirectImage.pushforward.{u, u + 1} B
      (closedComplementInclusion B i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B (closedComplement B i))
      (ComplexShape.up ℤ))

/-- The comparison map exhibiting `Rj_*` as the right derived functor of direct image along the
inclusion of the open complement. -/
public abbrev complementDerivedPushforwardUnit :
    (Stacks.HigherDirectImage.pushforward.{u, u + 1} B
        (closedComplementInclusion B i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ complementDerivedPushforward B i :=
  ((Stacks.HigherDirectImage.pushforward.{u, u + 1} B
      (closedComplementInclusion B i)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B (closedComplement B i))
      (ComplexShape.up ℤ))

/-- **The comparison map exhibiting `j^{-1} ⋙ Rj_*` as a candidate right derived functor of
`F ↦ j_*(F|_U)`.** It is the unit of `Rj_*` whiskered with restriction to the open complement,
read through the identification `Qh ⋙ j^{-1} ≅ K(j^{-1}) ⋙ Qh` of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` — available because `j^{-1}` is exact — and
through the identification of `K(j^{-1} ⋙ j_*)` with `K(j^{-1}) ⋙ K(j_*)`. -/
public def complementRestrictPushDerivedUnit :
    (complementRestrictPush B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (SmallEtale.openRestriction.{u, u + 1} B
          (closedComplementInclusion B i)).mapDerivedCategory ⋙
            complementDerivedPushforward B i :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (SmallEtale.openRestriction.{u, u + 1} B (closedComplementInclusion B i) ⋙
        Stacks.HigherDirectImage.pushforward.{u, u + 1} B (closedComplementInclusion B i)))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (complementDerivedPushforwardUnit B i) ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (SmallEtale.openRestriction.{u, u + 1} B
      (closedComplementInclusion B i)).mapDerivedCategoryFactorsh.symm
      (complementDerivedPushforward B i)).hom ≫
    (Functor.associator _ _ _).hom

/-- **`Rj_* ∘ j^{-1}` is the right derived functor of `F ↦ j_*(F|_U)`**, for the comparison map
`AlgebraicGeometry.complementRestrictPushDerivedUnit`.

A comparison map invertible at the K-injective complexes exhibits its functor as a right derived
functor.  At a K-injective complex `I` of abelian sheaves on `X_étale` the comparison is, up to
isomorphisms, the unit of `Rj_*` evaluated at `I|_U`, which is K-injective by
`AlgebraicGeometry.isKInjective_complementPullback`; the unit of `Rj_*` is invertible at
K-injective complexes because `Rj_*` is computed by K-injective resolutions. -/
public theorem isRightDerivedFunctor_complementRestrictPush :
    ((SmallEtale.openRestriction.{u, u + 1} B
        (closedComplementInclusion B i)).mapDerivedCategory ⋙
      complementDerivedPushforward B i).IsRightDerivedFunctor
      (complementRestrictPushDerivedUnit B i)
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective _
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B X) _ _ _ ?_
  intro I hI
  have := hI
  have hK : CochainComplex.IsKInjective
      (((SmallEtale.openRestriction.{u, u + 1} B
        (closedComplementInclusion B i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_complementPullback B i I
  have : IsIso ((complementDerivedPushforwardUnit B i).app
      (((SmallEtale.openRestriction.{u, u + 1} B
          (closedComplementInclusion B i)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SmallEtaleAbelianSheaf B X)
          (ComplexShape.up ℤ)).obj I))) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective _
      (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B (closedComplement B i))).2
      DerivedCategory.Qh (complementDerivedPushforward B i)
      (complementDerivedPushforwardUnit B i) _ hK
  dsimp only [complementRestrictPushDerivedUnit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- **Stacks 0A45, the distinguished triangle at `Rj_*(-|_U)`.**  The third assertion of
`AlgebraicGeometry.exists_distTriang_supportedSections` instantiated at the honest right derived
functor of `j_*` precomposed with restriction to the open complement: for a right derived
functor `RH` of `F ↦ i_*ℋ_Z(F)` and `RI` of the identity, the triangle

`i_*Rℋ_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ i_*Rℋ_Z(K)⟦1⟧`

is distinguished at every object `K` of `D(X_étale)`, the first two maps being the derived
versions of the canonical maps `i_*ℋ_Z ⟶ 𝟭` and `𝟭 ⟶ j_*(-|_U)`.

`Rj_* ∘ j^{-1}` is a right derived functor of `F ↦ j_*(F|_U)` by
`AlgebraicGeometry.isRightDerivedFunctor_complementRestrictPush`, so this is a special case of
the triangle stated for an arbitrary triple of right derived functors. -/
public theorem exists_distTriang_supportedSections_derivedPushforward
    (RH RI : DerivedCategory (SmallEtaleAbelianSheaf B X) ⥤
      DerivedCategory (SmallEtaleAbelianSheaf B X))
    (aH : (supportedSectionsPushforward B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (aI : (𝟭 (SmallEtaleAbelianSheaf B X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RI)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))]
    [RI.IsRightDerivedFunctor aI
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))] :
    ∃ (rf : RH ⟶ RI)
      (rg : RI ⟶ (SmallEtale.openRestriction.{u, u + 1} B
        (closedComplementInclusion B i)).mapDerivedCategory ⋙ complementDerivedPushforward B i)
      (δ : ((SmallEtale.openRestriction.{u, u + 1} B
          (closedComplementInclusion B i)).mapDerivedCategory ⋙
            complementDerivedPushforward B i) ⟶
        RH ⋙ shiftFunctor (DerivedCategory (SmallEtaleAbelianSheaf B X)) (1 : ℤ)),
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (supportedSectionsPushforwardInclusion B i) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ aI =
        aH ≫ Functor.whiskerLeft DerivedCategory.Qh rf ∧
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (complementRestriction B i) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ complementRestrictPushDerivedUnit B i =
        aI ≫ Functor.whiskerLeft DerivedCategory.Qh rg ∧
      ∀ K, CategoryTheory.Pretriangulated.Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        CategoryTheory.Pretriangulated.distinguishedTriangles
          (C := DerivedCategory (SmallEtaleAbelianSheaf B X)) :=
  have := isRightDerivedFunctor_complementRestrictPush B i
  exists_distTriang_supportedSections B i RH RI _ aH aI
    (complementRestrictPushDerivedUnit B i)

end Derived

end AlgebraicGeometry

end
