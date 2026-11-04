module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativelyAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeIsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralPushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeTrace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDenseBlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleMain
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteLocallyFreeAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup

/-!
# Blowing up to the resolution property

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` whose point space
has finitely many irreducible components.  Given a quasi-compact open `U ⊆ X` with dense point
set and a surjective proper morphism `g : Y ⟶ X` which is finite locally free over `U`, with `Y`
quasi-compact, quasi-separated and carrying the resolution property, there is a `U`-admissible
blowing up `X' ⟶ X` whose source has the resolution property.  This is the conclusion of
Stacks 0GV5 given the cover of steps 1 and 2 of its proof.

## Main definitions

* `AlgebraicGeometry.Space.IsFiniteLocallyFreeOverOpenSubspace`: a morphism `g : Y ⟶ X` is
  finite locally free over an open subspace `U ⊆ X`.

## Main results

* `hasResolutionProperty_strictTransformSpace_of_isBlowupAlong`: for `g : Y ⟶ X` with `Y`
  quasi-compact, quasi-separated and carrying the resolution property, and for `b : X' ⟶ X` the
  blowing up of `X` in a closed subspace `Z` whose closed immersion is of finite presentation,
  the strict transform of `Y` along `b` has the resolution property.
* `isSurjective_strictTransformSpaceToBlowUp_of_isSurjective`: the strict transform of a
  surjective morphism along a blowing up is surjective over the blowing up, as soon as it is
  finite locally free there.
* `isFiniteLocallyFree_restrictOverHom_of_isFiniteLocallyFreeOverOpenSubspace`: finite local
  freeness over an open subspace, read on the base change formed in presheaves.
* `exists_isBlowupAlong_isFiniteLocallyFree_strictTransform_of_isFiniteLocallyFreeOverOpen`:
  a proper morphism finite locally free over a quasi-compact open `U` has a strict transform
  that is finite locally free along a blowing up in a centre disjoint from `U` (Stacks 0B4K).
* `exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover`: the
  conclusion of Stacks 0GV5 from a surjective proper cover with the resolution property, finite
  locally free over a dense quasi-compact open.
* `exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover`: the
  same with the cover representable and its resolution property asked of the representing
  scheme.
* `finite_irreducibleComponents_points_yoneda_iff`: the point space of a representable
  algebraic space has finitely many irreducible components exactly when the representing scheme
  does.

## References

* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0B4K](https://stacks.math.columbia.edu/tag/0B4K)
* [Stacks Project, Tag 0GM2](https://stacks.math.columbia.edu/tag/0GM2)
* [Stacks Project, Tag 0BAL](https://stacks.math.columbia.edu/tag/0BAL)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZY](https://stacks.math.columbia.edu/tag/03ZY)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 0GTP](https://stacks.math.columbia.edu/tag/0GTP)
* [Stacks Project, Tag 0GMM](https://stacks.math.columbia.edu/tag/0GMM)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`g` is finite locally free over the open subspace `U`**: the base change of `g` along the
open immersion of `U` is finite locally free in the sense of Stacks 03ZV. -/
abbrev IsFiniteLocallyFreeOverOpenSubspace {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (U : OpenSubspaces B S hS X.1) : Prop :=
  IsFiniteLocallyFree B S hS
    (pullback.snd g (ObjectProperty.homMk U.1.ι :
      (⟨U.1.toFunctor, U.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X))

/-- **The strict transform along a blowing up inherits the resolution property.**  Let `g : Y ⟶ X`
be an algebraic space over `X`, with `Y` quasi-compact, quasi-separated and carrying the
resolution property, and let `b : X' ⟶ X` be the blowing up of `X` in a closed subspace `Z`
whose closed immersion is of finite presentation.  Then the strict transform of `Y` along `b`
has the resolution property. -/
theorem hasResolutionProperty_strictTransformSpace_of_isBlowupAlong
    {X Y X' : AlgebraicSpaces B S hS} (g : Y ⟶ X) {Z : ClosedSubspaces B S hS X.1}
    (hfp : IsFinitePresentation B S hS Z.1.ι) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (hYres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, u} B S hS
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1).1
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1).2 := by
  have hbl := isBlowupAlong_strictTransform B S hS g b Z hb
  have hfp' : IsFinitePresentation B S hS (preimageClosedSubspace g Z).1.ι :=
    isFinitePresentation_ι_preimage g Z hfp
  have hinv : IsInvertibleModule
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1)
      (idealSheafOfModules B S hS
        (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1)
        (preimageClosedSubspace (strictTransformSpaceι B S hS g b
            (preimageClosedSubspace b Z).1 ≫ strictTransformPullbackToSource B S hS g b)
          (preimageClosedSubspace g Z))) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hbl.isPullbackDefined
  exact hasResolutionProperty_source_of_isRelativelyAmple B.contains_terminal _ _ hinv
    (isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong hfp' hbl) hYqc hYqs hYres

/-- **The strict transform of a surjective morphism along a blowing up is surjective.**  Let
`g : Y ⟶ X` be a surjective morphism of algebraic spaces, let `b : X' ⟶ X` be the blowing up of
`X` in a closed subspace `Z`, and suppose the strict transform of `Y` along `b` is finite locally
free over `X'`.  Then it is surjective over `X'`. -/
theorem isSurjective_strictTransformSpaceToBlowUp_of_isSurjective
    {X Y X' : AlgebraicSpaces B S hS} (g : Y ⟶ X) {Z : ClosedSubspaces B S hS X.1}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) (hgsurj : IsSurjective B S hS g.hom)
    (hflf : IsFiniteLocallyFree B S hS
      (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1)) :
    IsSurjective B S hS
      (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1).hom := by
  have hclosed : IsClosed (Set.range (pointsMap B S hS
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1).1
      (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1).hom)) :=
    isClosed_range_pointsMap_of_isIntegralHom B S hS _
      (IsFinite.isIntegralHom B S hS (isFinite_of_isFiniteLocallyFree B S hS _ hflf))
  have hdense : Dense (subspacePointSet B S hS X'.1
      ((openComplementOfClosedSubspace B S hS X Z).1.preimage b.hom)) :=
    dense_subspacePointSet_preimage_of_isBlowupAlong
      (openComplementOfClosedSubspace B S hS X Z) Z hb
      (by rw [subspacePointSet_openComplement B S hS X Z, compl_compl])
  have hsub : subspacePointSet B S hS X'.1
      ((openComplementOfClosedSubspace B S hS X Z).1.preimage b.hom) ⊆
      Set.range (pointsMap B S hS
        (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1).1
        (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1).hom) := by
    intro x hx
    obtain ⟨p, hp⟩ := isSurjective_pullback_snd B S hS Y.2 X.2 X'.2 g.hom b.hom hgsurj x
    have hbx : pointsMap B S hS X'.1 b.hom x ∉ subspacePointSet B S hS X.1 Z.1 := by
      rwa [show subspacePointSet B S hS X'.1
            ((openComplementOfClosedSubspace B S hS X Z).1.preimage b.hom) =
            pointsMap B S hS X'.1 b.hom ⁻¹'
              subspacePointSet B S hS X.1 (openComplementOfClosedSubspace B S hS X Z).1 from
          range_pointsMap_preimage_ι B S hS b.hom _,
        subspacePointSet_openComplement B S hS X Z] at hx
    have hcond : pointsMap B S hS (strictTransformPullback B S hS g b).1
        ((strictTransformPullbackToSource B S hS g b).hom ≫ g.hom) p =
        pointsMap B S hS X'.1 b.hom x := by
      rw [show (strictTransformPullbackToSource B S hS g b).hom ≫ g.hom =
            (strictTransformPullbackToBlowUp B S hS g b).hom ≫ b.hom from pullback.condition,
        pointsMap_comp]
      exact congrArg (pointsMap B S hS X'.1 b.hom) hp
    have hpCp : p ∈ subspacePointSet B S hS (strictTransformPullback B S hS g b).1
        (((openComplementOfClosedSubspace B S hS X Z).1.preimage g.hom).preimage
          (strictTransformPullbackToSource B S hS g b).hom) := by
      rw [subspacePointSet_preimage_openComplement_eq_compl_exceptionalPreimageSet B S hS g b Z,
        exceptionalPreimageSet_eq_preimage_centre B S hS g b Z]
      exact fun hmem => hbx (hcond ▸ hmem)
    obtain ⟨t, ht⟩ : p ∈ subspacePointSet B S hS (strictTransformPullback B S hS g b).1
        (strictTransform B S hS g b (Z.1.preimage b.hom)).1 := by
      obtain ⟨y, rfl⟩ := hpCp
      rw [← Subfunctor.homOfLe_ι
        (preimage_openComplement_le_strictTransform_of_isBlowupAlong B S hS g b Z hb),
        pointsMap_comp]
      exact ⟨_, rfl⟩
    refine ⟨t, ?_⟩
    rw [show (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1).hom =
        (strictTransformSpaceι B S hS g b (preimageClosedSubspace b Z).1).hom ≫
          (strictTransformPullbackToBlowUp B S hS g b).hom from rfl, pointsMap_comp]
    exact (congrArg (pointsMap B S hS (strictTransformPullback B S hS g b).1
      (strictTransformPullbackToBlowUp B S hS g b).hom) ht).trans hp
  have huniv : Set.range (pointsMap B S hS
      (strictTransformSpace B S hS g b (preimageClosedSubspace b Z).1).1
      (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1).hom) =
      Set.univ := by
    rw [← hclosed.closure_eq, (hdense.mono hsub).closure_eq]
  exact fun x => Set.eq_univ_iff_forall.mp huniv x

/-- **The conclusion of Stacks 0GV5 from a proper cover and Stacks 0B4K.**  A quasi-compact,
quasi-separated algebraic space `X` over a scheme `S` whose point space has finitely many
irreducible components admits a quasi-compact open `U ⊆ X` with dense point set and a
`U`-admissible blowing up `X' ⟶ X` such that `X'` has the resolution property, given the cover
`hcover` and Stacks 0B4K for it, `h0B4K`. -/
theorem exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_properCover
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hcomp : (irreducibleComponents (points B S hS X.1)).Finite)
    (hcover : (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS Y.1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 ∧
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2 ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U)
    (h0B4K : ∀ (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X) (U : OpenSubspaces B S hS X.1),
      IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      IsQuasiCompactSpace B S hS U.1.toFunctor →
      IsProper B S hS g.hom → IsFiniteLocallyFreeOverOpenSubspace B S hS g U →
      ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1),
        IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1) ∧
        IsBlowupAlong B S hS Z b ∧
        IsFiniteLocallyFree B S hS
          (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1)) :
    ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
      Dense (subspacePointSet B S hS X.1 U.1) ∧
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
          HasResolutionProperty.{u, u} B S hS X'.1 X'.2 := by
  obtain ⟨U, Y, g, hUqc, hUdense, hgsurj, hgproper, hYqc, hYqs, hYres, hgflf⟩ := hcover hcomp
  obtain ⟨X', b, Z, hZfp, hZdisj, hb, hflf⟩ :=
    h0B4K Y g U hXqc hXqs hUqc hgproper hgflf
  exact ⟨U, hUqc, hUdense, X', b, ⟨Z, hZfp, hZdisj, hb⟩,
    hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional B S hS _
      (isSurjective_strictTransformSpaceToBlowUp_of_isSurjective B S hS g hb hgsurj hflf) hflf
      (hasResolutionProperty_strictTransformSpace_of_isBlowupAlong B S hS g hZfp hb hYqc hYqs
        hYres)⟩

/-- **The conclusion of Stacks 0GV5 for every algebraic space**, from the hypotheses of
`exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_properCover` quantified
over the algebraic space. -/
theorem forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_properCover
    (hcover : ∀ (X : AlgebraicSpaces B S hS),
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS Y.1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 ∧
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2 ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U)
    (h0B4K : ∀ (X Y : AlgebraicSpaces B S hS) (g : Y ⟶ X) (U : OpenSubspaces B S hS X.1),
      IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      IsQuasiCompactSpace B S hS U.1.toFunctor →
      IsProper B S hS g.hom → IsFiniteLocallyFreeOverOpenSubspace B S hS g U →
      ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1),
        IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1) ∧
        IsBlowupAlong B S hS Z b ∧
        IsFiniteLocallyFree B S hS
          (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1)) :
    ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  fun X hXqc hXqs hcomp =>
    exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_properCover B S hS X
      hXqc hXqs hcomp (hcover X) (h0B4K X)

/-! ### Finite local freeness over an open subspace

`AlgebraicGeometry.Space.IsFiniteLocallyFreeOverOpenSubspace` is finite local freeness of the
second projection of the fibre product `Y ×_X U` in the category of algebraic spaces, and
`AlgebraicGeometry.Space.restrictOverHom` is the second projection of the fibre product taken in
presheaves on the big fppf site; the two differ by the comparison isomorphism of the two fibre
products. -/

/-- **The two readings of "`g` is finite locally free over `U`" agree.**  If the base change of
`g : Y ⟶ X` along the open immersion of `U ⊆ X`, formed in the category of algebraic spaces, is
finite locally free, then so is `AlgebraicGeometry.Space.restrictOverHom`, the base change formed
in presheaves on the big fppf site. -/
theorem isFiniteLocallyFree_restrictOverHom_of_isFiniteLocallyFreeOverOpenSubspace
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (U : OpenSubspaces B S hS X.1)
    (h : IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    IsFiniteLocallyFree B S hS (restrictOverHom g U) := by
  replace h := (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS _).2 h
  rw [← isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree]
  have key : (restrictOverHom g U).hom =
      ((ObjectProperty.ι (IsAlgebraicSpace B S hS)).mapIso
        (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι).isoPullback).hom ≫
        (pullback.snd g U.toSpaceι).hom :=
    congrArg (fun k => k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι).isoPullback_hom_snd.symm
  rw [key]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h

/-- **Stacks 0B4K for a morphism finite locally free over an open subspace.**  Let `X` be
quasi-compact and quasi-separated, `U ⊆ X` a quasi-compact open subspace and `g : Y ⟶ X` a proper
morphism which is finite locally free over `U`.  Then there is a blowing up `b : X' ⟶ X` in a
closed subspace `Z` of finite presentation, disjoint from `U`, such that the strict transform of
`Y` along `b` is finite locally free over `X'`. -/
theorem exists_isBlowupAlong_isFiniteLocallyFree_strictTransform_of_isFiniteLocallyFreeOverOpen
    {X : AlgebraicSpaces B S hS} (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X)
    (U : OpenSubspaces B S hS X.1) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor) (hgproper : IsProper B S hS g.hom)
    (hgflf : IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1),
      IsFinitePresentation B S hS Z.1.ι ∧
      Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1) ∧
      IsBlowupAlong B S hS Z b ∧
      IsFiniteLocallyFree B S hS
        (strictTransformSpaceToBlowUp B S hS g b (preimageClosedSubspace b Z).1) :=
  exists_admissibleBlowup_isFiniteLocallyFree_strictTransform g U hXqc hXqs hUqc hgproper
    (isFiniteLocallyFree_restrictOverHom_of_isFiniteLocallyFreeOverOpenSubspace B S hS g U hgflf)

/-- **The conclusion of Stacks 0GV5 from a proper cover.**  A quasi-compact, quasi-separated
algebraic space `X` over a scheme `S` whose point space has finitely many irreducible components
admits a quasi-compact open `U ⊆ X` with dense point set and a `U`-admissible blowing up
`X' ⟶ X` such that `X'` has the resolution property, given a surjective proper `g : Y ⟶ X`,
finite locally free over such a `U`, with `Y` quasi-compact, quasi-separated and carrying the
resolution property (`hcover`). -/
theorem exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hcomp : (irreducibleComponents (points B S hS X.1)).Finite)
    (hcover : (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS Y.1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 ∧
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2 ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
      Dense (subspacePointSet B S hS X.1 U.1) ∧
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
          HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_properCover B S hS X
    hXqc hXqs hcomp hcover
    fun Y g U hXqc' hXqs' hUqc hgproper hgflf =>
      exists_isBlowupAlong_isFiniteLocallyFree_strictTransform_of_isFiniteLocallyFreeOverOpen
        B S hS Y g U hXqc' hXqs' hUqc hgproper hgflf

/-- **The conclusion of Stacks 0GV5 for every algebraic space, from a proper cover**: the
hypothesis of `exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover`
quantified over the algebraic space. -/
theorem forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover
    (hcover : ∀ (X : AlgebraicSpaces B S hS),
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (Y : AlgebraicSpaces B S hS) (g : Y ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS Y.1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 ∧
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2 ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  fun X hXqc hXqs hcomp =>
    exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover B S hS X
      hXqc hXqs hcomp (hcover X)

/-- **The two readings of "finitely many irreducible components" for a representable algebraic
space agree.**  The point space of `yoneda.obj W`, with the point topology of Stacks 03BX, has
finitely many irreducible components exactly when the scheme representing `W` does. -/
theorem finite_irreducibleComponents_points_yoneda_iff (W : BigFppfOver B S hS) :
    (irreducibleComponents (points B S hS (yoneda.obj W))).Finite ↔
      (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj W)).Finite := by
  rw [← (schemePointsHomeomorph B S hS W).image_irreducibleComponents]
  exact ⟨fun h => h.image _, fun h => h.of_finite_image
    (Set.image_injective.mpr (schemePointsHomeomorph B S hS W).injective).injOn⟩

/-! ### A cover by a scheme with the resolution property of Stacks 0F86 -/

/-- **The conclusion of Stacks 0GV5 from a cover by a scheme with the resolution property of
Stacks 0F86.**  This is
`AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_`
`of_cover` with the cover required to be representable and its resolution property asked of the
representing scheme rather than of the algebraic space. -/
theorem exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hcomp : (irreducibleComponents (points B S hS X.1)).Finite)
    (hschemeCover : (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (T : BigFppfOver B S hS)
        (g : representedAlgebraicSpace B S hS T ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS (representedAlgebraicSpace B S hS T).1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
          (representedAlgebraicSpace B S hS T).1 ∧
        _root_.AlgebraicGeometry.HasResolutionProperty ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
      Dense (subspacePointSet B S hS X.1 U.1) ∧
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
          HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_cover B S hS X hXqc
    hXqs hcomp fun hc => by
      obtain ⟨U, T, g, hUqc, hUdense, hgsurj, hgproper, hYqc, hYqs, hTres, hgflf⟩ :=
        hschemeCover hc
      exact ⟨U, representedAlgebraicSpace B S hS T, g, hUqc, hUdense, hgsurj, hgproper, hYqc,
        hYqs, hasResolutionProperty_representedAlgebraicSpace_of_hasResolutionProperty B S hS T
          hTres, hgflf⟩

/-- **The conclusion of Stacks 0GV5 for every algebraic space, from a cover by a scheme with the
resolution property of Stacks 0F86**: the hypothesis of
`exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover` quantified
over the algebraic space. -/
theorem
    forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover
    (hschemeCover : ∀ (X : AlgebraicSpaces B S hS),
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ (U : OpenSubspaces B S hS X.1) (T : BigFppfOver B S hS)
        (g : representedAlgebraicSpace B S hS T ⟶ X),
        IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
        IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
        IsQuasiCompactSpace B S hS (representedAlgebraicSpace B S hS T).1 ∧
        IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
          (representedAlgebraicSpace B S hS T).1 ∧
        _root_.AlgebraicGeometry.HasResolutionProperty ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsFiniteLocallyFreeOverOpenSubspace B S hS g U) :
    ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  fun X hXqc hXqs hcomp =>
    exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover B S hS X
      hXqc hXqs hcomp (hschemeCover X)

end AlgebraicGeometry.Space

end
