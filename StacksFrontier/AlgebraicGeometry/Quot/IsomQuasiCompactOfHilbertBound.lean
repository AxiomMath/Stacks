/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveMorFunctorsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceHilbertModels
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# `Isom_U(Z, X)` is quasi-compact once its graphs have finitely many Hilbert polynomials

Let `U` be a Noetherian affine object of the big fppf site over `Spec ℤ`, let `z : Z ⟶ U` be
flat, proper and of finite presentation and `x : X ⟶ U` separated and proper, and let
`π : Z ×_U X ⟶ ℙⁿ_U` be a closed immersion over `U`. Sending a relative morphism to its graph and
the graph to its image in `ℙⁿ_U` is an immersion `Mor_U(Z, X) ⟶ Hilb_{ℙⁿ_U/U}` (Stacks 0D1B and
0DPF, `AlgebraicGeometry.Space.morToHilbertModel_isOpenImmersion` and
`AlgebraicGeometry.Space.isClosedImmersion_hilbertModelMapOfClosed`), read in the model of the
Hilbert functor of `ℙⁿ_U` built from the Hilbert schemes `Hilb^P_{ℙⁿ_ℤ/ℤ}`
(`AlgebraicGeometry.C1590Private.projectiveSpaceHilbertModel`), which is the disjoint union of
its open subfunctors `Hilb^P`, each represented by `U ×_ℤ Hilb^P_{ℙⁿ_ℤ/ℤ}`, a Noetherian scheme
proper over `U`.

If the graph of every field-valued point of `Isom_U(Z, X) ⊆ Mor_U(Z, X)` lies in `Hilb^P` for `P`
in one finite set, then `Isom_U(Z, X)` is covered by the finitely many base changes of the
immersion to the `Hilb^P`, schemes immersed in Noetherian schemes, hence quasi-compact; so
`Isom_U(Z, X)` is a quasi-compact algebraic space (Stacks 040W) and its morphism to the affine `U`
is quasi-compact (Stacks 073B). This is the last paragraph of the proof of Stacks 0DSQ, the
boundedness of the Hilbert polynomials being supplied by Riemann–Roch.

## Main definitions

* `AlgebraicGeometry.Space.graphHilbertModelMap`: the immersion
  `Mor_U(Z, X) ⟶ Hilb_{ℙⁿ_U/U}`.

## Main results

* `AlgebraicGeometry.Space.isImmersion_graphHilbertModelMap`.
* `AlgebraicGeometry.Space.isQuasiCompact_isomSubfunctor_of_hilbertBound`.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0D1B](https://stacks.math.columbia.edu/tag/0D1B)
* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The objects of the site over `Spec ℤ` have binary products, from the terminal object and
pullbacks. -/
local instance : HasBinaryProducts (BigFppfOver B integerBase B.contains_integerBase) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

section

variable {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U)
  (n : ℕ)
  (π : graphAmbient B integerBase B.contains_integerBase (yoneda.map q₁) (yoneda.map q₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) ⟶
      schemeSpace (ProjectiveQuot.projectiveSite B n U))
  (hπ : π ≫ schemeSpaceMap (ProjectiveQuot.projectiveSiteStructure B n U) =
    graphAmbientMap B integerBase B.contains_integerBase (yoneda.map q₁) (yoneda.map q₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U))
  (hclosed : IsClosedImmersion B integerBase B.contains_integerBase π.hom)
  (hsep : IsSeparated B integerBase B.contains_integerBase (yoneda.map q₂))
  (hfp : IsFinitePresentation B integerBase B.contains_integerBase (yoneda.map q₁))
  (hflat : IsFlat B integerBase B.contains_integerBase (yoneda.map q₁))
  (hproper : IsProper B integerBase B.contains_integerBase (yoneda.map q₁))

/-- **The graph of a relative morphism, read in the Hilbert functor of `ℙⁿ_U`.** The graph
transformation `Mor_U(Z, X) ⟶ Hilb_{Z ×_U X/U}` of Stacks 0D1A followed by the morphism of
Hilbert functors induced by the closed immersion `π : Z ×_U X ⟶ ℙⁿ_U` (Stacks 0DPF), landing in
the model `AlgebraicGeometry.C1590Private.projectiveSpaceHilbertModel` of `Hilb_{ℙⁿ_U/U}`. -/
noncomputable def graphHilbertModelMap :
    relativeHom B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂) (yoneda.obj U)
        (yoneda.map q₁) (yoneda.map q₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) ⟶
      (C1590Private.projectiveSpaceHilbertModel n U).presheaf :=
  morToHilbertModel (yoneda.map q₁) (yoneda.map q₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)
      (HilbertPresheafModel.canonical _) hsep hfp hflat hproper ≫
    hilbertModelMapOfClosed hπ hclosed (HilbertPresheafModel.canonical _)
      (C1590Private.projectiveSpaceHilbertModel n U)

include hπ hclosed in
/-- **The graph map `Mor_U(Z, X) ⟶ Hilb_{ℙⁿ_U/U}` is an immersion**: an open immersion
(Stacks 0D1B) followed by a closed immersion (Stacks 0DPF). -/
theorem isImmersion_graphHilbertModelMap :
    IsImmersion B integerBase B.contains_integerBase
      (graphHilbertModelMap q₁ q₂ n π hπ hclosed hsep hfp hflat hproper) :=
  isImmersion_comp B integerBase B.contains_integerBase _ _
    (isImmersion_of_isOpenImmersion B integerBase B.contains_integerBase
      (morToHilbertModel_isOpenImmersion _ _ _ _ _ _ hsep hfp hflat hproper))
    (isImmersion_of_isClosedImmersion B integerBase B.contains_integerBase
      (isClosedImmersion_hilbertModelMapOfClosed hπ hclosed
        (isFinitePresentation_yoneda_map B integerBase B.contains_integerBase _
          (ProjectiveQuot.finitePresentation_projectiveSpaceOver n _)) _ _))

/-- The object `U ×_ℤ Hilb^P_{ℙⁿ_ℤ/ℤ}` representing `Hilb^P_{ℙⁿ_U/U}` is Noetherian when `U` is. -/
theorem isNoetherian_hilbertQuotSite_prod
    (hUn : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj U)) (P : Polynomial ℚ) :
    _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj (U ⨯ C1590Private.hilbertQuotSite B n P)) := by
  set H := C1590Private.hilbertQuotSite B n P
  let f := terminal.from U
  let g := terminal.from H
  have _ : PreservesLimitsOfShape WalkingCospan (𝒯) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  have hsq : IsPullback ((𝒯).map (pullback.fst f g)) ((𝒯).map (pullback.snd f g))
      ((𝒯).map f) ((𝒯).map g) := (IsPullback.of_hasPullback f g).map (𝒯)
  have hg : _root_.AlgebraicGeometry.IsProper ((𝒯).map g) := by
    have h₁ := C1590Private.isProper_hilbertQuotScheme.{u} n P
    let e : ⊤_ (BigFppfOver B integerBase B.contains_integerBase) ≅
        Over.mk (𝟙 (B.obj B.contains_integerBase)) := terminalIsoIsTerminal Over.mkIdTerminal
    have heq : (𝒯).map g ≫ (𝒯).map e.hom =
        terminal.from (C1590Private.hilbertQuotScheme.{u} n P) ≫ specULiftZIsTerminal.from _ :=
      specULiftZIsTerminal.hom_ext _ _
    have : IsIso (specULiftZIsTerminal.from (⊤_ Scheme.{u})) :=
      ⟨⟨terminal.from _, terminal.hom_ext _ _, specULiftZIsTerminal.hom_ext _ _⟩⟩
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := @_root_.AlgebraicGeometry.IsProper)
      _ ((𝒯).map e.hom), heq]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := @_root_.AlgebraicGeometry.IsProper) _ _).mpr h₁
  have hfst : _root_.AlgebraicGeometry.IsProper ((𝒯).map (pullback.fst f g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper) hsq.flip hg
  let φ := (𝒯).map (prodIsoPullback U H).hom ≫ (𝒯).map (pullback.fst f g)
  have hφ : _root_.AlgebraicGeometry.IsProper φ := inferInstance
  have hcomp : CompactSpace ((𝒯).obj (U ⨯ H)) := QuasiCompact.compactSpace_of_compactSpace φ
  have hln : _root_.AlgebraicGeometry.IsLocallyNoetherian ((𝒯).obj (U ⨯ H)) :=
    LocallyOfFiniteType.isLocallyNoetherian φ
  exact {}

/-- The open subfunctor `Hilb^P` of the model of `Hilb_{ℙⁿ_U/U}` is represented by
`U ×_ℤ Hilb^P_{ℙⁿ_ℤ/ℤ}`. -/
noncomputable def hilbertModelSubfunctorReprIso (P : Polynomial ℚ) :
    yoneda.obj (U ⨯ C1590Private.hilbertQuotSite B n P) ≅
      (C1590Private.hilbertModelSubfunctor n U P).toFunctor :=
  (((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ).preimageIso
      (C1590Private.hilbertModelSubfunctorIso n U P ≪≫
        C1590Private.hilbertSubfunctorReprIso P)).symm

include hπ hclosed in
/-- **`Isom_U(Z, X)` is quasi-compact over a Noetherian affine `U` once the graphs of its
field-valued points have Hilbert polynomials in a finite set.** -/
theorem isQuasiCompact_isomSubfunctor_of_hilbertBound
    (hU : _root_.AlgebraicGeometry.IsAffine ((𝒯).obj U))
    (hUn : _root_.AlgebraicGeometry.IsNoetherian ((𝒯).obj U))
    (hxproper : IsProper B integerBase B.contains_integerBase (yoneda.map q₂))
    (S : Finset (Polynomial ℚ))
    (hS : ∀ p : FieldValuedPoint B integerBase B.contains_integerBase
        (isomSubfunctor B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
          (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)).toFunctor,
      ∃ P ∈ S, ((isomSubfunctor B integerBase B.contains_integerBase (yoneda.obj Z₁)
          (yoneda.obj Z₂) (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)).ι ≫
            graphHilbertModelMap q₁ q₂ n π hπ hclosed hsep hfp hflat hproper).app _ p.value ∈
        (C1590Private.hilbertModelSubfunctor n U P).obj _) :
    IsQuasiCompact B integerBase B.contains_integerBase
      ((isomSubfunctor B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
          (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)).ι ≫
        relativeHomProjection B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
          (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
          (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)) := by
  classical
  set I := isomSubfunctor B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
    (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)
  set r := graphHilbertModelMap q₁ q₂ n π hπ hclosed hsep hfp hflat hproper
  have hr := isImmersion_graphHilbertModelMap q₁ q₂ n π hπ hclosed hsep hfp hflat hproper
  have hMor := isAlgebraicSpace_of_relativelyRepresentable B integerBase B.contains_integerBase
    r hr.1 (C1590Private.isAlgebraicSpace_projectiveSpaceHilbertModel n U)
  have hIopen := isOpenSubspace_isomSubfunctor B integerBase B.contains_integerBase _ _ _ _ _
    _ _ _ hfp hflat hproper hxproper hMor
  set ρ := I.ι ≫ r
  have hρ : IsImmersion B integerBase B.contains_integerBase ρ :=
    isImmersion_comp B integerBase B.contains_integerBase _ _
      (isImmersion_of_isOpenImmersion B integerBase B.contains_integerBase hIopen.2) hr
  -- the charts: base changes of `ρ` to the representing objects of the `Hilb^P`, `P ∈ S`
  let V : S → BigFppfOver B integerBase B.contains_integerBase := fun P =>
    U ⨯ C1590Private.hilbertQuotSite B n P.1
  let eV : ∀ P : S, yoneda.obj (V P) ≅ (C1590Private.hilbertModelSubfunctor n U P.1).toFunctor :=
    fun P => hilbertModelSubfunctorReprIso n P.1
  let a : ∀ P : S, yoneda.obj (V P) ⟶ (C1590Private.projectiveSpaceHilbertModel n U).presheaf :=
    fun P => (eV P).hom ≫ (C1590Private.hilbertModelSubfunctor n U P.1).ι
  let W : S → BigFppfOver B integerBase B.contains_integerBase := fun P => hρ.1.pullback (a P)
  let fW : ∀ P : S, yoneda.obj (W P) ⟶ I.toFunctor := fun P => hρ.1.fst (a P)
  have hWqc : ∀ P : S, IsQuasiCompactSpace B integerBase B.contains_integerBase
      (yoneda.obj (W P)) := fun P => by
    have := isNoetherian_hilbertQuotSite_prod n hUn P.1
    have himm : AlgebraicGeometry.IsImmersion ((𝒯).map (hρ.1.snd (a P))) :=
      hρ.2 (a P) _ _ (hρ.1.isPullback (a P))
    exact isQuasiCompactSpace_yoneda_of_compactSpace B integerBase B.contains_integerBase (W P)
      (isCompact_univ_iff.mp <| ((𝒯).map (hρ.1.snd (a P))).isEmbedding.isCompact_iff.mpr
        (TopologicalSpace.NoetherianSpace.isCompact _))
  have hsurj : IsJointlySurjective B integerBase B.contains_integerBase
      (fun P : S => yoneda.obj (W P)) fW := by
    rw [isJointlySurjective_iff]
    intro y
    obtain ⟨p, rfl⟩ := Quot.exists_rep y
    obtain ⟨P, hP, hmem⟩ := hS p
    let b : FieldValuedPoint B integerBase B.contains_integerBase (yoneda.obj (V ⟨P, hP⟩)) :=
      { carrier := p.carrier
        contained := p.contained
        toBase := p.toBase
        value := (eV ⟨P, hP⟩).inv.app _ ⟨_, hmem⟩ }
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B integerBase B.contains_integerBase
      (hρ.1.isPullback (a ⟨P, hP⟩)) (p.class B integerBase B.contains_integerBase _)
      (b.class B integerBase B.contains_integerBase _) (by
        have key : (a ⟨P, hP⟩).app _ b.value = ρ.app _ p.value :=
          congrArg ((C1590Private.hilbertModelSubfunctor n U P).ι.app _)
            (Iso.inv_hom_id_app_apply (eV ⟨P, hP⟩) _ _)
        rw [pointsMap_class, pointsMap_class]
        congr 1
        exact (congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
          FieldValuedPoint B integerBase B.contains_integerBase _)) key).symm)
    exact ⟨⟨P, hP⟩, w, hw⟩
  have hIqc := isQuasiCompactSpace_of_finite_jointly_surjective B integerBase
    B.contains_integerBase (fun P => isAlgebraicSpace_yoneda B integerBase B.contains_integerBase
      (W P)) hIopen.1 fW hsurj hWqc
  exact isQuasiCompact_of_isQuasiCompactSpace B integerBase B.contains_integerBase
    B.contains_terminal (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)
    (isAbsolutelyQuasiSeparated_yoneda_obj B integerBase B.contains_integerBase
      B.contains_terminal U inferInstance) hIqc _

end

end AlgebraicGeometry.Space

end
