module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsInterColim
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjInterSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentEdsPieces

/-!
# The system of intersections of the base changes of a square is a system of Situation 0DKU

The elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ needs
the colimit statement of Stacks 09RI for the system of intersections
`AlgebraicGeometry.Space.edsPreimageInterLimitSystem hsq pb T` of the base changes of an
elementary distinguished square: that is what the four
`CategoryTheory.PullbackData.LimitSystem.IsColim` hypotheses of
`AlgebraicGeometry.Space.exists_interStageIso_of_isColim` and
`…exists_interStageIso_projHom_of_isColim` ask about.

**This file supplies those four hypotheses.**  The system `T` over `W_b` is taken to be the
system of base changes `AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem` of a
Situation 0DKU `D` with `X₀ = W_b` — which is what it is in Stacks 09RJ, where `W₀` is an
algebraic space étale over `X₀` and `T_j = W₀ ×_{X₀} X_j` — and then the system of intersections
is itself the system of base changes of a Situation 0DKU, namely the one over the intersection
`P_b` of the square over `W_b`.  Stacks 09RI for the system of base changes of Situation 0DKU is
`AlgebraicGeometry.Space.RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent`,
in `LimitPerfectObjectsInterColim.lean`.

## The identification is a `rfl`

`AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem_edsPreimageInterSituation`
holds by `rfl`: the source data below is written at the *same spelling* the system of
intersections uses — the stages are `edsInter (edsPreimage hsq (k_j ≫ p_b))` and the structure
morphisms, transition morphisms and projections are `edsPreimageInterMap`s along the composites
`k_j ≫ p_b` — so the nine fields of
`AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem` of the resulting situation
are the nine fields of `AlgebraicGeometry.Space.edsPreimageInterLimitSystem`, term for term.

The spelling matters.  `AlgebraicGeometry.Space.RelativeDescentSituation.edsInterSource`
(`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeDescentEdsPieces.lean`)
already builds Situation 0DKU over the intersection of a square
of `X₀`, but with the *iterated* preimage `edsPreimage (edsPreimage hsq p_b) k_j` at the stages,
whose open member is `(U₀.preimage p_b).preimage k_j` and étale member
`(V₀ ×_{W₀} W_b) ×_{W_b} T_j`.  Those are not the composite-preimage members
`U₀.preimage (k_j ≫ p_b)` and `V₀ ×_{W₀} T_j`, only canonically isomorphic to them, and nothing
in the tree identifies the two — so that situation's system of base changes is *not* the system
of intersections and no `rfl` relates them.  Hence the source data is rebuilt here rather than
reused.

## The one piece of new mathematics

`AlgebraicGeometry.Space.isPullback_hom_edsPreimageInterMap`: for a factorisation `q ≫ p = p'`,
the intersection of the base change of the square along `p'` is the base change along `q` of the
intersection of the base change along `p`.  This is the fibre-product description of the
intersections that
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjInterSystem.lean` names in its
module documentation and declines to assume, in the spelling the system of intersections uses.
It is not new content: both intersections are base changes of the intersection of the square
itself (`…RelativeDescentSituation.isPullback_pullbackPreimageιLift`), and two cartesian squares
over one cospan give the third.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.edsPreimageInterSource` and
  `edsPreimageInterSituation`: Situation 0DKU over the intersection of the base change of the
  square along `X₀ ⟶ W₀`.

## Main results

* `AlgebraicGeometry.Space.isPullback_hom_edsPreimageInterMap`: the cartesian square above.
* `AlgebraicGeometry.Space.RelativeDescentSituation.sourceLimitSystem_edsPreimageInterSituation`:
  its system of base changes **is** the system of intersections, by `rfl`.
* `…RelativeDescentSituation.isColim_edsPreimageInterLimitSystem_of_pseudoCoherent`
  and `isColim_canonicalPullbackData_edsPreimageInterLimitSystem_of_pseudoCoherent`: **Stacks
  09RI's conclusion for the system of intersections**, in the two pullback-pseudofunctor data.

## What is assumed

Beyond Stacks 0DKV's own two restrictions (`I : Type u` and `#I < B.cutoff.ord.cof`) and the
hypotheses of Stacks 09RI on the two objects, exactly one geometric hypothesis survives:

* `hfp`, that the intersection `P_b` of the square over `X₀` is of **finite presentation** over
  `X₀`.  It is étale (Stacks 03FT, `AlgebraicGeometry.Space.isEtale_edsInterHom`), which gives
  flatness outright, and `AlgebraicGeometry.Space.RelativeDescentSituation.edsInterSource`
  carries the identical hypothesis.

  It is *not* irreducible: `…RelativeDescentSituation.isFinitePresentation_of_isEtale_of_qcqs`
  does derive finite presentation from étaleness.  But it needs four further hypotheses — `X₀`
  quasi-separated, and `P_b` quasi-compact and quasi-separated as a space, neither of which the
  tree derives for an intersection, together with the étaleness — so discharging `hfp` would
  replace one hypothesis by four.  The caller is better placed to choose: in the induction of
  `RelativelyPerfectEssSurjInduction.lean` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/`) the four are available
  and that is exactly how `hfpP` is produced there.

No limit property of the system of intersections is assumed: it comes from `D`, through
`AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_of_size`, which depends only on
`D.Y`, `D.limitCone` and `D.i₀`.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Lemma 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
* [Stacks Project, Lemma 65.39.2 (Tag 03FT)](https://stacks.math.columbia.edu/tag/03FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

section EdsPreimageInterPullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {W W' : AlgebraicSpaces B S hS} (p : W ⟶ W₀) (p' : W' ⟶ W₀) (q : W' ⟶ W)
  (hq : q ≫ p = p')

/-- **The intersection of the base change of an elementary distinguished square along `p'` is the
base change along `q` of the intersection of the base change along `p`**, for a factorisation
`q ≫ p = p'`.  Both intersections are base changes of the intersection of the square itself
(`AlgebraicGeometry.Space.RelativeDescentSituation.isPullback_pullbackPreimageιLift`), the first
along `p'` and the second along `p`, and the map induced by `q` lies over both `q` and the
intersection of the square; so the square over `q` is cartesian because the outer square is and
the lower one is. -/
theorem isPullback_hom_edsPreimageInterMap :
    IsPullback (edsInterHom B S hS (edsPreimage hsq p')).hom
      (edsPreimageInterMap hsq p p' q hq).hom q.hom
      (edsInterHom B S hS (edsPreimage hsq p)).hom := by
  refine IsPullback.of_bot ?_ ?_
    (RelativeDescentSituation.isPullback_pullbackPreimageιLift U₀ f₀ p.hom).flip
  · rw [edsPreimageInterMap_hom_comp_pullbackPreimageιLift hsq p p' q hq,
      show q.hom ≫ p.hom = p'.hom from congrArg (fun φ => φ.hom) hq]
    exact (RelativeDescentSituation.isPullback_pullbackPreimageιLift U₀ f₀ p'.hom).flip
  · exact (congrArg (fun φ => φ.hom) (edsPreimageInterMap_comp_edsInterHom hsq p p' q hq)).symm

end EdsPreimageInterPullback

namespace RelativeDescentSituation

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  (pb : D.initialSource ⟶ W₀)

/-- **Situation 0DKU over the intersection of the base change along `X₀ ⟶ W₀` of an elementary
distinguished square of `W₀`**, for that intersection of finite presentation over `X₀`: the
source data whose space over the chosen stage is the intersection `P_b` of the square over `X₀`,
whose base changes are the intersections of the base changes of the square along the composites
`X_i ⟶ X₀ ⟶ W₀` and `X ⟶ X₀ ⟶ W₀`, and whose transitions and projections are the maps of
intersections of `AlgebraicGeometry.Space.edsPreimageInterMap`.

The cartesian squares are the new cartesian square
`AlgebraicGeometry.Space.isPullback_hom_edsPreimageInterMap` pasted with those of `D`, and the
structure morphism is flat and of finite presentation because the intersection is étale over
`X₀` (Stacks 03FT) and `p₀` is flat and of finite presentation. -/
abbrev edsPreimageInterSource
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom) :
    SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := (edsInter B S hS (edsPreimage hsq pb)).1
  p₀ := (edsInterHom B S hS (edsPreimage hsq pb)).hom ≫ D.p₀
  initial_isAlgebraicSpace := (edsInter B S hS (edsPreimage hsq pb)).2
  initial_isFlat := isFlat_comp B S hS (edsInter B S hS (edsPreimage hsq pb)).2
    D.initial_isAlgebraicSpace (D.stage_isAlgebraicSpace D.i₀) _ _
    (isFlat_of_isEtale B S hS (isEtale_edsInterHom B S hS (edsPreimage hsq pb)))
    D.initial_isFlat
  initial_isFinitePresentation := isFinitePresentation_comp B S hS
    (edsInter B S hS (edsPreimage hsq pb)).2 D.initial_isAlgebraicSpace
    (D.stage_isAlgebraicSpace D.i₀) _ _ hfp D.initial_isFinitePresentation
  Xᵢ i hi := (edsInter B S hS (edsPreimage hsq (D.stageToInitial ⟨i, hi⟩ ≫ pb))).1
  stageX_isAlgebraicSpace i hi :=
    (edsInter B S hS (edsPreimage hsq (D.stageToInitial ⟨i, hi⟩ ≫ pb))).2
  toX₀ i hi := (edsPreimageInterMap hsq pb (D.stageToInitial ⟨i, hi⟩ ≫ pb)
    (D.stageToInitial ⟨i, hi⟩) rfl).hom
  toYᵢ i hi := (edsInterHom B S hS
    (edsPreimage hsq (D.stageToInitial ⟨i, hi⟩ ≫ pb))).hom ≫ D.toYᵢ i hi
  stage_isPullback i hi :=
    (isPullback_hom_edsPreimageInterMap hsq pb (D.stageToInitial ⟨i, hi⟩ ≫ pb)
      (D.stageToInitial ⟨i, hi⟩) rfl).paste_horiz (D.stage_isPullback i hi)
  fᵢⱼ i j hi hj hij := (edsPreimageInterMap hsq (D.stageToInitial ⟨i, hi⟩ ≫ pb)
    (D.stageToInitial ⟨j, hj⟩ ≫ pb) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    (by rw [← Category.assoc, D.sourceTransition_comp_stageToInitial
      (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij])).hom
  fᵢⱼ_toYᵢ i j hi hj hij :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toYᵢ i hi)
      (congrArg (fun φ => φ.hom) (edsPreimageInterMap_comp_edsInterHom hsq
        (D.stageToInitial ⟨i, hi⟩ ≫ pb) (D.stageToInitial ⟨j, hj⟩ ≫ pb)
        (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij) _))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg _ (D.fᵢⱼ_toYᵢ i j hi hj hij)).trans (Category.assoc _ _ _).symm)))
  fᵢⱼ_toX₀ i j hi hj hij := congrArg (fun φ => φ.hom)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb (D.stageToInitial ⟨i, hi⟩ ≫ pb)
      (D.stageToInitial ⟨j, hj⟩ ≫ pb) (D.stageToInitial ⟨i, hi⟩)
      (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij) rfl _
      (D.stageToInitial ⟨j, hj⟩)
      (D.sourceTransition_comp_stageToInitial (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij).symm rfl)
  X := (edsInter B S hS (edsPreimage hsq (D.limitToInitial ≫ pb))).1
  X_isAlgebraicSpace := (edsInter B S hS (edsPreimage hsq (D.limitToInitial ≫ pb))).2
  toInitial := (edsPreimageInterMap hsq pb (D.limitToInitial ≫ pb) D.limitToInitial rfl).hom
  toLimit := (edsInterHom B S hS (edsPreimage hsq (D.limitToInitial ≫ pb))).hom ≫ D.toLimit
  limit_isPullback :=
    (isPullback_hom_edsPreimageInterMap hsq pb (D.limitToInitial ≫ pb) D.limitToInitial
      rfl).paste_horiz D.limit_isPullback
  fᵢ i hi := (edsPreimageInterMap hsq (D.stageToInitial ⟨i, hi⟩ ≫ pb) (D.limitToInitial ≫ pb)
    (D.sourceProjection ⟨i, hi⟩)
    (by rw [← Category.assoc, D.sourceProjection_comp_stageToInitial ⟨i, hi⟩])).hom
  fᵢ_toYᵢ i hi :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toYᵢ i hi)
      (congrArg (fun φ => φ.hom) (edsPreimageInterMap_comp_edsInterHom hsq
        (D.stageToInitial ⟨i, hi⟩ ≫ pb) (D.limitToInitial ≫ pb)
        (D.sourceProjection ⟨i, hi⟩) _))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg _ (D.fᵢ_toYᵢ i hi)).trans (Category.assoc _ _ _).symm)))
  fᵢ_toX₀ i hi := congrArg (fun φ => φ.hom)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb (D.stageToInitial ⟨i, hi⟩ ≫ pb)
      (D.limitToInitial ≫ pb) (D.stageToInitial ⟨i, hi⟩) (D.sourceProjection ⟨i, hi⟩) rfl _
      D.limitToInitial (D.sourceProjection_comp_stageToInitial ⟨i, hi⟩).symm rfl)

/-- **Situation 0DKU over the intersection of the base change of an elementary distinguished
square**, as a situation. -/
abbrev edsPreimageInterSituation
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom) :
    RelativeDescentSituation B S hS hZ I :=
  D.withSource (D.edsPreimageInterSource hsq pb hfp)

/-- **The system of base changes of Situation 0DKU over the intersection of the base change of
an elementary distinguished square is the system of intersections of the base changes of the
square** along the system of base changes of `D`.  The two are the same term: both have the
intersections of the base changes of the square along the composites as their stages, and the
maps of intersections induced by the structure morphisms, transition morphisms and projections
of the system of base changes of `D` as their structure morphisms, transition morphisms and
projections. -/
theorem sourceLimitSystem_edsPreimageInterSituation
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom) :
    (D.edsPreimageInterSituation hsq pb hfp).sourceLimitSystem =
      edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem :=
  rfl

/-! ### Stacks 09RI for the system of intersections -/

/-- **Stacks 09RI's conclusion for the system of intersections of the base changes of an
elementary distinguished square.**  Let `(U₀ ⊆ W₀, V₀ ⟶ W₀)` be an elementary distinguished
square, let `D` be a Situation 0DKU indexed by a directed preorder `I` in the universe of the
site with fewer elements than the cofinality of the site's size cutoff, let `p_b : X₀ ⟶ W₀` be a
morphism, and let the intersection `P_b` of the square over `X₀` be of finite presentation over
`X₀`.  Let `K` and `L` be objects of `D(𝒪_{P_b})` with `K` pseudo-coherent and `L` in
`D_QCoh(𝒪_{P_b})` of locally finite Tor dimension along `P_b ⟶ Y_0`.  Then

`colim_{i ≥ 0} Hom_{D(𝒪_{P_i})}(Lt_i^*K, Lt_i^*L) ⟶ Hom_{D(𝒪_{P'})}(Ls^*K, Ls^*L)`

is bijective for `AlgebraicGeometry.Space.edsPreimageInterLimitSystem` along the system of base
changes of `D`.

This is `…RelativeDescentSituation.isColim_sourceLimitSystem_of_pseudoCoherent`
for `AlgebraicGeometry.Space.RelativeDescentSituation.edsPreimageInterSituation`, whose system of
base changes *is* the system of intersections
(`…sourceLimitSystem_edsPreimageInterSituation`). -/
theorem isColim_edsPreimageInterLimitSystem_of_pseudoCoherent
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom)
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (K L : derivedModules B S hS (edsInter B S hS (edsPreimage hsq pb)))
    (hK : IsPseudoCoherentObject K)
    (hL : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) L)
    (hTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) L) :
    (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).IsColim
      (smallEtaleDerivedPullbackData B S hS) K L :=
  isColim_sourceLimitSystem_of_pseudoCoherent (D.edsPreimageInterSituation hsq pb hfp) K L hI
    hK hL hTor

/-- **Stacks 09RI's conclusion for the system of intersections, for the canonical
pullback-pseudofunctor datum** — the form the four hypotheses of
`AlgebraicGeometry.Space.exists_interStageIso_of_isColim` and
`…exists_interStageIso_projHom_of_isColim` are stated in.  The two data give the same statement,
`AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff`. -/
theorem isColim_canonicalPullbackData_edsPreimageInterLimitSystem_of_pseudoCoherent
    (hfp : IsFinitePresentation B S hS (edsInterHom B S hS (edsPreimage hsq pb)).hom)
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (K L : derivedModules B S hS (edsInter B S hS (edsPreimage hsq pb)))
    (hK : IsPseudoCoherentObject K)
    (hL : IsInQuasicoherentDerived (edsInter B S hS (edsPreimage hsq pb)) L)
    (hTor : HasLocallyFiniteTorDimensionAlong
      (edsInterHom B S hS (edsPreimage hsq pb) ≫ D.initialStructure) L) :
    (edsPreimageInterLimitSystem hsq pb D.sourceLimitSystem).IsColim
      (canonicalPullbackData B S hS) K L :=
  (isColim_canonicalPullbackData_iff _ K L).2
    (D.isColim_edsPreimageInterLimitSystem_of_pseudoCoherent hsq pb hfp hI K L hK hL hTor)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
