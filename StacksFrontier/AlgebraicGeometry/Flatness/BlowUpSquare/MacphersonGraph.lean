module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.EtaDerivedDivisorComplement
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDivisorSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupTag
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationPropertiesOfRep
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowing up complexes, III: Macpherson's graph construction

Let `X` be a scheme, `E` a perfect object of `D(𝒪_X)` and `U ⊆ X` the maximal open over which
the cohomology sheaves of `E` are locally free.  With `p : 𝐏¹_X ⟶ X` the projection and
`(𝐏¹_X)_∞` the divisor at infinity, `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` is a triple as in Situation 0F8S;
let `b : W ⟶ 𝐏¹_X` be the morphism of Stacks tag 0GTY for it and `Q = Lη_ℐ Lb^*Lp^*E` the object
of tag 0F8U.  Stacks tag 0F90 lists the properties of this construction.

## Main definitions

In the namespace `AlgebraicGeometry.ComplexAndDivisorSituation`:

* `projectiveLineTriple`: the triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`.

## Main results

* `isIso_resLE_projectiveLineTriple`: **clause (1) of Stacks tag 0F90**, `b` is an isomorphism
  over `𝐏¹_U ∪ 𝐀¹_X`.
* `nonempty_etaDerivedPullbackRestrict_projectiveLineTriple`: **clause (2) of Stacks tag 0F90**,
  the restriction of `Q` to `𝐀¹_X` is the pullback of `E`.
* `exists_closedSubscheme_projectiveLineTriple`: **clauses (3) and (4) of Stacks tag 0F90**, the
  closed subscheme `T` of `W_∞` and the ranks of the cohomology of `Li^*Q`.
* `exists_isLocallyBoundedFiniteLocallyFree_projectiveLineTriple`: **clause (5) of Stacks tag
  0F90**.

## Implementation notes

`𝐏¹_X` is `Stacks.Chow.relativeProjectiveLine X`, the base change of the two-chart projective line
over `ℤ`, and `(𝐏¹_X)_∞` is `Stacks.Chow.lineInfinityDivisor X`.  The chart `𝐀¹_X` enters the
statements as `AlgebraicGeometry.ComplexAndDivisorSituation.divisorComplement`, the complement of
`(𝐏¹_X)_∞`; it is the image of the chart `Stacks.Chow.affineChart X` by
`AlgebraicGeometry.ComplexAndDivisorSituation.opensRange_affineChart_eq_divisorComplement`.
`𝐏¹_U` is `p ⁻¹ᵁ U`.

## References

* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect RingedSpaceModuleAdjunction

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- The projection `𝐏¹_ℤ ⟶ Spec ℤ`, composed with the terminal morphism, is flat. -/
instance flat_terminalFrom_projectiveLine :
    Flat (terminal.from (projectiveLine (ULift.{u} ℤ))) := by
  rw [← terminal.comp_from (projectiveLine (ULift.{u} ℤ) ↘ Spec (.of (ULift.{u} ℤ)))]
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal (specULiftZIsTerminal.{u}) terminalIsTerminal _
  infer_instance

/-- The projection `𝐏¹_X ⟶ X` is flat, being a base change of `𝐏¹_ℤ ⟶ Spec ℤ`. -/
@[ega "IV 14.4.10" "(ii)"]
instance flat_relativeProjectiveLine_over (X : Scheme.{u}) :
    Flat (Stacks.Chow.relativeProjectiveLine X ↘ X) :=
  MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback (terminal.from X)
      (terminal.from (projectiveLine (ULift.{u} ℤ)))).flip
    inferInstance

variable (X : Scheme.{u}) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (hE : RingedSpace.IsPerfect E)

/-- The triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` of Situation 0F8S attached to a perfect object `E` of
`D(𝒪_X)`, where `p : 𝐏¹_X ⟶ X` is the projection and `(𝐏¹_X)_∞` the divisor at infinity. -/
def projectiveLineTriple : ComplexAndDivisorSituation.{u, u + 1} where
  X := Stacks.Chow.relativeProjectiveLine X
  D := Stacks.Chow.lineInfinityDivisor X
  isEffectiveCartierDivisor := Stacks.Chow.lineInfinityDivisor_isEffectiveCartierDivisor X
  hasDerivedCategory := HasDerivedCategory.standard _
  M := (derivedPullback (Stacks.Chow.relativeProjectiveLine X ↘ X).toLRSHom.toShHom).obj E
  isPerfect := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE

/-- The chart `𝐀¹_X = D₊(T₀)` of `𝐏¹_X` is the complement of `(𝐏¹_X)_∞`, that is, the divisor
complement of the triple. -/
theorem opensRange_affineChart_eq_divisorComplement :
    (Stacks.Chow.affineChart X).opensRange = (projectiveLineTriple X E hE).divisorComplement :=
  TopologicalSpace.Opens.ext (Stacks.Chow.range_affineChart_eq_compl_support_lineInfinityDivisor X)

/-- The maximal open subscheme of `X` over which the cohomology sheaves of `E` are locally
free. -/
def cohomologyLocallyFreeOpen : X.Opens :=
  ⟨RingedSpace.cohomologyFiniteFreeLocus E, RingedSpace.isOpen_cohomologyFiniteFreeLocus E hE⟩

/-- The module pullback along the flat projection `𝐏¹_X ⟶ X` preserves finite limits and finite
colimits. -/
private theorem exact_modulePullback_projection :
    PreservesFiniteLimits
        (modulePullback (Stacks.Chow.relativeProjectiveLine X ↘ X).toLRSHom.toShHom) ∧
      PreservesFiniteColimits
        (modulePullback (Stacks.Chow.relativeProjectiveLine X ↘ X).toLRSHom.toShHom) :=
  ⟨preservesFiniteLimits_modulePullback_of_isFlat _ fun y => AlgebraicGeometry.Flat.stalkMap _ y,
    preservesFiniteColimits_modulePullback _⟩

/-- `𝐏¹_U` lies in the locus where the cohomology sheaves of `Lp^*E` are locally free: `p` is flat,
so `H^i(Lp^*E) = p^*H^i(E)`. -/
theorem preimage_cohomologyLocallyFreeOpen_le_locallyFreeLocus :
    (Stacks.Chow.relativeProjectiveLine X ↘ X) ⁻¹ᵁ cohomologyLocallyFreeOpen X E hE ≤
      (projectiveLineTriple X E hE).locallyFreeLocus := by
  obtain ⟨_, _⟩ := exact_modulePullback_projection X
  intro x hx
  exact Stacks.BlowUpComplexes.preimage_subset_cohomologyFiniteFreeLocus_derivedPullback _ E hx

/-- **Clause (1) of Stacks tag 0F90.**  The morphism `b : W ⟶ 𝐏¹_X` of Stacks tag 0GTY for the
triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` is an isomorphism over `𝐏¹_U ∪ 𝐀¹_X`. -/
@[stacks 0F90 "clause (1): `b` is an isomorphism over `𝐏¹_U ∪ 𝐀¹_X`, with `𝐀¹_X` the complement \
of `(𝐏¹_X)_∞`"]
theorem isIso_resLE_projectiveLineTriple :
    IsIso ((projectiveLineTriple X E hE).goodBlowupToBase.resLE
      ((Stacks.Chow.relativeProjectiveLine X ↘ X) ⁻¹ᵁ cohomologyLocallyFreeOpen X E hE ⊔
        (projectiveLineTriple X E hE).divisorComplement)
      ((projectiveLineTriple X E hE).goodBlowupToBase ⁻¹ᵁ
        ((Stacks.Chow.relativeProjectiveLine X ↘ X) ⁻¹ᵁ cohomologyLocallyFreeOpen X E hE ⊔
          (projectiveLineTriple X E hE).divisorComplement)) le_rfl) := by
  set S := projectiveLineTriple X E hE
  have hW : IsIso (S.goodBlowupToBase.resLE S.locallyFreeLocus
      (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact S.isIso_morphismRestrict_goodBlowupToBase_locallyFreeLocus
  exact S.isGoodBlowup_goodBlowupToBase.isIso_resLE_sup_divisorComplement hW
    (preimage_cohomologyLocallyFreeOpen_le_locallyFreeLocus X E hE)

/-- **Clause (2) of Stacks tag 0F90.**  The restriction of `Q = Lη_ℐ Lb^*Lp^*E` to the preimage
`j : b⁻¹(𝐀¹_X) ⟶ W` of `𝐀¹_X` is the pullback of `E`: `Lj^*Q ≅ L(p ∘ b ∘ j)^*E`.  By clause (1)
`b⁻¹(𝐀¹_X) ⟶ 𝐀¹_X` is an isomorphism. -/
@[stacks 0F90 "clause (2): the restriction of `Q` to `𝐀¹_X` is the pullback of `E`"]
theorem nonempty_etaDerivedPullbackRestrict_projectiveLineTriple :
    Nonempty ((projectiveLineTriple X E hE).etaDerivedPullbackRestrict
        (projectiveLineTriple X E hE).goodBlowupToBase
        (projectiveLineTriple X E hE).isPullbackDefined_goodBlowupToBase
        ((projectiveLineTriple X E hE).goodBlowupToBase ⁻¹ᵁ
          (projectiveLineTriple X E hE).divisorComplement).ι ≅
      (derivedPullback (((projectiveLineTriple X E hE).goodBlowupToBase ⁻¹ᵁ
          (projectiveLineTriple X E hE).divisorComplement).ι ≫
          (projectiveLineTriple X E hE).goodBlowupToBase ≫
          (Stacks.Chow.relativeProjectiveLine X ↘ X)).toLRSHom.toShHom).obj E) := by
  set S := projectiveLineTriple X E hE
  set j := (S.goodBlowupToBase ⁻¹ᵁ S.divisorComplement).ι
  obtain ⟨e⟩ := S.nonempty_etaDerivedPullbackRestrict_divisorComplement S.goodBlowupToBase
    S.isPullbackDefined_goodBlowupToBase
  have hE : (𝟭 (DerivedCategory (OXMod.{u, u} S.X.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} S.X.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} S.X.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).functor :=
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  exact ⟨e ≪≫ (derivedPullback (j ≫ S.goodBlowupToBase).toLRSHom.toShHom).mapIso
      (hE.symm.app S.M) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (j ≫ S.goodBlowupToBase).toLRSHom.toShHom
      (Stacks.Chow.relativeProjectiveLine X ↘ X).toLRSHom.toShHom).app E⟩

/-- **Clause (5) of Stacks tag 0F90.**  If `E` is represented by a locally bounded complex of
finite locally free `𝒪_X`-modules, then `Q = Lη_ℐ Lb^*Lp^*E` is represented by a locally bounded
complex of finite locally free `𝒪_W`-modules. -/
@[stacks 0F90 "clause (5): a locally bounded finite locally free representative of `E` gives one \
of `Q`"]
theorem exists_isLocallyBoundedFiniteLocallyFree_projectiveLineTriple
    (hrep : ∃ P : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) :
    ∃ 𝒬 : CochainComplex (projectiveLineTriple X E hE).goodBlowup.Modules ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
        Nonempty (DerivedCategory.Q.obj 𝒬 ≅
          (projectiveLineTriple X E hE).etaDerivedPullbackObject
            (projectiveLineTriple X E hE).goodBlowupToBase
            (projectiveLineTriple X E hE).isPullbackDefined_goodBlowupToBase) := by
  set S := projectiveLineTriple X E hE
  obtain ⟨P, hP, ⟨e⟩⟩ := hrep
  set p := Stacks.Chow.relativeProjectiveLine X ↘ X
  have hkf := Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P hP
  have hrep' : ∃ ℳ : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
      Stacks.Chow.IsLocallyBoundedFiniteLocallyFree ℳ ∧
        Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj ℳ ≅ S.M) :=
    ⟨((Scheme.Modules.pullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback p P hP,
      ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat p.toLRSHom.toShHom P hkf).symm ≪≫
        (derivedPullback p.toLRSHom.toShHom).mapIso e⟩⟩
  exact (S.isGoodBlowup_goodBlowupToBase.isIso_and_imp_isPerfect_and_exists_rep.2 hrep').2

/-- **Clauses (3) and (4) of Stacks tag 0F90.**  For the morphism `b : W ⟶ 𝐏¹_X` of tag 0GTY
for the triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`, with `W_∞ = b⁻¹(𝐏¹_X)_∞` and `Q = Lη_ℐ Lb^*Lp^*E`,
there is a closed immersion `i : T ⟶ W_∞` locally of finite presentation such that
* (3) `(W_∞ ⟶ X)⁻¹U ⊆ T` scheme theoretically and the cohomology sheaves of `Li^*Q` are finite
  locally free, and
* (4) for `t ∈ T` with image `x ∈ U` in `X`, the stalk `H^n(Li^*Q)_t` is free over `𝒪_{T,t}` of
  the rank of `H^n(E)_x` over `𝒪_{X,x}`.

This is tag 0F8X for the triple, read through `H^n(Lp^*E)_y = 𝒪_{𝐏¹_X,y} ⊗ H^n(E)_{p y}`, `p`
being flat, and the inclusion of `𝐏¹_U` in the locus where the cohomology of `Lp^*E` is locally
free. -/
@[stacks 0F90 "clauses (3) and (4): the closed immersion `i : T → W_∞` locally of finite \
presentation, with `(W_∞ → X)⁻¹U ⊆ T` scheme theoretically, `Li^*Q` with finite locally free \
cohomology sheaves, and for `t ∈ T` over `x ∈ U` the stalk `H^n(Li^*Q)_t` free over `𝒪_{T,t}` of \
the rank (Module.finrank) of `H^n(E)_x` over `𝒪_{X,x}`; `Li^*Q` is etaDerivedPullbackRestrict \
along `T → W_∞ → W`"]
theorem exists_closedSubscheme_projectiveLineTriple :
    ∃ T : ((projectiveLineTriple X E hE).D.comap
        (projectiveLineTriple X E hE).goodBlowupToBase).subscheme.IdealSheafData,
      LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((((projectiveLineTriple X E hE).D.comap
          (projectiveLineTriple X E hE).goodBlowupToBase).subschemeι ≫
          (projectiveLineTriple X E hE).goodBlowupToBase ≫
          (Stacks.Chow.relativeProjectiveLine X ↘ X)) ⁻¹ᵁ
            cohomologyLocallyFreeOpen X E hE).ι = ⊥ ∧
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((projectiveLineTriple X E hE).etaDerivedPullbackRestrictHomology
          (projectiveLineTriple X E hE).goodBlowupToBase
          (projectiveLineTriple X E hE).isGoodOver_goodBlowupToBase.pullbackDefined
          (T.subschemeι ≫ ((projectiveLineTriple X E hE).D.comap
            (projectiveLineTriple X E hE).goodBlowupToBase).subschemeι) n)) ∧
      ∀ (n : ℤ) (t : T.subscheme)
        (_ : ((T.subschemeι ≫ ((projectiveLineTriple X E hE).D.comap
          (projectiveLineTriple X E hE).goodBlowupToBase).subschemeι) ≫
          (projectiveLineTriple X E hE).goodBlowupToBase ≫
          (Stacks.Chow.relativeProjectiveLine X ↘ X)).base t ∈ cohomologyLocallyFreeOpen X E hE),
        letI F := (projectiveLineTriple X E hE).etaDerivedPullbackRestrictHomology
          (projectiveLineTriple X E hE).goodBlowupToBase
          (projectiveLineTriple X E hE).isGoodOver_goodBlowupToBase.pullbackDefined
          (T.subschemeι ≫ ((projectiveLineTriple X E hE).D.comap
            (projectiveLineTriple X E hE).goodBlowupToBase).subschemeι) n
        letI x := ((T.subschemeι ≫ ((projectiveLineTriple X E hE).D.comap
          (projectiveLineTriple X E hE).goodBlowupToBase).subschemeι) ≫
          (projectiveLineTriple X E hE).goodBlowupToBase ≫
          (Stacks.Chow.relativeProjectiveLine X ↘ X)).base t
        letI : Module (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
            (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) :=
          RingedSpace.moduleStalk (X := T.subscheme.toRingedSpace) F t
        letI : Module (ToType (X.presheaf.stalk x))
            (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (OXMod.{u, u} X.toRingedSpace) n).obj E).val.presheaf x)) :=
          RingedSpace.moduleStalk (X := X.toRingedSpace)
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E) x
        Module.Free (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
            (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) ∧
          Module.finrank (ToType (TopCat.Presheaf.stalk T.subscheme.presheaf t))
              (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) =
            Module.finrank (ToType (X.presheaf.stalk x))
              (ToType (TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (OXMod.{u, u} X.toRingedSpace) n).obj E).val.presheaf x)) := by
  set S := projectiveLineTriple X E hE
  set p := Stacks.Chow.relativeProjectiveLine X ↘ X
  obtain ⟨T, hfp, hbot, hlf, hrank⟩ := S.exists_closedSubscheme_goodBlowup
  refine ⟨T, hfp, Scheme.IdealSheafData.comap_ι_eq_bot_of_le T
    (fun y hy => preimage_cohomologyLocallyFreeOpen_le_locallyFreeLocus X E hE hy) hbot,
    hlf, fun n t hx => ?_⟩
  set y := ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
    S.goodBlowupToBase).base t
  have hpy : p.base y = ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
      S.goodBlowupToBase ≫ p).base t := by
    rfl
  have hw : y ∈ S.locallyFreeLocus :=
    preimage_cohomologyLocallyFreeOpen_le_locallyFreeLocus X E hE
      (show p.base y ∈ cohomologyLocallyFreeOpen X E hE by rw [hpy]; exact hx)
  obtain ⟨h1, h2⟩ := hrank n t hw
  obtain ⟨_, _⟩ := exact_modulePullback_projection X
  have _ : Nontrivial (ToType ((Stacks.Chow.relativeProjectiveLine X).presheaf.stalk y)) :=
    LocallyFreeRank.scheme_stalksNontrivial (Stacks.Chow.relativeProjectiveLine X) y
  have hfree : RingedSpace.FreeAndFiniteStalk
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E)
      (p.toLRSHom.toShHom.hom.base y) := by
    have hx' : p.base y ∈ RingedSpace.cohomologyFiniteFreeLocus E := by rw [hpy]; exact hx
    exact hx' n
  obtain ⟨-, h3⟩ := Stacks.BlowUpComplexes.freeAndFiniteStalk_and_finrank_homology_derivedPullback
    p.toLRSHom.toShHom E y n hfree
  have hpy' : (ConcreteCategory.hom p.toLRSHom.toShHom.hom.base) y =
      ((T.subschemeι ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
        S.goodBlowupToBase ≫ p).base t := hpy
  refine ⟨h1, h2.trans (h3.trans ?_)⟩
  rw [hpy']

end AlgebraicGeometry.ComplexAndDivisorSituation

end
