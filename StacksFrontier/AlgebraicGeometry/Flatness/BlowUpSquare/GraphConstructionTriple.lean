module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.EtaDerivedDivisorComplement
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupAdmissible
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupModification
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowupGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Macpherson's graph construction

Let `f : X ⟶ S` be a morphism of schemes and let `E` be a perfect object of `D(𝒪_X)`. Write
`p : 𝐏¹_X = X ×_S 𝐏¹_S ⟶ X` for the projection, `𝐀¹_X ⊆ 𝐏¹_X` for the first standard affine
chart and `(𝐏¹_X)_∞` for the complementary effective Cartier divisor, the image of the infinity
section. Then `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` is a triple as in Situation 0F8S. Let
`b : W ⟶ 𝐏¹_X` be the morphism of Stacks tag 0GTY attached to it and let
`Q = Lη_ℐ L(p ∘ b)^*E` be the object of Stacks tag 0F8U, where `ℐ` is the ideal sheaf of
`W_∞ = b⁻¹(𝐏¹_X)_∞`. Let `U ⊆ X` be the maximal open over which the cohomology sheaves of `E` are
locally free.

Stacks tag 0F90 asserts, among other things, that

1. `b` is an isomorphism over `𝐏¹_U ∪ 𝐀¹_X`,
2. the restriction of `Q` to `𝐀¹_X` is the pullback of `E`, and
5. if `E` is represented by a locally bounded complex of finite locally free `𝒪_X`-modules, then
   `Q` is represented by a locally bounded complex of finite locally free `𝒪_W`-modules.

## Main definitions

* `Stacks.Chow.graphTriple`: the triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`.
* `Stacks.Chow.graphBlowupToBase`: the morphism `b : W ⟶ 𝐏¹_X` of Stacks tag 0GTY for it.
* `Stacks.Chow.graphObject`: the object `Q = Lη_ℐ Lb^*Lp^*E` of `D(𝒪_W)`.

## Main results

* `Stacks.Chow.isIso_resLE_graphBlowupToBase`: clause (1), `b` is an isomorphism over
  `p⁻¹U ∪ 𝐀¹_X`; and `Stacks.Chow.isIso_pullback_snd_graphBlowupToBase`, its base change along
  `𝐀¹_X ⟶ 𝐏¹_X` is an isomorphism.
* `Stacks.Chow.nonempty_derivedPullback_graphObject_of_comp_eq`: clause (2), the pullback of `Q`
  along a lift `𝐀¹_X ⟶ W` of the chart is the pullback of `E` along `𝐀¹_X ⟶ X`; and
  `Stacks.Chow.nonempty_derivedPullback_modificationSectionAtZero_graphObject`, the pullback of
  `Q` along the section at zero `X ⟶ W` is `E`.
* `Stacks.Chow.exists_isLocallyBoundedFiniteLocallyFree_graphObject`: clause (5).

## Implementation notes

Over `𝐀¹_X` the divisor has no points, and `𝐀¹_X` is the complement of the support of the
divisor (`Stacks.Chow.divisorComplement_graphTriple`). Clause (1) over `𝐀¹_X` is therefore
clause (1) of Stacks tag 0F9Y, and over `p⁻¹U` it is Stacks tag 0F8W, because `p` is flat and
so `p⁻¹U` lies in the locally free locus of `Lp^*E`. Clause (2) is proved for every morphism
`g : T ⟶ W` with `b ∘ g` landing in `𝐀¹_X`
(`Stacks.Chow.nonempty_derivedPullback_graphObject`), by factoring `g` through `b⁻¹(𝐀¹_X)`.

"Isomorphism over `V`" is `IsIso (b.resLE V (b ⁻¹ᵁ V) le_rfl)`. The derived categories are the
standard models.

## References

* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0F8Z](https://stacks.math.columbia.edu/tag/0F8Z)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0GU0](https://stacks.math.columbia.edu/tag/0GU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect Stacks.Chow
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Base change along an open immersion `j` is an isomorphism exactly when the morphism is an
isomorphism over the image of `j`. -/
theorem isIso_pullback_snd_iff_isIso_resLE {X Y Z : Scheme.{u}} (b : X ⟶ Y) (j : Z ⟶ Y)
    [IsOpenImmersion j] :
    IsIso (pullback.snd b j) ↔ IsIso (b.resLE j.opensRange (b ⁻¹ᵁ j.opensRange) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact ((MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictOpensRange b j)).symm

/-- Base change along the inclusion of an open subscheme `U` is an isomorphism exactly when the
morphism is an isomorphism over `U`. -/
theorem isIso_pullback_snd_ι_iff_isIso_resLE {X Y : Scheme.{u}} (b : X ⟶ Y) (U : Y.Opens) :
    IsIso (pullback.snd b U.ι) ↔ IsIso (b.resLE U (b ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict, ← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  exact isIso_comp_left_iff _ _

namespace ComplexAndDivisorSituation

/-- Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism along which
`D' = b⁻¹D` is defined and let `Q = Lη_{ℐ'}Lb^*M`. For every `g : T ⟶ X'` with `b ∘ g` landing
in `X ∖ D`, `Lg^*Q ≅ L(b ∘ g)^*M`: the morphism `g` factors through `b⁻¹(X ∖ D)`, over which
this is clause (2) of Stacks tag 0F90 in the form
`nonempty_etaDerivedPullbackRestrict_divisorComplement`. -/
theorem nonempty_derivedPullback_etaDerivedPullbackObject_of_mem
    (S : ComplexAndDivisorSituation.{u, d}) {X' T : Scheme.{u}} (b : X' ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined b S.D) (g : T ⟶ X')
    (hg : ∀ t, (g ≫ b).base t ∈ S.divisorComplement) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj (S.etaDerivedPullbackObject b hD) ≅
      S.derivedPullbackObject (g ≫ b)) := by
  let j := (b ⁻¹ᵁ S.divisorComplement).ι
  have hr : Set.range g.base ⊆ Set.range j.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg t
  obtain ⟨e⟩ := S.nonempty_etaDerivedPullbackRestrict_divisorComplement b hD
  rw [← IsOpenImmersion.lift_fac j g hr, Category.assoc]
  exact ⟨((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (IsOpenImmersion.lift j g hr).toLRSHom.toShHom j.toLRSHom.toShHom).app _).symm ≪≫
    (derivedPullback (IsOpenImmersion.lift j g hr).toLRSHom.toShHom).mapIso e ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (IsOpenImmersion.lift j g hr).toLRSHom.toShHom (j ≫ b).toLRSHom.toShHom).app _⟩

end ComplexAndDivisorSituation

end AlgebraicGeometry

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory X.Modules)
  (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)

/-- **The triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` of Section 0F8Z**, for `f : X ⟶ S` and a perfect
object `E` of `D(𝒪_X)`: the scheme is `𝐏¹_X = X ×_S 𝐏¹_S`, the divisor is the image of the
infinity section and the object is the derived pullback of `E` along the projection `p`. -/
def graphTriple : ComplexAndDivisorSituation.{u, u + 1} where
  X := projectiveLineProduct f
  D := (infinitySection f).ker
  isEffectiveCartierDivisor := isEffectiveCartierDivisor_ker_infinitySection f
  hasDerivedCategory := HasDerivedCategory.standard _
  M := (derivedPullback (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom).obj E
  isPerfect := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE

/-- The scheme `W` of Section 0F8Z, the source of the morphism of Stacks tag 0GTY for
`Stacks.Chow.graphTriple`. -/
abbrev graphBlowup : Scheme.{u} :=
  (graphTriple f E hE).goodBlowup

/-- The morphism `b : W ⟶ 𝐏¹_X` of Section 0F8Z, the morphism of Stacks tag 0GTY for
`Stacks.Chow.graphTriple`. -/
def graphBlowupToBase : graphBlowup f E hE ⟶ projectiveLineProduct f :=
  (graphTriple f E hE).goodBlowupToBase

/-- The pulled-back triple along `b` is good, and every morphism good for the triple factors
uniquely through `b`. -/
theorem isGoodBlowup_graphBlowupToBase :
    (graphTriple f E hE).IsGoodBlowup (graphBlowupToBase f E hE) :=
  (graphTriple f E hE).isGoodBlowup_goodBlowupToBase

/-- The morphism `b : W ⟶ 𝐏¹_X` is proper. -/
instance isProper_graphBlowupToBase : IsProper (graphBlowupToBase f E hE) :=
  ComplexAndDivisorSituation.isProper_goodBlowupToBase (graphTriple f E hE)

/-- The perfect object `Q = Lη_ℐ Lb^*Lp^*E` of `D(𝒪_W)` of Section 0F8Z, where `ℐ` is the
ideal sheaf of `W_∞ = b⁻¹(𝐏¹_X)_∞`. -/
def graphObject : DerivedCategory (graphBlowup f E hE).Modules :=
  (graphTriple f E hE).etaDerivedPullbackObject (graphTriple f E hE).goodBlowupToBase
    (graphTriple f E hE).isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined

/-- The complement of the divisor `(𝐏¹_X)_∞` is the affine chart `𝐀¹_X`. -/
theorem divisorComplement_graphTriple :
    @Eq (projectiveLineProduct f).Opens (graphTriple f E hE).divisorComplement
      (projectiveLineAffineChart f).opensRange := by
  ext x
  show x ∉ ((infinitySection f).ker.support : Set (projectiveLineProduct f)) ↔
    x ∈ Set.range (projectiveLineAffineChart f).base
  rw [Scheme.Hom.support_ker, (infinitySection f).isClosedEmbedding.isClosed_range.closure_eq,
    ← compl_range_projectiveLineAffineChart]
  exact Set.notMem_compl_iff

/-- **Clause (1) of Stacks tag 0F90, over `𝐀¹_X`.** The base change of `b : W ⟶ 𝐏¹_X` along
the chart `𝐀¹_X ⟶ 𝐏¹_X` is an isomorphism. -/
@[stacks 0F90 "clause (1), over A^1_X, as the base change of b along A^1_X ⟶ P^1_X"]
theorem isIso_pullback_snd_graphBlowupToBase :
    IsIso (pullback.snd (graphBlowupToBase f E hE) (projectiveLineAffineChart f)) := by
  have h : IsIso ((graphBlowupToBase f E hE).resLE (graphTriple f E hE).divisorComplement
      (graphBlowupToBase f E hE ⁻¹ᵁ (graphTriple f E hE).divisorComplement) le_rfl) :=
    (graphTriple f E hE).isGoodBlowup_goodBlowupToBase.isIso_resLE_divisorComplement
  rw [divisorComplement_graphTriple] at h
  exact (isIso_pullback_snd_iff_isIso_resLE _ _).2 h

/-- **Clause (1) of Stacks tag 0F90.** The morphism `b : W ⟶ 𝐏¹_X` is an isomorphism over
`𝐏¹_U ∪ 𝐀¹_X = p⁻¹U ∪ 𝐀¹_X`, where `U ⊆ X` is the maximal open over which the cohomology
sheaves of `E` are locally free. -/
@[stacks 0F90 "clause (1)"]
theorem isIso_resLE_graphBlowupToBase :
    IsIso ((graphBlowupToBase f E hE).resLE
      (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ
          ⟨RingedSpace.cohomologyFiniteFreeLocus E,
            RingedSpace.isOpen_cohomologyFiniteFreeLocus E hE⟩ ⊔
        (projectiveLineAffineChart f).opensRange)
      (graphBlowupToBase f E hE ⁻¹ᵁ
        (pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹ᵁ
          ⟨RingedSpace.cohomologyFiniteFreeLocus E,
            RingedSpace.isOpen_cohomologyFiniteFreeLocus E hE⟩ ⊔
        (projectiveLineAffineChart f).opensRange)) le_rfl) := by
  let p := pullback.fst f (relativeProjectiveLine S ↘ S)
  let U : X.Opens := ⟨RingedSpace.cohomologyFiniteFreeLocus E,
    RingedSpace.isOpen_cohomologyFiniteFreeLocus E hE⟩
  have hV : p ⁻¹ᵁ U ≤ (graphTriple f E hE).locallyFreeLocus := fun x hx => by
    have hfl : AlgebraicGeometry.IsFlat p.toLRSHom.toShHom := fun y =>
      AlgebraicGeometry.Flat.stalkMap p y
    have _ : PreservesFiniteLimits
        (RingedSpaceModuleAdjunction.modulePullback p.toLRSHom.toShHom) :=
      RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _ hfl
    have _ : PreservesFiniteColimits
        (RingedSpaceModuleAdjunction.modulePullback p.toLRSHom.toShHom) :=
      RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
    exact Stacks.BlowUpComplexes.preimage_subset_cohomologyFiniteFreeLocus_derivedPullback
      p.toLRSHom.toShHom E hx
  have h : IsIso ((graphBlowupToBase f E hE).resLE
      (p ⁻¹ᵁ U ⊔ (graphTriple f E hE).divisorComplement)
      (graphBlowupToBase f E hE ⁻¹ᵁ (p ⁻¹ᵁ U ⊔ (graphTriple f E hE).divisorComplement))
      le_rfl) :=
    (graphTriple f E hE).isGoodBlowup_goodBlowupToBase.isIso_resLE_sup_divisorComplement
      ((isIso_pullback_snd_ι_iff_isIso_resLE _ _).1
        (graphTriple f E hE).isIso_pullback_snd_goodBlowupToBase_locallyFreeLocus) hV
  rwa [divisorComplement_graphTriple] at h

/-- For every `g : T ⟶ W` with `b ∘ g` landing in `𝐀¹_X`, `Lg^*Q ≅ L(p ∘ b ∘ g)^*E`. -/
theorem nonempty_derivedPullback_graphObject {T : Scheme.{u}} (g : T ⟶ graphBlowup f E hE)
    (hg : ∀ t, (g ≫ graphBlowupToBase f E hE).base t ∈
      Set.range (projectiveLineAffineChart f).base) :
    Nonempty ((derivedPullback g.toLRSHom.toShHom).obj (graphObject f E hE) ≅
      (derivedPullback (g ≫ graphBlowupToBase f E hE ≫
        pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom).obj E) := by
  obtain ⟨e₁⟩ := (graphTriple f E hE).nonempty_derivedPullback_etaDerivedPullbackObject_of_mem
    _ (graphTriple f E hE).isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined g fun t => by
      have h := hg t
      rwa [← Scheme.Hom.coe_opensRange, ← divisorComplement_graphTriple] at h
  have hI : (𝟭 (DerivedCategory (OXMod.{u, u} (projectiveLineProduct f).toRingedSpace))) ≅
      (Localization.uniq
        (DerivedCategory.Q (C := OXMod.{u, u} (projectiveLineProduct f).toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} (projectiveLineProduct f).toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} (projectiveLineProduct f).toRingedSpace)
          (ComplexShape.up ℤ))).functor :=
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  rw [← Category.assoc]
  exact ⟨e₁ ≪≫ (derivedPullback (g ≫ graphBlowupToBase f E hE).toLRSHom.toShHom).mapIso
      (hI.symm.app _) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (g ≫ graphBlowupToBase f E hE).toLRSHom.toShHom
      (pullback.fst f (relativeProjectiveLine S ↘ S)).toLRSHom.toShHom).app E⟩

/-- **Clause (2) of Stacks tag 0F90, along the section at zero.** The pullback of `Q` along the
section at zero `i_0 : X ⟶ W`, which exists because `b` is an isomorphism over `𝐀¹_X`, is
`E`. -/
@[stacks 0F90 "clause (2), restricted along the section at zero X ⟶ W"]
theorem nonempty_derivedPullback_modificationSectionAtZero_graphObject :
    Nonempty ((derivedPullback (modificationSectionAtZero f (graphBlowupToBase f E hE)
        (isIso_modificationFibreAtZeroProjection f _
          (isIso_pullback_snd_graphBlowupToBase f E hE))).toLRSHom.toShHom).obj
        (graphObject f E hE) ≅ E) := by
  have hA := isIso_pullback_snd_graphBlowupToBase f E hE
  obtain ⟨e⟩ := nonempty_derivedPullback_graphObject f E hE
    (modificationSectionAtZero f _ (isIso_modificationFibreAtZeroProjection f _ hA))
    fun t => ⟨affineLineZeroSection X t, by
      rw [← Scheme.Hom.comp_apply, affineLineZeroSection_comp_projectiveLineAffineChart,
        modificationSectionAtZero_comp f _ hA]⟩
  have hs : modificationSectionAtZero f _ (isIso_modificationFibreAtZeroProjection f _ hA) ≫
      graphBlowupToBase f E hE ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
    modificationSectionAtZero_comp_projection f _ hA
  rw [hs] at e
  exact ⟨e ≪≫
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app E⟩

/-- **Clause (2) of Stacks tag 0F90.** The restriction of `Q` to `𝐀¹_X` is the pullback of `E`:
for the open immersion `a : 𝐀¹_X ⟶ W` lifting the chart `𝐀¹_X ⟶ 𝐏¹_X` (it exists by
`Stacks.Chow.isIso_pullback_snd_graphBlowupToBase`), `La^*Q` is the pullback of `E` along the
projection `𝐀¹_X ⟶ X`. -/
@[stacks 0F90 "clause (2)"]
theorem nonempty_derivedPullback_graphObject_of_comp_eq
    (a : affineLineOver X ⟶ graphBlowup f E hE)
    (ha : a ≫ graphBlowupToBase f E hE = projectiveLineAffineChart f) :
    Nonempty ((derivedPullback a.toLRSHom.toShHom).obj (graphObject f E hE) ≅
      (derivedPullback (pullback.fst (terminal.from X)
        (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))).toLRSHom.toShHom).obj E) := by
  obtain ⟨e⟩ := nonempty_derivedPullback_graphObject f E hE a fun t => ⟨t, by rw [ha]⟩
  rw [← Category.assoc, ha, projectiveLineAffineChart_fst] at e
  exact ⟨e⟩

/-- **Clause (5) of Stacks tag 0F90.** If `E` is represented by a locally bounded complex of
finite locally free `𝒪_X`-modules, then `Q` is represented by a locally bounded complex of
finite locally free `𝒪_W`-modules. The pullback along `p` of a representative of `E` represents
`Lp^*E`, and Stacks tag 0GU0 applies. -/
@[stacks 0F90 "clause (5)"]
theorem exists_isLocallyBoundedFiniteLocallyFree_graphObject
    (hrep : ∃ ℳ : CochainComplex X.Modules ℤ, IsLocallyBoundedFiniteLocallyFree ℳ ∧
      Nonempty (DerivedCategory.Q.obj ℳ ≅ E)) :
    ∃ 𝒬 : CochainComplex (graphBlowup f E hE).Modules ℤ,
      IsLocallyBoundedFiniteLocallyFree 𝒬 ∧
        Nonempty (DerivedCategory.Q.obj 𝒬 ≅ graphObject f E hE) := by
  obtain ⟨ℳ, hℳ, ⟨e⟩⟩ := hrep
  let p := pullback.fst f (relativeProjectiveLine S ↘ S)
  exact ((graphTriple f E hE).isGoodBlowup_goodBlowupToBase.isIso_and_isPerfect_and_exists_rep
    ⟨((Scheme.Modules.pullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ,
      Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback p ℳ hℳ,
      ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat p.toLRSHom.toShHom ℳ
          (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree ℳ hℳ)).symm ≪≫
        (derivedPullback p.toLRSHom.toShHom).mapIso e⟩⟩).2.2

end Stacks.Chow
