module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionStagePoints
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic

/-!
# The completion of an adic\* affine formal algebraic space is a formal spectrum

Let `A` be a weakly admissible topological ring presenting the fppf sheaf `X` over `S` by a
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`, let `A` moreover be adic with a
finitely generated ideal of definition, and let `T ⊆ |X|` be closed with quasi-compact
complement. This file proves that the completion `X_{/T}` is the formal spectrum of the
`𝔞`-adic completion of `A`, for a finitely generated ideal `𝔞 ⊆ A` cutting out `T`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isClosedImmersionInto_completionSheafULift_stageIdeal_eq`:
  **for every weak ideal of definition `K` inside `𝔞 ^ n` there is an affine scheme of the site
  closed-immersed in `X_{/T}` cutting out exactly `𝔞 ^ n`.** This is the hypothesis `hsmall` of
  `AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso_of_stageIdeal`.
* `AlgebraicGeometry.FormalSpace.exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift`:
  **the completion of `X` along `T` is the formal spectrum of the `𝔞`-adic completion of `A`.**
* `AlgebraicGeometry.FormalSpace.isCompact_of_isNoetherianRing`: for a Noetherian presenting
  ring every set of points of `X` is quasi-compact, so the quasi-compactness hypothesis is
  automatic there.

## The two ideals

The ideal `𝔞` of `AlgebraicGeometry.FormalSpace.exists_fg_cutsOutAtStage` contains the finitely
generated ideal of definition `I` supplied by adicness\*, but `I` need not be the ideal whose
powers *define* the topology: `TopologicalRing.IsAdic` asks for *some* ideal of definition `I₀`
with `_root_.IsAdic I₀`, and nothing ties the two together. So the weak ideals of definition
used to cut out the powers of `𝔞` are built from `I₀`: with `m ≠ 0` such that `I₀ ^ m ≤ I`
(`TopologicalRing.CompletionOver.exists_pow_le_of_isWeakIdealOfDefinition`), the ideal
`I₀ ^ (m * n)` is a weak ideal of definition
(`TopologicalRing.CompletionOver.isWeakIdealOfDefinition_pow`) contained in `𝔞 ^ n`.

## The double quotient

The stage of the presentation at a weak ideal of definition `K` is the spectrum of `A ⧸ K`, and it
is an object of the site; nothing is assumed about `Spec A` itself, which is *not* an object of the
site in general — see `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`.
So the affine scheme cutting out `𝔞 ^ n` is built as a quotient of the *stage* ring rather than of
`A`: it is `Spec ((A ⧸ K) ⧸ 𝔟)` for `𝔟` the image of `𝔞 ^ n` in `A ⧸ K`, which by
`AlgebraicGeometry.FormalSpace.contains_spec_quotient` lies in the site. Taking the *double*
quotient avoids transporting any ring isomorphism: the kernel of the second quotient map is
literally `𝔟`, and its inverse image in `A` is `𝔞 ^ n ⊔ K`, which is `𝔞 ^ n` because `K ≤ 𝔞 ^ n`.

That the points of `Spec ((A ⧸ K) ⧸ 𝔟)` lie in `T` is *not* the inclusion
`V(𝔟) ⊆ V(image of 𝔞)` of zero loci read off from `𝔞 ^ n ≤ 𝔞`, which goes the wrong way: zero
loci are antitone. It is the equality `V(J ^ n) = V(J)` of `PrimeSpectrum.zeroLocus_pow`, valid
for `n ≠ 0` — a prime containing a positive power of an ideal contains the ideal.

## References

* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology Space.pointTopologyULift
attribute [local instance] sheaf_hasColimits

/-! ### Two facts about the spectrum of a quotient ring -/

section Rings

/-- **The ideal cut out by the closed immersion `Spec (R ⧸ 𝔟) ⟶ Spec R` is `𝔟`.** On global
sections that closed immersion is the quotient map `R ⟶ R ⧸ 𝔟` followed by the isomorphism
identifying `R ⧸ 𝔟` with the global sections of its spectrum. -/
theorem ker_hom_ΓSpecIso_inv_comp_appTop_specMap_quotientMk {R : Type u} [CommRing R]
    (𝔟 : Ideal R) :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔟))).appTop).hom) = 𝔟 := by
  have hinj : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ 𝔟))).inv).hom :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ 𝔟))).inv).injective
  rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.ker_comp_of_injective _ hinj, Ideal.mk_ker]

/-- **The image of `Spec (R ⧸ 𝔟) ⟶ Spec R` lies in the zero locus of `J`** whenever a positive
power of `J` lies in `𝔟`: the image is `V(𝔟) ⊆ V(J ^ n) = V(J)`, the last equality because a
prime containing a positive power of an ideal contains the ideal. -/
theorem range_comap_quotientMk_subset_zeroLocus {R : Type u} [CommRing R] {𝔟 J : Ideal R}
    {n : ℕ} (hn : n ≠ 0) (h : J ^ n ≤ 𝔟) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔟)) ⊆
      PrimeSpectrum.zeroLocus (J : Set R) := by
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact (PrimeSpectrum.zeroLocus_anti_mono_ideal h).trans
    (le_of_eq (PrimeSpectrum.zeroLocus_pow J hn))

end Rings

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  (X : FppfSheaf B S hS) (P : WeakIdealColimitPresentation B S hS A X)

/-! ### A quotient of a stage ring as an affine object of the site -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
include S hS X P in
/-- The spectrum of the quotient of `A` by a weak ideal of definition lies in the site: it is
isomorphic to the stage of the presentation there, and `AlgebraicGeometry.Scheme.size` is
invariant under isomorphism. -/
theorem contains_spec_weakIdealQuotient (K : WeakIdeals A) :
    B.Contains (Spec (.of (A ⧸ K.1))) :=
  (Scheme.size_congr (P.quotientIso K).symm).trans_lt (P.diagram.obj K).obj.left.property

/-- The structure morphism `Spec (A ⧸ K) ⟶ S` of a stage of the presentation, read through the
identification of that stage with the spectrum of the quotient. -/
def weakIdealQuotientOver (K : WeakIdeals A) : Spec (.of (A ⧸ K.1)) ⟶ S :=
  (P.quotientIso K).inv ≫ (P.diagram.obj K).obj.hom.hom

/-- **The spectrum of the double quotient `(A ⧸ K) ⧸ 𝔟` of a stage ring**, as an affine object
of the big fppf site over `S`; here `𝔟` is the image in `A ⧸ K` of an ideal `𝔠` of `A`. -/
def stageQuotientOver (K : WeakIdeals A) (𝔠 : Ideal A) : BigAffineFppf B S hS :=
  quotientOver B S hS (weakIdealQuotientOver B S hS A X P K)
    (contains_spec_weakIdealQuotient B S hS A X P K)
    (Ideal.map (Ideal.Quotient.mk K.1) 𝔠)

/-- The closed immersion `Spec ((A ⧸ K) ⧸ 𝔟) ⟶ Spec (A ⧸ K)` of the site, from the double
quotient of a stage ring into that stage. -/
def stageQuotientToStage (K : WeakIdeals A) (𝔠 : Ideal A) :
    stageQuotientOver B S hS A X P K 𝔠 ⟶ P.diagram.obj K :=
  ObjectProperty.homMk <| Over.homMk
    (U := (stageQuotientOver B S hS A X P K 𝔠).obj) (V := (P.diagram.obj K).obj)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) ≫ (P.quotientIso K).inv))
    (by
      apply ObjectProperty.hom_ext
      change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) ≫ (P.quotientIso K).inv) ≫
          (P.diagram.obj K).obj.hom.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) ≫
          weakIdealQuotientOver B S hS A X P K
      rw [weakIdealQuotientOver]
      exact Category.assoc _ _ _)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The morphism of schemes underlying
`AlgebraicGeometry.FormalSpace.stageQuotientToStage`. -/
theorem toScheme_map_stageQuotientToStage (K : WeakIdeals A) (𝔠 : Ideal A) :
    (BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) ≫
        (P.quotientIso K).inv :=
  rfl

/-- The point of `X` attached to the double quotient of a stage ring: the closed immersion into
the stage, followed by the tautological point of that stage. -/
abbrev stageQuotientPoint (K : WeakIdeals A) (𝔠 : Ideal A) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (stageQuotientOver B S hS A X P K 𝔠)) ⟶ X :=
  (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠)) ≫
    weakIdealStagePoint B S hS A P K

/-- **The double quotient of a stage ring is closed-immersed in `X`.** Its morphism into the
stage is a closed immersion of schemes, hence of the represented sheaves, and the stage is a
closed immersion into `X` by **Stacks 0AI9** in the form
`AlgebraicGeometry.FormalSpace.isThickening_quotient`, a thickening of schemes being a closed
immersion. -/
theorem isClosedImmersionInto_stageQuotientPoint
    (hA : TopologicalRing.IsWeaklyAdmissible A) (K : WeakIdeals A) (𝔠 : Ideal A) :
    IsClosedImmersionInto B S hS (stageQuotientPoint B S hS A X P K 𝔠) := by
  have hq : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (Ideal.Quotient.mk K.1) 𝔠)))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  have hmap : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠))) :=
    MorphismProperty.RespectsIso.postcomp
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (P.quotientIso K).inv _ hq
  exact isClosedImmersionInto_comp' _ _
    (isClosedImmersionInto_sheafifiedYoneda_map B S hS _ hmap)
    (MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        (fun _ _ _ h ↦ h.1)) _
      (isThickening_quotient B S hS A X P hA K))

/-! ### The ideal cut out by the double quotient of a stage ring -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The morphism of schemes from the double quotient of a stage ring to the spectrum of the
stage ring, through the identification of the stage with that spectrum. -/
theorem toScheme_map_stageQuotientToStage_comp_quotientIso (K : WeakIdeals A) (𝔠 : Ideal A) :
    (BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠)) ≫
        (P.quotientIso K).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) :=
  ((Category.assoc (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.map (Ideal.Quotient.mk K.1) 𝔠)))) (P.quotientIso K).inv
          (P.quotientIso K).hom).trans
      (congrArg (fun g : Spec (CommRingCat.of (A ⧸ K.1)) ⟶
            Spec (CommRingCat.of (A ⧸ K.1)) ↦
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))) ≫ g)
        (P.quotientIso K).inv_hom_id)).trans
    (Category.comp_id _)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The ring map `A ⧸ K ⟶ Γ(Spec ((A ⧸ K) ⧸ 𝔟), 𝒪)` cut out by the double quotient of a stage
ring has kernel `𝔟`. -/
theorem ker_stageQuotientRingMap_stageQuotientToStage (K : WeakIdeals A) (𝔠 : Ideal A) :
    RingHom.ker (stageQuotientRingMap B S hS A X P K
        ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠))) =
      Ideal.map (Ideal.Quotient.mk K.1) 𝔠 :=
  (congrArg (fun g : Spec (CommRingCat.of
        ((A ⧸ K.1) ⧸ Ideal.map (Ideal.Quotient.mk K.1) 𝔠)) ⟶
        Spec (CommRingCat.of (A ⧸ K.1)) ↦
      RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ K.1))).inv ≫
        Scheme.Hom.appTop g).hom))
    (toScheme_map_stageQuotientToStage_comp_quotientIso B S hS A X P K 𝔠)).trans
      (ker_hom_ΓSpecIso_inv_comp_appTop_specMap_quotientMk
        (Ideal.map (Ideal.Quotient.mk K.1) 𝔠))

/-- **The ideal of `A` cut out by the double quotient of a stage ring** is `𝔠 ⊔ K`: the kernel of
the double quotient map is the image of `𝔠` in `A ⧸ K`, whose inverse image in `A` is `𝔠 ⊔ K`. -/
theorem stageIdeal_stageQuotientPoint (K : WeakIdeals A) (𝔠 : Ideal A) :
    stageIdeal B S hS A P
        ((BigAffineFppf.inclusion B S hS).obj (stageQuotientOver B S hS A X P K 𝔠))
        (stageQuotientPoint B S hS A X P K 𝔠) = 𝔠 ⊔ K.1 :=
  (stageIdeal_comp_weakIdealStagePoint B S hS A X P K
        ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K 𝔠))).trans
    ((congrArg (Ideal.comap (Ideal.Quotient.mk K.1))
          (ker_stageQuotientRingMap_stageQuotientToStage B S hS A X P K 𝔠)).trans
      ((Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective 𝔠).trans
        (congrArg (fun J : Ideal A ↦ 𝔠 ⊔ J) Ideal.mk_ker)))

/-! ### The points of the double quotient of a stage ring lie in the closed set -/

/-- **The points of the double quotient of a stage ring at `𝔞 ^ n` lie in `T`**, for `𝔞` an ideal
cutting out `T` at every stage and `n ≠ 0`. The image of the double quotient in `Spec (A ⧸ K)`
lies in the zero locus of the image of `𝔞`
(`AlgebraicGeometry.FormalSpace.range_comap_quotientMk_subset_zeroLocus`), which is the set of
primes naming the points of `T`. -/
theorem range_pointsMapULift_stageQuotientPoint
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) (𝔞 : Ideal A)
    (hcuts : ∀ K : WeakIdeals A, CutsOutAtStage B S hS A X P K T 𝔞)
    (K : WeakIdeals A) {n : ℕ} (hn : n ≠ 0) :
    Set.range (Space.pointsMapULift.{u + 1} B S hS _
      (stageQuotientPoint B S hS A X P K (𝔞 ^ n)).hom) ⊆ T := by
  rw [range_pointsMapULift_comp_weakIdealStagePoint B S hS A X P K
    ((BigAffineFppf.inclusion B S hS).map (stageQuotientToStage B S hS A X P K (𝔞 ^ n)))]
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  have hz : ((BigFppfOver.toScheme B S hS).map
        ((BigAffineFppf.inclusion B S hS).map
          (stageQuotientToStage B S hS A X P K (𝔞 ^ n)))) z =
      (P.quotientIso K).inv.base (PrimeSpectrum.comap
        (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk K.1) (𝔞 ^ n))) z) :=
    Scheme.Hom.comp_apply _ _ z
  refine Set.mem_of_eq_of_mem (congrArg (stagePointsMap B S hS A X P K) hz) ?_
  exact (hcuts K).ge (range_comap_quotientMk_subset_zeroLocus hn
    (le_of_eq (Ideal.map_pow (Ideal.Quotient.mk K.1) 𝔞 n).symm) ⟨z, rfl⟩)

/-! ### An affine closed-immersed in the completion cutting out a power of the ideal -/

/-- **The hypothesis `hsmall` of
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso_of_stageIdeal`.** Let
`𝔞` be an ideal of `A` cutting out the set `T` of points of `X` at every stage, let `n ≠ 0` and
let `K` be a weak ideal of definition inside `𝔞 ^ n`. Then there is an affine scheme of the site
closed-immersed in the completion `X_{/T}` whose composite into `X` cuts out exactly `𝔞 ^ n`.

It is the double quotient `Spec ((A ⧸ K) ⧸ 𝔟)` of the stage ring at `K` by the image `𝔟` of
`𝔞 ^ n`: it is closed-immersed in `X` by
`AlgebraicGeometry.FormalSpace.isClosedImmersionInto_stageQuotientPoint`, its points lie in `T`
by `AlgebraicGeometry.FormalSpace.range_pointsMapULift_stageQuotientPoint` so that it factors
through the completion by `AlgebraicGeometry.Space.completionSheafULiftLift`, and that
factorization is a closed immersion because the inclusion of the completion is a monomorphism
(`AlgebraicGeometry.Space.mono_completionSheafULiftInclusion`). -/
theorem exists_isClosedImmersionInto_completionSheafULift_stageIdeal_eq
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) (𝔞 : Ideal A)
    (hcuts : ∀ K : WeakIdeals A, CutsOutAtStage B S hS A X P K T 𝔞)
    (K : WeakIdeals A) {n : ℕ} (hn : n ≠ 0) (hle : (K.1 : Ideal A) ≤ 𝔞 ^ n) :
    ∃ (V : BigAffineFppf B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj V) ⟶
        Space.completionSheafULift B S hS X T),
      IsClosedImmersionInto B S hS c ∧
        stageIdeal B S hS A P ((BigAffineFppf.inclusion B S hS).obj V)
          (c ≫ Space.completionSheafULiftInclusion B S hS X T) = 𝔞 ^ n := by
  refine ⟨stageQuotientOver B S hS A X P K (𝔞 ^ n),
    Space.completionSheafULiftLift B S hS X T _ (stageQuotientPoint B S hS A X P K (𝔞 ^ n))
      (range_pointsMapULift_stageQuotientPoint B S hS A X P T 𝔞 hcuts K hn), ?_, ?_⟩
  · refine isClosedImmersionInto_of_comp_mono' _ (Space.completionSheafULiftInclusion B S hS X T)
      (Space.mono_completionSheafULiftInclusion B S hS X T) ?_
    rw [Space.completionSheafULiftLift_comp]
    exact isClosedImmersionInto_stageQuotientPoint B S hS A X P hA K (𝔞 ^ n)
  · rw [Space.completionSheafULiftLift_comp,
      stageIdeal_stageQuotientPoint B S hS A X P K (𝔞 ^ n), sup_eq_left.mpr hle]

/-! ### The completion is the formal spectrum of an adic completion -/

include P in
/-- **The completion of an adic\* affine formal algebraic space along a closed subset with
quasi-compact complement is the formal spectrum of an adic completion of the presenting ring.**
This is the step of the source's proof of clause (4) of **Stacks 0GVV**,
`X_{/T} = Spf (lim A/𝔞^n)`, with `𝔞` finitely generated.

The ideal `𝔞` is the one of `AlgebraicGeometry.FormalSpace.exists_fg_cutsOutAtStage`; the two
hypotheses of
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso_of_stageIdeal` are
`AlgebraicGeometry.FormalSpace.le_radical_stageIdeal_of_range_subset` and
`AlgebraicGeometry.FormalSpace.exists_isClosedImmersionInto_completionSheafULift_stageIdeal_eq`,
the weak ideals of definition for the latter being the powers `I₀ ^ (m * n)` of an ideal of
definition defining the topology — see the section "The two ideals" of this file. -/
theorem exists_fg_quotientSystem_formalSpectrum_iso_completionSheafULift
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hXaff : IsAffineFormalAlgebraicSpace B S hS X)
    (hadic : TopologicalRing.IsAdic A)
    {I : Ideal A} (hIdef : TopologicalRing.IsIdealOfDefinition I) (hIfg : I.FG)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) Tᶜ) :
    ∃ 𝔞 : Ideal A, 𝔞.FG ∧
      ∃ D : @QuotientSystem B S hS (AdicCompletion 𝔞 A) _ (adicCompletionLimitTopology A 𝔞),
        Nonempty (Space.completionSheafULift B S hS X T ≅
          @formalSpectrum B S hS (AdicCompletion 𝔞 A) _
            (adicCompletionLimitTopology A 𝔞) D) := by
  obtain ⟨I₀, hI₀def, hI₀adic⟩ := hadic.1
  obtain ⟨m, hm, hmle⟩ :=
    TopologicalRing.CompletionOver.exists_pow_le_of_isWeakIdealOfDefinition hI₀def
      (TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition hIdef)
  obtain ⟨𝔞, h𝔞fg, hI𝔞, hcuts⟩ :=
    exists_fg_cutsOutAtStage B S hS A X P hA hIdef hIfg T hT hqc
  refine ⟨𝔞, h𝔞fg, ?_⟩
  have hZ : IsAffineFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS X T) :=
    ⟨satisfiesSetTheoreticCondition_completionSheafULift B S hS X hXaff T hT,
      exists_affinePresentation_completionSheafULift' B S hS X hXaff T hT⟩
  have hw : ∀ (W : BigFppfOver B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶
        Space.completionSheafULift B S hS X T),
      IsClosedImmersionInto B S hS c →
      IsClosedImmersionInto B S hS
        (c ≫ Space.completionSheafULiftInclusion B S hS X T) :=
    completionClosedSubscheme_of_isAffineFormalAlgebraicSpace B S hS X hXaff T hT
  have hrangeW : Set.range (Space.pointsMapULift.{u + 1} B S hS
      (Space.completionSheafULift B S hS X T).obj
      (Space.completionSheafULiftInclusion B S hS X T).hom) ⊆ T :=
    Space.range_pointsMapULift_completionSheafULiftInclusion_subset B S hS X T
      (Space.isSheaf_completionSubfunctorULift B S hS X T)
  refine exists_quotientSystem_formalSpectrum_iso_of_stageIdeal B S hS A hA hXaff.1 P hZ
    (Space.completionSheafULiftInclusion B S hS X T) hw 𝔞 h𝔞fg ?_ ?_
  · -- `hbig`: an affine closed-immersed in `X_{/T}` has its points in `T`
    intro V c hc
    refine le_radical_stageIdeal_of_range_subset B S hS A X P hA hXaff.1 T 𝔞 hcuts V _
      (hw _ c hc) ?_
    rintro _ ⟨q, rfl⟩
    refine hrangeW ⟨Space.pointsMapULift.{u + 1} B S hS _ c.hom q, ?_⟩
    exact (congrFun (Space.pointsMapULift_comp B S hS _ c.hom
      (Space.completionSheafULiftInclusion B S hS X T).hom) q).symm
  · -- `hsmall`: the double quotients of the stages at the powers of `I₀`
    intro t
    have hwid : TopologicalRing.IsWeakIdealOfDefinition (I₀ ^ (m * (t + 1))) :=
      TopologicalRing.CompletionOver.isWeakIdealOfDefinition_pow hI₀def hI₀adic
        (Nat.mul_ne_zero hm (Nat.succ_ne_zero t))
    have hKle : (I₀ ^ (m * (t + 1)) : Ideal A) ≤ 𝔞 ^ (t + 1) := by
      rw [pow_mul]
      exact pow_le_pow_left' (hmle.trans hI𝔞) (t + 1)
    obtain ⟨V, c, hc, hideal⟩ :=
      exists_isClosedImmersionInto_completionSheafULift_stageIdeal_eq B S hS A X P hA T 𝔞 hcuts
        (⟨I₀ ^ (m * (t + 1)), hwid⟩ : WeakIdeals A) (Nat.succ_ne_zero t) hKle
    refine ⟨V, c, hc, ?_⟩
    rw [hideal]
    exact Ideal.pow_le_pow_right (Nat.le_succ t)

/-! ### The Noetherian case: quasi-compactness is automatic -/

include P in
/-- **For a Noetherian presenting ring every set of points of `X` is quasi-compact.** The point
space of `X` is the prime spectrum of a quotient of `A`
(`AlgebraicGeometry.FormalSpace.isHomeomorph_stagePrimeMap`), which is a Noetherian topological
space, and in a Noetherian space every subset is quasi-compact. This is the source's observation
that clause (5) of **Stacks 0GVV** needs no quasi-compactness hypothesis. -/
theorem isCompact_of_isNoetherianRing [IsNoetherianRing A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {I : Ideal A}
    (hIdef : TopologicalRing.IsIdealOfDefinition I)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj)) :
    @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W := by
  have hhomeo := isHomeomorph_stagePrimeMap B S hS A X P hA
    (⟨I, TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition hIdef⟩ : WeakIdeals A)
  rw [← Set.image_preimage_eq W hhomeo.bijective.surjective]
  exact (TopologicalSpace.NoetherianSpace.isCompact _).image hhomeo.continuous

end AlgebraicGeometry.FormalSpace

end
