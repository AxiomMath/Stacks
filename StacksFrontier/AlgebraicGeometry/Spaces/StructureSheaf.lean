module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions

/-!
# The structure sheaf on the small étale site of an algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `F` be a presheaf on the big fppf
site of `S`.  The *structure presheaf* of the small étale site of `F` assigns to an étale
chart `φ : yoneda.obj U ⟶ F` the ring `Γ(U, 𝒪_U)` of global regular functions on the scheme
underlying `U`, with the canonical pullback maps as restrictions.  It is a sheaf of
commutative rings, which is étale descent of functions read on the charts of `F`.

Two ingredients carry the proof, and the first of them is the reusable one.  The étale charts
of `F` are closed under fibre products: a fibre product of two charts is computed in the
scheme charts of `F`, where the projection away from a chart is a base change of a morphism
between charts, hence étale, and composing it with a chart gives a chart again.  So the small
étale site has fibre products and all of `Space.SmallEtale.toOver`,
`Space.SmallEtale.toSchemes` and the canonical functor to all schemes preserve them.  The
second ingredient is that the canonical functor to all schemes carries a covering family of
charts to an étale, hence fpqc, covering family, which is exactly the étale condition built
into `AlgebraicGeometry.Space.SmallEtale.IsCovering`.  Those two make that functor continuous
for the small étale topology and the fpqc topology, and the structure presheaf is the
restriction along it of the global-functions presheaf of all schemes, an fpqc sheaf by
`Stacks.Sites.isSheaf_fpqcTopology_globalSections`.

## Main definitions

* `AlgebraicGeometry.Space.structurePresheaf` is the presheaf of global regular functions on
  the étale charts of `F`.
* `AlgebraicGeometry.Space.structureSheaf` is it, packaged as a sheaf of commutative rings.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.instHasPullbacks` and the three accompanying
  preservation instances: the small étale site of `F` has fibre products and they are the
  fibre products of the underlying schemes.
* `AlgebraicGeometry.Space.SmallEtale.isContinuous_toScheme`: the canonical functor from the
  small étale site of `F` to all schemes is continuous for the fpqc topology.
* `AlgebraicGeometry.Space.SmallEtale.isPushout_structurePresheaf_map_of_isPullback`: **the
  structure presheaf carries a fibre product of charts with affine underlying scheme to a
  pushout of rings**, `𝒪(Y ×_W Z) = 𝒪(Y) ⊗_{𝒪(W)} 𝒪(Z)`.
* `AlgebraicGeometry.Space.structurePresheaf_isSheaf`: the structure presheaf is a sheaf.
* `AlgebraicGeometry.Space.injective_sections_apply_of_presheafSurjective`: a global section of
  the structure presheaf is determined by its value on any one *surjective* étale chart.
* `AlgebraicGeometry.Space.exists_surjective_etale_chart_injective_sections`: if `F` has an
  étale-local property of schemes, then it has a surjective étale chart with that property on
  which restriction of global sections is injective.

## Implementation notes

The closure of the étale charts under fibre products does **not** need `F` to be an algebraic
space, and neither does the sheaf condition: the étale-chart condition already carries
representability of each chart, so the two inputs — cancellation of étale charts
(`AlgebraicGeometry.Space.etale_of_comp_etale_chart`) and composition of an étale morphism of
the site with an étale chart (`AlgebraicGeometry.Space.etale_comp_of_scheme`, part (1) of Stacks
03EC) — are available with no hypothesis on `F`, and the diagonal of `F` never enters.

Stacks 03G6 states the result for an algebraic space, and both forms are provided: the primed
`structurePresheaf_isSheaf'` and `structureSheaf'` are the general statements, with no
algebraicity hypothesis, and the unprimed `structurePresheaf_isSheaf` and `structureSheaf` —
which carry the tag — keep 03G6's own hypothesis in its original binder position, discarding
it, so
that dependent results written against 03G6 apply them positionally. Keeping only the general
form would have been a silent signature change: an application passing the algebraicity
hypothesis fails to elaborate against it.

Mathlib's `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` is not applicable to a presheaf
of rings on the small étale site, because it asks the morphisms of the coefficient category to
live in the universe `max u v` of the site, which `CommRingCat.{u}` over a site with objects in
`Type (u + 1)` fails.  `Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget` is the replacement:
it reflects the limit defining the sheaf condition along the forgetful functor, which is
possible because the limit over a covering sieve of the underlying presheaf of types exists and
is therefore small.  It is the `CommRingCat` counterpart of
`Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`, which proves the same thing for `RingCat` by
amalgamating elementwise instead; Stacks 03G6 is stated for `CommRingCat`, so the
limit-reflection form is the one used here.

`Stacks.Sites.isContinuous_toGrothendieck_of_le_comap` is the form of continuity needed for a
site presented by covering families.  Mathlib's
`CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy` asks the source
precoverage itself to be stable under base change, which for the small étale site would mean
base-changing a *chosen* covering family of the big fppf site and staying chosen.  That is
avoided by applying Mathlib's lemma to the comapped precoverage — which is stable under base
change for free — and then descending along `CategoryTheory.Precoverage.toGrothendieck_mono`,
so that only the inequality of precoverages is needed.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Sites

/-- A functor is continuous for a topology generated by a precoverage as soon as it preserves
fibre products and the image of every presieve of the precoverage generates a covering sieve.

This is weaker in its hypotheses than
`CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`, which asks the
source precoverage to be stable under base change: that lemma is applied here to the
precoverage comapped from the target, which is stable under base change because the functor
preserves fibre products, and the conclusion is transported to the smaller topology generated
by `J`. -/
theorem isContinuous_toGrothendieck_of_le_comap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [HasPullbacks C] [HasPullbacks D] (J : Precoverage C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [PreservesLimitsOfShape WalkingCospan G]
    (hJ : J ≤ K.toPrecoverage.comap G) : G.IsContinuous J.toGrothendieck K := by
  refine ⟨fun P => ?_⟩
  apply (isSheaf_iff_isSheaf_of_type _ _).mp
  have : G.IsContinuous (K.toPrecoverage.comap G).toGrothendieck
      K.toPrecoverage.toGrothendieck :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy G _ K.toPrecoverage le_rfl
  refine Presheaf.IsSheaf.of_le (Precoverage.toGrothendieck_mono hJ)
    (G.op_comp_isSheaf_of_isSheaf _ K.toPrecoverage.toGrothendieck P.obj ?_)
  exact Presheaf.IsSheaf.of_le (GrothendieckTopology.toGrothendieck_toPrecoverage_le K) P.property

/-- A presheaf of commutative rings whose underlying presheaf of types is a sheaf is a sheaf.

The sheaf condition is a limit over each covering sieve, and the forgetful functor to types
reflects that limit: it exists in types by hypothesis, so it is small, and the forgetful functor
preserves it.  This is the `CommRingCat` counterpart of
`Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`, and like it carries no universe restriction
relating the site to the coefficients. -/
theorem isSheaf_commRingCat_of_isSheaf_forget {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ CommRingCat.{u})
    (h : Presieve.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat.{u})) :
    Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit]
  have h' : Presheaf.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 h
  rw [Presheaf.isSheaf_iff_isLimit] at h'
  intro X R hR
  obtain ⟨t⟩ := h' R hR
  let D := R.arrows.diagram.op ⋙ P
  have : HasLimit (D ⋙ CategoryTheory.forget CommRingCat.{u}) := ⟨_, t⟩
  have : Small.{u} (D ⋙ CategoryTheory.forget CommRingCat.{u}).sections :=
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have : PreservesLimit D (CategoryTheory.forget CommRingCat.{u}) :=
    preservesLimit_of_preserves_limit_cone (CommRingCat.limitConeIsLimit D)
      (Types.Small.limitConeIsLimit _)
  have : ReflectsLimit D (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsLimit_of_reflectsIsomorphisms D (CategoryTheory.forget CommRingCat.{u})
  exact ⟨isLimitOfReflects (CategoryTheory.forget CommRingCat.{u}) t⟩

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Fibre products of étale charts -/

/-- Being an étale chart of `F` is invariant under isomorphism of scheme charts, because the
representable étale morphisms to `F` are closed under isomorphism. -/
instance isEtaleChart_isClosedUnderIsomorphisms :
    (IsEtaleChart B S hS F).IsClosedUnderIsomorphisms :=
  inferInstanceAs (((MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf.costructuredArrowObj
      yoneda (X := F)).IsClosedUnderIsomorphisms)

/-- A fibre product of two étale charts of `F`, formed in the scheme charts of `F`, is again an
étale chart: the projection to the first factor is a base change of the morphism of charts
induced by the second, hence étale by part (2) of Stacks 03EC and stability of étaleness under
base change, and part (1) of Stacks 03EC composes it with a chart to give a chart. -/
instance isEtaleChart_isClosedUnderLimitsOfShape_walkingCospan :
    (IsEtaleChart B S hS F).IsClosedUnderLimitsOfShape WalkingCospan := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  intro X hX
  obtain ⟨D, hD⟩ := hX
  set G := BigFppfOver.toScheme B S hS
  let pl := limit.π D WalkingCospan.left
  have hpb : IsPullback (G.map pl.left) (G.map (limit.π D WalkingCospan.right).left)
      (G.map (D.map WalkingCospan.Hom.inl).left)
      (G.map (D.map WalkingCospan.Hom.inr).left) :=
    IsPullback.of_isLimit_cone
      (isLimitOfPreserves (CostructuredArrow.proj yoneda F ⋙ G) (limit.isLimit D))
  have hr : Etale (G.map (D.map WalkingCospan.Hom.inr).left) :=
    etale_of_comp_etale_chart B S hS (hD WalkingCospan.right) (hD WalkingCospan.one)
      (D.map WalkingCospan.Hom.inr).w
  have hpl : Etale (G.map pl.left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hr
  change (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) G)) (limit D).hom
  rw [show (limit D).hom = yoneda.map pl.left ≫ (D.obj WalkingCospan.left).hom by
    simp [pl]]
  exact etale_comp_of_scheme B S hS pl.left (D.obj WalkingCospan.left).hom hpl
    (hD WalkingCospan.left)

namespace SmallEtale

/-- The small étale site of `F` has fibre products. -/
instance instHasPullbacks : HasPullbacks (SmallEtale B S hS F) :=
  inferInstanceAs (HasPullbacks (IsEtaleChart B S hS F).FullSubcategory)

/-- The inclusion of the étale charts into all scheme charts of `F` creates fibre products. -/
noncomputable instance instCreatesPullbacksInclusion :
    CreatesLimitsOfShape WalkingCospan (inclusion B S hS F) :=
  inferInstanceAs (CreatesLimitsOfShape WalkingCospan (IsEtaleChart B S hS F).ι)

/-- The object of the big fppf site of `S` underlying a fibre product of étale charts is the
fibre product of the underlying objects. -/
instance instPreservesPullbacksToOver :
    PreservesLimitsOfShape WalkingCospan (toOver B S hS F) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (inclusion B S hS F ⋙ CostructuredArrow.proj yoneda F))

/-- The scheme underlying a fibre product of étale charts is the fibre product of the
underlying schemes. -/
instance instPreservesPullbacksToSchemes :
    PreservesLimitsOfShape WalkingCospan (toSchemes B S hS F) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    (toOver B S hS F ⋙ BigFppfOver.forget B S hS))

/-! ### Continuity of the canonical functor to all schemes -/

/-- A covering family of étale charts of `F` has, as a family of morphisms of schemes, a sieve
generating an fpqc covering sieve: it is an étale covering family by the definition of
`AlgebraicGeometry.Space.SmallEtale.IsCovering`, and the étale topology is coarser than the
fpqc topology. -/
theorem precoverage_le_comap_fpqcTopology :
    precoverage B S hS F ≤
      Scheme.fpqcTopology.toPrecoverage.comap (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS) := by
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    ← PreZeroHypercover.presieve₀_map]
  exact Stacks.Sites.etaleTopology_le_fpqcTopology _
    (Precoverage.generate_mem_toGrothendieck hE.2)

/-- The canonical functor from the small étale site of `F` to all schemes is continuous for the
small étale topology of `F` and the fpqc topology: it preserves fibre products and carries
covering families of charts to fpqc covering families. -/
theorem isContinuous_toScheme :
    (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).IsContinuous
      (topology B S hS F) Scheme.fpqcTopology :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (precoverage_le_comap_fpqcTopology B S hS F)

end SmallEtale

/-! ### The structure sheaf -/

/-- The presheaf of global regular functions on the étale charts of `F`: the chart
`φ : yoneda.obj U ⟶ F` is sent to `Γ(U, 𝒪_U)`, with the canonical pullback maps on global
sections as restrictions. -/
def structurePresheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} :=
  (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- **The structure presheaf carries a fibre product of étale charts with affine underlying
schemes to a pushout of rings**: for a fibre product square `Pb = Y ×_W Z` of the small étale
site of `F` whose three given charts have affine underlying scheme,
`𝒪(Pb) = 𝒪(Y) ⊗_{𝒪(W)} 𝒪(Z)`.

The small étale site has fibre products and `AlgebraicGeometry.Space.SmallEtale.toOver` and
`AlgebraicGeometry.BigFppfOver.toScheme` preserve them, so the square of underlying schemes is a
fibre product square; the global functions of a fibre product of affine schemes are the tensor
product, which is `AlgebraicGeometry.isPushout_appTop_of_isPullback`.

No affineness is asked of `Pb` itself: it is automatic, and is
`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback` in the form for a slice. -/
theorem SmallEtale.isPushout_structurePresheaf_map_of_isPullback
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z}
    {g₁ : Y ⟶ W} {g₂ : Z ⟶ W} (h : IsPullback fst snd g₁ g₂)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W)))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Y)))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj Z))) :
    IsPushout ((structurePresheaf B S hS F).map g₁.op)
      ((structurePresheaf B S hS F).map g₂.op)
      ((structurePresheaf B S hS F).map fst.op)
      ((structurePresheaf B S hS F).map snd.op) :=
  @AlgebraicGeometry.isPushout_appTop_of_isPullback _ _ _ _ _ _ _ _ hY hZ hW
    ((h.map (SmallEtale.toOver B S hS F)).map (BigFppfOver.toScheme B S hS))

/-- Global regular functions on the étale charts of `F` form a sheaf of types for the small
étale topology: the canonical functor to all schemes is continuous for the fpqc topology, and
global functions are an fpqc sheaf on all schemes. -/
theorem isSheaf_globalSections :
    Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (structurePresheaf B S hS F ⋙ CategoryTheory.forget CommRingCat.{u}) :=
  have := SmallEtale.isContinuous_toScheme B S hS F
  (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op_comp_isSheaf_of_isSheaf_type
    (SmallEtale.topology B S hS F) Stacks.Sites.isSheaf_fpqcTopology_globalSections

/-- Global regular functions form a sheaf of commutative rings on the small étale site of an
arbitrary presheaf.

This is the general form of `structurePresheaf_isSheaf` (Stacks 03G6), which it proves: the
`AlgebraicGeometry.IsAlgebraicSpace` hypothesis of 03G6 is genuinely unnecessary, because the
étale-chart condition already bundles representability of each chart and the diagonal never
enters the argument. See the implementation notes. -/
theorem structurePresheaf_isSheaf' :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F) (structurePresheaf B S hS F) :=
  Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget _ _ (isSheaf_globalSections B S hS F)

/-- **Stacks 03G6.** Global regular functions form a sheaf of commutative rings on the small
étale site of an algebraic space.

Stated with 03G6's own hypotheses, in their original binder order, so that dependent results apply
it positionally; the hypothesis is discarded, and `structurePresheaf_isSheaf'` is the general
statement. -/
@[stacks 03G6]
theorem structurePresheaf_isSheaf (_hF : IsAlgebraicSpace B S hS F) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F) (structurePresheaf B S hS F) :=
  structurePresheaf_isSheaf' B S hS F

/-- The structure sheaf of commutative rings on the small étale site of an arbitrary presheaf
`F`. This is the general form of `structureSheaf`, which needs no algebraicity hypothesis. -/
def structureSheaf' : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  ⟨structurePresheaf B S hS F, structurePresheaf_isSheaf' B S hS F⟩

/-- The structure sheaf of commutative rings on the small étale site of the algebraic space `F`.

Stated with 03G6's own hypotheses, in their original binder order, so that a ringed site built on
it applies this positionally; `structureSheaf'` is the general form, and the two are equal by
`rfl`. -/
@[stacks 03G7 "the structure sheaf of an algebraic space"]
def structureSheaf (_hF : IsAlgebraicSpace B S hS F) :
    Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  structureSheaf' B S hS F

/-- The structure sheaf of the small étale site of `F` has the presheaf of global regular
functions as its underlying presheaf. -/
@[simp]
theorem structureSheaf'_obj :
    (structureSheaf' B S hS F).obj = structurePresheaf B S hS F := rfl

/-- The structure sheaf of the small étale site of an algebraic space `F` has the presheaf of
global regular functions as its underlying presheaf. -/
@[simp]
theorem structureSheaf_obj (hF : IsAlgebraicSpace B S hS F) :
    (structureSheaf B S hS F hF).obj = structurePresheaf B S hS F := rfl

/-! ### Restriction of global sections to a surjective étale chart -/

section SurjectiveChart

open Opposite

/-- **Restriction of global sections to a surjective étale chart is injective.** A global
section of the structure presheaf of `F` — a compatible family of regular functions on the
étale charts of `F` — is determined by its value on any single chart which is surjective.

Every chart `W` of `F` is covered, in the small étale site, by charts factoring through the
given surjective chart `V`: the fibre product of `V` and `W` over `F` is again a chart of `F`,
and it is surjective étale over `W`, so the one-member family it forms is an étale covering
family. The bounded site admits only *selected* covering families, so that family is replaced
by a combinatorially equivalent selected one, whose members then each factor through it; two
sections agreeing on `V` therefore agree on a covering family of `W`. Separatedness of the
sheaf of global functions concludes. -/
theorem injective_sections_apply_of_presheafSurjective
    (V : SmallEtale B S hS F)
    (hV : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) V.1.hom) :
    Function.Injective (fun s : (structurePresheaf B S hS F ⋙
      CategoryTheory.forget CommRingCat.{u}).sections ↦ s.1 (op V)) := by
  classical
  intro s t hst
  let O := structurePresheaf B S hS F
  apply Functor.sections_ext_iff.mpr
  intro Wop
  let W := unop Wop
  -- Pulling `V` back to `W` gives a surjective étale chart over `W`. The bounded site admits
  -- only selected covering families, so that one-arrow family is replaced by a selected one,
  -- every arrow of which still factors through it.
  obtain ⟨E, hE, hfactor⟩ : ∃ E : PreZeroHypercover W,
      E.presieve₀ ∈ (SmallEtale.precoverage B S hS F) W ∧
      ∀ i, s.1 (op (E.X i)) = t.1 (op (E.X i)) := by
    let C₀ := BigFppfOver B S hS
    let T := BigFppfOver.toScheme B S hS
    let Q := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
    let : HasPullbacks B.Schemes := inferInstance
    let : HasPullbacks C₀ := inferInstance
    let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
    let : PreservesLimitsOfShape WalkingCospan T := by
      apply comp_preservesLimitsOfShape
    let : MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) := ⟨by
      intro X Y Z f g hf hg
      let : AlgebraicGeometry.Etale f := hf
      let : AlgebraicGeometry.Etale g := hg
      exact inferInstance⟩
    let : Q.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    let : Q.IsStableUnderBaseChange := by
      constructor
      intro X Y Y' T' f g f' g' hs hg
      show AlgebraicGeometry.Etale (T.map g')
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})) (hs.map T) hg
    have hVQ : Q.presheaf V.1.hom := V.2
    let R := hVQ.1
    let a := R.fst' W.1.hom
    let q := R.snd W.1.hom
    have hPB := R.isPullback' W.1.hom
    have hqEtale : AlgebraicGeometry.Etale (T.map q) :=
      hVQ.property W.1.hom (yoneda.map a) q hPB
    have hqSurjective : AlgebraicGeometry.Surjective (T.map q) :=
      hV.property W.1.hom (yoneda.map a) q hPB
    have haEtale : AlgebraicGeometry.Etale (T.map a) :=
      W.2.property V.1.hom (yoneda.map q) a hPB.flip
    -- Precomposing a chart with an étale morphism of schemes gives a chart.
    have hchart : ∀ {A : C₀} {Z : C₀} (x : A ⟶ Z) (z : yoneda.obj Z ⟶ F),
        AlgebraicGeometry.Etale (T.map x) → Q.presheaf z → Q.presheaf (yoneda.map x ≫ z) :=
      fun x z hx hz ↦ MorphismProperty.comp_mem _ _ _
        ((MorphismProperty.relative_map_iff (P := Q)).2 hx) hz
    have hP₀chart : Q.presheaf (yoneda.map a ≫ V.1.hom) := hchart a _ haEtale hVQ
    let Pchart : SmallEtale B S hS F :=
      ⟨CostructuredArrow.mk (yoneda.map a ≫ V.1.hom), hP₀chart⟩
    let qchart : Pchart ⟶ W :=
      ObjectProperty.homMk (CostructuredArrow.homMk q (by
        show yoneda.map q ≫ W.1.hom = yoneda.map a ≫ V.1.hom
        exact hPB.w.symm))
    let TS := SmallEtale.toSchemes B S hS F
    let qS := TS.map qchart
    have hqS_eq : qS = (BigFppfOver.forget B S hS).map q := rfl
    have hqS_etale : AlgebraicGeometry.Etale (B.inclusion.map qS) := by
      show AlgebraicGeometry.Etale (T.map q)
      exact hqEtale
    have hqS_surjective : AlgebraicGeometry.Surjective (B.inclusion.map qS) := by
      show AlgebraicGeometry.Surjective (T.map q)
      exact hqSurjective
    let E₀ : Covering B.Schemes := ⟨TS.obj W, PreZeroHypercover.singleton qS⟩
    have hE₀ : IsEtaleCovering E₀ := by
      show (PreZeroHypercover.singleton (B.inclusion.map qS)).presieve₀ ∈
        Scheme.precoverage (@AlgebraicGeometry.Etale) (B.inclusion.obj (TS.obj W))
      rw [PreZeroHypercover.presieve₀_singleton,
        Scheme.singleton_mem_precoverage_iff (P := @AlgebraicGeometry.Etale)]
      exact ⟨hqS_surjective.surj, hqS_etale⟩
    obtain ⟨E', hE'cover, hComb⟩ := etaleCovering_has_representative B E₀ hE₀
    rcases E' with ⟨E'target, E'⟩
    change ∃ hTarget : E₀.1 = E'target,
      PreZeroHypercover.CombinatoriallyEquivalent (hTarget ▸ E₀.2) E' at hComb
    rcases hComb with ⟨hTarget, hComb⟩
    cases hTarget
    have hPresieve : E'.presieve₀ = (PreZeroHypercover.singleton qS).presieve₀ :=
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb).symm
    have hEtale (i : E'.I₀) : AlgebraicGeometry.Etale (B.inclusion.map (E'.f i)) := by
      have hmem : (E'.map B.inclusion).presieve₀ ∈
          Scheme.etalePrecoverage (B.inclusion.obj (TS.obj W)) := hE'cover.2
      exact (Scheme.ofArrows_mem_precoverage_iff
        (P := @AlgebraicGeometry.Etale)).mp hmem |>.2 i
    let Wover := (SmallEtale.toOver B S hS F).obj W
    have singletonFactor (i : E'.I₀) :
        (PreZeroHypercover.singleton qS).presieve₀ (E'.f i) := by
      rw [← hPresieve]
      exact E'.presieve₀_f i
    let chartArrow (i : E'.I₀) : E'.X i ⟶ TS.obj Pchart :=
      eqToHom (singletonFactor i).obj_idx.symm
    have chartArrow_fac (i : E'.I₀) : E'.f i = chartArrow i ≫ qS :=
      (singletonFactor i).eq_eqToHom_comp_hom_idx
    let Ui (i : E'.I₀) : C₀ := Over.mk (E'.f i ≫ Wover.hom)
    let liftToPullback (i : E'.I₀) : Ui i ⟶ R.pullback W.1.hom :=
      Over.homMk (chartArrow i) (by
        show chartArrow i ≫ (R.pullback W.1.hom).hom = E'.f i ≫ Wover.hom
        calc
          chartArrow i ≫ (R.pullback W.1.hom).hom
              = chartArrow i ≫ (q.left ≫ Wover.hom) := by
            rw [← Over.w q]
            rfl
          _ = (chartArrow i ≫ q.left) ≫ Wover.hom := by rw [← Category.assoc]
          _ = E'.f i ≫ Wover.hom := by
            congr 1
            show chartArrow i ≫ qS = E'.f i
            exact (chartArrow_fac i).symm)
    have liftToPullback_comp (i : E'.I₀) :
        liftToPullback i ≫ q = Over.homMk (E'.f i) := by
      apply Over.OverMorphism.ext
      show chartArrow i ≫ (BigFppfOver.forget B S hS).map q = E'.f i
      rw [← hqS_eq, chartArrow_fac i]
    let familyObj : ∀ i : E'.I₀, SmallEtale B S hS F := fun i ↦ by
      have hriEtale : AlgebraicGeometry.Etale (T.map (liftToPullback i)) := by
        have hcomp : T.map (liftToPullback i) ≫ T.map q = B.inclusion.map (E'.f i) := by
          show B.inclusion.map (chartArrow i ≫
            (BigFppfOver.forget B S hS).map q) = _
          rw [← hqS_eq, chartArrow_fac i]
        let : AlgebraicGeometry.Etale (T.map q) := hqEtale
        let : AlgebraicGeometry.Etale (T.map (liftToPullback i) ≫ T.map q) := by
          rw [hcomp]
          exact hEtale i
        exact AlgebraicGeometry.Etale.of_comp (f := T.map (liftToPullback i)) (T.map q)
      exact ⟨CostructuredArrow.mk
        (yoneda.map (liftToPullback i) ≫ (yoneda.map a ≫ V.1.hom)),
        hchart _ _ hriEtale hP₀chart⟩
    let familyMap : ∀ i : E'.I₀, familyObj i ⟶ W := fun i ↦
      ObjectProperty.homMk <| CostructuredArrow.homMk (Over.homMk (E'.f i)) (by
        show yoneda.map (Over.homMk (E'.f i)) ≫ W.1.hom =
          yoneda.map (liftToPullback i) ≫ (yoneda.map a ≫ V.1.hom)
        calc
          yoneda.map (Over.homMk (E'.f i)) ≫ W.1.hom =
              (yoneda.map (liftToPullback i) ≫ yoneda.map q) ≫ W.1.hom := by
            rw [← Functor.map_comp]
            exact congrArg (fun g => yoneda.map g ≫ W.1.hom)
              (liftToPullback_comp i).symm
          _ = yoneda.map (liftToPullback i) ≫ (yoneda.map a ≫ V.1.hom) := by
            rw [Category.assoc, hPB.w.symm])
    let Esmall : PreZeroHypercover W := ⟨E'.I₀, familyObj, familyMap⟩
    have hmap : Esmall.map TS = E' := by
      ext
      · rfl
      · apply heq_of_eq
        funext i
        rfl
      · apply heq_of_eq
        funext i
        show TS.map (familyMap i) = E'.f i
        apply B.inclusion.map_injective
        simp [TS, SmallEtale.toSchemes, SmallEtale.toOver, familyMap]
    have hcover : SmallEtale.IsCovering B S hS F ⟨W, Esmall⟩ := by
      show B.etaleCovering ⟨TS.obj W, Esmall.map TS⟩
      rw [hmap]
      exact hE'cover
    refine ⟨Esmall, ⟨Esmall, rfl, hcover⟩, ?_⟩
    intro i
    show s.1 (op (familyObj i)) = t.1 (op (familyObj i))
    let hi : familyObj i ⟶ V :=
      ObjectProperty.homMk <| CostructuredArrow.homMk
        (liftToPullback i ≫ a) (by
          show yoneda.map (liftToPullback i ≫ a) ≫ V.1.hom =
            yoneda.map (liftToPullback i) ≫ (yoneda.map a ≫ V.1.hom)
          simp [Functor.map_comp, Category.assoc])
    exact (s.property hi.op).symm.trans
      ((congrArg (O.map hi.op).hom hst).trans (t.property hi.op))
  refine ((isSheaf_globalSections B S hS F).isSheafFor_of_mem_precoverage
    hE).isSeparatedFor.ext ?_
  rintro _ _ ⟨i⟩
  exact (s.property (E.f i).op).trans ((hfactor i).trans (t.property (E.f i).op).symm)

/-- **An étale-local property is realized on a surjective chart with injective restriction.**
If `F` has an étale-local property `P` of schemes in the sense of Stacks 03E6, then `F` has a
surjective étale chart whose underlying scheme has `P` and on which restriction of global
sections of the structure presheaf is injective.

Applied to reducedness — an étale-local property of schemes by
`AlgebraicGeometry.isReduced_isLocal_etale` — this says that a reduced algebraic
space has a reduced surjective étale chart on which global regular functions restrict
injectively. -/
theorem exists_surjective_etale_chart_injective_sections
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (hP : HasEtaleLocalProperty B S hS F P) :
    ∃ V : SmallEtale B S hS F,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) V.1.hom ∧
      P ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)) ∧
      Function.Injective (fun s : (structurePresheaf B S hS F ⋙
        CategoryTheory.forget CommRingCat.{u}).sections ↦ s.1 (op V)) := by
  obtain ⟨U, f, hsurj, hetale, hPU⟩ := hP
  exact ⟨⟨CostructuredArrow.mk f, hetale⟩, hsurj, hPU,
    injective_sections_apply_of_presheafSurjective B S hS F _ hsurj⟩

end SurjectiveChart

end AlgebraicGeometry.Space

end
