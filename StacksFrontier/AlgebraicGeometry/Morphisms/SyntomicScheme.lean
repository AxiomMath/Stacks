module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.StandardRefinement
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic descent on the source

A property of morphisms of schemes is local on the source for the syntomic precoverage as soon
as it is Zariski local on the source and on the target, is preserved by precomposition with
syntomic morphisms, and descends along surjective syntomic morphisms of affine schemes.

## Main results

* `AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent` is the syntomic affine descent
  criterion.
* `AlgebraicGeometry.syntomic_isLocalAtSource_of_affine_descent` is that criterion applied to
  syntomicity itself, leaving the affine descent of syntomicity as its only hypothesis.

## Implementation notes

The syntomic precoverage is Mathlib's jointly surjective precoverage
`AlgebraicGeometry.Scheme.precoverage` associated to `AlgebraicGeometry.Syntomic`; its covering
families are exactly the syntomic coverings of Tag 0225.

The reduction to affine schemes is `AlgebraicGeometry.isLocalAtSource_of_affineCriterion`, which
is stated for an arbitrary precoverage stable under base change and an arbitrary morphism
property `Q` whose morphisms the given property respects on the left. It replaces an arbitrary
morphism by its restrictions to the affine charts of an affine cover of the target and of the
induced cover of the source, and base-changes the covering family along the resulting open
immersion.

Specialising to the syntomic precoverage, a syntomic covering of an affine scheme is refined by
a *finite* covering by affine schemes that are standard syntomic over the target, by
`AlgebraicGeometry.exists_finite_affine_standardSyntomic_refinement` (Tag 0228). The coproduct
of such a finite family is again affine and syntomic over the target, and is surjective, so the
affine descent hypothesis applies to it. This is why the criterion asks for descent only along
*affine* surjective syntomic morphisms.

## References

* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 0225](https://stacks.math.columbia.edu/tag/0225)
* [Stacks Project, Tag 0228](https://stacks.math.columbia.edu/tag/0228)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

section Reduction

variable {Q : MorphismProperty Scheme.{u}}

/-- A property that is Zariski local on the source descends along a *finite* affine cover whose
coproduct map satisfies `Q`, provided it descends along surjective `Q`-morphisms of affine
schemes. -/
theorem affine_descent_of_finite_affineCover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (V : Scheme.AffineCover.{w} Q X) [Finite V.I₀] (hV : ∀ i, P (V.f i ≫ f))
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Q g → P (g ≫ f) → P f)
    (hQ : Q (Sigma.desc V.f)) : P f := by
  have hsurj : Surjective (Sigma.desc V.f) :=
    Surjective.sigmaDesc_of_union_range_eq_univ V.cover.iUnion_range
  have hcomp : P (Sigma.desc V.f ≫ f) := by
    have h' : P (Sigma.desc fun i ↦ V.f i ≫ f) :=
      IsZariskiLocalAtSource.sigmaDesc (P := P) hV
    convert h' using 1
    ext i
    simp
  exact hAffine (Sigma.desc V.f) f hsurj hQ hcomp

/-- A property that is Zariski local on the source descends along a covering family that is
refined, by open immersions, by a finite affine `Q`-cover with `Q`-coproduct map. -/
theorem affine_descent_of_refinement (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (U : Scheme.Cover.{v} (Scheme.precoverage Q) X) (V : Scheme.AffineCover.{w} Q X)
    [Finite V.I₀] (r : V.cover.toPreZeroHypercover.Hom U.toPreZeroHypercover)
    (hOpen : ∀ i, IsOpenImmersion (r.h₀ i)) (hU : ∀ i, P (U.f i ≫ f))
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Q g → P (g ≫ f) → P f)
    (hQ : Q (Sigma.desc V.f)) : P f := by
  refine affine_descent_of_finite_affineCover P f V (fun i ↦ ?_) hAffine hQ
  change P (V.cover.f i ≫ f)
  have : IsOpenImmersion (r.h₀ i) := hOpen i
  rw [← r.w₀ i]
  exact IsZariskiLocalAtSource.comp (hU (r.s₀ i)) (r.h₀ i)

/-- The coproduct map of a family of `Q`-morphisms is a `Q`-morphism, when `Q` comes from a
property of ring maps. -/
theorem sigmaDesc_of_hasRingHomProperty
    {R : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop} [HasRingHomProperty Q R]
    {I : Type v} [Small.{u} I] {X : I → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (h : ∀ i, Q (f i)) : Q (Sigma.desc f) :=
  HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc h

/-- **Reduction of source-locality to the affine case.** A property that is Zariski local on the
source and on the target, and that is preserved by precomposition with the `Q`-morphisms
appearing in `K`-coverings, is local at the source for `K` as soon as it can be checked on
`K`-coverings of affine schemes over affine bases. -/
theorem isLocalAtSource_of_affineCriterion (P : MorphismProperty Scheme.{u})
    {K : Precoverage Scheme.{u}} [K.IsStableUnderBaseChange]
    [P.RespectsLeft Q] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hCoverProp : ∀ {X : Scheme.{u}} (U : K.ZeroHypercover.{u + 1} X) (i), Q (U.f i))
    (hAffine : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
      (U : K.ZeroHypercover.{u + 1} X), (∀ i, P (U.f i ≫ f)) → P f) :
    P.IsLocalAtSource K := by
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover fun {X Y} f U ↦ ?_
  refine ⟨fun hf i ↦ MorphismProperty.RespectsLeft.precomp (P := P) (Q := Q)
    (U.toPreZeroHypercover.f i) (hCoverProp U i) f hf, fun h ↦ ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P) Y.affineCover).2 fun j ↦ ?_
  let v := Y.affineCover.f j
  change P (pullback.snd f v)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (pullback f v).affineCover]
  intro k
  let w := (pullback f v).affineCover.f k
  let f' : (pullback f v).affineCover.X k ⟶ Y.affineCover.X j := w ≫ pullback.snd f v
  let g : (pullback f v).affineCover.X k ⟶ X := w ≫ pullback.fst f v
  have : IsOpenImmersion g := by dsimp only [g, w]; infer_instance
  let E := U.toPreZeroHypercover
  let U' : K.ZeroHypercover _ :=
    { I₀ := E.I₀
      X i := pullback g (E.f i)
      f i := pullback.fst g (E.f i)
      mem₀ := K.mem_coverings_of_isPullback E.f U.mem₀ g
        (fun i ↦ pullback.fst g (E.f i)) (fun i ↦ pullback.snd g (E.f i))
        (fun i ↦ IsPullback.of_hasPullback g (E.f i)) }
  refine hAffine f' U' fun i ↦ ?_
  let c := pullback.snd g (E.f i)
  have : IsOpenImmersion c := by dsimp only [c]; infer_instance
  have hcomp : P (c ≫ E.f i ≫ f) := IsZariskiLocalAtSource.comp (h i) c
  have heq : c ≫ E.f i ≫ f = (U'.f i ≫ f') ≫ v := by
    calc c ≫ E.f i ≫ f = pullback.fst g (E.f i) ≫ g ≫ f := by
          simpa [c, Category.assoc] using
            (pullback.condition_assoc (f := g) (g := E.f i) f).symm
      _ = pullback.fst g (E.f i) ≫ f' ≫ v := by
          simp only [g, f', Category.assoc, pullback.condition]
      _ = (U'.f i ≫ f') ≫ v := by rw [Category.assoc]; rfl
  have hv : IsOpenImmersion v := by dsimp only [v]; infer_instance
  have hpb : IsPullback (𝟙 _) (U'.f i ≫ f') ((U'.f i ≫ f') ≫ v) v :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact IsZariskiLocalAtTarget.of_isPullback hpb (heq ▸ hcomp)

/-- The precoverage attached to a base-change-stable morphism property of schemes is stable
under base change. -/
theorem precoverage_isStableUnderBaseChange (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] : (Scheme.precoverage Q).IsStableUnderBaseChange :=
  inferInstance

end Reduction

/-- **Stacks Project, Tag 036H, syntomic case.** A property of morphisms of schemes which is
Zariski local on the source and on the target, which is preserved by precomposition with
syntomic morphisms, and which descends along surjective syntomic morphisms of affine schemes,
is syntomic local on the source. -/
@[stacks 036H "syntomic case"]
theorem isLocalAtSource_syntomic_of_affine_descent (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Syntomic.{u})] [IsZariskiLocalAtSource P] [IsZariskiLocalAtTarget P]
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Syntomic g → P (g ≫ f) → P f) :
    P.IsLocalAtSource (Scheme.precoverage (@Syntomic.{u})) := by
  have := precoverage_isStableUnderBaseChange (@Syntomic.{u})
  refine isLocalAtSource_of_affineCriterion (P := P) (Q := @Syntomic.{u})
    (K := Scheme.precoverage (@Syntomic.{u})) (fun U i ↦ ?_) (fun {X Y} _ _ f U hU ↦ ?_)
  · exact ((Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀).2 i
  · obtain ⟨hcover, hmaps⟩ :=
      (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀
    have hsyntomicCover : IsSyntomicCovering U.X U.f := by
      refine ⟨hmaps, Set.eq_univ_iff_forall.mpr fun x ↦ ?_⟩
      obtain ⟨i, y, hy⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, hy⟩⟩
    obtain ⟨V, r, hfinite, -, hopen⟩ :=
      exists_finite_affine_standardSyntomic_refinement U.toPreZeroHypercover hsyntomicCover
    have : Finite V.I₀ := hfinite
    exact affine_descent_of_refinement P f
      { __ := U.toPreZeroHypercover, mem₀ := U.mem₀ } V r hopen hU hAffine
      (sigmaDesc_of_hasRingHomProperty (Q := @Syntomic.{u}) V.f V.map_prop)

/-- Being syntomic is local on the source for the syntomic topology, given that syntomicity
descends along a surjective syntomic morphism of affine schemes.

This is the reduction of **Stacks 036S** to a single statement about affine schemes: it is
`AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent` (**Stacks 036H**, syntomic case)
applied to `AlgebraicGeometry.Syntomic`, with all three of that criterion's instance arguments
supplied here. Precomposition with a syntomic morphism preserves syntomicity because syntomic
morphisms compose, and the two Zariski localities are the `AlgebraicGeometry.HasRingHomProperty`
structure of `AlgebraicGeometry.Syntomic` over `RingHom.Syntomic`.

The remaining hypothesis is the syntomic case of **Stacks 02KM**. It is deliberately left open,
so this statement carries no tag; a consumer that discharges it obtains Tag 036S outright. -/
theorem syntomic_isLocalAtSource_of_affine_descent
    (hAffine : ∀ {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
      (g : X' ⟶ X) (f : X ⟶ Y), Surjective g → Syntomic g → Syntomic (g ≫ f) → Syntomic f) :
    MorphismProperty.IsLocalAtSource (@Syntomic.{u}) (Scheme.precoverage (@Syntomic.{u})) :=
  let : MorphismProperty.RespectsLeft (@Syntomic.{u}) (@Syntomic.{u}) :=
    ⟨fun g hg f hf ↦ MorphismProperty.comp_mem _ g f hg hf⟩
  let : IsZariskiLocalAtSource (@Syntomic.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Syntomic)
  let : IsZariskiLocalAtTarget (@Syntomic.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Syntomic.{u}) (Q := RingHom.Syntomic)
  isLocalAtSource_syntomic_of_affine_descent (@Syntomic.{u}) hAffine

end AlgebraicGeometry

end
