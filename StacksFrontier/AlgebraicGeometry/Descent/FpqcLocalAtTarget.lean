module

public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing

/-!
# Properties of morphisms local on the target for the fpqc topology

A property `P` of morphisms of schemes is *fpqc local on the base* if, for every fpqc covering
`{Yᵢ → Y}` and every `f : X ⟶ Y`, the morphism `f` has `P` if and only if each base change
`Yᵢ ×_Y X ⟶ Yᵢ` has `P`. In Mathlib this is `CategoryTheory.MorphismProperty.IsLocalAtTarget P
AlgebraicGeometry.Scheme.fpqcPrecoverage`.

The main result is a criterion for this: a property which is Zariski local on the target, stable
under *flat* base change, and which descends along surjective flat morphisms of affine schemes is
fpqc local on the target. It is then applied to quasi-compactness, to finite type and to closed
immersions.

## Main definitions

* `Stacks.Descent.IsStableUnderFlatBaseChange`: a property of morphisms of schemes is stable
  under flat base change when the base change of a morphism with the property along an arbitrary
  flat morphism again has the property. This is hypothesis (1) of Tag 02KP for the fpqc topology.

## Main results

* `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage_of_affineDescent` is the criterion: it reduces
  being fpqc local on the target to Zariski locality, stability under flat base change and descent
  along surjective flat morphisms of affine schemes.
* `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` is the same criterion with descent assumed
  along *every* surjective flat quasi-compact morphism, which is the form its consumers supply.
* `Stacks.Descent.iff_of_fpqcZeroHypercover_of_affineDescent` is the criterion relativized to a
  class `C` of morphisms stable under base change: the descent step is assumed only for morphisms
  in `C`, and the conclusion is the fpqc-local characterization for morphisms in `C`.
* `Stacks.Descent.quasiCompact_descendsAlong_surjective_inf_flat_inf_quasiCompact`: quasi-compact
  morphisms satisfy fpqc descent.
* `Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc`: quasi-compactness is fpqc local on the base.
* `Stacks.Descent.surjective_isLocalAtTarget_fpqc`: surjectivity is fpqc local on the base.
* `Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc`: being locally of finite type is fpqc
  local on the base.
* `Stacks.Descent.finiteType_isLocalAtTarget_fpqc`: being of finite type is fpqc local on the base.
* `Stacks.Descent.isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact`: closed
  immersions satisfy fpqc descent.
* `Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc`: being a closed immersion is fpqc local
  on the base.
* `Stacks.Descent.diagonal_isOpenImmersion_isLocalAtTarget_fpqc` and
  `Stacks.Descent.isOpenImmersion_diagonal_iff_of_fpqcCover`: having an open diagonal is fpqc
  local on the base.

## Implementation notes

The criterion is the fpqc case of Tag 02KP. Its proof follows the Stacks argument: Zariski
locality on the target reduces the claim to an affine base `V`; the quasi-compactness of the
covering (`AlgebraicGeometry.QuasiCompactCover`) then provides, by
`AlgebraicGeometry.QuasiCompactCover.exists_hom`, a *finite* refinement of the covering by flat
morphisms from affine schemes; the disjoint union of that finite family is a single surjective
flat morphism `W ⟶ V` of *affine* schemes, `W` being a finite disjoint union of affine schemes,
and the assumed descent along such morphisms finishes the proof.

Descent is therefore only ever used along a surjective flat morphism of affine schemes, which is
what hypothesis (3) of the tag asks for and what
`isLocalAtTarget_fpqcPrecoverage_of_affineDescent` assumes. The variant
`isLocalAtTarget_fpqcPrecoverage` instead takes
`CategoryTheory.MorphismProperty.DescendsAlong P (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, a
strictly stronger hypothesis since it quantifies over non-affine morphisms as well; it is derived
from the affine form, a surjective flat morphism of affine schemes being quasi-compact, and is
kept because it is the shape instance synthesis can supply and so the one the consumers in this
development use.

Hypothesis (1) of Tag 02KP asks, for the fpqc topology, only for stability under *flat* base
change, and that is what `IsStableUnderFlatBaseChange` records and all the criterion needs: every
base change performed below is along an open immersion, along a member of the given flat
covering, or along a base change of one of those, hence along a flat morphism. Stability under
arbitrary base change would be a strictly stronger hypothesis that the intended consumers cannot
supply: the three regularity conditions on immersions of Tag 0694 are preserved under flat base
change (Tag 067P) but not under arbitrary base change. For instance `(x) ⊆ k[x]` is generated by
the Koszul-regular sequence `x`, while its extension along `k[x] ⟶ k[x]/(x²)` is generated by the
image of `x`, which that image annihilates, so the Koszul complex of any generating sequence of
the extended ideal has nonvanishing top homology. A property that does happen to be stable under
arbitrary base change supplies the hypothesis automatically, through Mathlib's instance deriving
`CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong` from
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`; the three applications at the end of
this file rely on that.

A morphism of finite type is, following Mathlib's convention, a morphism which is both
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`, so the morphism
property for Tag 02KZ is the infimum of those two.

The Stacks proof of Tag 02L6 deduces that `f` is affine from Tag 02L5, that affineness is fpqc
local on the base. That is replaced here by the observation used in Mathlib's proof of Tag 02L4:
a morphism which is universally closed and universally injective is a closed embedding on points,
and a morphism whose underlying map is inducing with closed image is affine
(`AlgebraicGeometry.isAffineHom_of_isInducing`). Both universal closedness and universal
injectivity already satisfy fpqc descent in Mathlib, so this avoids Tag 02L5 entirely; the
surjectivity of the map on global sections then descends by
`RingHom.FaithfullyFlat.codescendsAlong_surjective`.

Several auxiliary declarations below merely re-package Mathlib instances. They are needed because
instance synthesis cannot solve for the ring-homomorphism or affine-target parameter of
`AlgebraicGeometry.HasRingHomProperty` and `AlgebraicGeometry.HasAffineProperty`, nor match a
morphism property appearing as a factor of an infimum, without reducibility settings that this
development does not use.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02KQ](https://stacks.math.columbia.edu/tag/02KQ)
* [Stacks Project, Tag 02KV](https://stacks.math.columbia.edu/tag/02KV)
* [Stacks Project, Tag 02KX](https://stacks.math.columbia.edu/tag/02KX)
* [Stacks Project, Tag 02KZ](https://stacks.math.columbia.edu/tag/02KZ)
* [Stacks Project, Tag 02L6](https://stacks.math.columbia.edu/tag/02L6)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe w v u

namespace Stacks.Descent

/-- The sections of a morphism over the whole space are its action on global sections. -/
lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app f

/-- A flat morphism precomposed with an open immersion is flat. -/
private lemma flat_respectsLeft_isOpenImmersion :
    MorphismProperty.RespectsLeft (@Flat : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
  @IsZariskiLocalAtSource.respectsLeft_isOpenImmersion _ flat_isZariskiLocalAtSource

/-- Quasi-compactness is Zariski local on the target. -/
private lemma quasiCompact_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

/-- Being locally of finite type is Zariski local on the target. -/
private lemma locallyOfFiniteType_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)

/-- **Stability under flat base change**, hypothesis (1) of Tag 02KP for the fpqc topology: the
base change of a morphism with `P` along an arbitrary flat morphism again has `P`. -/
class IsStableUnderFlatBaseChange (P : MorphismProperty Scheme.{u}) : Prop where
  /-- `P` is stable under base change along any flat morphism. -/
  isStableUnderBaseChangeAlong {A B : Scheme.{u}} (q : A ⟶ B) [Flat q] :
    P.IsStableUnderBaseChangeAlong q

/-- A property stable under arbitrary base change is stable under flat base change.

Apply this **by name** on a property whose morphism arguments are implicit rather than strict
implicit, such as `@QuasiCompact`: instance search would have to assign a metavariable of type
`MorphismProperty Scheme.{u}` to such a term, which needs `MorphismProperty` to be unfolded in a
type and so is not available at the transparency instance search uses. -/
instance isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    IsStableUnderFlatBaseChange P where
  isStableUnderBaseChangeAlong _ := inferInstance

section Pullback

variable (P : MorphismProperty Scheme.{u})

/-- Pulling `f` back along `k ≫ g` is the same as pulling the base change of `f` along `g` back
along `k`. -/
lemma pullback_snd_comp_iff [P.RespectsIso] {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y)
    (g : Z ⟶ Y) (k : Z' ⟶ Z) :
    P (pullback.snd (pullback.snd f g) k) ↔ P (pullback.snd f (k ≫ g)) := by
  have h₁ : IsPullback (pullback.fst (pullback.snd f g) k) (pullback.snd (pullback.snd f g) k)
      (pullback.snd f g) k := .of_hasPullback _ _
  have h₂ : IsPullback (pullback.fst f g) (pullback.snd f g) f g := .of_hasPullback _ _
  have h := (h₁.flip.paste_vert h₂.flip).flip
  rw [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

/-- If the base change of `f` along `g` has `P`, then so does its base change along `k ≫ g`, for
`k` flat. -/
private lemma pullback_snd_comp [P.RespectsIso] [IsStableUnderFlatBaseChange P]
    {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (k : Z' ⟶ Z) [Flat k]
    (h : P (pullback.snd f g)) :
    P (pullback.snd f (k ≫ g)) :=
  have _ := IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong (P := P) k
  (pullback_snd_comp_iff P f g k).mp (P.pullback_snd _ _ h)

/-- Base changing along a flat `p` and then along the first projection of `V ×_Y Z` is base
changing along `g : Z ⟶ Y`. -/
private lemma pullback_snd_pullback_fst [P.RespectsIso] [IsStableUnderFlatBaseChange P]
    {X Y V Z : Scheme.{u}} (f : X ⟶ Y) (p : V ⟶ Y) [Flat p] (g : Z ⟶ Y)
    (h : P (pullback.snd f g)) :
    P (pullback.snd (pullback.snd f p) (pullback.fst p g)) := by
  rw [pullback_snd_comp_iff P, pullback.condition]
  exact pullback_snd_comp P f g _ h

/-- If every base change of `f` along a family `g` has `P`, then so does the base change of `f`
along the induced morphism from the disjoint union. -/
private lemma pullback_snd_sigmaDesc [IsZariskiLocalAtTarget P]
    {X V : Scheme.{u}} (f : X ⟶ V) {ι : Type*} [Small.{u} ι] {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ V) (h : ∀ i, P (pullback.snd f (g i))) :
    P (pullback.snd f (Sigma.desc g)) := by
  have key : ∀ i : ι, P (pullback.snd (pullback.snd f (Sigma.desc g)) (Sigma.ι W i)) := by
    intro i
    rw [pullback_snd_comp_iff P, Sigma.ι_desc]
    exact h i
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (K := Scheme.zariskiPrecoverage) (sigmaOpenCover W) key

end Pullback

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
  [IsStableUnderFlatBaseChange P]

/-- A property which is Zariski local on the target, stable under flat base change and which
descends along surjective flat morphisms of affine schemes (for morphisms in an auxiliary class
`C`, only ever invoked on `f` itself) holds for `f : X ⟶ V` with `V` affine as soon as it holds for
the base changes of `f` along the members of a quasi-compact flat covering of `V`. -/
private lemma of_quasiCompactCover_of_class (C : MorphismProperty Scheme.{u})
    (hdesc : ∀ {S S' T : Scheme.{u}} [IsAffine S] [IsAffine S'] (g : S' ⟶ S), Surjective g →
      Flat g → ∀ f : T ⟶ S, C f → P (pullback.snd f g) → P f)
    {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V) (hC : C f)
    (𝒱 : Scheme.Cover.{v} (Scheme.precoverage @Flat) V)
    [qc : QuasiCompactCover 𝒱.toPreZeroHypercover] (h : ∀ i, P (pullback.snd f (𝒱.f i))) :
    P f := by
  have := flat_respectsLeft_isOpenImmersion.{u}
  obtain ⟨𝒲, φ, hfin, hoi⟩ := QuasiCompactCover.exists_hom (P := @Flat) 𝒱
  have _ : ∀ j, Flat (𝒲.cover.f j) := 𝒲.map_prop
  have _ : Finite 𝒲.cover.I₀ := hfin
  have _ : ∀ j, IsAffine (𝒲.cover.X j) := fun j ↦ inferInstanceAs (IsAffine (Spec _))
  have hsurj : Surjective (Sigma.desc fun j ↦ 𝒲.cover.f j) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨𝒲.idx x, 𝒲.covers x⟩)
  -- A finite disjoint union of affine schemes is affine, so the collapsed refinement is a
  -- surjective flat morphism of affine schemes and `hdesc` applies to it.
  have _ : IsAffine (∐ fun j ↦ 𝒲.cover.X j) := inferInstance
  refine hdesc (Sigma.desc fun j ↦ 𝒲.cover.f j) hsurj inferInstance f hC ?_
  refine pullback_snd_sigmaDesc P f _ fun j ↦ ?_
  rw [← φ.w₀ j]
  have _ : IsOpenImmersion (φ.h₀ j) := hoi j
  exact pullback_snd_comp P f (𝒱.f (φ.s₀ j)) (φ.h₀ j) (h (φ.s₀ j))

/-- The members of an fpqc covering family are flat. -/
private lemma flat_of_mem₀_fpqcPrecoverage {Y : Scheme.{u}}
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage Y) (i : 𝒰.I₀) : Flat (𝒰.f i) :=
  ((Scheme.presieve₀_mem_precoverage_iff _).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ 𝒰.mem₀)).2 i

/-- **Stacks Project, Tag 02KP** for the fpqc topology, as a criterion valid on a class `C` of
morphisms rather than on all of them. Let `P` be a property of morphisms of schemes which is
stable under base change along flat morphisms and Zariski local on the base, and let `C` be a
class of morphisms stable under base change. Assume that for every surjective flat morphism
`g : S' ⟶ S` of affine schemes and every morphism of schemes `f : X ⟶ S` **in `C`**, the property
`P` holds for `f` if it holds for the base change `S' ×_S X ⟶ S'`. Then, for a morphism `f` in
`C`, the property `P` holds for `f` if and only if it holds for the base changes of `f` along the
members of any fpqc covering of the target.

The unrestricted criterion is the case `C = ⊤`, which is
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage_of_affineDescent` below. The restricted form is
what a property whose descent step is only available on a sub-class can supply: the descent of
the three regularity conditions of Stacks tag 0694 is known for morphisms already known to be
immersions, being an immersion itself being fpqc local on the base only for quasi-compact
immersions (Stacks tag 02L8). -/
@[sga "3 IV 6.4.1" "Case C = ⊤"]
theorem iff_of_fpqcZeroHypercover_of_affineDescent (C : MorphismProperty Scheme.{u})
    [C.IsStableUnderBaseChange]
    (hdesc : ∀ {S S' T : Scheme.{u}} [IsAffine S] [IsAffine S'] (g : S' ⟶ S), Surjective g →
      Flat g → ∀ f : T ⟶ S, C f → P (pullback.snd f g) → P f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hC : C f)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage Y) :
    P f ↔ ∀ i, P (pullback.snd f (𝒰.f i)) := by
  refine ⟨fun hf i ↦ ?_, fun h ↦ ?_⟩
  · have _ : Flat (𝒰.f i) := flat_of_mem₀_fpqcPrecoverage 𝒰 i
    have _ := IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong (P := P) (𝒰.f i)
    exact P.pullback_snd _ _ hf
  · have key : ∀ i : Y.affineCover.I₀, P (pullback.snd f (Y.affineCover.f i)) := fun i ↦
      of_quasiCompactCover_of_class P C hdesc _ (C.pullback_snd f (Y.affineCover.f i) hC)
        { toPreZeroHypercover := (𝒰.pullback₁ (Y.affineCover.f i)).toPreZeroHypercover
          mem₀ := (𝒰.pullback₁ (Y.affineCover.f i)).mem₀.2 }
        (qc := Scheme.presieve₀_mem_qcPrecoverage_iff.mp
          (𝒰.pullback₁ (Y.affineCover.f i)).mem₀.1)
        fun k ↦ pullback_snd_pullback_fst P f _ (𝒰.f k) (h k)
    exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (K := Scheme.zariskiPrecoverage) Y.affineCover key

/-- **Stacks Project, Tag 02KP** for the fpqc topology. Let `P` be a property of morphisms of
schemes. Assume that

1. `P` is stable under base change along flat morphisms;
2. `P` is Zariski local on the base;
3. for every surjective flat morphism `g : S' ⟶ S` of affine schemes and every morphism of
   schemes `f : X ⟶ S`, the property `P` holds for `f` if it holds for the base change
   `S' ×_S X ⟶ S'`.

Then `P` is fpqc local on the base. -/
@[stacks 02KP "the fpqc case"]
theorem isLocalAtTarget_fpqcPrecoverage_of_affineDescent
    (hdesc : ∀ {S S' T : Scheme.{u}} [IsAffine S] [IsAffine S'] (g : S' ⟶ S), Surjective g →
      Flat g → ∀ f : T ⟶ S, P (pullback.snd f g) → P f) :
    P.IsLocalAtTarget Scheme.fpqcPrecoverage := by
  apply MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover
  intro X Y f 𝒰
  exact iff_of_fpqcZeroHypercover_of_affineDescent P ⊤ (fun g hs hf f _ ↦ hdesc g hs hf f) f
    trivial 𝒰

/-- The derived stronger form of `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage_of_affineDescent`:
a property which is Zariski local on the base, stable under flat base change, and which descends
along *every* surjective flat quasi-compact morphism, is fpqc local on the base.

Descent along all of `@Surjective ⊓ @Flat ⊓ @QuasiCompact` is more than Tag 02KP asks for, since
that class contains morphisms of non-affine schemes; it is however the form that instance
synthesis can supply, and it implies the tag's hypothesis because a surjective flat morphism of
affine schemes is quasi-compact. -/
theorem isLocalAtTarget_fpqcPrecoverage
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] :
    P.IsLocalAtTarget Scheme.fpqcPrecoverage := by
  apply isLocalAtTarget_fpqcPrecoverage_of_affineDescent P
  intro S S' T _ _ g hsurj hflat f hp
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
    ⟨⟨hsurj, hflat⟩, inferInstance⟩ hp

/-- **Stacks Project, Tag 02KQ.** Quasi-compact morphisms satisfy fpqc descent: if the base change
of `g` along a surjective flat quasi-compact morphism is quasi-compact, then so is `g`. -/
@[stacks 02KQ "the descent step", ega "IV 1.1.4" "special case"]
instance quasiCompact_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := quasiCompact_isZariskiLocalAtTarget.{u}
  have := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  refine IsZariskiLocalAtTarget.descendsAlong @QuasiCompact (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
    fun {R X Y} f g hf hfst ↦ ?_
  obtain ⟨⟨hs, -⟩, hqc⟩ := hf
  have _ : Surjective f := hs
  have _ : QuasiCompact f := hqc
  have _ : CompactSpace X := (quasiCompact_iff_compactSpace f).mp hqc
  have hc : IsCompact (Set.univ : Set ↥(pullback f g)) := by
    simpa using QuasiCompact.isCompact_preimage (f := pullback.fst f g) Set.univ isOpen_univ
      CompactSpace.isCompact_univ
  have _ : Surjective (pullback.snd f g) := inferInstance
  have hY : CompactSpace Y := by
    constructor
    rw [← Set.image_univ_of_surjective (pullback.snd f g).surjective]
    exact hc.image (pullback.snd f g).continuous
  exact (quasiCompact_iff_compactSpace g).mpr hY

/-- **Stacks Project, Tag 02KQ.** Quasi-compactness of a morphism of schemes is fpqc local on the
base. -/
@[stacks 02KQ, sga "4 IV 8.5.5"]
instance quasiCompact_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := quasiCompact_isZariskiLocalAtTarget.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@QuasiCompact : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02KV.** Surjectivity of a morphism of schemes is fpqc local on the
base. -/
@[stacks 02KV, sga "4 IV 8.5.5"]
instance surjective_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Surjective : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Surjective : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02KX.** Being locally of finite type is fpqc local on the base. -/
@[stacks 02KX]
instance locallyOfFiniteType_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- **Stacks Project, Tag 02KZ.** Being of finite type is fpqc local on the target for scheme
morphisms. -/
@[stacks 02KZ]
instance finiteType_isLocalAtTarget_fpqc :
    IsLocalAtTarget (@LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  .inf _ _

/-- A morphism of affine schemes is a closed immersion precisely when the induced map on global
sections is surjective. -/
private lemma isClosedImmersion_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IsClosedImmersion (Spec.map φ) ↔ Function.Surjective φ.hom :=
  ⟨fun _ ↦ (RingHom.surjective_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine φ)).mpr
      (IsClosedImmersion.isAffine_surjective_of_isAffine (f := Spec.map φ)).2,
    IsClosedImmersion.spec_of_surjective φ⟩

/-- Closed immersions satisfy fpqc descent: if the base change of `g` along a surjective flat
quasi-compact morphism is a closed immersion, then so is `g`. -/
@[stacks 02L6 "the descent step",
  ega "IV 2.7.1" "(xii)",
  sga "1 VIII 5.5" "closed-immersion clause",
  sga "3 IV 4.7" "partial",
  sga "4 IV 8.5.5" "partial"]
instance isClosedImmersion_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isStableUnderBaseChange_surjective_inf_flat.{u}
  have := isStableUnderComposition_surjective_inf_flat.{u}
  have := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsClosedImmersion
    (@Surjective ⊓ @Flat) isLocalIso_inf_surjective_le_surjective_inf_flat ?_
  intro R S Y φ g h hfst
  obtain ⟨hs, hfl⟩ := h
  have _ : Surjective (Spec.map φ) := hs
  have _ : Flat (Spec.map φ) := hfl
  have _ : IsClosedImmersion (pullback.fst (Spec.map φ) g) := hfst
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map φ) :=
    ⟨⟨hs, hfl⟩, inferInstance⟩
  -- The base change is universally closed and universally injective, and both properties
  -- descend, so `g` is a closed embedding on points, hence affine; in particular `Y` is affine.
  have _ : UniversallyClosed g :=
    of_pullback_fst_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ inferInstance
  have _ : UniversallyInjective g :=
    of_pullback_fst_of_descendsAlong (P := @UniversallyInjective)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ inferInstance
  have hce : Topology.IsClosedEmbedding g.base :=
    .of_continuous_injective_isClosedMap g.continuous g.injective g.isClosedMap
  have _ : IsAffineHom g := isAffineHom_of_isInducing g hce.isInducing hce.isClosed_range
  have _ : IsAffine Y := isAffine_of_isAffineHom g
  -- Hence we may assume `Y` is the spectrum of a ring and appeal to the descent of surjectivity
  -- along faithfully flat ring maps.
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) Y.isoSpec.inv g]
  have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) Y.isoSpec.inv (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
  have hfst' : IsClosedImmersion (pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g)) := by
    rw [heq, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
    exact hfst
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  rw [← hψ] at hfst' ⊢
  refine of_pullback_fst_Spec_of_codescendsAlong (P := @IsClosedImmersion)
      (Q' := RingHom.FaithfullyFlat) (Q := fun f ↦ Function.Surjective f)
      (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_surjective (fun hf ↦ ?_) (fun {_ _ f} ↦ ?_)
      ⟨hs, hfl⟩ hfst'
  · rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · exact isClosedImmersion_SpecMap_iff f

/-- **Stacks Project, Tag 02L6.** Being a closed immersion is fpqc local on the base. -/
@[stacks 02L6,
  ega "IV 2.7.1" "(xii)",
  sga "3 VIB 12.1" "more general",
  sga "3 VIII 1.7.3" "Closed immersion clause",
  sga "4 IV 8.5.5"]
instance isClosedImmersion_isLocalAtTarget_fpqc :
    (show MorphismProperty Scheme.{u} from @IsClosedImmersion).IsLocalAtTarget
      Scheme.fpqcPrecoverage :=
  have := IsClosedImmersion.isZariskiLocalAtTarget.{u}
  have := IsClosedImmersion.isStableUnderBaseChange.{u}
  isLocalAtTarget_fpqcPrecoverage _

/-- Having an open diagonal is fpqc local on the base.

Being an open immersion is Zariski local on the target, stable under base change and satisfies
fpqc descent, and all three properties pass to the diagonal, so the criterion applies. -/
instance diagonal_isOpenImmersion_isLocalAtTarget_fpqc :
    IsLocalAtTarget (MorphismProperty.diagonal @IsOpenImmersion : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  have := isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (MorphismProperty.diagonal @IsOpenImmersion : MorphismProperty Scheme.{u})
  isLocalAtTarget_fpqcPrecoverage _

/-- The diagonal of a morphism of schemes is an open immersion if and only if the diagonal of
every one of its base changes along an fpqc covering of the target is an open immersion. -/
theorem isOpenImmersion_diagonal_iff_of_fpqcCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage S) :
    IsOpenImmersion (pullback.diagonal f) ↔
      ∀ i, IsOpenImmersion (pullback.diagonal (pullback.snd f (𝒰.f i))) :=
  IsLocalAtTarget.iff_of_zeroHypercover
    (P := (MorphismProperty.diagonal @IsOpenImmersion : MorphismProperty Scheme.{u})) 𝒰

end Stacks.Descent

end
