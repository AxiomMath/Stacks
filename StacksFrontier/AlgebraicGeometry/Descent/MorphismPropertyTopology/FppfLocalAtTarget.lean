module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria

/-!
# Properties of morphisms local on the target for the fppf topology

A property `P` of morphisms of schemes is *fppf local on the base* if, for every fppf covering
`{Yᵢ → Y}` and every `f : X ⟶ Y`, the morphism `f` has `P` if and only if each base change
`Yᵢ ×_Y X ⟶ Yᵢ` has `P`. In Mathlib this is `CategoryTheory.MorphismProperty.IsLocalAtTarget P
AlgebraicGeometry.Scheme.fppfPrecoverage`.

The first result is a criterion for this, in the shape of the fpqc criterion in
`StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget` but with the smaller class of descent
morphisms that an fppf covering provides: a property which is Zariski local on the target, stable
under base change, and which descends along surjective flat quasi-compact morphisms *locally of
finite presentation* is fppf local on the target. It is then applied to immersions, which are not
known to be fpqc local on the base.

The file also records the consequence of fppf descent that a surjective étale chart carries: a
morphism of schemes is an isomorphism as soon as its base change along a surjective étale
morphism is. A surjective étale morphism is surjective, flat and locally of finite presentation
but need not be quasi-compact, so the fpqc descent of isomorphisms of Tag 02L4 does not apply to
it directly.

## Main results

* `Stacks.Descent.isLocalAtTarget_fppfPrecoverage_of_descendsAlong` is the criterion.
* `Stacks.Descent.isIso_of_pullbackSnd_of_surjective_etale`: a morphism of schemes is an
  isomorphism as soon as its base change along a surjective étale morphism is.
* `Stacks.Descent.isImmersion_isLocalAtTarget_fppf`: being an immersion is fppf local on the base.

## Implementation notes

The criterion is the fppf case of Tag 02KP and its proof follows the Stacks argument: Zariski
locality on the target reduces the claim to an affine base `V`; a member of an fppf covering
family is flat and locally of finite presentation, hence an open map, so the family is a
quasi-compact covering and `AlgebraicGeometry.QuasiCompactCover.exists_hom` provides a *finite*
refinement of it by flat, finitely presented morphisms from affine schemes; the disjoint union of
that finite family is a single surjective, flat, affine -- hence quasi-compact -- morphism
`W ⟶ V` locally of finite presentation, and the assumed descent along such morphisms finishes the
proof.

For immersions the descent step is Tag 02YM. Given `g : S' ⟶ S` surjective, flat, quasi-compact
and locally of finite presentation and `f : X ⟶ S` whose base change along `g` is an immersion,
local closedness of the range of `f` follows from local closedness of the range of the base
change because `g` is an open surjection; so `V := coborder (Set.range f)` is open in `S` and
contains the image of `f`. Restricting everything over `V` turns `f` into a morphism whose base
change along `g ∣_ V` is a *closed* immersion, and closed immersions are already known to be fpqc
local on the base, which identifies the restriction of `f` as a closed immersion. Composing it
with the open immersion `V.ι` exhibits `f` as an immersion.

Both halves need finite presentation for a different reason, and only through openness of `g`:
without it the range of `f` need not be locally closed, and `V` would not be available.

The descent of isomorphisms along a surjective étale morphism does *not* go through the criterion
above, and in particular does not have to shrink the chart to a quasi-compact piece. Mathlib
already removes the quasi-compactness hypothesis from Tag 02L4 once and for all, in the instance
deriving `CategoryTheory.MorphismProperty.DescendsAlong P (@Surjective ⊓ @Flat ⊓
@LocallyOfFinitePresentation)` from the quasi-compact form for any `P` which is Zariski local on
the target; being an isomorphism is such a `P`. So all that is left is to read a surjective étale
morphism as a surjective flat morphism locally of finite presentation.

## References

* [Stacks Project, Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
* [Stacks Project, Tag 02YM](https://stacks.math.columbia.edu/tag/02YM)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

universe v u

namespace Stacks.Descent

/-! ### Covering families for the fppf precoverage -/

/-- An fppf covering family is jointly surjective. -/
private lemma jointlySurjective_fppfPrecoverage :
    Scheme.JointlySurjective Scheme.fppfPrecoverage.{u} :=
  inferInstanceAs <| Scheme.JointlySurjective
    (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))

/-- Being flat and locally of finite presentation is Zariski local at the source. -/
private alias isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation :=
  AlgebraicGeometry.isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation

/-- A flat morphism locally of finite presentation precomposed with an open immersion is again
flat and locally of finite presentation. -/
private lemma respectsLeft_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
  have := isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation.{u}
  ⟨fun i _ _ hf => IsZariskiLocalAtSource.comp
    (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) hf i⟩

/-- Every fppf covering family is a quasi-compact covering family, its members being open maps. -/
private lemma quasiCompactCover_of_fppfCover {V : Scheme.{u}}
    (𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage.{u} V) :
    QuasiCompactCover 𝒱.toPreZeroHypercover := by
  have := jointlySurjective_fppfPrecoverage.{u}
  refine QuasiCompactCover.of_isOpenMap fun i => ?_
  obtain ⟨_, _⟩ : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (𝒱.f i) :=
    𝒱.map_prop i
  exact (𝒱.f i).isOpenMap

/-! ### The criterion -/

variable (P : MorphismProperty Scheme.{u})

section Pullback

/-- If the base change of `f` along `g` has `P`, then so does its base change along `k ≫ g`. -/
private lemma pullbackSnd_comp [P.RespectsIso] [P.IsStableUnderBaseChange]
    {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (k : Z' ⟶ Z)
    (h : P (pullback.snd f g)) :
    P (pullback.snd f (k ≫ g)) :=
  (pullback_snd_comp_iff P f g k).mp (P.pullback_snd _ _ h)

/-- Base changing along `p` and then along the first projection of `V ×_Y Z` is base changing
along `g : Z ⟶ Y`. -/
private lemma pullbackSnd_pullbackFst [P.RespectsIso] [P.IsStableUnderBaseChange]
    {X Y V Z : Scheme.{u}} (f : X ⟶ Y) (p : V ⟶ Y) (g : Z ⟶ Y) (h : P (pullback.snd f g)) :
    P (pullback.snd (pullback.snd f p) (pullback.fst p g)) := by
  rw [pullback_snd_comp_iff P, pullback.condition]
  exact pullbackSnd_comp P f g _ h

/-- If every base change of `f` along a family `g` has `P`, then so does the base change of `f`
along the induced morphism from the disjoint union. -/
private lemma pullbackSnd_sigmaDesc [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    {X V : Scheme.{u}} (f : X ⟶ V) {ι : Type*} [Small.{u} ι] {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ V) (h : ∀ i, P (pullback.snd f (g i))) :
    P (pullback.snd f (Sigma.desc g)) := by
  have key : ∀ i : ι, P (pullback.snd (pullback.snd f (Sigma.desc g)) (Sigma.ι W i)) := by
    intro i
    rw [pullback_snd_comp_iff P, Sigma.ι_comp_desc]
    exact h i
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (K := Scheme.zariskiPrecoverage) (sigmaOpenCover W) key

end Pullback

/-- A property which is Zariski local on the target, stable under base change and which descends
along surjective flat quasi-compact morphisms locally of finite presentation holds for
`f : X ⟶ V` with `V` affine as soon as it holds for the base changes of `f` along the members of
an fppf covering of `V`. -/
private lemma of_fppfCover_of_isAffine [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [MorphismProperty.DescendsAlong P
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation ⊓ @QuasiCompact)]
    {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage.{u} V)
    (h : ∀ i, P (pullback.snd f (𝒱.f i))) : P f := by
  have := respectsLeft_flat_inf_locallyOfFinitePresentation.{u}
  have := isZariskiLocalAtSource_flat_inf_locallyOfFinitePresentation.{u}
  let 𝒱' : Scheme.Cover.{v} (Scheme.precoverage
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) V :=
    { __ := 𝒱.toPreZeroHypercover, mem₀ := 𝒱.mem₀ }
  have _ : QuasiCompactCover 𝒱'.toPreZeroHypercover := quasiCompactCover_of_fppfCover 𝒱
  obtain ⟨𝒲, φ, hfin, -⟩ := QuasiCompactCover.exists_hom
    (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) 𝒱'
  have _ : ∀ j, Flat (𝒲.cover.f j) := fun j => (𝒲.map_prop j).1
  have _ : ∀ j, LocallyOfFinitePresentation (𝒲.cover.f j) := fun j => (𝒲.map_prop j).2
  have _ : Finite 𝒲.cover.I₀ := hfin
  have _ : ∀ j, IsAffine (𝒲.cover.X j) := fun j => inferInstanceAs (IsAffine (Spec _))
  have hsurj : Surjective (Sigma.desc 𝒲.cover.f) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨𝒲.idx x, 𝒲.covers x⟩)
  have _ : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  have hlfp : LocallyOfFinitePresentation (Sigma.desc 𝒲.cover.f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation) fun _ => inferInstance
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation ⊓ @QuasiCompact :
      MorphismProperty Scheme.{u}))
    (g := Sigma.desc 𝒲.cover.f)
    ⟨⟨⟨hsurj, inferInstance⟩, hlfp⟩, inferInstance⟩ ?_
  refine pullbackSnd_sigmaDesc P f _ fun j => ?_
  rw [← φ.w₀ j]
  exact pullbackSnd_comp P f (𝒱'.f (φ.s₀ j)) (φ.h₀ j) (h (φ.s₀ j))

/-- **Stacks Project, Tag 02KP** for the fppf topology. A property of morphisms of schemes which
is Zariski local on the base, stable under base change, and which descends along surjective flat
quasi-compact morphisms locally of finite presentation, is fppf local on the base. -/
theorem isLocalAtTarget_fppfPrecoverage_of_descendsAlong [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange]
    [MorphismProperty.DescendsAlong P
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation ⊓ @QuasiCompact)] :
    P.IsLocalAtTarget Scheme.fppfPrecoverage.{u} := by
  apply MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange
  intro X Y f 𝒰 h
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (K := Scheme.zariskiPrecoverage) Y.affineCover fun i =>
      of_fppfCover_of_isAffine P _
        { toPreZeroHypercover := (𝒰.pullback₁ (Y.affineCover.f i)).toPreZeroHypercover
          mem₀ := (𝒰.pullback₁ (Y.affineCover.f i)).mem₀ }
        fun k => pullbackSnd_pullbackFst P f _ (𝒰.f k) (h k)

/-! ### Isomorphisms -/

/-- **A morphism of schemes is an isomorphism as soon as its base change along a surjective
étale morphism is.** No hypothesis is placed on `φ`.

This is the descent of isomorphisms, Tag 02L4, along a morphism which is surjective, flat and
locally of finite presentation but need not be quasi-compact. The quasi-compactness is removed
by the Mathlib instance deriving `CategoryTheory.MorphismProperty.DescendsAlong P (@Surjective ⊓
@Flat ⊓ @LocallyOfFinitePresentation)` from the quasi-compact form for a `P` which is Zariski
local on the target, applied to `P = CategoryTheory.MorphismProperty.isomorphisms Scheme`. -/
@[sga "3 V 6.1" "special case", sga "4 IV 8.5.5" "partial"]
theorem isIso_of_pullbackSnd_of_surjective_etale {X Y Z : Scheme.{u}}
    (φ : X ⟶ Y) (ψ : Z ⟶ Y) [Surjective ψ] [Etale ψ] (h : IsIso (pullback.snd φ ψ)) :
    IsIso φ :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-! ### Immersions -/

/-- Taking coborders commutes with preimages under a continuous open map. -/
private lemma coborder_preimage_of_isOpenMap {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hopen : IsOpenMap g) (hcont : Continuous g) (s : Set Y) :
    coborder (g ⁻¹' s) = g ⁻¹' coborder s := by
  simp only [coborder, Set.preimage_compl, Set.preimage_sdiff,
    hopen.preimage_closure_eq_closure_preimage hcont]

/-- A subset of the target of a continuous open surjection is locally closed as soon as its
preimage is. -/
private lemma isLocallyClosed_of_isLocallyClosed_preimage {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y) (hopen : IsOpenMap g)
    (hcont : Continuous g) (hsurj : Function.Surjective g) (s : Set Y)
    (hs : IsLocallyClosed (g ⁻¹' s)) : IsLocallyClosed s := by
  rw [isLocallyClosed_iff_isOpen_coborder, ← Set.image_preimage_eq (coborder s) hsurj]
  simpa only [coborder_preimage_of_isOpenMap hopen hcont] using hopen _ hs.isOpen_coborder

/-- If `P` respects isomorphisms, it holds for the second projection of a pullback square as soon
as it holds for the second projection of the chosen pullback. -/
private lemma pullbackSnd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z T : Scheme.{u}} {fst : T ⟶ X} {snd : T ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback fst snd f g) (hs : P snd) : P (pullback.snd f g) := by
  rwa [← MorphismProperty.cancel_left_of_respectsIso P h.isoPullback.hom,
    h.isoPullback_hom_snd]

/-- A morphism to an open `V` of the target of a surjective flat quasi-compact `g` is a closed
immersion as soon as its base change along the restriction of `g` over `V` is. -/
private lemma isClosedImmersion_of_pullbackSnd_resLE {X S S' : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g] [Flat g] [QuasiCompact g] (V : S.Opens) (fV : X ⟶ V)
    (h : IsClosedImmersion (pullback.snd fV (g.resLE V (g ⁻¹ᵁ V) le_rfl))) :
    IsClosedImmersion fV := by
  have _ : QuasiCompact (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have _ : Surjective (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ := g.surjective y.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change g x ∈ V
      rw [hx]
      exact y.2
    · apply Subtype.ext
      simpa using hx
  exact MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsClosedImmersion) (K := Scheme.fpqcPrecoverage)
    (Scheme.Hom.singleton_mem_fpqcPrecoverage _) (by
      rintro _ _ _ ⟨⟩
      exact h)

/-- **Stacks Project, Tag 02YM**, descent step. If the base change of `f` along a surjective,
flat, quasi-compact morphism locally of finite presentation is an immersion, then so is `f`. -/
private lemma isImmersion_of_pullbackSnd {X S S' : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] [QuasiCompact g] (f : X ⟶ S)
    (hf : IsImmersion (pullback.snd f g)) : IsImmersion f := by
  let q := pullback.snd f g
  have hqrange : Set.range q = g.base ⁻¹' Set.range f := Scheme.Pullback.range_snd f g
  have hloc : IsLocallyClosed (Set.range f) :=
    isLocallyClosed_of_isLocallyClosed_preimage g.base g.isOpenMap g.continuous
      g.surjective _ (by simpa only [← hqrange] using hf.isLocallyClosed_range)
  let V : S.Opens := ⟨coborder (Set.range f), hloc.isOpen_coborder⟩
  let V' : S'.Opens := g ⁻¹ᵁ V
  have hVeq : q.coborderRange = V' := SetLike.coe_injective <|
    (congrArg coborder hqrange).trans (coborder_preimage_of_isOpenMap g.isOpenMap g.continuous _)
  have hqV : Set.range q ⊆ (V' : Set S') := by
    rw [hqrange]
    exact Set.preimage_mono subset_coborder
  let W : (pullback f g).Opens := q ⁻¹ᵁ V'
  have hWtop : W = ⊤ := eq_top_iff.mpr fun z _ => hqV ⟨z, rfl⟩
  let U : X.Opens := f ⁻¹ᵁ V
  have hUtop : U = ⊤ := eq_top_iff.mpr fun x _ => subset_coborder ⟨x, rfl⟩
  let fV := f.resLE V U le_rfl
  let gV := g.resLE V V' le_rfl
  let qV := q.resLE V' W le_rfl
  let eX : W.toScheme ≅ pullback f g :=
    (pullback f g).isoOfEq hWtop ≪≫ (pullback f g).topIso
  let eY : q.coborderRange.toScheme ≅ V'.toScheme := S'.isoOfEq hVeq
  have hqVeq : eX.hom ≫ q.liftCoborder ≫ eY.hom = qV := by
    apply (cancel_mono V'.ι).1
    calc eX.hom ≫ q.liftCoborder ≫ eY.hom ≫ V'.ι = W.ι ≫ q := by
          simp [eX, eY, q.liftCoborder_ι]
      _ = qV ≫ V'.ι := (Scheme.Hom.resLE_comp_ι q (e := le_rfl)).symm
  have hqVclosed : IsClosedImmersion qV := hqVeq ▸ inferInstance
  have hpre : q ⁻¹ᵁ V' = pullback.fst f g ⁻¹ᵁ U := by
    change (q ≫ g) ⁻¹ᵁ V = (pullback.fst f g ≫ f) ⁻¹ᵁ V
    rw [pullback.condition]
  have hpbRes := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := V) (UT := V') (UX := U) (UY := W) le_rfl le_rfl (by
      dsimp only [W]
      rw [hpre]
      simp)
  have hfVclosed : IsClosedImmersion fV :=
    isClosedImmersion_of_pullbackSnd_resLE g V fV (pullbackSnd_of_isPullback _ hpbRes hqVclosed)
  have hfac : (X.isoOfEq hUtop ≪≫ X.topIso).inv ≫ fV ≫ V.ι = f := by
    simp [fV, Scheme.Hom.resLE_comp_ι]
  rw [← hfac]
  infer_instance

/-- **Stacks Project, Tag 02YM**, descent step. Immersions descend along surjective flat
quasi-compact morphisms locally of finite presentation. -/
private lemma isImmersion_descendsAlong :
    MorphismProperty.DescendsAlong (@IsImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation ⊓ @QuasiCompact) where
  of_isPullback {_ _ _ _ _ _ f g} h hf hfst := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := hf
    have _ : MorphismProperty.RespectsIso (@IsImmersion : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact isImmersion_of_pullbackSnd f g (pullbackSnd_of_isPullback _ h.flip hfst)

/-- **Stacks Project, Tag 02YM.** Being an immersion is fppf local on the base. -/
instance isImmersion_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@IsImmersion : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  have := isImmersion_descendsAlong.{u}
  isLocalAtTarget_fppfPrecoverage_of_descendsAlong _

add_to_stacks 02YM Stacks.Descent.isImmersion_isLocalAtTarget_fppf

end Stacks.Descent

end
