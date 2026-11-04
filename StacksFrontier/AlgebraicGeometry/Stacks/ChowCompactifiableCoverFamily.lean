module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactificationSection

/-!
# Finite families of proper compactifiable covers

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space. A *proper
compactifiable cover* of `f` is a commutative diagram `Z̄ ⟵ Z ⟶ 𝒳` over `Y` with `Z ⟶ Z̄` an open
immersion of algebraic spaces and `Z̄ ⟶ Y`, `Z ⟶ 𝒳` proper; its *image* is the image of
`|Z| ⟶ |Y|`. The conclusion of [Stacks, Tag 0CQ7] for `(f, V)` is one such cover whose image
contains `|V|` (`AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover`).

The proof of [Stacks, Tag 0CQ7] repeatedly replaces `V` by finitely many pieces covering it and
takes the disjoint union of the covers found for the pieces. This file records the finite form of
the conclusion, a finite family of proper compactifiable covers whose images together contain a
given set of points of `Y`, for which that step is a union of index types. The disjoint union is
taken once, at the end of the proof of [Stacks, Tag 0CQ8].

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.CompactifiableCover`: a proper compactifiable cover
  of `f`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasCompactifiableCovers`: a finite family of them
  whose images contain a set of points of `Y`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasCompactifiableCovers.union`: the step "it suffices
  to treat the members of a finite covering".
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasCompactifiableCovers.of_proper`: the initial remark
  of the proof of [Stacks, Tag 0CQ7].
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasCompactifiableCovers.of_baseChange`: the initial
  remark along a proper surjective base change.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A proper compactifiable cover** of a 1-morphism `f : 𝒳 ⟶ Y` from an algebraic stack to an
algebraic space: algebraic spaces `Z ⊆ Z̄` (an open immersion `j`), a proper morphism
`ḡ : Z̄ ⟶ Y` and a proper 1-morphism `h : Z ⟶ 𝒳` with `h ≫ f` 2-isomorphic to `j ≫ ḡ`. -/
structure CompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) where
  /-- The compactification. -/
  Zbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The cover. -/
  Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  isAlgebraicSpace_Zbar : IsAlgebraicSpace B S hS Zbar
  isAlgebraicSpace_Z : IsAlgebraicSpace B S hS Z
  /-- The open immersion of the cover into its compactification. -/
  j : Z ⟶ Zbar
  /-- The proper morphism of the compactification to `Y`. -/
  gbar : Zbar ⟶ Y
  /-- The proper 1-morphism of the cover to `𝒳`. -/
  h : algebraicSpaceStack.{u, w} B S hS Z isAlgebraicSpace_Z ⟶ 𝒳
  isOpenImmersion_j : Space.IsOpenImmersion B S hS j
  isProper_gbar : Space.IsProper B S hS gbar
  isProper_h : IsProper B S hS h
  iso : Nonempty (h ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS isAlgebraicSpace_Z hY (j ≫ gbar))

namespace CompactifiableCover

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}

/-- The image of a proper compactifiable cover: the image of `|Z| ⟶ |Y|`. -/
def image (c : CompactifiableCover hY f) : Set (Space.points B S hS Y) :=
  Set.range (Space.pointsMap B S hS c.Z (c.j ≫ c.gbar))

/-- **The initial remark of the proof of [Stacks, Tag 0CQ7], for one cover.** A proper
compactifiable cover of `f'` gives one of `f`, along a proper morphism `p : Y' ⟶ Y` of algebraic
spaces and a proper 1-morphism `a : 𝒳' ⟶ 𝒳` with `a ≫ f` 2-isomorphic to `f' ≫ p`; its image is
the image under `p` of the image of the given cover. -/
noncomputable def pushforward {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY' : IsAlgebraicSpace B S hS Y'} {𝒳' : AlgebraicStacks.{u, w} B S hS}
    {f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY'}
    (c : CompactifiableCover hY' f') (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p) (a : 𝒳' ⟶ 𝒳)
    (ha : IsProper B S hS a)
    (e : a ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY p) :
    CompactifiableCover hY f where
  Zbar := c.Zbar
  Z := c.Z
  isAlgebraicSpace_Zbar := c.isAlgebraicSpace_Zbar
  isAlgebraicSpace_Z := c.isAlgebraicSpace_Z
  j := c.j
  gbar := c.gbar ≫ p
  h := c.h ≫ a
  isOpenImmersion_j := c.isOpenImmersion_j
  isProper_gbar := Space.isProper_comp B S hS c.isAlgebraicSpace_Zbar hY' hY c.gbar p
    c.isProper_gbar hp
  isProper_h := isProper_comp B S hS c.h a c.isProper_h ha
  iso := by
    obtain ⟨eh⟩ := c.iso
    have hcomp : algebraicSpaceStackMap.{u, w} B S hS c.isAlgebraicSpace_Z hY ((c.j ≫ c.gbar) ≫ p) =
        algebraicSpaceStackMap.{u, w} B S hS c.isAlgebraicSpace_Z hY' (c.j ≫ c.gbar) ≫
          algebraicSpaceStackMap.{u, w} B S hS hY' hY p := by
      simp only [algebraicSpaceStackMap, associatedMap_comp]
      rfl
    exact ⟨Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso c.h e ≪≫
      (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso eh _ ≪≫
      eqToIso hcomp.symm ≪≫ eqToIso (by rw [Category.assoc])⟩

/-- The image of the pushforward of a proper compactifiable cover along `p` is the image under
`p` of the image of the cover. -/
theorem image_pushforward {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY' : IsAlgebraicSpace B S hS Y'} {𝒳' : AlgebraicStacks.{u, w} B S hS}
    {f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY'}
    (c : CompactifiableCover hY' f') (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p) (a : 𝒳' ⟶ 𝒳)
    (ha : IsProper B S hS a)
    (e : a ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY p) :
    (c.pushforward p hp a ha e).image = Space.pointsMap B S hS Y' p '' c.image := by
  ext y
  simp only [image, pushforward, Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, by rw [← Space.pointsMap_comp_apply, Category.assoc]⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, by rw [← Space.pointsMap_comp_apply, Category.assoc]⟩

end CompactifiableCover

/-- **The conclusion of [Stacks, Tag 0CQ7], in finite form**: a finite family of proper
compactifiable covers of `f` whose images together contain the set `P` of points of `Y`. -/
def HasCompactifiableCovers {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (P : Set (Space.points B S hS Y)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (c : ι → CompactifiableCover hY f), P ⊆ ⋃ i, (c i).image

namespace HasCompactifiableCovers

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}

/-- The empty family covers the empty set. -/
theorem empty : HasCompactifiableCovers hY f ∅ :=
  ⟨Empty, inferInstance, Empty.elim, Set.empty_subset _⟩

/-- A family covering a set covers every subset of it. -/
theorem mono {P Q : Set (Space.points B S hS Y)} (h : HasCompactifiableCovers hY f Q)
    (hPQ : P ⊆ Q) : HasCompactifiableCovers hY f P := by
  obtain ⟨ι, hι, c, hc⟩ := h
  exact ⟨ι, hι, c, hPQ.trans hc⟩

/-- A single cover is a family. -/
theorem of_cover (c : CompactifiableCover hY f) {P : Set (Space.points B S hS Y)}
    (hP : P ⊆ c.image) : HasCompactifiableCovers hY f P :=
  ⟨Unit, inferInstance, fun _ => c, fun _ hy => Set.mem_iUnion.2 ⟨(), hP hy⟩⟩

/-- **Two families combine**: the disjoint union of the index types covers the union. -/
theorem union {P Q : Set (Space.points B S hS Y)} (hP : HasCompactifiableCovers hY f P)
    (hQ : HasCompactifiableCovers hY f Q) : HasCompactifiableCovers hY f (P ∪ Q) := by
  obtain ⟨ι, hι, c, hc⟩ := hP
  obtain ⟨κ, hκ, d, hd⟩ := hQ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c d, ?_⟩
  rw [Set.iUnion_sum]
  exact Set.union_subset_union hc hd

/-- **Finitely many families combine**: a finite union of covered sets is covered. -/
theorem iUnion {κ : Type} [Finite κ] (P : κ → Set (Space.points B S hS Y))
    (hP : ∀ k, HasCompactifiableCovers hY f (P k)) :
    HasCompactifiableCovers hY f (⋃ k, P k) := by
  choose ι hι c hc using hP
  refine ⟨Σ k, ι k, inferInstance, fun x => c x.1 x.2, ?_⟩
  rw [Set.iUnion_sigma]
  exact Set.iUnion_mono hc

/-- **Finitely many families combine**, over a finite set of indices. -/
theorem biUnion {κ : Type*} (s : Set κ) (hs : s.Finite) (P : κ → Set (Space.points B S hS Y))
    (hP : ∀ k ∈ s, HasCompactifiableCovers hY f (P k)) :
    HasCompactifiableCovers hY f (⋃ k ∈ s, P k) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using (empty : HasCompactifiableCovers hY f ∅)
  | @insert a s _ _ ih =>
    rw [Set.biUnion_insert]
    exact union (hP a (Set.mem_insert a s))
      (ih fun k hk => hP k (Set.mem_insert_of_mem a hk))

/-- **The initial remark of the proof of [Stacks, Tag 0CQ7].** Let `p : Y' ⟶ Y` be a proper
morphism of algebraic spaces and `a : 𝒳' ⟶ 𝒳` a proper 1-morphism with `a ≫ f` 2-isomorphic to
`f' ≫ p`. If a finite family of proper compactifiable covers of `f'` covers `P'`, then one of `f`
covers every set of points of `Y` contained in the image of `P'`. -/
theorem of_proper {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY' : IsAlgebraicSpace B S hS Y'}
    {𝒳' : AlgebraicStacks.{u, w} B S hS} {f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY'}
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p) (a : 𝒳' ⟶ 𝒳) (ha : IsProper B S hS a)
    (e : a ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY p)
    {P' : Set (Space.points B S hS Y')} (h : HasCompactifiableCovers hY' f' P')
    {P : Set (Space.points B S hS Y)} (hP : P ⊆ Space.pointsMap B S hS Y' p '' P') :
    HasCompactifiableCovers hY f P := by
  obtain ⟨ι, hι, c, hc⟩ := h
  refine ⟨ι, hι, fun i => (c i).pushforward p hp a ha e, fun y hy => ?_⟩
  obtain ⟨y', hy', rfl⟩ := hP hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hc hy')
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  rw [CompactifiableCover.image_pushforward]
  exact ⟨y', hi, rfl⟩

/-- **The initial remark of the proof of [Stacks, Tag 0CQ7] along a base change.** Let
`g : Y' ⟶ Y` be a proper morphism of algebraic spaces. If a finite family of proper
compactifiable covers of the base change `𝒳 ×_Y Y' ⟶ Y'` covers `P'`, then one of `f` covers
every set of points contained in the image of `P'`: the projection `𝒳 ×_Y Y' ⟶ 𝒳` is proper
(Stacks 0CL6). -/
theorem of_baseChange {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (g : Y' ⟶ Y) (hg : Space.IsProper B S hS g) {P' : Set (Space.points B S hS Y')}
    (h : HasCompactifiableCovers hY'
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f).fst P')
    {P : Set (Space.points B S hS Y)} (hP : P ⊆ Space.pointsMap B S hS Y' g '' P') :
    HasCompactifiableCovers hY f P := by
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f
  exact of_proper g hg Q.snd
    (isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f Q.swap
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare B S hS _ f))
      ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hY' hY g).2 hg))
    Q.iso.symm h hP

/-- The single-cover conclusion of [Stacks, Tag 0CQ7] is a family. -/
theorem of_hasProperCompactifiableCover {V : Subfunctor Y}
    (h : HasProperCompactifiableCover.{u, w} B S hS hY f V) :
    HasCompactifiableCovers hY f (Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) := by
  obtain ⟨Zbar, Z, hZbar, hZ, j, gbar, h, hj, hgbar, hh, eh, hcov⟩ := h
  exact of_cover ⟨Zbar, Z, hZbar, hZ, j, gbar, h, hj, hgbar, hh, eh⟩ hcov

end HasCompactifiableCovers

end AlgebraicGeometry.Stack.AlgebraicStacks

end
