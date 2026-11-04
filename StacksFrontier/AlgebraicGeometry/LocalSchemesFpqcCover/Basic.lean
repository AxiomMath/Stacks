module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.Basic

/-!
# The complement of finitely many closed points together with their local schemes is an fpqc cover

Let `S` be a scheme and let `s : I → S` be a finite family of closed points.  Write
`U = S \ {s i | i}` for the open complement and `S_i = Spec 𝒪_{S, s i}` for the local scheme at
`s i`.  This file shows that the family consisting of the open immersion `U ⟶ S` and the
canonical morphisms `S_i ⟶ S` is a covering family for the fpqc topology, provided `U ⟶ S` is
quasi-compact.

## Main results

* `AlgebraicGeometry.instFlatFromSpecStalk`: the canonical morphism `Spec 𝒪_{S, x} ⟶ S` is flat,
  as an instance.
* `AlgebraicGeometry.LocalSchemesCover.exists_mem_range`: the family is jointly surjective.
* `AlgebraicGeometry.LocalSchemesCover.flatCover`: the family, as a covering family for the flat
  precoverage.
* `AlgebraicGeometry.LocalSchemesCover.quasiCompactCover`: the family is a quasi-compact cover.
* `AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`: the family is a covering
  family for the fpqc topology.
* `AlgebraicGeometry.LocalSchemesCover.hom_ext`: a morphism out of `S` is determined by its
  restrictions to `U` and to the local schemes.
* `AlgebraicGeometry.LocalSchemesCover.range_inter_range_subset`: for `i ≠ j` the overlap of the
  images of `S_i` and `S_j` lies in `U`.

## Implementation notes

The index type of the family is `Option I`, with `none` naming the open complement and `some i`
naming the local scheme at `s i`.

Quasi-compactness of the covering family is *not* quasi-compactness of each of its members: the
morphism `Spec 𝒪_{S, x} ⟶ S` need not be quasi-compact when `S` is not quasi-separated, since the
preimage of an affine open need not be a quasi-compact open of the spectrum of the local ring.
The condition that the fpqc topology actually asks for is the weaker one of
`AlgebraicGeometry.QuasiCompactCover`: every affine open of `S` is a finite union of images of
quasi-compact opens of the members.  That holds here, and the proof uses the whole of each `S_i`,
which is quasi-compact because it is affine.

The key point for the local members is that if an open `V` contains `s i` then it contains every
point specializing to `s i`, so the image of the whole of `S_i` is already inside `V`.  The same
observation, applied to the closed points themselves, is what makes the overlap of two distinct
local schemes land in the open complement: a point specializing to both `s i` and `s j` cannot be
any of the closed points of the family unless `i = j`.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 022B](https://stacks.math.columbia.edu/tag/022B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The canonical morphism `Spec 𝒪_{X, x} ⟶ X` is flat, available to instance search. -/
instance instFlatFromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) :=
  flat_fromSpecStalk X x

/-- If an open subset contains `x`, then it contains every point specializing to `x`. -/
theorem mem_of_specializes_of_isOpen {X : Scheme.{u}} {V : Set X} (hV : IsOpen V) {x y : X}
    (hx : x ∈ V) (hy : y ⤳ x) : y ∈ V :=
  hy.mem_open hV hx

namespace LocalSchemesCover

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- The members of the covering family: the open complement of the family of closed points for
`none`, and the local scheme at `s i` for `some i`. -/
noncomputable def obj : Option I → Scheme.{u}
  | none => (complementOfClosedPoints s hs).toScheme
  | some i => Spec (S.presheaf.stalk (s i))

/-- The morphisms of the covering family: the open immersion of the complement for `none`, and
the canonical morphism from the local scheme for `some i`. -/
noncomputable def map : (a : Option I) → obj s hs a ⟶ S
  | none => (complementOfClosedPoints s hs).ι
  | some i => S.fromSpecStalk (s i)

/-- Every member of the covering family is flat over `S`. -/
instance (a : Option I) : Flat (map s hs a) := by
  cases a with
  | none => exact inferInstanceAs (Flat (complementOfClosedPoints s hs).ι)
  | some i => exact inferInstanceAs (Flat (S.fromSpecStalk (s i)))

/-- The local scheme at `s i` is quasi-compact. -/
instance (i : I) : CompactSpace (obj s hs (some i)) :=
  inferInstanceAs (CompactSpace (Spec (S.presheaf.stalk (s i))))

/-- The image of the open complement is the open complement. -/
theorem range_map_none :
    Set.range (map s hs none) = (complementOfClosedPoints s hs : Set S) :=
  (complementOfClosedPoints s hs).range_ι

/-- The image of the local scheme at `s i` is the set of points specializing to `s i`. -/
theorem range_map_some (i : I) :
    Set.range (map s hs (some i)) = { y | y ⤳ s i } :=
  Scheme.range_fromSpecStalk

/-- Every point of the local scheme at `s i` maps to a point specializing to `s i`. -/
theorem specializes_map_some (i : I) (z : obj s hs (some i)) :
    (map s hs (some i)) z ⤳ s i :=
  (Scheme.range_fromSpecStalk (x := s i)).le ⟨z, rfl⟩

/-- Membership in the open complement, unfolded. -/
theorem mem_complementOfClosedPoints_iff {y : S} :
    y ∈ (complementOfClosedPoints s hs : Set S) ↔ ∀ i, y ≠ s i := by
  simp [complementOfClosedPoints, Set.mem_iInter]

/-- A point avoiding every `s i` is in the image of the open complement. -/
private theorem mem_range_map_none {y : S} (h : ∀ i, y ≠ s i) : y ∈ Set.range (map s hs none) := by
  rw [range_map_none]; exact (mem_complementOfClosedPoints_iff s hs).mpr h

/-- The point `s i` is in the image of the local scheme at `s i`. -/
private theorem mem_range_map_some {y : S} {i : I} (h : y = s i) :
    y ∈ Set.range (map s hs (some i)) := by
  rw [range_map_some]; exact specializes_of_eq h

/-- The covering family is jointly surjective: a point of `S` either avoids every `s i`, and so
lies in the open complement, or equals some `s i`, and so is the image of the closed point of the
corresponding local scheme. -/
theorem exists_mem_range (y : S) : ∃ a, y ∈ Set.range (map s hs a) := by
  by_cases h : ∀ i, y ≠ s i
  · exact ⟨none, mem_range_map_none s hs h⟩
  · obtain ⟨i, hi⟩ := not_forall.mp h
    exact ⟨some i, mem_range_map_some s hs (not_not.mp hi)⟩

omit [Finite I] in
include hs in
/-- A closed point of the family that specializes to `s i` *is* `s i`. -/
theorem eq_of_specializes {i k : I} (h : s k ⤳ s i) : s i = s k := by
  have := h.mem_closure
  rwa [(mem_closedPoints_iff.mp (hs k)).closure_eq, Set.mem_singleton_iff] at this

/-- A point specializing to both `s i` and `s j`, for two *distinct* points of the family, lies in
the open complement: it cannot be any `s k`, since `s k ⤳ s i` forces `s i = s k` for the closed
point `s k`, and the same for `s j`. -/
theorem specializes_mem_complement {y : S} {i j : I} (hij : s i ≠ s j) (hi : y ⤳ s i)
    (hj : y ⤳ s j) : y ∈ (complementOfClosedPoints s hs : Set S) := by
  refine (mem_complementOfClosedPoints_iff s hs).mpr fun k hk ↦ ?_
  subst hk
  exact hij ((eq_of_specializes s hs hi).trans (eq_of_specializes s hs hj).symm)

/-- For `i ≠ j` in an injectively indexed family, the overlap of the images of the two local
schemes `S_i` and `S_j` is contained in the open complement `U`.  This is why compatibility of
gluing data over the punctured local schemes `U_i` already controls every pairwise overlap of the
covering family. -/
theorem range_inter_range_subset (hinj : Function.Injective s) {i j : I} (hij : i ≠ j) :
    Set.range (map s hs (some i)) ∩ Set.range (map s hs (some j)) ⊆
      (complementOfClosedPoints s hs : Set S) := by
  rw [range_map_some, range_map_some]
  exact fun y ⟨hi, hj⟩ ↦ specializes_mem_complement s hs (fun h ↦ hij (hinj h)) hi hj

/-! ### The family is an fpqc covering family -/

/-- The quasi-compact opens that cover an affine open `W`: the preimage of `W` in the open
complement, and the whole of the local scheme at each point of the family lying in `W`. -/
noncomputable def coverOpens (W : S.Opens) :
    (k : Option { i // s i ∈ (W : Set S) }) → (obj s hs (k.map Subtype.val)).Opens
  | none => (map s hs none) ⁻¹ᵁ W
  | some _ => ⊤

include hs in
/-- The image of the chosen quasi-compact opens is exactly `W`.  Over the open complement the
image is `W ∩ U`; over the local scheme at a point `s i ∈ W` the image is the whole set of points
specializing to `s i`, which is contained in `W` because `W` is open and contains `s i`. -/
theorem iUnion_image_coverOpens (W : S.Opens) :
    ⋃ k, (map s hs (k.map Subtype.val)) '' (coverOpens s hs W k : Set _) = (W : Set S) := by
  apply Set.eq_of_subset_of_subset
  · refine Set.iUnion_subset fun k ↦ ?_
    cases k with
    | none =>
      rintro y ⟨z, hz, rfl⟩
      exact hz
    | some i =>
      rintro y ⟨z, -, rfl⟩
      exact mem_of_specializes_of_isOpen W.2 i.2 (specializes_map_some s hs i.1 z)
  · intro y hy
    by_cases h : ∀ i, y ≠ s i
    · refine Set.mem_iUnion.mpr ⟨none, ?_⟩
      obtain ⟨z, rfl⟩ := mem_range_map_none s hs h
      exact ⟨z, hy, rfl⟩
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hyi : y = s i := not_not.mp hi
      refine Set.mem_iUnion.mpr ⟨some ⟨i, hyi ▸ hy⟩, ?_⟩
      obtain ⟨z, rfl⟩ := mem_range_map_some s hs hyi
      exact ⟨z, trivial, rfl⟩

variable (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)

include hs hqc in
/-- Every affine open of `S` is a finite union of images of quasi-compact opens of the members of
the family.  This is the quasi-compactness condition the fpqc topology asks of a covering family;
note that it is *weaker* than quasi-compactness of each member. -/
theorem isCompactOpenCovered (W : S.Opens) (hW : IsAffineOpen W) :
    IsCompactOpenCovered (fun a ↦ (map s hs a).base) (W : Set S) := by
  refine IsCompactOpenCovered.of_finite
    (fun k : Option { i // s i ∈ (W : Set S) } ↦ k.map Subtype.val) (coverOpens s hs W)
    (fun k ↦ ?_) (iUnion_image_coverOpens s hs W)
  cases k with
  | none =>
    have : QuasiCompact (map s hs none) := hqc
    exact (map s hs none).isCompact_preimage hW.isCompact
  | some i =>
    change IsCompact (Set.univ : Set (obj s hs (some i.1)))
    exact CompactSpace.isCompact_univ

/-- The family as a covering family of `S` for the flat precoverage: the members are flat, being
an open immersion and canonical morphisms from spectra of local rings, and they are jointly
surjective. -/
@[simps! I₀ X f]
noncomputable def flatCover : Scheme.Cover.{u} (Scheme.precoverage @Flat) S where
  I₀ := Option I
  X := obj s hs
  f := map s hs
  mem₀ := (Scheme.presieve₀_mem_precoverage_iff _).mpr
    ⟨fun y ↦ exists_mem_range s hs y, fun _ ↦ inferInstance⟩

include hs hqc in
/-- The family is a quasi-compact cover in the sense of [Stacks, Tag 022B]. -/
theorem quasiCompactCover : QuasiCompactCover (flatCover s hs).toPreZeroHypercover :=
  ⟨fun hW ↦ isCompactOpenCovered s hs hqc _ hW⟩

include hs hqc in
/-- **The complement of a finite family of closed points, together with the local schemes at
those points, is an fpqc covering family of the ambient scheme.**  The members are flat — an open
immersion and the canonical morphisms from spectra of local rings — they are jointly surjective,
and the family is quasi-compact because the open complement is. -/
theorem presieve₀_mem_fpqcPrecoverage :
    (flatCover s hs).presieve₀ ∈ Scheme.fpqcPrecoverage S :=
  ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr (quasiCompactCover s hs hqc),
    (flatCover s hs).mem₀⟩

include hs hqc in
/-- **A morphism out of `S` is determined by its restrictions to the open complement and to the
local schemes at the points of the family.**  This is the faithfulness half of fpqc descent of
morphisms for the covering family, and it is the content that [Stacks, Tag 0E8Q] leaves to the
reader when it omits the proof of full faithfulness. -/
theorem hom_ext {Y : Scheme.{u}} (f g : S ⟶ Y)
    (h : ∀ a, map s hs a ≫ f = map s hs a ≫ g) : f = g := by
  have hsf : Presieve.IsSheafFor (yoneda.obj Y) (flatCover s hs).presieve₀ :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck (presieve₀_mem_fpqcPrecoverage s hs hqc))
  refine hsf.isSeparatedFor.ext ?_
  rintro Z p ⟨a⟩
  exact h a

end LocalSchemesCover

end AlgebraicGeometry

end
