module

public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# A slice point of an unramified morphism out of a smooth scheme over a field

Let `V` be a scheme smooth over a field `k` and let `φ : V ⟶ U` be a morphism of schemes locally
of finite type which is unramified at some point of `V`. Then there is a closed point `v ∈ V`
whose residue field is a finite separable extension of `k`, together with elements
`f₁, …, f_d` of the maximal ideal of `𝒪_{U, φ(v)}`, `d = dim 𝒪_{V, v}`, whose images in
`𝒪_{V, v}` generate its maximal ideal and form a regular sequence there.

This is the point-selection step in the proof of **Stacks 06N3** (a DM algebraic stack is
Deligne–Mumford): there `V` is an étale scheme chart of the fibre `F = U ×_𝒳 Spec k` of a smooth
chart `U ⟶ 𝒳` over an unramified field point, and the `fᵢ` cut out the slice
`V(f₁, …, f_d) ⊆ U` which **Stacks 06MD** makes flat over `𝒳`. The source's sentence is: pick a
closed point `v ∈ V` with `k ⊆ κ(v)` finite separable (**Stacks 056U**); `𝒪_{V, v}` is regular
(**Stacks 056S**) and `φ(𝔪_u) 𝒪_{V, v} = 𝔪_v` (**Stacks 02GF**), hence there are
`f₁, …, f_d ∈ 𝒪_{U, u}` whose images form a basis of `𝔪_v / 𝔪_v²`, and they form a regular
sequence (**Stacks 00NQ**).

## Main results

* `IsLocalRing.exists_list_map_eq_maximalIdeal`: if a ring map `φ : R → T` into a Noetherian
  local ring sends the maximal ideal of the local ring `R` onto generators of the maximal
  ideal of `T`, then a minimal generating list of `𝔪_T` can be taken from `φ(𝔪_R)`.
* `AlgebraicGeometry.exists_closedPoint_regular_slice_of_smooth_of_unramifiedAt`: the
  point-selection step of **Stacks 06N3**.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace IsLocalRing

/-- **A minimal generating list of the maximal ideal can be taken from the image of a maximal
ideal that generates it.** Let `φ : R → T` be a ring map from a local ring to a Noetherian local
ring such that `φ(𝔪_R)` generates `𝔪_T`. Then there is a list of elements of `𝔪_R`, of length
the minimal number of generators of `𝔪_T`, whose images generate `𝔪_T`. -/
theorem exists_list_map_eq_maximalIdeal {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing R]
    [IsLocalRing T] [IsNoetherianRing T] (φ : R →+* T)
    (hφ : (maximalIdeal R).map φ = maximalIdeal T) :
    ∃ xs : List R, (∀ x ∈ xs, x ∈ maximalIdeal R) ∧
      xs.length = (maximalIdeal T).spanFinrank ∧
      Ideal.ofList (xs.map φ) = maximalIdeal T := by
  classical
  have hmem : ∀ x ∈ maximalIdeal R, φ x ∈ maximalIdeal T := fun x hx =>
    hφ ▸ Ideal.mem_map_of_mem φ hx
  -- the image of `𝔪_R`, as a set of elements of `𝔪_T`
  let s : Set (maximalIdeal T) := {y | ∃ x ∈ maximalIdeal R, φ x = (y : T)}
  have hcoe : ∀ t : Set (maximalIdeal T),
      Submodule.span T t = ⊤ ↔ Ideal.span (((↑) : maximalIdeal T → T) '' t) = maximalIdeal T := by
    intro t
    rw [← Submodule.map_injective_of_injective (maximalIdeal T).injective_subtype |>.eq_iff,
      Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    rfl
  have hs : Submodule.span T s = ⊤ := by
    rw [hcoe]
    refine Eq.trans ?_ hφ
    rw [Ideal.map]
    congr 1
    ext y
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨φ x, hmem x hx⟩, ⟨x, hx, rfl⟩, rfl⟩
  rw [← CotangentSpace.span_image_eq_top_iff] at hs
  obtain ⟨b, hbs, hbspan, hbli⟩ :=
    exists_linearIndependent (ResidueField T) ((maximalIdeal T).toCotangent '' s)
  rw [hs] at hbspan
  have hbfin : b.Finite := hbli.setFinite
  -- choose an element of `𝔪_R` over each element of `b`
  have hpre : ∀ c ∈ b, ∃ x, ∃ hx : x ∈ maximalIdeal R,
      (maximalIdeal T).toCotangent ⟨φ x, hmem x hx⟩ = c := by
    intro c hc
    obtain ⟨y, ⟨x, hx, hxy⟩, rfl⟩ := hbs hc
    exact ⟨x, hx, congrArg _ (Subtype.ext hxy)⟩
  choose! pre hpreR hpreC using hpre
  let bs : Finset (CotangentSpace T) := hbfin.toFinset
  have hbs' : (bs : Set (CotangentSpace T)) = b := hbfin.coe_toFinset
  let xs : List R := bs.toList.map pre
  refine ⟨xs, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact hpreR c (hbfin.mem_toFinset.1 (Finset.mem_toList.1 hc))
  · have hli : LinearIndependent (ResidueField T) ((↑) : bs → CotangentSpace T) := by
      rwa [← hbs'] at hbli
    have := finrank_span_finset_eq_card hli
    rw [hbs', hbspan, finrank_top] at this
    rw [List.length_map, Finset.length_toList, ← this,
      spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  · -- the chosen elements, as elements of `𝔪_T`, still span the cotangent space
    let t : Set (maximalIdeal T) :=
      {y | ∃ c ∈ b, ∃ h : c ∈ b, y = ⟨φ (pre c), hmem _ (hpreR c h)⟩}
    have ht : (maximalIdeal T).toCotangent '' t = b := by
      ext c
      constructor
      · rintro ⟨y, ⟨d, hd, -, rfl⟩, rfl⟩
        rwa [hpreC d hd]
      · exact fun hc => ⟨_, ⟨c, hc, hc, rfl⟩, hpreC c hc⟩
    have htop : Submodule.span T t = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ht, hbspan]
    rw [hcoe] at htop
    rw [← htop, Ideal.ofList]
    congr 1
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      have hc' := hbfin.mem_toFinset.1 (Finset.mem_toList.1 hc)
      exact ⟨_, ⟨c, hc', hc', rfl⟩, rfl⟩
    · rintro ⟨_, ⟨c, hc, -, rfl⟩, rfl⟩
      exact List.mem_map.2 ⟨pre c, List.mem_map.2
        ⟨c, Finset.mem_toList.2 (hbfin.mem_toFinset.2 hc), rfl⟩, rfl⟩

end IsLocalRing

namespace AlgebraicGeometry

/-- **The point-selection step of Stacks 06N3.** Let `V` be a scheme smooth over a field `k` and
let `φ : V ⟶ U` be a morphism of schemes locally of finite type which is unramified at some
point of `V`. Then there is a closed point `v ∈ V` whose residue field is a finite separable
extension of `k`, and a list `f₁, …, f_d` of elements of the maximal ideal of `𝒪_{U, φ(v)}`,
of length `d = dim 𝒪_{V, v}`, whose images in `𝒪_{V, v}` generate the maximal ideal and form a
regular sequence. -/
theorem exists_closedPoint_regular_slice_of_smooth_of_unramifiedAt
    {k : Type u} [Field k] {V U : Scheme.{u}} (g : V ⟶ Spec (.of k)) [Smooth g]
    (φ : V ⟶ U) [LocallyOfFiniteType φ] (v₀ : V) (hv₀ : UnramifiedAt φ v₀) :
    ∃ v : V, v ∈ closedPoints V ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ V.Γevaluation v).hom.toAlgebra;
        Module.Finite k (V.residueField v) ∧ Algebra.IsSeparable k (V.residueField v)) ∧
      ∃ xs : List (U.presheaf.stalk (φ v)),
        (∀ x ∈ xs, x ∈ maximalIdeal (U.presheaf.stalk (φ v))) ∧
        (xs.length : WithBot ℕ∞) = ringKrullDim (V.presheaf.stalk v) ∧
        Ideal.ofList (xs.map (φ.stalkMap v).hom) = maximalIdeal (V.presheaf.stalk v) ∧
        RingTheory.Sequence.IsRegular (V.presheaf.stalk v) (xs.map (φ.stalkMap v).hom) := by
  -- a closed point with separable residue field inside the open unramified locus
  obtain ⟨v, hvU, hvc, hvsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth g).inter_open_nonempty
      {x : V | UnramifiedAt φ x} (isOpen_setOf_unramifiedAt φ) ⟨v₀, hv₀⟩
  refine ⟨v, hvc, hvsep, ?_⟩
  have hreg : IsRegularLocalRing (V.presheaf.stalk v) :=
    (isRegular_of_smooth_over_field g).isRegularLocalRing_stalk v
  have h17 := (unramifiedAt_tfae φ v).out 1 7
  have hmap := (h17.1 hvU).1
  obtain ⟨xs, hxs, hlen, hgen⟩ := IsLocalRing.exists_list_map_eq_maximalIdeal
    (R := U.presheaf.stalk (φ v)) (T := V.presheaf.stalk v) (φ.stalkMap v).hom hmap
  have hlen' : (xs.map (φ.stalkMap v).hom).length =
      (maximalIdeal (V.presheaf.stalk v)).spanFinrank := by
    rw [List.length_map, hlen]
  refine ⟨xs, hxs, ?_, hgen, ?_⟩
  · rw [hlen, IsRegularLocalRing.spanFinrank_maximalIdeal]
  · exact ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      _).1 _ hgen hlen').1

end AlgebraicGeometry

end
