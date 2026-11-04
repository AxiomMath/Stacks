module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.Devissage
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.TamePullback

/-!
# The fibrewise properties along a tower

Let `(S, δ)` be the base situation of chapter 42, let `q : E ⟶ B` be an affine-space bundle of
rank `m` and `p : B ⟶ V` one of rank `1`. The composite `q ≫ p` has fibres of dimension `m + 1`,
the fibre over `x` being fibred by `q` over the fibre `p⁻¹(x)`, which consists of its generic
point `ζ` and of the points of relative dimension `δ(x)`. This file derives the two fibrewise
properties `Stacks.Chow.FibreBoundaryLift` and `Stacks.Chow.FibreUnitDescent` of `q ≫ p` from
those of `q` and `p`, given that the tame-symbol differential commutes, along the fibre over
`x`, with pulling back along `q` (an input in which the local rings of `closure {ζ}` at the
points of `p⁻¹(x)` are discrete valuation rings), which is
`Stacks.Chow.milnorChainRestrict_pointwiseMilnorBoundary_bundleChainPullback`.

This is the induction step of the computation of the first higher Chow groups of Stacks 0GUA of
affine space over a field, `𝔸^{m+1} = 𝔸^m × 𝔸^1`: a chain on the fibre over `x` is first
cut down along the fibres of `q`, and what is left is the pullback of a chain on `p⁻¹(x)`,
which is handled by the property of `p`.

## Main results

* `Stacks.Chow.fibreBoundaryLift_comp`
* `Stacks.Chow.fibreUnitDescent_comp`

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- Transport of Milnor K-theory along the residue field map of a composite. -/
theorem exists_milnorKTransport_residueFieldMap_comp {E B V : Scheme.{u}} (q : E ⟶ B)
    (p : B ⟶ V) (ξ : E) {n : ℕ} (c : MilnorKTheory (V.residueField (p.base (q.base ξ))) n) :
    ∃ c' : MilnorKTheory (V.residueField ((q ≫ p).base ξ)) n,
      milnorKTransport ((q ≫ p).residueFieldMap ξ).hom n c' =
        milnorKTransport (q.residueFieldMap ξ).hom n
          (milnorKTransport (p.residueFieldMap (q.base ξ)).hom n c) :=
  ⟨c, by
    rw [milnorKTransport_comp_apply, Scheme.residueFieldMap_comp]
    rfl⟩

variable (C : ChowSituation.{u}) {E B V : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (q : E ⟶ B) (p : B ⟶ V) (hq : q ≫ sB = sE) (hp : p ≫ sV = sB) {m : ℕ}
  (hbq : IsAffineSpaceBundle q m) (hbp : IsAffineSpaceBundle p 1)

/-! ### Bookkeeping -/

omit [LocallyOfFiniteType sE] in
/-- On the fibre of `q` over a point `z` above `x`, restricting first to the fibre of `q ≫ p`
over `x` changes nothing. -/
theorem fibreRestrict_fibreRestrict_comp [LocallyOfFiniteType sE] {z : B} {x : V}
    (hz : p.base z = x) {j : ℤ} {n : ℕ} (c : MilnorChainGroup C sE j n) :
    fibreRestrict C sE q z j n (fibreRestrict C sE (q ≫ p) x j n c) =
      fibreRestrict C sE q z j n c := by
  have hset : q.base ⁻¹' {z} ∩ (q ≫ p).base ⁻¹' {x} = q.base ⁻¹' {z} := by
    refine Set.inter_eq_left.mpr fun w hw ↦ ?_
    show p.base (q.base w) = x
    rw [show q.base w = z from hw, hz]
  rw [fibreRestrict, fibreRestrict, milnorChainRestrict_milnorChainRestrict, hset]

omit [LocallyOfFiniteType sE] in
/-- Two chains supported on the fibre of `q ≫ p` over `x` are equal as soon as they agree on the
fibres of `q` over the points above `x`. -/
theorem eq_of_forall_fibreRestrict_eq [LocallyOfFiniteType sE] {x : V} {j : ℤ} {n : ℕ}
    {a b : MilnorChainGroup C sE j n}
    (ha : fibreRestrict C sE (q ≫ p) x j n a = a) (hb : fibreRestrict C sE (q ≫ p) x j n b = b)
    (h : ∀ z : B, p.base z = x → fibreRestrict C sE q z j n a = fibreRestrict C sE q z j n b) :
    a = b := by
  refine Subtype.ext (funext fun w ↦ ?_)
  by_cases hw : p.base (q.base w.1) = x
  · simpa [milnorChainRestrict_apply_of_mem (T := q.base ⁻¹' {q.base w.1}) _
      (show w.1 ∈ q.base ⁻¹' {q.base w.1} from rfl)] using
      congrArg (fun c : MilnorChainGroup C sE j n ↦ c.1 w) (h _ hw)
  · have h1 := congrArg (fun c : MilnorChainGroup C sE j n ↦ c.1 w) ha
    have h2 := congrArg (fun c : MilnorChainGroup C sE j n ↦ c.1 w) hb
    rw [milnorChainRestrict_apply_of_notMem _ (show w.1 ∉ (q ≫ p).base ⁻¹' {x} from hw)] at h1 h2
    rw [← h1, ← h2]

include hp hbp in
/-- **The fibre of a line bundle-like map.** A point of the fibre of `p` over `x` is either the
generic point `ζ` of that fibre, of relative dimension `δ(x) + 1`, or of relative dimension
`δ(x)`. -/
theorem eq_or_relativeDimension_eq_of_fibre {ζ z : B} {x : V} (hζ : p.base ζ = x)
    (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1) (hz : p.base z = x) :
    z = ζ ∨ relativeDimension C.dimensionFunction sB z =
      relativeDimension C.dimensionFunction sV x := by
  have h1 := relativeDimension_le_add_of_isAffineSpaceBundle C sB sV p hp hbp z
  have h2 := relativeDimension_le_of_isAffineSpaceBundle C sB sV p hp hbp z
  rw [hz] at h1 h2
  refine or_iff_not_imp_right.mpr fun h ↦ ?_
  refine eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sB sV p hp hbp
    (hz.trans hζ.symm) ?_ ?_
  · rw [hz]
    push_cast
    omega
  · rw [hζ, hζdim]
    push_cast
    ring

section General

variable {E V : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (g : E ⟶ V)

omit [LocallyOfFiniteType sE] in
/-- A point carrying a chain supported on the fibre of `g` over `x` lies over `x`. -/
private theorem base_eq_of_fibreRestrict_eq_self {x : V} {j : ℤ} {n : ℕ}
    {c : MilnorChainGroup C sE j n}
    (hc : fibreRestrict C sE g x j n c = c) {ξ : pointsOfDimension C sE j} (hξ : c.1 ξ ≠ 0) :
    g.base ξ.1 = x := by
  rw [← hc] at hξ
  by_contra h
  exact hξ (milnorChainRestrict_apply_of_notMem _ h)

/-- **On a fibre, the divisor of the fibrewise part of a chain.** If a K₁-chain `c` has no
divisor on the fibre of `g` over `x`, and no point carrying `c` off that fibre specializes into
it, then the part of `c` on the fibre has no divisor on the fibre either. -/
theorem fibreRestrict_divisor_fibreRestrict_eq_zero {x : V} (k : ℤ)
    (c : PointwiseKOneGroup C sE k)
    (hc : fibreRestrict C sE g x k 0 (pointwiseDivisorDifferential C sE k c) = 0)
    (hsp : ∀ ξ : pointsOfDimension C sE (k + 1), c.1 ξ ≠ 0 → g.base ξ.1 ≠ x →
      ∀ y : E, g.base y = x → ¬ (ξ.1 ⤳ y)) :
    fibreRestrict C sE g x k 0 (pointwiseDivisorDifferential C sE k
      (fibreRestrict C sE g x (k + 1) 1 c)) = 0 := by
  have hrest : fibreRestrict C sE g x k 0 (pointwiseDivisorDifferential C sE k
      (c - fibreRestrict C sE g x (k + 1) 1 c)) = 0 := by
    refine milnorChainRestrict_pointwiseDivisorDifferential_eq_zero k _ fun ξ hξ y hy ↦ ?_
    have hval : (c - fibreRestrict C sE g x (k + 1) 1 c).1 ξ =
        c.1 ξ - (fibreRestrict C sE g x (k + 1) 1 c).1 ξ := rfl
    have hgξ : g.base ξ.1 ≠ x := by
      intro h
      rw [hval, milnorChainRestrict_apply_of_mem _ (show ξ.1 ∈ g.base ⁻¹' {x} from h),
        sub_self] at hξ
      exact hξ rfl
    refine hsp ξ (fun h0 ↦ ?_) hgξ y hy
    rw [hval, h0, milnorChainRestrict_apply_of_notMem _
      (show ξ.1 ∉ g.base ⁻¹' {x} from hgξ), sub_zero] at hξ
    exact hξ rfl
  have hsub := congrArg (fibreRestrict C sE g x k 0)
    (congrArg (pointwiseDivisorDifferential C sE k)
      (sub_add_cancel c (fibreRestrict C sE g x (k + 1) 1 c)))
  rwa [map_add, map_add, hrest, zero_add, hc] at hsub

/-- **On a fibre, the divisor of the fibrewise part of a boundary vanishes.** If `η` is supported
on the fibre of `g` over `x`, the divisor of the part on that fibre of the tame-symbol boundary of
`η` has no component on the fibre: the boundary has divisor zero, and its part off the fibre lies
over proper specializations of `x`. -/
theorem fibreRestrict_divisor_fibreRestrict_boundary {x : V} (k : ℤ)
    (η : PointwiseKTwoGroup C sE k) (hη : fibreRestrict C sE g x (k + 2) 2 η = η) :
    fibreRestrict C sE g x k 0 (pointwiseDivisorDifferential C sE k
      (fibreRestrict C sE g x (k + 1) 1 (pointwiseMilnorBoundary C sE k η))) = 0 := by
  refine fibreRestrict_divisor_fibreRestrict_eq_zero C sE g k _
    (by rw [pointwiseDivisorDifferential_pointwiseMilnorBoundary, map_zero]) ?_
  intro ξ hξ hgξ y hy hspec
  obtain ⟨w, hw, hws⟩ := exists_specializes_of_pointwiseMilnorBoundary_apply_ne_zero k η hξ
  have h1 : x ⤳ g.base ξ.1 := by
    rw [← base_eq_of_fibreRestrict_eq_self C sE g hη hw]
    exact hws.map g.continuous
  have h2 : g.base ξ.1 ⤳ x := hy ▸ hspec.map g.continuous
  exact hgξ (h2.antisymm h1).eq

omit [LocallyOfFiniteType sE] in
/-- Over a compact open `W`, only finitely many fibres of a quasi-compact `g` carry a part of a
given chain. -/
theorem finite_setOf_fibreRestrict_ne_zero [QuasiCompact g] {j : ℤ} {n : ℕ}
    (a : MilnorChainGroup C sE j n) (W : V.Opens) (hW : IsCompact (W : Set V)) :
    {z : V | z ∈ W ∧ fibreRestrict C sE g z j n a ≠ 0}.Finite := by
  obtain ⟨U, hU, hWU⟩ := exists_isCompact_opens_superset
    (QuasiCompact.isCompact_preimage (f := g) _ W.2 hW)
  refine ((a.2 U hU).image fun ξ : pointsOfDimension C sE j ↦ g.base ξ.1).subset ?_
  rintro z ⟨hzW, hz⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ, (fibreRestrict C sE g z j n a).1 ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hz (Subtype.ext (funext hall))
  have hξz : g.base ξ.1 = z := by
    by_contra hne
    exact hξ (milnorChainRestrict_apply_of_notMem _ (show ξ.1 ∉ g.base ⁻¹' {z} from hne))
  refine ⟨ξ, ⟨hWU (show ξ.1 ∈ g.base ⁻¹' (W : Set V) by
    rwa [Set.mem_preimage, hξz]), fun h0 ↦ hξ ?_⟩, hξz⟩
  rw [milnorChainRestrict_apply_of_mem _ (show ξ.1 ∈ g.base ⁻¹' {z} from hξz), h0]

end General

/-! ### The generic point of the fibre of `p` -/

include hp hbp in
/-- **The first step along a tower: the part of a chain over the generic point of `p⁻¹(x)`.**
For a K₁-chain `a` supported on the fibre of `q ≫ p` over `x`, with no divisor on that fibre,
there is a K₂-chain `η₁` on the same fibre such that `a` minus the fibrewise part of the boundary
of `η₁` vanishes over the generic point `ζ` of `p⁻¹(x)`, while keeping the two properties. -/
theorem exists_fibreRestrict_comp_generic (k : ℤ)
    (hLq : ∀ z : B, FibreBoundaryLift C sE sB q m k z) {x : V} {ζ : B} (hζ : p.base ζ = x)
    (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    (hζk : relativeDimension C.dimensionFunction sB ζ ≠ k + 1 - m)
    (a : PointwiseKOneGroup C sE k) (ha : fibreRestrict C sE (q ≫ p) x (k + 1) 1 a = a)
    (hdiv : fibreRestrict C sE (q ≫ p) x k 0 (pointwiseDivisorDifferential C sE k a) = 0) :
    ∃ η₁ : PointwiseKTwoGroup C sE k, fibreRestrict C sE (q ≫ p) x (k + 2) 2 η₁ = η₁ ∧
      fibreRestrict C sE (q ≫ p) x (k + 1) 1
          (a - fibreRestrict C sE (q ≫ p) x (k + 1) 1 (pointwiseMilnorBoundary C sE k η₁)) =
        a - fibreRestrict C sE (q ≫ p) x (k + 1) 1 (pointwiseMilnorBoundary C sE k η₁) ∧
      fibreRestrict C sE q ζ (k + 1) 1
          (a - fibreRestrict C sE (q ≫ p) x (k + 1) 1 (pointwiseMilnorBoundary C sE k η₁)) = 0 ∧
      fibreRestrict C sE (q ≫ p) x k 0 (pointwiseDivisorDifferential C sE k
          (a - fibreRestrict C sE (q ≫ p) x (k + 1) 1
            (pointwiseMilnorBoundary C sE k η₁))) = 0 := by
  have hqfib : ∀ w : E, q.base w = ζ → p.base (q.base w) = x := fun w hw ↦ by rw [hw, hζ]
  have hdivζ : fibreRestrict C sE q ζ k 0 (pointwiseDivisorDifferential C sE k
      (fibreRestrict C sE q ζ (k + 1) 1 a)) = 0 := by
    refine fibreRestrict_divisor_fibreRestrict_eq_zero C sE q k a
      (by rw [← fibreRestrict_fibreRestrict_comp C sE q p hζ, hdiv, map_zero]) ?_
    intro ξ haξ hqξ y hy hspec
    have hsp : q.base ξ.1 ⤳ ζ := hy ▸ hspec.map q.continuous
    have hpx : p.base (q.base ξ.1) = x := base_eq_of_fibreRestrict_eq_self C sE (q ≫ p) ha haξ
    have h₁ := relativeDimension_le_of_specializes C sB hsp
    have h₂ := (eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim hpx).resolve_left hqξ
    omega
  obtain ⟨η₁, hη₁sup, hη₁⟩ := hLq ζ hζk (fibreRestrict C sE q ζ (k + 1) 1 a)
    (by rw [milnorChainRestrict_milnorChainRestrict, Set.inter_self]) hdivζ
  have hη₁x : fibreRestrict C sE (q ≫ p) x (k + 2) 2 η₁ = η₁ := by
    have hset : (q ≫ p).base ⁻¹' {x} ∩ q.base ⁻¹' {ζ} = q.base ⁻¹' {ζ} :=
      Set.inter_eq_right.mpr fun w hw ↦ hqfib w hw
    rw [← hη₁sup, fibreRestrict, fibreRestrict, milnorChainRestrict_milnorChainRestrict, hset]
  refine ⟨η₁, hη₁x, ?_, ?_, ?_⟩
  · rw [map_sub, ha, fibreRestrict, milnorChainRestrict_milnorChainRestrict, Set.inter_self]
  · rw [map_sub, fibreRestrict_fibreRestrict_comp C sE q p hζ, hη₁, sub_self]
  · rw [map_sub, map_sub, hdiv, fibreRestrict_divisor_fibreRestrict_boundary C sE (q ≫ p) k η₁
      hη₁x, sub_zero]

/-! ### The closed points of the fibre of `p` -/

omit [LocallyOfFiniteType sE] in
include hp hbp in
/-- A point carrying a K₁-chain on the fibre of `q ≫ p` over `x` that vanishes over the generic
point `ζ` of `p⁻¹(x)` lies over a point of `p⁻¹(x)` other than `ζ`, of relative dimension
`δ(x)`. -/
theorem relativeDimension_base_eq_of_apply_ne_zero {k : ℤ} {x : V} {ζ : B} (hζ : p.base ζ = x)
    (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    {a : PointwiseKOneGroup C sE k} (ha : fibreRestrict C sE (q ≫ p) x (k + 1) 1 a = a)
    (haζ : fibreRestrict C sE q ζ (k + 1) 1 a = 0) {ξ : pointsOfDimension C sE (k + 1)}
    (hξ : a.1 ξ ≠ 0) :
    p.base (q.base ξ.1) = x ∧ q.base ξ.1 ≠ ζ ∧
      relativeDimension C.dimensionFunction sB (q.base ξ.1) =
        relativeDimension C.dimensionFunction sV x := by
  have hpx : p.base (q.base ξ.1) = x := base_eq_of_fibreRestrict_eq_self C sE (q ≫ p) ha hξ
  have hqζ : q.base ξ.1 ≠ ζ := by
    intro h
    have := congrArg (fun c : PointwiseKOneGroup C sE k ↦ c.1 ξ) haζ
    rw [milnorChainRestrict_apply_of_mem _ (show ξ.1 ∈ q.base ⁻¹' {ζ} from h)] at this
    exact hξ this
  exact ⟨hpx, hqζ,
    (eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim hpx).resolve_left hqζ⟩

include hp hbp in
/-- **The boundary-lifting property at a closed point of `p⁻¹(x)`.** For a K₁-chain `a` on the
fibre of `q ≫ p` over `x`, vanishing over the generic point `ζ` of `p⁻¹(x)` and with no divisor
on the fibre, the part of `a` over a point `z ≠ ζ` of `p⁻¹(x)` is the fibrewise part of a
boundary, provided `δ(x) ≠ k + 1 - m`. -/
theorem exists_fibreRestrict_boundary_eq_of_ne (k : ℤ)
    (hLq : ∀ z : B, FibreBoundaryLift C sE sB q m k z) {x : V} {ζ : B} (hζ : p.base ζ = x)
    (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    (hxk : relativeDimension C.dimensionFunction sV x ≠ k + 1 - m)
    (a : PointwiseKOneGroup C sE k) (ha : fibreRestrict C sE (q ≫ p) x (k + 1) 1 a = a)
    (haζ : fibreRestrict C sE q ζ (k + 1) 1 a = 0)
    (hdiv : fibreRestrict C sE (q ≫ p) x k 0 (pointwiseDivisorDifferential C sE k a) = 0)
    (z : B) (hz : p.base z = x) (hzζ : z ≠ ζ) :
    ∃ η : PointwiseKTwoGroup C sE k, fibreRestrict C sE q z (k + 2) 2 η = η ∧
      fibreRestrict C sE q z (k + 1) 1 (pointwiseMilnorBoundary C sE k η) =
        fibreRestrict C sE q z (k + 1) 1 a := by
  have hzdim :=
    (eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim hz).resolve_left hzζ
  refine hLq z (by rwa [hzdim]) _
    (by rw [milnorChainRestrict_milnorChainRestrict, Set.inter_self]) ?_
  refine fibreRestrict_divisor_fibreRestrict_eq_zero C sE q k a
    (by rw [← fibreRestrict_fibreRestrict_comp C sE q p hz, hdiv, map_zero]) ?_
  intro ξ haξ hqξ y hy hspec
  have hsp : q.base ξ.1 ⤳ z := hy ▸ hspec.map q.continuous
  refine hqξ (eq_of_specializes_of_relativeDimension_le C sB hsp ?_)
  rw [(relativeDimension_base_eq_of_apply_ne_zero C sE sB sV q p hp hbp hζ hζdim ha haζ
    haξ).2.2, hzdim]

include hp hbp in
/-- For a fibre family of K₂-chains whose members sit over points of `p⁻¹(x)` other than its
generic point `ζ`, the boundary of the part of the sum away from `q⁻¹(z)` has no part on
`q⁻¹(z)`, for every `z` in `p⁻¹(x)`. -/
theorem fibreRestrict_boundary_fibreFamily_sum_sub_eq_zero (k : ℤ) {x : V} {ζ z : B}
    (hζ : p.base ζ = x) (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    (F : FibreFamily C sE q (k + 2) 2) (hF : ∀ w, F.chain w ≠ 0 → p.base w = x ∧ w ≠ ζ)
    (hz : p.base z = x) :
    fibreRestrict C sE q z (k + 1) 1
      (pointwiseMilnorBoundary C sE k (F.sum - F.chain z)) = 0 := by
  refine milnorChainRestrict_pointwiseMilnorBoundary_eq_zero k _ fun w hw y hy hspec ↦ ?_
  obtain ⟨hwz, hFw⟩ := fibreFamily_sum_sub_apply_ne_zero F z hw
  have hsp : q.base w.1 ⤳ z := (show q.base y = z from hy) ▸ hspec.map q.continuous
  have hwdim := (eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim
    (hF _ hFw).1).resolve_left (hF _ hFw).2
  rcases eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim hz with h | h
  · have := relativeDimension_le_of_specializes C sB hsp
    rw [h, hζdim, hwdim] at this
    omega
  · exact hwz (eq_of_specializes_of_relativeDimension_le C sB hsp (by rw [hwdim, h]))

include hbq hp hbp in
/-- **The second step along a tower, away from the generic level.** A K₁-chain on the fibre of
`q ≫ p` over `x`, vanishing over the generic point `ζ` of `p⁻¹(x)` and with no divisor on the
fibre, lies over the points of `p⁻¹(x)` of relative dimension `δ(x)`; if `δ(x) ≠ k + 1 - m`, the
boundary-lifting property of `q` at each of them, summed over them, exhibits it as the fibrewise
part of a boundary. -/
theorem exists_fibreRestrict_comp_closed (k : ℤ)
    (hLq : ∀ z : B, FibreBoundaryLift C sE sB q m k z) {x : V} {ζ : B} (hζ : p.base ζ = x)
    (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    (hxk : relativeDimension C.dimensionFunction sV x ≠ k + 1 - m)
    (a : PointwiseKOneGroup C sE k) (ha : fibreRestrict C sE (q ≫ p) x (k + 1) 1 a = a)
    (haζ : fibreRestrict C sE q ζ (k + 1) 1 a = 0)
    (hdiv : fibreRestrict C sE (q ≫ p) x k 0 (pointwiseDivisorDifferential C sE k a) = 0) :
    ∃ η : PointwiseKTwoGroup C sE k, fibreRestrict C sE (q ≫ p) x (k + 2) 2 η = η ∧
      fibreRestrict C sE (q ≫ p) x (k + 1) 1 (pointwiseMilnorBoundary C sE k η) = a := by
  classical
  have := quasiCompact_of_isAffineSpaceBundle q m hbq
  have hpiece := exists_fibreRestrict_boundary_eq_of_ne C sE sB sV q p hp hbp k hLq hζ hζdim hxk
    a ha haζ hdiv
  let good : B → Prop := fun z ↦ p.base z = x ∧ z ≠ ζ ∧ fibreRestrict C sE q z (k + 1) 1 a ≠ 0
  let ch : B → PointwiseKTwoGroup C sE k := fun z ↦
    if h : good z then (hpiece z h.1 h.2.1).choose else 0
  have hch : ∀ z (h : good z), ch z = (hpiece z h.1 h.2.1).choose := fun z h ↦ dite_eq_left h
  have hch₀ : ∀ z, ¬ good z → ch z = 0 := fun z h ↦ dite_eq_right h
  have hgood : ∀ z, ch z ≠ 0 → good z := fun z hz ↦ of_not_not fun h ↦ hz (hch₀ z h)
  let F : FibreFamily C sE q (k + 2) 2 :=
    { chain := ch
      supported := fun z w hw ↦ by
        have h := hgood z fun h0 ↦ hw (by rw [h0]; rfl)
        rw [hch z h] at hw
        exact base_eq_of_fibreRestrict_eq_self C sE q (hpiece z h.1 h.2.1).choose_spec.1 hw
      finite := fun W hW ↦ (finite_setOf_fibreRestrict_ne_zero C sE q a W hW).subset
        fun z hz ↦ ⟨hz.1, (hgood z hz.2).2.2⟩ }
  refine ⟨F.sum, ?_, ?_⟩
  · refine milnorChainRestrict_eq_self _ fun w hw ↦ ?_
    refine (hgood (q.base w.1) fun h0 ↦ hw ?_).1
    show (ch (q.base w.1)).1 w = 0
    rw [h0]
    rfl
  · refine eq_of_forall_fibreRestrict_eq C sE q p (by
      rw [fibreRestrict, milnorChainRestrict_milnorChainRestrict, Set.inter_self]) ha fun z hz ↦ ?_
    have hsplit := congrArg (fibreRestrict C sE q z (k + 1) 1)
      (congrArg (pointwiseMilnorBoundary C sE k) (sub_add_cancel F.sum (F.chain z)))
    rw [map_add, map_add, fibreRestrict_boundary_fibreFamily_sum_sub_eq_zero C sE sB sV q p hp hbp
      k hζ hζdim F (fun w hw ↦ ⟨(hgood w hw).1, (hgood w hw).2.1⟩) hz, zero_add] at hsplit
    rw [fibreRestrict_fibreRestrict_comp C sE q p hz, ← hsplit]
    show fibreRestrict C sE q z (k + 1) 1 (pointwiseMilnorBoundary C sE k (ch z)) = _
    by_cases hgz : good z
    · rw [hch z hgz]
      exact (hpiece z hgz.1 hgz.2.1).choose_spec.2
    · rw [hch₀ z hgz, map_zero, map_zero]
      by_cases hzζ : z = ζ
      · rw [hzζ, haζ]
      · by_contra hne
        exact hgz ⟨hz, hzζ, Ne.symm hne⟩

/-! ### The two fibrewise properties along a tower -/

/-- The fibre of `q ≫ p` over `x` is the preimage under `q` of the fibre of `p` over `x`. -/
theorem preimage_comp_singleton (x : V) :
    (q ≫ p).base ⁻¹' {x} = q.base ⁻¹' (p.base ⁻¹' {x}) := rfl

include hq hbq hp hbp in
/-- **The second step along a tower, at the generic level of `q`.** If `δ(x) = k + 1`, a
K₁-chain on the fibre of `q ≫ p` over `x`, vanishing over the generic point `ζ` of `p⁻¹(x)` and
with no divisor on the fibre, descends along `q` to a chain on `p⁻¹(x)`, and lifting that along
`p` exhibits it as the fibrewise part of a boundary. -/
theorem exists_fibreRestrict_comp_of_relativeDimension_eq (k : ℤ) {x : V} {ζ : B}
    (hUq : ∀ z : B, FibreUnitDescent C sE sB q m (k + m) z)
    (hLp : FibreBoundaryLift C sB sV p 1 k x)
    (hdvr : ∀ (ζ w : B) (hw : ζ ⤳ w), p.base ζ = p.base w → ζ ≠ w →
      IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
        (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    (hζ : p.base ζ = x) (hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1)
    (ht : relativeDimension C.dimensionFunction sV x = k + 1)
    (a : PointwiseKOneGroup C sE (k + m)) (ha : fibreRestrict C sE (q ≫ p) x (k + m + 1) 1 a = a)
    (haζ : fibreRestrict C sE q ζ (k + m + 1) 1 a = 0)
    (hdiv : fibreRestrict C sE (q ≫ p) x (k + m) 0
      (pointwiseDivisorDifferential C sE (k + m) a) = 0) :
    ∃ η : PointwiseKTwoGroup C sE (k + m), fibreRestrict C sE (q ≫ p) x (k + m + 2) 2 η = η ∧
      fibreRestrict C sE (q ≫ p) x (k + m + 1) 1
        (pointwiseMilnorBoundary C sE (k + m) η) = a := by
  have hcarry := fun (ξ : pointsOfDimension C sE (k + m + 1)) (hξ : a.1 ξ ≠ 0) ↦
    relativeDimension_base_eq_of_apply_ne_zero C sE sB sV q p hp hbp hζ hζdim ha haζ hξ
  obtain ⟨b, hb, hbsupp⟩ := exists_eq_bundleChainPullback_of_fibreUnitDescent C sE sB q hq hbq
    k hUq a (fun ξ hξ ↦ ((hcarry ξ hξ).2.2.trans ht).le) (fun ξ hξ ↦ by
      rw [← fibreRestrict_fibreRestrict_comp C sE q p (hcarry ξ hξ).1, hdiv, map_zero])
  have hbx : fibreRestrict C sB p x (k + 1) 1 b = b := by
    refine milnorChainRestrict_eq_self _ fun y hy ↦ ?_
    obtain ⟨ξ, hξy, hξ⟩ := hbsupp y hy
    rw [Set.mem_preimage, ← hξy]
    exact (hcarry ξ hξ).1
  have hbdiv : fibreRestrict C sB p x k 0 (pointwiseDivisorDifferential C sB k b) = 0 := by
    refine milnorChainRestrict_eq_zero _ fun y _ hyx ↦ ?_
    have h1 := relativeDimension_le_of_isAffineSpaceBundle C sB sV p hp hbp y.1
    rw [show p.base y.1 = x from hyx, (mem_pointsOfDimension C sB).mp y.2, ht] at h1
    omega
  obtain ⟨η', hη'x, hη'⟩ := hLp (by rw [ht]; push_cast; omega) b hbx hbdiv
  refine ⟨bundleChainPullback C sE sB q hq hbq (k + 2) (k + m + 2) (by ring) 2 η', ?_, ?_⟩
  · rw [fibreRestrict, preimage_comp_singleton q p x,
      milnorChainRestrict_preimage_bundleChainPullback]
    exact congrArg _ hη'x
  · rw [fibreRestrict, preimage_comp_singleton q p x,
      milnorChainRestrict_pointwiseMilnorBoundary_bundleChainPullback C sE sB q hq hbq k
      (p.base ⁻¹' {x}) η' ?_, hη', hb]
    intro β hβ w hw hβw hwdim
    have hβx : p.base β.1 = x := base_eq_of_fibreRestrict_eq_self C sB p hη'x hβ
    refine hdvr β.1 w hβw (hβx.trans hw.symm) fun h ↦ ?_
    have := (mem_pointsOfDimension C sB).mp β.2
    rw [h, hwdim] at this
    omega

include hq hbq hp hbp in
/-- **The boundary-lifting property along a tower.** -/
theorem fibreBoundaryLift_comp
    (hLq : ∀ (k : ℤ) (z : B), FibreBoundaryLift C sE sB q m k z)
    (hUq : ∀ (k : ℤ) (z : B), FibreUnitDescent C sE sB q m k z)
    (hLp : ∀ (k : ℤ) (x : V), FibreBoundaryLift C sB sV p 1 k x)
    (hdvr : ∀ (ζ w : B) (hw : ζ ⤳ w), p.base ζ = p.base w → ζ ≠ w →
      IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
        (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    (k : ℤ) (x : V) : FibreBoundaryLift C sE sV (q ≫ p) (m + 1) k x := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + m := ⟨k - m, by ring⟩
  intro hx a ha hdiv
  obtain ⟨ζ, hζ, hζdim₀, -⟩ :=
    exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sB sV p hp hbp x
  have hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1 := by
    rw [hζdim₀]
    push_cast
    ring
  obtain ⟨η₁, hη₁x, ha'x, ha'ζ, ha'div⟩ := exists_fibreRestrict_comp_generic C sE sB sV q p hp hbp
    (k' + m) (hLq _) hζ hζdim (by push_cast at hx; omega) a ha hdiv
  set a' := a - fibreRestrict C sE (q ≫ p) x (k' + m + 1) 1
    (pointwiseMilnorBoundary C sE (k' + m) η₁) with ha'
  suffices h : ∃ η₂ : PointwiseKTwoGroup C sE (k' + m),
      fibreRestrict C sE (q ≫ p) x (k' + m + 2) 2 η₂ = η₂ ∧
        fibreRestrict C sE (q ≫ p) x (k' + m + 1) 1
          (pointwiseMilnorBoundary C sE (k' + m) η₂) = a' by
    obtain ⟨η₂, hη₂x, hη₂⟩ := h
    refine ⟨η₁ + η₂, by rw [map_add, hη₁x, hη₂x], ?_⟩
    rw [map_add, map_add, hη₂, ha']
    abel
  by_cases ht : relativeDimension C.dimensionFunction sV x = k' + 1
  · exact exists_fibreRestrict_comp_of_relativeDimension_eq C sE sB sV q p hq hp hbq hbp k' (hUq _)
      (hLp k' x) hdvr hζ hζdim ht a' ha'x ha'ζ ha'div
  · exact exists_fibreRestrict_comp_closed C sE sB sV q p hp hbq hbp (k' + m) (hLq _) hζ hζdim
      (by omega) a' ha'x ha'ζ ha'div

include hq hbq hp hbp in
/-- **The unit-descent property along a tower.** -/
theorem fibreUnitDescent_comp
    (hUq : ∀ (k : ℤ) (z : B), FibreUnitDescent C sE sB q m k z)
    (hUp : ∀ (k : ℤ) (x : V), FibreUnitDescent C sB sV p 1 k x)
    (k : ℤ) (x : V) : FibreUnitDescent C sE sV (q ≫ p) (m + 1) k x := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + m := ⟨k - m, by ring⟩
  intro hx a ha hdiv ξ hξ
  have hx' : relativeDimension C.dimensionFunction sV x = k' := by push_cast at hx; omega
  obtain ⟨ζ, hζ, hζdim₀, -⟩ :=
    exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sB sV p hp hbp x
  have hζdim : relativeDimension C.dimensionFunction sB ζ =
      relativeDimension C.dimensionFunction sV x + 1 := by
    rw [hζdim₀]
    push_cast
    ring
  -- every point carrying `a` lies over `ζ`
  have hcarry : ∀ ξ' : pointsOfDimension C sE (k' + m + 1), a.1 ξ' ≠ 0 →
      p.base (q.base ξ'.1) = x ∧ q.base ξ'.1 = ζ := by
    intro ξ' hξ'
    have hpx : p.base (q.base ξ'.1) = x := base_eq_of_fibreRestrict_eq_self C sE (q ≫ p) ha hξ'
    refine ⟨hpx, (eq_or_relativeDimension_eq_of_fibre C sB sV p hp hbp hζ hζdim
      hpx).resolve_right fun h ↦ ?_⟩
    have h1 := relativeDimension_le_add_of_isAffineSpaceBundle C sE sB q hq hbq ξ'.1
    rw [(mem_pointsOfDimension C sE).mp ξ'.2, h, hx'] at h1
    omega
  obtain ⟨b, hb, hbsupp⟩ := exists_eq_bundleChainPullback_of_fibreUnitDescent C sE sB q hq hbq
    k' (hUq (k' + m)) a (fun ξ' hξ' ↦ by rw [(hcarry ξ' hξ').2, hζdim, hx']) (fun ξ' hξ' ↦ by
      rw [← fibreRestrict_fibreRestrict_comp C sE q p (hcarry ξ' hξ').1, hdiv, map_zero])
  have hbx : fibreRestrict C sB p x (k' + 1) 1 b = b := by
    refine milnorChainRestrict_eq_self _ fun y hy ↦ ?_
    obtain ⟨ξ', hξ'y, hξ'⟩ := hbsupp y hy
    rw [Set.mem_preimage, ← hξ'y]
    exact (hcarry ξ' hξ').1
  have hbdiv : fibreRestrict C sB p x k' 0 (pointwiseDivisorDifferential C sB k' b) = 0 := by
    apply bundleChainPullback_zero_injective C sE sB q hq hbq (rfl : k' + m = k' + m)
    rwa [map_zero, ← milnorChainRestrict_preimage_bundleChainPullback,
      ← pointwiseDivisorDifferential_bundleChainPullback C sE sB q hq hbq k' b, ← hb]
  by_cases haξ : a.1 ξ = 0
  · exact ⟨0, by rw [haξ, map_zero]⟩
  have hqξ : q.base ξ.1 ∈ pointsOfDimension C sB (k' + 1) := by
    rw [mem_pointsOfDimension, (hcarry ξ haξ).2, hζdim, hx']
  obtain ⟨c, hc⟩ := hUp k' x (by rw [hx']; push_cast; ring) b hbx hbdiv ⟨q.base ξ.1, hqξ⟩
    (hcarry ξ haξ).1
  obtain ⟨c', hc'⟩ := exists_milnorKTransport_residueFieldMap_comp q p ξ.1 c
  refine ⟨c', ?_⟩
  have := congrArg (fun a : PointwiseKOneGroup C sE (k' + m) ↦ a.1 ξ) hb
  rw [this, bundleChainPullback_apply_of_mem C sE sB q hq hbq _ b ξ hqξ, hc, hc']

end Stacks.Chow

end
