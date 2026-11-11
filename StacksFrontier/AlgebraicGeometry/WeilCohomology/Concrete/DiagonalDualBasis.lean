module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDisjointUnion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.DiagonalBasis

/-!
# The Künneth coordinates of the class of the diagonal are a signed dual basis

Let `H^*` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth
projective schemes over `k` (`Stacks.WeilCohomology.WeilData`), satisfying (A), (B) and (C). Let
`X` be nonempty and equidimensional of dimension `d`, and choose a basis `e_{i,j}` of `H^i(X)`.
Stacks 0FHH: writing, by the Künneth formula,

`γ([Δ]) = ∑_i ∑_j e_{i,j} ⊗ e'_{2d-i,j}` in `⨁_i H^i(X) ⊗_F H^{2d-i}(X)(d)`,

one has `∫_X e_{i,j} ∪ e'_{2d-i,j'} = (-1)^i δ_{jj'}`.

Everything is about the actual objects: `[Δ] ∈ CH^d(X × X)` is the class of the diagonal
(`Stacks.WeilCohomology.closedSubschemeClass` of `SmoothProjectiveScheme.diag X`), `γ` the cycle
class map of (D2), and the decomposition of `H^{2d}(X × X)(d)` is the inverse of the Künneth
isomorphism of (B)(a) (`WeilData.kunnethComponentTw`). Nothing the source's proof derives is
assumed. The proof is the source's:

* `γ([Δ]) = Δ_*1` is Stacks 0FHG for the diagonal
  (`WeilData.cycleClass_diagonal_eq_pushforward_one`, which uses Stacks 0FHF);
* hence `∫_{X × X} (a ⊗ b) ∪ γ([Δ]) = ∫_X Δ^*(a ⊗ b) = ∫_X a ∪ b`, by the trace equation of the
  pushforward (`WeilData.traceProj_pull_diag`) and the first half of Remark 0FHD, that pulling
  `pr₁^*a ∪ pr₂^*b` back along the diagonal gives `a ∪ b` (`WeilData.pull_diag_mul`);
* by axiom (B)(b) the same trace, evaluated on the Künneth decomposition, is
  `∑_j (∫_X a ∪ e_{i,j})(∫_X e'_{2d-i,j} ∪ b)` (`WeilData.traceProj_mul_kunnethMap`): the two
  interchanges of order cost `(-1)^{i·i}` and `(-1)^{i(2d-i)}`, which cancel, and the components
  of other bidegrees contribute nothing;
* so `∫_X a ∪ b = ∑_j (∫_X a ∪ e_{i,j})(∫_X e'_{2d-i,j} ∪ b)` — the identity the base's
  `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_mul_dualBasis` had to assume
  (that declaration, which carries it as `hdecomp`, is the linear-algebra step only and is not
  registered for 0FHH) — and Poincaré duality (A)(b) makes `e'` the dual basis
  (`WeilData.traceProj_mul_basis`, from `Stacks.WeilCohomology.dualBasis_of_pairing_decomposition`);
  graded commutativity gives the sign `(-1)^{i(2d-i)} = (-1)^i`.

## Main definitions

* `Stacks.WeilCohomology.WeilData.traceProj`: `∫_X` on the whole ring `H^*(X)`, through the
  degree-`2d` component.
* `Stacks.WeilCohomology.WeilData.kunnethComponent`,
  `Stacks.WeilCohomology.WeilData.kunnethComponentTw`: the Künneth components of a class of
  `H^*(X × X)`, resp. `H^n(X × X)(m)`, in `H^p(X) ⊗ H^q(X)`, resp. `H^i(X) ⊗ H^j(X)(m)`.
* `Stacks.WeilCohomology.WeilData.diagonalKunnethCoordinates`: the coordinates `e'_{2d-i,j}` of
  `γ([Δ])` with respect to a basis of `H^i(X)`.

## Main results

* `Stacks.WeilCohomology.WeilData.pairing_kunnethComponentTw_diagonal`: **Stacks 0FHH**, for any
  family `e'` with `γ([Δ])_{(i, 2d-i)} = ∑_j e_{i,j} ⊗ e'_j`.
* `Stacks.WeilCohomology.WeilData.pairing_diagonalKunnethCoordinates`: **Stacks 0FHH**, for the
  Künneth coordinates themselves.

## Implementation notes

The twisted groups `H^n(X)(m) = H^n(X) ⊗ F(m)` are compared with `H^n(X)` through the
coordinate `WeilData.twCoord` of `F(1)` with which the twisted cup products are defined, so that
all computations take place in the rings `H^*(X)` and `H^*(X × X)`. The trace `∫_X` is extended
to the whole ring by zero outside the degree `2d` (`WeilData.traceProj`), the convention under
which the source reads axiom (B)(b).

## References

* [Stacks Project, Tag 0FHH](https://stacks.math.columbia.edu/tag/0FHH)
* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow DirectSum
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- The product of two nonempty equidimensional smooth projective schemes of dimensions `d` and
`e` is nonempty and equidimensional of dimension `d + e`. -/
theorem isNonemptyEquidimensional_prod {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) :
    IsNonemptyEquidimensional (prod X Y) (d + e) where
  nonempty := by
    have := hX.nonempty
    have := hY.nonempty
    exact (inferInstance : Nonempty (Limits.pullback X.obj.hom Y.obj.hom : Scheme.{u}))
  relativeDimension := by
    rw [Nat.add_comm]
    exact RelativeDimension.comp_of_flat (pullback.fst X.obj.hom Y.obj.hom) X.obj.hom
      (RelativeDimension.of_isPullback (IsPullback.of_hasPullback X.obj.hom Y.obj.hom).flip
        hY.relativeDimension) hX.relativeDimension

/-- The diagonal `X → X × X` composed with the first projection is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem diag_fst (X : (SmoothProjectiveScheme k).FullSubcategory) : diag X ≫ fst X X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.diagonal_fst X.obj.hom))

/-- The diagonal `X → X × X` composed with the second projection is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem diag_snd (X : (SmoothProjectiveScheme k).FullSubcategory) : diag X ≫ snd X X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.diagonal_snd X.obj.hom))

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- In coordinates, the cup product with an untwisted left factor is the cup product. -/
theorem twCoord_tateCupLeft (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ)
    (h : i + j = n) (m : ℤ)
    (a : W.grade X i) (b : W.Tw X j m) :
    (W.twCoord X n m (tateCupLeft (W.cup X i j n h) m a b) : W.H X) =
      (a : W.H X) * (W.twCoord X j m b : W.H X) := by
  rw [tateCupLeft, LinearMap.mk₂_apply, twCoord, tateTwistCoordinates_map]
  rfl

/-- The trace `∫_X` read on the whole cohomology ring: the degree-`2d` component, untwisted by
the coordinates, followed by `∫_X`. -/
def traceProj (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    W.H X →ₗ[F] F :=
  (W.trace X d hX).comp ((W.twCoord X (2 * (d : ℤ)) d).symm.toLinearMap.comp
    ((DirectSum.component F ℤ (fun n ↦ W.grade X n) (2 * (d : ℤ))).comp
      (DirectSum.decomposeLinearEquiv (W.grade X)).toLinearMap))

/-- `traceProj` is `∫_X` of the degree-`2d` component. -/
theorem traceProj_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (x : W.H X) :
    W.traceProj X d hX x = W.trace X d hX
      ((W.twCoord X (2 * (d : ℤ)) d).symm (DirectSum.decompose (W.grade X) x (2 * (d : ℤ)))) :=
  rfl

/-- On `H^{2d}(X)`, `traceProj` is `∫_X`. -/
theorem traceProj_of_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) {x : W.H X} (hx : x ∈ W.grade X (2 * (d : ℤ))) :
    W.traceProj X d hX x = W.trace X d hX ((W.twCoord X (2 * (d : ℤ)) d).symm ⟨x, hx⟩) := by
  rw [traceProj_apply]
  congr 2
  exact Subtype.ext (DirectSum.decompose_of_mem_same _ hx)

/-- `traceProj` vanishes on `H^n(X)` for `n ≠ 2d`. -/
theorem traceProj_of_mem_ne (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) {x : W.H X} {n : ℤ} (hx : x ∈ W.grade X n)
    (hn : n ≠ 2 * (d : ℤ)) : W.traceProj X d hX x = 0 := by
  rw [traceProj_apply]
  have : (DirectSum.decompose (W.grade X) x) (2 * (d : ℤ)) = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne _ hx hn)
  simp [this]

/-- `∫_X z` is `traceProj` of the coordinates of `z`. -/
theorem trace_eq_traceProj (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (z : W.Tw X (2 * (d : ℤ)) d) :
    W.trace X d hX z = W.traceProj X d hX (W.twCoord X _ _ z : W.H X) := by
  rw [W.traceProj_of_mem X d hX (W.twCoord X _ _ z).2]
  simp

/-- The pairing `(a, b) ↦ ∫_X a ∪ b` of (A)(b) in coordinates. -/
theorem pairing_eq_traceProj (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (a : W.grade X i)
    (b : W.Tw X j d) :
    W.pairing X d hX i j h a b =
      W.traceProj X d hX ((a : W.H X) * (W.twCoord X j d b : W.H X)) := by
  rw [pairing, LinearMap.compr₂_apply, trace_eq_traceProj, twCoord_tateCupLeft]

/-- The twisted pairing `(a, b) ↦ ∫_X a ∪ b` in coordinates. -/
theorem pairingTw_eq_traceProj (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ)
    (h' : s + t = d) (a : W.Tw X i s) (b : W.Tw X j t) :
    W.pairingTw X d hX i j h s t h' a b =
      W.traceProj X d hX ((W.twCoord X i s a : W.H X) * (W.twCoord X j t b : W.H X)) := by
  rw [pairingTw, LinearMap.compr₂_apply, trace_eq_traceProj, twCoord_cupTw, coe_cup]

/-- The graded commutativity of (D1), for traces: `∫ a ∪ b = (-1)^{ij} ∫ b ∪ a`. -/
theorem traceProj_mul_comm (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) {i j : ℤ} {a b : W.H X} (ha : a ∈ W.grade X i)
    (hb : b ∈ W.grade X j) :
    W.traceProj X d hX (a * b) = ((i * j).negOnePow : ℤ) * W.traceProj X d hX (b * a) := by
  rw [W.graded_comm X i j a b ha hb, map_zsmul, zsmul_eq_mul]

section Kunneth

variable {W} (hK : W.KunnethTrace) {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
  (hX : IsNonemptyEquidimensional X d)

include hK in
/-- Axiom (B)(b) in coordinates, on the Künneth component of top classes:
`∫_{X × X} pr₁^*α ∪ pr₂^*β = ∫_X α · ∫_X β` for `α, β ∈ H^{2d}(X)`. -/
theorem traceProj_prod_of_mem {α β : W.H X} (hα : α ∈ W.grade X (2 * (d : ℤ)))
    (hβ : β ∈ W.grade X (2 * (d : ℤ))) :
    W.traceProj (SmoothProjectiveScheme.prod X X) (d + d)
        (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
        (W.pull (SmoothProjectiveScheme.fst X X) α * W.pull
            (SmoothProjectiveScheme.snd X X) β) =
      W.traceProj X d hX α * W.traceProj X d hX β := by
  have h := (hK X X d d hX hX (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)).1
    ((W.twCoord X _ d).symm ⟨α, hα⟩) ((W.twCoord X _ d).symm ⟨β, hβ⟩)
  rw [trace_eq_traceProj, twCoord_cupTw, coe_cup, twCoord_pullTw, twCoord_pullTw, coe_pullDeg,
    coe_pullDeg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  rw [h, traceProj_of_mem _ _ _ _ hα, traceProj_of_mem _ _ _ _ hβ]

include hK in
/-- Axiom (B)(b) in coordinates, on the other Künneth components of degree `4d`:
`∫_{X × X} pr₁^*α ∪ pr₂^*β = 0` for `α ∈ H^m(X)`, `β ∈ H^{m'}(X)`, `m + m' = 4d`, `m ≠ 2d`. -/
theorem traceProj_prod_of_mem_ne {m m' : ℤ} (hmm : m + m' = 2 * ((d + d : ℕ) : ℤ))
    (hm : m ≠ 2 * (d : ℤ)) {α β : W.H X} (hα : α ∈ W.grade X m) (hβ : β ∈ W.grade X m') :
    W.traceProj (SmoothProjectiveScheme.prod X X) (d + d)
        (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
        (W.pull (SmoothProjectiveScheme.fst X X) α *
          W.pull (SmoothProjectiveScheme.snd X X) β) = 0 := by
  have h := (hK X X d d hX hX (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)).2
    m m' hmm hm ((W.twCoord X m d).symm ⟨α, hα⟩) ((W.twCoord X m' d).symm ⟨β, hβ⟩)
  rwa [trace_eq_traceProj, twCoord_cupTw, coe_cup, twCoord_pullTw, twCoord_pullTw, coe_pullDeg,
    coe_pullDeg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h

end Kunneth

/-! ### Pairing exterior products with the diagonal class -/

/-- Pulling an exterior product `pr₁^*a ∪ pr₂^*b` back along the diagonal gives `a ∪ b`
(Remark 0FHD). -/
theorem pull_diag_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (a b : W.H X) :
    W.pull (SmoothProjectiveScheme.diag X)
        (W.pull (SmoothProjectiveScheme.fst X X) a * W.pull
            (SmoothProjectiveScheme.snd X X) b) =
      a * b := by
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← W.pull_comp, ← W.pull_comp,
    SmoothProjectiveScheme.diag_fst, SmoothProjectiveScheme.diag_snd, W.pull_id]
  rfl

/-- The product of homogeneous classes of degrees `p` and `q` lies in degree `n = p + q`. -/
private theorem mul_mem_grade_of_add_eq {Y : (SmoothProjectiveScheme k).FullSubcategory}
    {a b : W.H Y} {p q n : ℤ} (ha : a ∈ W.grade Y p) (hb : b ∈ W.grade Y q) (h : p + q = n) :
    a * b ∈ W.grade Y n :=
  h ▸ SetLike.GradedMul.mul_mem ha hb

/-- Products of signs in `F`. -/
private theorem negOnePow_cast_mul_negOnePow_cast (a b : ℤ) :
    ((a.negOnePow : ℤ) : F) * ((b.negOnePow : ℤ) : F) = (((a + b).negOnePow : ℤ) : F) := by
  rw [Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- **The sign rule for exterior products**:
`(pr₁^*a ∪ pr₂^*b) ∪ (pr₁^*u ∪ pr₂^*v) = (-1)^{sp} pr₁^*(a ∪ u) ∪ pr₂^*(b ∪ v)` for `b ∈ H^s(X)`
and `u ∈ H^p(X)`, by graded commutativity (D1). -/
theorem externalProduct_mul_externalProduct (X : (SmoothProjectiveScheme k).FullSubcategory)
    {s p : ℤ}
    (a : W.H X) {b u : W.H X} (hb : b ∈ W.grade X s) (hu : u ∈ W.grade X p) (v : W.H X) :
    W.pull (SmoothProjectiveScheme.fst X X) a * W.pull (SmoothProjectiveScheme.snd X X) b *
        (W.pull (SmoothProjectiveScheme.fst X X) u * W.pull
            (SmoothProjectiveScheme.snd X X) v) =
      ((s * p).negOnePow : ℤ) • (W.pull (SmoothProjectiveScheme.fst X X) (a * u) *
        W.pull (SmoothProjectiveScheme.snd X X) (b * v)) := by
  have hc := W.graded_comm _ s p _ _ (W.pull_grade (SmoothProjectiveScheme.snd X X) s b hb)
    (W.pull_grade (SmoothProjectiveScheme.fst X X) p u hu)
  rw [map_mul, map_mul, mul_assoc, ← mul_assoc (W.pull _ b), hc, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc]

section Pairing

variable {W} (hK : W.KunnethTrace) {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
  (hX : IsNonemptyEquidimensional X d)

include hK in
/-- The trace of `(pr₁^*a ∪ pr₂^*b) ∪ (pr₁^*u ∪ pr₂^*v)` for `a ∈ H^{2d-i}(X)`, `b ∈ H^i(X)`
vanishes unless `u ⊗ v` has bidegree `(i, 2d - i)`: by degree, or by axiom (B)(b). -/
theorem traceProj_externalProduct_mul_externalProduct_eq_zero {i p q : ℤ} {a b u v : W.H X}
    (ha : a ∈ W.grade X (2 * d - i)) (hb : b ∈ W.grade X i) (hu : u ∈ W.grade X p)
    (hv : v ∈ W.grade X q) (hpq : p ≠ i ∨ q ≠ 2 * d - i) :
    W.traceProj _ (d + d) (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
      (W.pull (SmoothProjectiveScheme.fst X X) a * W.pull (SmoothProjectiveScheme.snd X X) b *
        (W.pull (SmoothProjectiveScheme.fst X X) u *
          W.pull (SmoothProjectiveScheme.snd X X) v)) = 0 := by
  rw [W.externalProduct_mul_externalProduct X a hb hu v, map_zsmul]
  have hau := SetLike.GradedMul.mul_mem ha hu
  have hbv := SetLike.GradedMul.mul_mem hb hv
  by_cases htot : 2 * (d : ℤ) - i + p + (i + q) = 2 * ((d + d : ℕ) : ℤ)
  · rw [traceProj_prod_of_mem_ne hK hX htot (by omega) hau hbv, smul_zero]
  · rw [W.traceProj_of_mem_ne _ _ _ (SetLike.GradedMul.mul_mem
      (W.pull_grade _ _ _ hau) (W.pull_grade _ _ _ hbv)) htot, smul_zero]

include hK in
/-- The trace of `(pr₁^*a ∪ pr₂^*b) ∪ (pr₁^*u ∪ pr₂^*v)` for `a ∈ H^{2d-i}(X)`, `b ∈ H^i(X)`,
`u ∈ H^i(X)`, `v ∈ H^{2d-i}(X)` is `(∫_X a ∪ u)(∫_X v ∪ b)`: by axiom (B)(b), after the two
interchanges of order, whose signs `(-1)^{i·i}` and `(-1)^{i(2d - i)}` cancel. -/
theorem traceProj_externalProduct_mul_externalProduct {i : ℤ} {a b u v : W.H X}
    (ha : a ∈ W.grade X (2 * d - i)) (hb : b ∈ W.grade X i) (hu : u ∈ W.grade X i)
    (hv : v ∈ W.grade X (2 * d - i)) :
    W.traceProj _ (d + d) (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
      (W.pull (SmoothProjectiveScheme.fst X X) a * W.pull (SmoothProjectiveScheme.snd X X) b *
        (W.pull (SmoothProjectiveScheme.fst X X) u *
          W.pull (SmoothProjectiveScheme.snd X X) v)) =
      W.traceProj X d hX (a * u) * W.traceProj X d hX (v * b) := by
  have hau : a * u ∈ W.grade X (2 * (d : ℤ)) := W.mul_mem_grade_of_add_eq ha hu (by ring)
  have hbv : b * v ∈ W.grade X (2 * (d : ℤ)) := W.mul_mem_grade_of_add_eq hb hv (by ring)
  rw [W.externalProduct_mul_externalProduct X a hb hu v, map_zsmul, zsmul_eq_mul,
    traceProj_prod_of_mem hK hX hau hbv, W.traceProj_mul_comm X d hX hb hv]
  have hsign : (((i * i).negOnePow : ℤ) : F) * (((i * (2 * d - i)).negOnePow : ℤ) : F) = 1 := by
    rw [negOnePow_cast_mul_negOnePow_cast, show i * i + i * (2 * d - i) = 2 * (i * d) by ring,
      Int.negOnePow_two_mul]
    simp
  linear_combination (W.traceProj X d hX (a * u) * W.traceProj X d hX (v * b)) * hsign

end Pairing

variable {W} in
/-- If `G = Δ_*1`, then `G` represents the trace pairing through the diagonal:
`∫_X Δ^*y = ∫_{X × X} y ∪ G` for `y ∈ H^{2d}(X × X)`. This is the trace equation of the
pushforward (`WeilData.pushforward_trace'`) against the unit. -/
theorem traceProj_pull_diag (hA : W.PerfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) {y : W.H (SmoothProjectiveScheme.prod X X)}
    (hy : y ∈ W.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ))) :
    W.traceProj X d hX (W.pull (SmoothProjectiveScheme.diag X) y) =
      W.traceProj _ (d + d) (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
        (y * W.twCoord _ _ _ (W.pushforward hA (SmoothProjectiveScheme.diag X) hX
          (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX) 0 0 (2 * d) d
          (by push_cast; ring) (by push_cast; ring) (W.unitTw X 0 0 rfl))) := by
  have h := pushforward_trace' hA (SmoothProjectiveScheme.diag X) hX
    (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX) 0 0 (2 * d) d
    (by push_cast; ring) (by push_cast; ring) (2 * d) d (by ring) (by ring) (by push_cast; ring)
    (by push_cast; ring) ((W.twCoord _ (2 * (d : ℤ)) d).symm ⟨y, hy⟩) (W.unitTw X 0 0 rfl)
  rw [pairingTw_eq_traceProj, pairingTw_eq_traceProj, twCoord_pullTw, coe_pullDeg,
    LinearEquiv.apply_symm_apply, coe_twCoord_unitTw, mul_one] at h
  exact h

variable {W} in
/-- **The dual basis.** If `∫_X a ∪ b = ∑_l (∫_X a ∪ e_l)(∫_X v_l ∪ b)` for all
`a ∈ H^{2d - i}(X)` and `b ∈ H^i(X)`, where `e` is a basis of `H^i(X)` and `v_l ∈ H^{2d - i}(X)`,
then `∫_X v_j ∪ e_{j'} = δ_{jj'}`: by Poincaré duality (A)(b) the pairing is nondegenerate, and
`Stacks.WeilCohomology.dualBasis_of_pairing_decomposition` applies. -/
theorem traceProj_mul_basis (hA : W.PerfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (i : ℤ) {J : Type*} [Fintype J] [DecidableEq J]
    (e : Module.Basis J F (W.grade X i)) (v : J → W.H X) (hv : ∀ j, v j ∈ W.grade X (2 * d - i))
    (hdecomp : ∀ a ∈ W.grade X (2 * d - i), ∀ b ∈ W.grade X i,
      W.traceProj X d hX (a * b) =
        ∑ l, W.traceProj X d hX (a * e l) * W.traceProj X d hX (v l * b))
    (j j' : J) :
    W.traceProj X d hX (v j * e j') = if j = j' then 1 else 0 := by
  let pair : W.grade X (2 * d - i) →ₗ[F] W.grade X i →ₗ[F] F :=
    ((LinearMap.mul F (W.H X)).compl₁₂ (W.grade X (2 * d - i)).subtype
      (W.grade X i).subtype).compr₂ (W.traceProj X d hX)
  have hflip : Function.Injective pair.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have := hA X d hX i (2 * d - i) (by ring)
    refine (LinearMap.IsPerfPair.bijective_left (W.pairing X d hX i (2 * d - i) _)).1 ?_
    rw [map_zero]
    refine LinearMap.ext fun a ↦ ?_
    rw [pairing_eq_traceProj, W.traceProj_mul_comm X d hX b.2 (W.twCoord X _ _ a).2,
      LinearMap.zero_apply]
    have := LinearMap.congr_fun hb (W.twCoord X _ _ a)
    simp only [LinearMap.flip_apply, LinearMap.zero_apply] at this
    rw [show W.traceProj X d hX ((W.twCoord X (2 * d - i) d a : W.H X) * b) = 0 from this,
      mul_zero]
  exact Stacks.WeilCohomology.dualBasis_of_pairing_decomposition pair hflip e
    (fun j ↦ ⟨v j, hv j⟩) (fun a b ↦ hdecomp a a.2 b b.2) j j'

/-! ### Künneth coordinates -/

section KunnethCoordinates

variable {W} (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The decomposition `H^*(X) ⊗_F H^*(X) ≃ ⨁_{(p, q)} H^p(X) ⊗_F H^q(X)` by bidegree. -/
def bidegreeEquiv :
    W.H X ⊗[F] W.H X ≃ₗ[F] ⨁ pq : ℤ × ℤ, W.grade X pq.1 ⊗[F] W.grade X pq.2 :=
  (TensorProduct.congr (DirectSum.decomposeLinearEquiv (W.grade X))
    (DirectSum.decomposeLinearEquiv (W.grade X))).trans
    (TensorProduct.directSum F F (fun n ↦ W.grade X n) (fun n ↦ W.grade X n))

/-- The component `H^p(X) ⊗_F H^q(X)` of bidegree `(p, q)` of `H^*(X) ⊗_F H^*(X)`. -/
def bidegreeComponent (p q : ℤ) : W.H X ⊗[F] W.H X →ₗ[F] W.grade X p ⊗[F] W.grade X q :=
  (DirectSum.component F (ℤ × ℤ) (fun pq ↦ W.grade X pq.1 ⊗[F] W.grade X pq.2) (p, q)).comp
    (bidegreeEquiv X).toLinearMap

/-- For `u ∈ H^p(X)` and `v ∈ H^q(X)`, `bidegreeEquiv` sends `u ⊗ v` to the element `u ⊗ v` of
the summand of bidegree `(p, q)`. -/
theorem bidegreeEquiv_tmul_of_mem {p q : ℤ} {u v : W.H X} (hu : u ∈ W.grade X p)
    (hv : v ∈ W.grade X q) :
    bidegreeEquiv X (u ⊗ₜ v) = DirectSum.lof F (ℤ × ℤ)
      (fun pq ↦ W.grade X pq.1 ⊗[F] W.grade X pq.2) (p, q) (⟨u, hu⟩ ⊗ₜ ⟨v, hv⟩) := by
  rw [bidegreeEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem _ hu, DirectSum.decompose_of_mem _ hv, ← DirectSum.lof_eq_of F,
    ← DirectSum.lof_eq_of F, TensorProduct.directSum_lof_tmul_lof]

/-- For `u ∈ H^p(X)` and `v ∈ H^q(X)`, the component of `u ⊗ v` of bidegree `(p, q)` is
`u ⊗ v`. -/
theorem bidegreeComponent_tmul_self {p q : ℤ} {u v : W.H X} (hu : u ∈ W.grade X p)
    (hv : v ∈ W.grade X q) :
    bidegreeComponent X p q (u ⊗ₜ v) = ⟨u, hu⟩ ⊗ₜ ⟨v, hv⟩ := by
  rw [bidegreeComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    bidegreeEquiv_tmul_of_mem X hu hv, DirectSum.component.lof_self]

/-- For `u ∈ H^{p'}(X)` and `v ∈ H^{q'}(X)` with `(p', q') ≠ (p, q)`, the component of bidegree
`(p, q)` of `u ⊗ v` is zero. -/
theorem bidegreeComponent_tmul_of_ne {p q p' q' : ℤ} {u v : W.H X} (hu : u ∈ W.grade X p')
    (hv : v ∈ W.grade X q') (h : (p', q') ≠ (p, q)) :
    bidegreeComponent X p q (u ⊗ₜ v) = 0 := by
  rw [bidegreeComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    bidegreeEquiv_tmul_of_mem X hu hv, DirectSum.component.of, dite_eq_right h]

variable (hBa : W.KunnethIsomorphism)

/-- **The Künneth component of bidegree `(p, q)`** of a class of `H^*(X × X)`: its preimage under
the isomorphism `H^*(X) ⊗_F H^*(X) ≅ H^*(X × X)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, of axiom (B)(a),
read in the summand `H^p(X) ⊗_F H^q(X)`. -/
def kunnethComponent (p q : ℤ) :
    W.H (SmoothProjectiveScheme.prod X X) →ₗ[F] W.grade X p ⊗[F] W.grade X q :=
  (bidegreeComponent X p q).comp
    (LinearEquiv.ofBijective (W.kunnethMap X X) (hBa X X)).symm.toLinearMap

/-- The Künneth component of the Künneth image `κ(x)` of `x ∈ H^*(X) ⊗_F H^*(X)` is the
component of `x` of the same bidegree `(p, q)`. -/
theorem kunnethComponent_kunnethMap (p q : ℤ) (x : W.H X ⊗[F] W.H X) :
    kunnethComponent X hBa p q (W.kunnethMap X X x) = bidegreeComponent X p q x := by
  rw [kunnethComponent, LinearMap.comp_apply]
  congr 1
  exact (LinearEquiv.ofBijective (W.kunnethMap X X) (hBa X X)).symm_apply_apply x

/-- **The Künneth component of bidegree `(i, j)`** of a class of `H^n(X × X)(m)`, in
`H^i(X) ⊗_F H^j(X)(m)`: for `H^n(X × X)(m) = H^n(X × X) ⊗_F F(m)`, the Künneth component of the
first factor, with `F(m)` reassociated onto the second factor. This is the decomposition
`H^{2d}(X × X)(d) = ⨁_i H^i(X) ⊗_F H^{2d - i}(X)(d)` in the statement of Lemma 0FHH. -/
def kunnethComponentTw (n m i j : ℤ) :
    W.Tw (SmoothProjectiveScheme.prod X X) n m →ₗ[F] W.grade X i ⊗[F] W.Tw X j m :=
  (TensorProduct.assoc F (W.grade X i) (W.grade X j) (tateLine F W.tate m)).toLinearMap.comp
    (TensorProduct.map ((kunnethComponent X hBa i j).comp
      (W.grade (SmoothProjectiveScheme.prod X X) n).subtype) LinearMap.id)

/-- Reassociating a twist onto the second factor and reading it in coordinates is scaling by the
coordinate of the twist. -/
private theorem map_twCoord_assoc (i j m : ℤ) (t : W.grade X i ⊗[F] W.grade X j)
    (l : tateLine F W.tate m) :
    TensorProduct.map LinearMap.id (W.twCoord X j m).toLinearMap
        (TensorProduct.assoc F _ _ _ (t ⊗ₜ l)) =
      tateLineCoordinates (tateLineCoordinate W.finrank_tate) m l • t := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, twCoord, tateTwistCoordinates_tmul, TensorProduct.tmul_smul]
  | add t t' ht ht' => rw [TensorProduct.add_tmul, map_add, map_add, ht, ht', smul_add]

/-- In coordinates on the twists, the twisted Künneth component is the Künneth component. -/
theorem map_twCoord_kunnethComponentTw (n m i j : ℤ)
    (z : W.Tw (SmoothProjectiveScheme.prod X X) n m) :
    TensorProduct.map LinearMap.id (W.twCoord X j m).toLinearMap
        (kunnethComponentTw X hBa n m i j z) =
      kunnethComponent X hBa i j (W.twCoord _ n m z : W.H
          (SmoothProjectiveScheme.prod X X)) := by
  induction z using TensorProduct.inductionOn with
  | tmul x l =>
    rw [kunnethComponentTw, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_twCoord_assoc, twCoord, tateTwistCoordinates_tmul,
      Submodule.coe_smul, map_smul]
    rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, Submodule.coe_add, map_add]

end KunnethCoordinates

/-! ### Stacks 0FHH -/

section DualBasis

variable {W} {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d)

/-- The bilinear form `u ⊗ v ↦ (∫_X a ∪ u)(∫_X v ∪ b)` on `H^i(X) ⊗ H^{2d - i}(X)`. -/
def tracePairingProduct (i : ℤ) (a b : W.H X) :
    W.grade X i →ₗ[F] W.grade X (2 * d - i) →ₗ[F] F :=
  (LinearMap.mul F F).compl₁₂
    ((W.traceProj X d hX).comp ((LinearMap.mulLeft F a).comp (W.grade X i).subtype))
    ((W.traceProj X d hX).comp ((LinearMap.mulRight F b).comp (W.grade X (2 * d - i)).subtype))

/-- The pairing `tracePairingProduct` evaluates `u ⊗ v` to `(∫_X a ∪ u)(∫_X v ∪ b)`. -/
theorem tracePairingProduct_apply (i : ℤ) (a b : W.H X) (u : W.grade X i)
    (v : W.grade X (2 * d - i)) :
    tracePairingProduct hX i a b u v =
      W.traceProj X d hX (a * u) * W.traceProj X d hX (v * b) :=
  rfl

include hX in
/-- **Pairing an exterior product with a Künneth class.** For `a ∈ H^{2d - i}(X)` and
`b ∈ H^i(X)`, the trace `∫_{X × X} (pr₁^*a ∪ pr₂^*b) ∪ κ(x)` of the product with the Künneth image
`κ(x)` of `x ∈ H^*(X) ⊗ H^*(X)` sees only the component of `x` of bidegree `(i, 2d - i)`, and
evaluates `u ⊗ v` there to `(∫_X a ∪ u)(∫_X v ∪ b)`. -/
theorem traceProj_mul_kunnethMap (hK : W.KunnethTrace) {i : ℤ} {a b : W.H X}
    (ha : a ∈ W.grade X (2 * d - i)) (hb : b ∈ W.grade X i) (x : W.H X ⊗[F] W.H X) :
    W.traceProj _ (d + d) (SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX)
      (W.pull (SmoothProjectiveScheme.fst X X) a * W.pull (SmoothProjectiveScheme.snd X X) b *
        W.kunnethMap X X x) =
      TensorProduct.lift (tracePairingProduct hX i a b) (bidegreeComponent X i (2 * d - i) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, mul_add, map_add, hx, hy, map_add, map_add]
  | tmul u v =>
    induction u using DirectSum.Decomposition.inductionOn (W.grade X) with
    | zero => simp
    | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, mul_add, map_add, hu, hu', map_add,
        map_add]
    | @homogeneous p u =>
      induction v using DirectSum.Decomposition.inductionOn (W.grade X) with
      | zero => simp
      | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add, mul_add, map_add, hv, hv',
          map_add, map_add]
      | @homogeneous q v =>
        rw [kunnethMap_tmul]
        by_cases hpq : p = i ∧ q = 2 * d - i
        · obtain ⟨rfl, rfl⟩ := hpq
          rw [traceProj_externalProduct_mul_externalProduct hK hX ha hb u.2 v.2,
            bidegreeComponent_tmul_self X u.2 v.2, TensorProduct.lift.tmul,
            tracePairingProduct_apply]
        · rw [traceProj_externalProduct_mul_externalProduct_eq_zero hK hX ha hb u.2 v.2
            (not_and_or.mp hpq), bidegreeComponent_tmul_of_ne X u.2 v.2
            (fun h ↦ hpq ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩), map_zero]

/-- `(-1)^{i(2d - i)} = (-1)^i`. -/
private theorem negOnePow_mul_two_mul_sub (i d : ℤ) :
    (i * (2 * d - i)).negOnePow = i.negOnePow := by
  rw [show i * (2 * d - i) = 2 * (i * d) - i * i by ring, Int.negOnePow_sub,
    Int.negOnePow_two_mul, Int.negOnePow_mul_self, one_mul]

/-- **Stacks Project, Tag 0FHH.** Assume given (D0), (D1), (D2), (D3) satisfying (A), (B) and
(C). Let `X` be a nonempty smooth projective scheme over `k`, equidimensional of dimension `d`,
and let `e_{i,1}, …, e_{i,β_i}` be a basis of `H^i(X)` over `F`. Write, using the Künneth formula,
the `(i, 2d - i)` component of the cohomology class of the diagonal as
`γ([Δ])_{(i, 2d - i)} = ∑_j e_{i,j} ⊗ e'_{2d-i,j}` in `H^i(X) ⊗_F H^{2d-i}(X)(d)`. Then
`∫_X e_{i,j} ∪ e'_{2d-i,j'} = (-1)^i δ_{jj'}`.

Here `[Δ] ∈ CH^d(X × X)` is the class of the diagonal, a closed subscheme of codimension `d`
(`Stacks.WeilCohomology.closedSubschemeClass`), `γ([Δ]) ∈ H^{2d}(X × X)(d)` its cohomology class,
and its components in `⨁_i H^i(X) ⊗_F H^{2d-i}(X)(d)` are those of the Künneth isomorphism
of axiom (B)(a) (`WeilData.kunnethComponentTw`). The proof is the source's: `γ([Δ]) = Δ_*1`
(Stacks 0FHG, from 0FHF), so `∫_{X × X} (a ⊗ b) ∪ γ([Δ]) = ∫_X a ∪ b` by the trace equation of
the pushforward and Remark 0FHD; axiom (B)(b) evaluates the same trace on the Künneth decomposition
as `∑_j (∫_X a ∪ e_{i,j})(∫_X e'_{2d-i,j} ∪ b)`; and Poincaré duality (A)(b) makes `e'` the dual
basis. -/
@[stacks 0FHH "under (D0)–(D3), (A), (B), (C): any family e' with γ([Δ])_(i,2d-i) = ∑ e ⊗ e', \
  for the actual cycle class γ([Δ]) of the diagonal, is the signed dual basis; the expansion \
  ∫ a ∪ b = ∑ (∫ a ∪ e)(∫ e' ∪ b) is derived, not assumed"]
theorem pairing_kunnethComponentTw_diagonal (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (i : ℤ) {J : Type*} [Fintype J]
    [DecidableEq J] (e : Module.Basis J F (W.grade X i)) (e' : J → W.Tw X (2 * d - i) d)
    (he : kunnethComponentTw X hB.kunnethIsomorphism (2 * d) d i (2 * d - i)
        (W.cycleClass (SmoothProjectiveScheme.prod X X) d
          (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
            (SmoothProjectiveScheme.diag X).hom.left d)) =
      ∑ j, e j ⊗ₜ e' j)
    (j j' : J) :
    W.pairing X d hX i (2 * d - i) (by ring) (e j) (e' j') =
      ((i.negOnePow : ℤ) : F) * if j = j' then 1 else 0 := by
  set hP := SmoothProjectiveScheme.isNonemptyEquidimensional_prod hX hX
  -- `γ([Δ]) = Δ_*1`, Stacks 0FHG for the diagonal
  have hγ := W.cycleClass_diagonal_eq_pushforward_one hA hB hC hX hP
  set γΔ := W.cycleClass (SmoothProjectiveScheme.prod X X) d
    (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
      (SmoothProjectiveScheme.diag X).hom.left d)
  set G : W.H (SmoothProjectiveScheme.prod X X) :=
    (W.twCoord (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)) d γΔ).1
  -- `γ([Δ])` represents the trace pairing through the diagonal
  have hG : ∀ y ∈ W.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)),
      W.traceProj X d hX (W.pull (SmoothProjectiveScheme.diag X) y) =
        W.traceProj _ (d + d) hP (y * G) := fun y hy ↦ by
    rw [traceProj_pull_diag hA.perfectPairing hX hy]
    simp only [G, γΔ, hγ]
  -- the Künneth preimage of `γ([Δ])`
  set x := (LinearEquiv.ofBijective (W.kunnethMap X X)
    (hB.kunnethIsomorphism X X)).symm G
  have hx : W.kunnethMap X X x = G :=
    (LinearEquiv.ofBijective (W.kunnethMap X X) (hB.kunnethIsomorphism X X)).apply_symm_apply G
  have hcomp : bidegreeComponent X i (2 * d - i) x =
      ∑ l, e l ⊗ₜ (W.twCoord X (2 * d - i) d (e' l)) := by
    rw [← kunnethComponent_kunnethMap X hB.kunnethIsomorphism, hx,
      ← map_twCoord_kunnethComponentTw, he, map_sum]
    rfl
  -- the expansion `∫ a ∪ b = ∑_l (∫ a ∪ e_l)(∫ e'_l ∪ b)`
  have hdecomp : ∀ a ∈ W.grade X (2 * d - i), ∀ b ∈ W.grade X i,
      W.traceProj X d hX (a * b) = ∑ l, W.traceProj X d hX (a * e l) *
        W.traceProj X d hX ((W.twCoord X (2 * d - i) d (e' l) : W.H X) * b) := by
    intro a ha b hb
    have hab : W.pull (SmoothProjectiveScheme.fst X X) a *
        W.pull (SmoothProjectiveScheme.snd X X) b ∈
          W.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)) :=
      W.mul_mem_grade_of_add_eq (W.pull_grade (SmoothProjectiveScheme.fst X X) _ _ ha)
        (W.pull_grade (SmoothProjectiveScheme.snd X X) _ _ hb) (by ring)
    rw [← W.pull_diag_mul X a b, hG _ hab, ← hx,
      traceProj_mul_kunnethMap hX hB.kunnethTrace ha hb, hcomp, map_sum]
    rfl
  have hdual := traceProj_mul_basis hA.perfectPairing hX i e
    (fun l ↦ (W.twCoord X (2 * d - i) d (e' l) : W.H X)) (fun l ↦ (W.twCoord X _ _ (e' l)).2)
    hdecomp j' j
  rw [pairing_eq_traceProj, W.traceProj_mul_comm X d hX (e j).2 (W.twCoord X _ _ (e' j')).2,
    hdual, negOnePow_mul_two_mul_sub]
  by_cases h : j = j'
  · simp [h]
  · simp [h, Ne.symm h]

variable (W) in
/-- **The Künneth coordinates `e'_{2d-i,j}` of the class of the diagonal** with respect to a
basis `e` of `H^i(X)`: the unique family in `H^{2d-i}(X)(d)` with
`γ([Δ])_{(i, 2d - i)} = ∑_j e_{i,j} ⊗ e'_{2d-i,j}`
(`WeilData.kunnethComponentTw_diagonal_eq_sum`). -/
def diagonalKunnethCoordinates (hBa : W.KunnethIsomorphism)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (i : ℤ) {J : Type*} [DecidableEq J] (e : Module.Basis J F (W.grade X i)) (j : J) :
    W.Tw X (2 * d - i) d :=
  TensorProduct.equivFinsuppOfBasisLeft e
    (kunnethComponentTw X hBa (2 * d) d i (2 * d - i)
      (W.cycleClass (SmoothProjectiveScheme.prod X X) d
        (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
          (SmoothProjectiveScheme.diag X).hom.left d))) j

omit hX in
/-- The Künneth decomposition of the class of the diagonal in bidegree `(i, 2d - i)`:
`γ([Δ])_{(i, 2d - i)} = ∑_j e_{i,j} ⊗ e'_{2d-i,j}`. -/
theorem kunnethComponentTw_diagonal_eq_sum (hBa : W.KunnethIsomorphism) (i : ℤ) {J : Type*}
    [Fintype J] [DecidableEq J] (e : Module.Basis J F (W.grade X i)) :
    kunnethComponentTw X hBa (2 * d) d i (2 * d - i)
        (W.cycleClass (SmoothProjectiveScheme.prod X X) d
          (closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
            (SmoothProjectiveScheme.diag X).hom.left d)) =
      ∑ j, e j ⊗ₜ W.diagonalKunnethCoordinates hBa X d i e j := by
  rw [← (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply
    (kunnethComponentTw X hBa (2 * d) d i (2 * d - i) _),
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

/-- **Stacks Project, Tag 0FHH**, for the Künneth coordinates themselves: with
`e'_{2d-i,j} = WeilData.diagonalKunnethCoordinates`, the coordinates of `γ([Δ])` in bidegree
`(i, 2d - i)` with respect to the basis `e` of `H^i(X)`,
`∫_X e_{i,j} ∪ e'_{2d-i,j'} = (-1)^i δ_{jj'}`. -/
@[stacks 0FHH "the Künneth coordinates of the actual cycle class γ([Δ]) with respect to a basis \
  of H^i(X) are the signed dual basis"]
theorem pairing_diagonalKunnethCoordinates (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (i : ℤ) {J : Type*} [Finite J]
    [DecidableEq J] (e : Module.Basis J F (W.grade X i)) (j j' : J) :
    W.pairing X d hX i (2 * d - i) (by ring) (e j)
        (W.diagonalKunnethCoordinates hB.kunnethIsomorphism X d i e j') =
      ((i.negOnePow : ℤ) : F) * if j = j' then 1 else 0 :=
  letI := Fintype.ofFinite J
  pairing_kunnethComponentTw_diagonal hX hA hB hC i e _
    (kunnethComponentTw_diagonal_eq_sum hB.kunnethIsomorphism i e) j j'

end DualBasis

end WeilData

end Stacks.WeilCohomology

end
