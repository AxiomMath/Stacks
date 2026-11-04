module

public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataIsoTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.RingTheory.GradedAlgebra.AlgEquivOfGrade
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Isomorphisms of Weil data from compatible isomorphisms of graded cohomology

Let `W` and `W'` be data (D0)–(D3) satisfying (A), (B), (C) (Section 0FHA). This file proves
that `W` and `W'` are isomorphic (`Stacks.WeilCohomology.WeilData.IsIsomorphic`) as soon as there
are isomorphisms `Θ : H^n(X) ≅ H'^n(X)` in every degree which commute with pullbacks and cup
products, send `1` to `1`, and are compatible with the operations
`a ↦ (∫_X a) · γ(β)`, `H^{2d}(X) → H^{2d}(Y)`, for `X` nonempty equidimensional of dimension `d`
and `β ∈ CH^d(Y)`, in coordinates of the Tate lines
(`Stacks.WeilCohomology.WeilData.GradedIso.isIsomorphic`). These operations are the actions on
cohomology of the correspondences `pr₂^!β ∈ Corr⁰(X, Y)` in the realization of Stacks 0FHL; this
is how the proof of Stacks 0FHM recovers data (D0)–(D3) from the functor they define.

The Tate lines are matched through a test curve `P` with a class `p ∈ CH¹(P)` of trace `1` (in the
application, `𝐏¹_k` and a rational point): `Θ(γ(p)) = λ γ'(p)` for the scalar
`λ = ∫'_P Θ(γ(p))`, and on the powers `Q_d = P × ⋯ × P` and the classes `p × ⋯ × p` one gets
`∫' ∘ Θ = λ^d ∫` in dimension `d` and `Θ ∘ γ = λ^i γ'` in codimension `i`. Scaling the
coordinate of `F(1)` by `λ⁻¹` then gives an isomorphism `F(1) ≅ F(1)'` for which `Θ` preserves
the cycle class maps and the trace maps.

## Main definitions

* `Stacks.WeilCohomology.WeilData.GradedIso`: degreewise isomorphisms commuting with pullbacks,
  cup products and units.
* `Stacks.WeilCohomology.WeilData.GradedIso.toIso`: the isomorphism of data (D0)–(D3) they
  induce, given an isomorphism of the Tate lines.

## Main results

* `Stacks.WeilCohomology.codimensionChowGroup_eq_zero_of_neg`: `CH^i(X) = 0` for `i < 0`.
* `Stacks.WeilCohomology.WeilData.GradedIso.isIsomorphic`: the criterion.

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F]

/-- **`CH^i(X) = 0` for `i < 0`**: a smooth scheme of constant dimension `d` has no cycles of
dimension `> d`. -/
theorem codimensionChowGroup_eq_zero_of_neg (X : (SmoothProjectiveScheme k).FullSubcategory) {i : ℤ}
    (hi : i < 0) (β : codimensionChowGroup k X.obj.hom i) : β = 0 := by
  funext d
  refine chowGroup_eq_zero (fieldChowSituation k) (partBase X.obj.hom d) (fun x ↦ ?_) (β d)
  have hδ := schemeDeltaDimension_le_of_relativeDimension (partBase X.obj.hom d)
    (relativeDimension_partBase X.obj.hom d)
  have h := relativeDimension_le_of_schemeDeltaDimension_le (fieldChowSituation k)
    (partBase X.obj.hom d) (𝟙 _) (k := (d : ℤ)) (by simpa only [Category.id_comp] using hδ) x
  have h' : relativeDimension (fieldChowSituation k).dimensionFunction (partBase X.obj.hom d) x ≤
      d := h
  omega

namespace WeilData

variable (W : WeilData k F)

/-! ### The axioms in coordinates -/

/-- Axiom (C)(a) in coordinates. -/
theorem cycleClassCoord_codimensionGysin (hCa : W.CycleClassPullback)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
    (β : codimensionChowGroup k Y.obj.hom i) :
    W.cycleClassCoord X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) =
      W.pullDeg f (2 * i) (W.cycleClassCoord Y i β) := by
  rw [cycleClassCoord_apply, hCa, twCoord_pullTw, cycleClassCoord_apply]

/-- Axiom (C)(c) in coordinates. -/
theorem coe_cycleClassCoord_intersection (hCc : W.CycleClassMul)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    (W.cycleClassCoord X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) : W.H X) =
      W.cycleClassCoord X i α * W.cycleClassCoord X j β := by
  rw [cycleClassCoord_apply, hCc, twCoord_cupTw]
  rfl

/-- For `a ∈ H^{2d}(X)` and `b ∈ H^{2e}(Y)`, the cup product `pr₁^*a ∪ pr₂^*b` lies in
`H^{2(d+e)}(X × Y)`. -/
theorem pull_fst_mul_pull_snd_mem {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (a : W.grade X (2 * (d : ℤ))) (b : W.grade Y (2 * (e : ℤ))) :
    W.pull (fst X Y) a * W.pull (snd X Y) b ∈ W.grade (prod X Y) (2 * ((d + e : ℕ) : ℤ)) := by
  have h := SetLike.GradedMul.mul_mem (W.pull_grade (fst X Y) _ _ a.2)
    (W.pull_grade (snd X Y) _ _ b.2)
  rwa [show 2 * (d : ℤ) + 2 * (e : ℤ) = 2 * ((d + e : ℕ) : ℤ) by push_cast; ring] at h

/-- Axiom (B)(b) in coordinates, on the component `H^{2d}(X) ⊗ H^{2e}(Y)`. -/
theorem traceCoord_pull_fst_mul_pull_snd (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (prod X Y) (d + e)) (a : W.grade X (2 * (d : ℤ)))
    (b : W.grade Y (2 * (e : ℤ))) :
    W.traceCoord (prod X Y) (d + e) hXY ⟨_, W.pull_fst_mul_pull_snd_mem a b⟩ =
      W.traceCoord X d hX a * W.traceCoord Y e hY b := by
  have h := (hK X Y d e hX hY hXY).1 ((W.twCoord X _ _).symm a) ((W.twCoord Y _ _).symm b)
  rw [trace_eq_traceCoord, trace_eq_traceCoord, trace_eq_traceCoord, twCoord_cupTw,
    twCoord_pullTw, twCoord_pullTw, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  rw [← h]
  rfl

/-- `γ([X]) = 1` in coordinates (Stacks 0FHF). -/
theorem coe_cycleClassCoord_fundamentalClass (hBa : W.KunnethIsomorphism)
    (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (W.cycleClassCoord X 0 (fundamentalClass X) : W.H X) = 1 := by
  rw [cycleClassCoord_apply, cycleClass_fundamentalClass hBa hCa hCc hCd]
  exact W.coe_twCoord_unitTw X 0 0 rfl

/-! ### Degreewise isomorphisms -/

variable {W} {W' : WeilData k F}

/-- **Degreewise isomorphisms of cohomology** `H^n(X) ≅ H'^n(X)` commuting with pullbacks, cup
products and units. -/
structure GradedIso (W W' : WeilData k F) where
  /-- The isomorphisms `H^n(X) ≅ H'^n(X)`. -/
  e : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ), W.grade X n ≃ₗ[F] W'.grade X n
  /-- They commute with pullbacks. -/
  e_pull : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : W.grade Y n),
    e X n (W.pullDeg f n a) = W'.pullDeg f n (e Y n a)
  /-- They commute with cup products. -/
  e_mul : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ) (a : W.grade X i)
    (b : W.grade X j),
    (e X (i + j) ⟨a * b, SetLike.GradedMul.mul_mem a.2 b.2⟩ : W'.H X) = e X i a * e X j b
  /-- They send `1` to `1`. -/
  e_one : ∀ X, (e X 0 ⟨1, SetLike.GradedOne.one_mem⟩ : W'.H X) = 1

namespace GradedIso

variable (Θ : GradedIso W W')

/-- `Θ` is compatible with transporting a homogeneous element along an equality of degrees. -/
theorem coe_e_congr (X : (SmoothProjectiveScheme k).FullSubcategory) {n m : ℤ} (h : n = m)
    (x : W.H X) (hx : x ∈ W.grade X n) : (Θ.e X n ⟨x, hx⟩ : W'.H X) = Θ.e X m ⟨x, h ▸ hx⟩ := by
  subst h
  rfl

/-- `Θ` sends an element of degree `0` equal to `1` to `1`. -/
theorem coe_e_eq_one (X : (SmoothProjectiveScheme k).FullSubcategory) {n : ℤ} (hn : n = 0)
    (x : W.grade X n) (hx : (x : W.H X) = 1) : (Θ.e X n x : W'.H X) = 1 := by
  subst hn
  obtain ⟨x, hx'⟩ := x
  simp only at hx
  subst hx
  exact Θ.e_one X

/-- If `x ∈ H^n(X)` is the product `y * z` of `y ∈ H^i(X)` and `z ∈ H^j(X)` with `i + j = n`, then
`Θ(x) = Θ(y) * Θ(z)`. -/
theorem coe_e_of_coe_eq_mul (X : (SmoothProjectiveScheme k).FullSubcategory) {i j n : ℤ}
    (h : i + j = n) (x : W.grade X n) (y : W.grade X i) (z : W.grade X j)
    (hx : (x : W.H X) = y * z) :
    (Θ.e X n x : W'.H X) = Θ.e X i y * Θ.e X j z := by
  subst h
  have : x = ⟨y * z, SetLike.GradedMul.mul_mem y.2 z.2⟩ := Subtype.ext hx
  rw [this]
  exact Θ.e_mul X i j y z

/-- The isomorphism of cohomology algebras `H^*(X) ≅ H'^*(X)` assembled from `Θ`. -/
def algEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) : W.H X ≃ₐ[F] W'.H X :=
  GradedAlgebra.algEquivOfGrade (Θ.e X) (Θ.e_mul X) (Θ.e_one X)

/-- On a homogeneous element of degree `n`, `Θ.algEquiv X` is the isomorphism `Θ.e X n`. -/
theorem algEquiv_apply_of_mem (X : (SmoothProjectiveScheme k).FullSubcategory) {n : ℤ} {a : W.H X}
    (ha : a ∈ W.grade X n) : Θ.algEquiv X a = Θ.e X n ⟨a, ha⟩ :=
  GradedAlgebra.algEquivOfGrade_apply_of_mem _ _ _ ha

/-- The isomorphism of data (D0)–(D3) given by `Θ` and an isomorphism `t` of the Tate lines. -/
def toIso (t : W.tate ≃ₗ[F] W'.tate) : Iso W W' where
  tateEquiv := t
  equiv := Θ.algEquiv
  map_grade X n := GradedAlgebra.map_algEquivOfGrade _ _ _ n
  equiv_pull {X Y} f a := by
    induction a using DirectSum.Decomposition.inductionOn (W.grade Y) with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | homogeneous ha =>
      rw [Θ.algEquiv_apply_of_mem X (W.pull_grade f _ _ ha.2), Θ.algEquiv_apply_of_mem Y ha.2]
      exact congrArg Subtype.val (Θ.e_pull f _ ⟨_, ha.2⟩)

/-- The isomorphism of Tate lines of `Θ.toIso t` is `t`. -/
@[simp]
theorem toIso_tateEquiv (t : W.tate ≃ₗ[F] W'.tate) : (Θ.toIso t).tateEquiv = t :=
  rfl

/-- In degree `n`, the isomorphism of cohomology of `Θ.toIso t` is `Θ.e X n`. -/
theorem gradeEquiv_toIso (t : W.tate ≃ₗ[F] W'.tate) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (n : ℤ) :
    (Θ.toIso t).gradeEquiv X n = Θ.e X n :=
  LinearEquiv.ext fun a ↦ Subtype.ext (Θ.algEquiv_apply_of_mem X a.2)

/-- **Compatibility with the operations `a ↦ (∫_X a) γ(β)`**, in coordinates: for `X` nonempty
equidimensional of dimension `d`, `Y` nonempty equidimensional, `β ∈ CH^d(Y)` and `a ∈ H^{2d}(X)`,
`(∫_X a) Θ(γ(β)) = (∫'_X Θ(a)) γ'(β)`. -/
def CorrCompatible : Prop :=
  ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d m : ℕ)
    (hX : IsNonemptyEquidimensional X d) (_ : IsNonemptyEquidimensional Y m)
    (β : codimensionChowGroup k Y.obj.hom d)
    (a : W.grade X (2 * (d : ℤ))),
    W.traceCoord X d hX a • Θ.e Y (2 * d) (W.cycleClassCoord Y d β) =
      W'.traceCoord X d hX (Θ.e X (2 * d) a) • W'.cycleClassCoord Y d β

end GradedIso

/-! ### Products of test classes -/

/-- In coordinates, `γ(pr₁^!e · pr₂^!p) = pr₁^*γ(e) ∪ pr₂^*γ(p)` on `Q × P`, for `e ∈ CH^d(Q)`
and `p ∈ CH¹(P)`. -/
theorem coe_cycleClassCoord_intersection_gysin (hC : W.CycleClassPullback) (hCc : W.CycleClassMul)
    (Q P : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (e : codimensionChowGroup k Q.obj.hom d) (p : codimensionChowGroup k P.obj.hom 1) :
    (W.cycleClassCoord (prod Q P) ((d + 1 : ℕ) : ℤ) (codimensionIntersectionProduct k
        (prod Q P).obj.hom d 1 (codimensionGysin _ _ (Over.w (fst Q P).hom) d e)
        (codimensionGysin _ _ (Over.w (snd Q P).hom) 1 p)) : W.H (prod Q P)) =
      W.pull (fst Q P) (W.cycleClassCoord Q d e) * W.pull (snd Q P) (W.cycleClassCoord P 1 p) := by
  show ((W.cycleClassCoord (prod Q P) ((d : ℤ) + 1) (codimensionIntersectionProduct k
    (prod Q P).obj.hom d 1 _ _) : W.grade (prod Q P) (2 * ((d : ℤ) + 1))) : W.H (prod Q P)) = _
  rw [coe_cycleClassCoord_intersection W hCc, cycleClassCoord_codimensionGysin W hC,
    cycleClassCoord_codimensionGysin W hC]
  rfl

/-- The trace of `γ(pr₁^!e · pr₂^!p)` on `Q × P` is `1` if `γ(e)` and `γ(p)` have trace `1`. -/
private theorem trace_cycleClassCoord_intersection_gysin (hK : W.KunnethTrace)
    (hC : W.CycleClassPullback) (hCc : W.CycleClassMul)
    {Q P : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hQ : IsNonemptyEquidimensional Q d) (hP : IsNonemptyEquidimensional P 1)
    (hQP : IsNonemptyEquidimensional (prod Q P) (d + 1))
    (e : codimensionChowGroup k Q.obj.hom d) (p : codimensionChowGroup k P.obj.hom 1)
    (h₁ : W.traceCoord Q d hQ (W.cycleClassCoord Q d e) = 1)
    (h₂ : W.traceCoord P 1 hP (W.cycleClassCoord P ((1 : ℕ) : ℤ) p) = 1) :
    W.traceCoord (prod Q P) (d + 1) hQP (W.cycleClassCoord (prod Q P) ((d + 1 : ℕ) : ℤ)
      (codimensionIntersectionProduct k (prod Q P).obj.hom d 1
        (codimensionGysin _ _ (Over.w (fst Q P).hom) d e)
        (codimensionGysin _ _ (Over.w (snd Q P).hom) 1 p))) = 1 := by
  have h := traceCoord_pull_fst_mul_pull_snd W hK hQ hP hQP
    (W.cycleClassCoord Q d e) (W.cycleClassCoord P ((1 : ℕ) : ℤ) p)
  rw [h₁, h₂, one_mul] at h
  refine Eq.trans ?_ h
  exact congrArg (W.traceCoord (prod Q P) (d + 1) hQP)
    (Subtype.ext (coe_cycleClassCoord_intersection_gysin hC hCc Q P d e p))

/-- A unit to an integer power times its inverse to the same power is `1`, in the field. -/
private theorem val_inv_zpow_mul_val_zpow (u : Fˣ) (n : ℤ) :
    ((u⁻¹ ^ n : Fˣ) : F) * ((u ^ n : Fˣ) : F) = 1 := by
  rw [← Units.val_mul, ← mul_zpow, inv_mul_cancel, one_zpow, Units.val_one]

/-! ### The criterion -/

namespace GradedIso

variable (Θ : GradedIso W W') (P : (SmoothProjectiveScheme k).FullSubcategory)
  (hP : IsNonemptyEquidimensional P 1) (p : codimensionChowGroup k P.obj.hom 1)

/-- The scalar `λ = ∫'_P Θ(γ(p))`. -/
def scalar : F :=
  W'.traceCoord P 1 hP (Θ.e P (2 * ((1 : ℕ) : ℤ)) (W.cycleClassCoord P ((1 : ℕ) : ℤ) p))

variable {Θ P hP p}
variable (hΘ : Θ.CorrCompatible)
  (hpW : W.traceCoord P 1 hP (W.cycleClassCoord P ((1 : ℕ) : ℤ) p) = 1)
  (hpW' : W'.traceCoord P 1 hP (W'.cycleClassCoord P ((1 : ℕ) : ℤ) p) = 1)
include hΘ hpW

/-- `Θ(γ(p)) = λ γ'(p)` for the scalar `λ = ∫'_P Θ(γ(p))`. -/
theorem e_cycleClassCoord_p :
    Θ.e P (2 * ((1 : ℕ) : ℤ)) (W.cycleClassCoord P ((1 : ℕ) : ℤ) p) =
      Θ.scalar P hP p • W'.cycleClassCoord P ((1 : ℕ) : ℤ) p := by
  have h := hΘ P P 1 1 hP hP p (W.cycleClassCoord P ((1 : ℕ) : ℤ) p)
  rwa [hpW, one_smul] at h

variable (hBa : W.KunnethIsomorphism) (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul)
  (hCd : W.CycleClassPoint) (hBa' : W'.KunnethIsomorphism) (hCa' : W'.CycleClassPullback)
  (hCc' : W'.CycleClassMul) (hCd' : W'.CycleClassPoint)
include hBa hCa hCc hCd hBa' hCa' hCc' hCd' hpW'

/-- **The test classes.** In every dimension `d` there is a nonempty equidimensional `Q`
of dimension `d` (namely `P × ⋯ × P`) with a class `e ∈ CH^d(Q)` (namely `p × ⋯ × p`) of trace `1`
for `W` and for `W'`, such that `Θ(γ(e)) = λ^d γ'(e)`. -/
theorem exists_testClass (hB : W.Kunneth) (hB' : W'.Kunneth) :
    ∀ d : ℕ, ∃ (Q : (SmoothProjectiveScheme k).FullSubcategory) (hQ : IsNonemptyEquidimensional Q d)
      (e : codimensionChowGroup k Q.obj.hom d),
      W.traceCoord Q d hQ (W.cycleClassCoord Q d e) = 1 ∧
      W'.traceCoord Q d hQ (W'.cycleClassCoord Q d e) = 1 ∧
      Θ.e Q (2 * (d : ℤ)) (W.cycleClassCoord Q d e) = Θ.scalar P hP p ^ d • W'.cycleClassCoord Q d e
  | 0 => by
    refine ⟨point k, isNonemptyEquidimensional_point, fundamentalClass (point k), ?_, ?_, ?_⟩
    · rw [← hCd, trace_eq_traceCoord]
      rfl
    · rw [← hCd', trace_eq_traceCoord]
      rfl
    · apply Subtype.ext
      rw [pow_zero, one_smul, Θ.coe_e_eq_one (point k) (n := 2 * ((0 : ℕ) : ℤ)) (by simp) _
        (by exact coe_cycleClassCoord_fundamentalClass W hBa hCa hCc hCd (point k))]
      exact (coe_cycleClassCoord_fundamentalClass W' hBa' hCa' hCc' hCd' (point k)).symm
  | d + 1 => by
    obtain ⟨Q, hQ, e, h₁, h₂, h₃⟩ := exists_testClass hB hB' d
    have hQP := isNonemptyEquidimensional_prod hQ hP
    refine ⟨prod Q P, hQP, codimensionIntersectionProduct k (prod Q P).obj.hom d 1
      (codimensionGysin _ _ (Over.w (fst Q P).hom) d e)
      (codimensionGysin _ _ (Over.w (snd Q P).hom) 1 p), ?_, ?_, ?_⟩
    · exact trace_cycleClassCoord_intersection_gysin hB.kunnethTrace hCa hCc hQ hP hQP e p h₁ hpW
    · exact trace_cycleClassCoord_intersection_gysin hB'.kunnethTrace hCa' hCc' hQ hP hQP e p h₂
        hpW'
    · apply Subtype.ext
      rw [SetLike.val_smul, Θ.coe_e_of_coe_eq_mul _
        (show 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ) by push_cast; ring) _
        (W.pullDeg (fst Q P) _ (W.cycleClassCoord Q d e))
        (W.pullDeg (snd Q P) _ (W.cycleClassCoord P ((1 : ℕ) : ℤ) p))
        (coe_cycleClassCoord_intersection_gysin hCa hCc Q P d e p),
        Θ.e_pull, Θ.e_pull, h₃, e_cycleClassCoord_p hΘ hpW,
        coe_cycleClassCoord_intersection_gysin hCa' hCc' Q P d e p, map_smul, map_smul,
        SetLike.val_smul, SetLike.val_smul, coe_pullDeg, coe_pullDeg, smul_mul_smul_comm,
        pow_succ]
      rfl

/-- **`∫' ∘ Θ = λ^d ∫`** on `H^{2d}(X)` for `X` nonempty equidimensional of dimension `d`. -/
theorem traceCoord_e (hB : W.Kunneth) (hB' : W'.Kunneth)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (a : W.grade X (2 * (d : ℤ))) :
    W'.traceCoord X d hX (Θ.e X (2 * d) a) = Θ.scalar P hP p ^ d * W.traceCoord X d hX a := by
  obtain ⟨Q, hQ, e, -, h₂, h₃⟩ :=
    exists_testClass hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB' d
  have h := congrArg (W'.traceCoord Q d hQ) (hΘ X Q d d hX hQ e a)
  rw [h₃, smul_smul, map_smul, map_smul, h₂, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
  rw [← h, mul_comm]

/-- **`Θ ∘ γ = λ^i γ'`** on `CH^i(Y)`, `i ≥ 0`, for `Y` nonempty equidimensional. -/
theorem e_cycleClassCoord_of_equidimensional (hB : W.Kunneth) (hB' : W'.Kunneth)
    (Y : (SmoothProjectiveScheme k).FullSubcategory) {m : ℕ} (hY : IsNonemptyEquidimensional Y m)
    (i : ℕ) (β : codimensionChowGroup k Y.obj.hom i) :
    Θ.e Y (2 * (i : ℤ)) (W.cycleClassCoord Y i β) =
      Θ.scalar P hP p ^ i • W'.cycleClassCoord Y i β := by
  obtain ⟨Q, hQ, e, h₁, h₂, h₃⟩ :=
    exists_testClass hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB' i
  have h := hΘ Q Y i m hQ hY β (W.cycleClassCoord Q i e)
  rwa [h₁, one_smul, h₃, map_smul, h₂, smul_eq_mul, mul_one] at h

/-- **`Θ ∘ γ = λ^i γ'`** on `CH^i(Y)`, `i ≥ 0`, for every `Y`: on each part `Y_m` of `Y` of
dimension `m`, by (C)(a) for the inclusion and the equidimensional case, and a class of `H^*(Y)`
is determined by its restrictions to the parts (Stacks 0FHJ). -/
theorem e_cycleClassCoord [CharZero F] (hB : W.Kunneth) (hB' : W'.Kunneth)
    (hA' : W'.PoincareDuality) (hC' : W'.CycleClassAxiom hA'.perfectPairing)
    (Y : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
    (β : codimensionChowGroup k Y.obj.hom i) :
    Θ.e Y (2 * (i : ℤ)) (W.cycleClassCoord Y i β) =
      Θ.scalar P hP p ^ i • W'.cycleClassCoord Y i β := by
  apply Subtype.ext
  refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero (hA := hA') (hB := hB') (hC := hC')
    (partSupport Y) (fun m ↦ partι Y m) (exists_mem_partSupport Y) fun m hm ↦ ?_)
  have hY := isNonemptyEquidimensional_part Y (nonempty_part_iff.2 (mem_partSupport.1 hm))
  have h₁ := Θ.e_pull (partι Y m) _ (W.cycleClassCoord Y i β)
  rw [← cycleClassCoord_codimensionGysin W hCa,
    e_cycleClassCoord_of_equidimensional hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB'
      (part Y m) hY i, cycleClassCoord_codimensionGysin W' hCa'] at h₁
  rw [map_sub, sub_eq_zero, SetLike.val_smul, map_smul, ← coe_pullDeg, ← coe_pullDeg, ← h₁,
    SetLike.val_smul]

/-- The scalar `λ = ∫'_P Θ(γ(p))` is nonzero. -/
theorem scalar_ne_zero (hB : W.Kunneth) (hB' : W'.Kunneth) : Θ.scalar P hP p ≠ 0 := by
  have h := traceCoord_e hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB' P 1 hP
    ((Θ.e P (2 * ((1 : ℕ) : ℤ))).symm (W'.cycleClassCoord P ((1 : ℕ) : ℤ) p))
  rw [LinearEquiv.apply_symm_apply, hpW', pow_one] at h
  exact left_ne_zero_of_mul (h ▸ one_ne_zero)

/-- **The criterion.** Degreewise isomorphisms `Θ` of cohomology commuting with pullbacks, cup
products and units, and compatible with the operations `a ↦ (∫_X a) γ(β)`, are the isomorphisms
of cohomology of an isomorphism of data (D0)–(D3) preserving the cycle class maps and the trace
maps; the isomorphism `F(1) ≅ F(1)'` is the coordinate of `F(1)` scaled by `λ⁻¹`, for a test
curve `P` with a class `p ∈ CH¹(P)` of trace `1`. -/
theorem isIsomorphic [CharZero F] (hB : W.Kunneth) (hB' : W'.Kunneth) (hA' : W'.PoincareDuality)
    (hC' : W'.CycleClassAxiom hA'.perfectPairing) : W.IsIsomorphic W' := by
  set u : Fˣ := Units.mk0 (Θ.scalar P hP p)
    (scalar_ne_zero hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB') with hu
  set t : W.tate ≃ₗ[F] W'.tate := (tateLineCoordinate W.finrank_tate).trans
    ((LinearEquiv.smulOfUnit u⁻¹).trans (tateLineCoordinate W'.finrank_tate).symm)
  have ht : t.trans (tateLineCoordinate W'.finrank_tate) =
      (tateLineCoordinate W.finrank_tate).trans (LinearEquiv.smulOfUnit u⁻¹) :=
    LinearEquiv.ext fun l ↦ by simp [t]
  have key : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) (x : W.Tw X n m),
      W'.twCoord X n m ((Θ.toIso t).twEquiv X n m x) =
        ((u⁻¹ ^ m : Fˣ) : F) • Θ.e X n (W.twCoord X n m x) := by
    intro X n m x
    rw [twCoord, Iso.twEquiv, tateTwistCoordinates_tateTwistCongr, toIso_tateEquiv, ht,
      tateTwistCoordinates_smulOfUnit, map_smul, gradeEquiv_toIso]
    rfl
  have hcancel : ∀ n : ℕ, ((u⁻¹ ^ (n : ℤ) : Fˣ) : F) * Θ.scalar P hP p ^ n = 1 := fun n ↦ by
    simpa [hu] using val_inv_zpow_mul_val_zpow u n
  refine ⟨Θ.toIso t, fun X i α ↦ ?_, fun X d hX a ↦ ?_⟩
  · apply (W'.twCoord X _ _).injective
    rw [key]
    rcases le_or_gt 0 i with hi | hi
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      show W'.cycleClassCoord X n α = _ • Θ.e X (2 * (n : ℤ)) (W.cycleClassCoord X n α)
      rw [e_cycleClassCoord hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB' hA' hC' X n α,
        smul_smul, hcancel, one_smul]
    · rw [codimensionChowGroup_eq_zero_of_neg X hi α]
      simp
  · rw [trace_eq_traceCoord, trace_eq_traceCoord, key, map_smul,
      traceCoord_e hΘ hpW hpW' hBa hCa hCc hCd hBa' hCa' hCc' hCd' hB hB' X d hX, smul_eq_mul,
      ← mul_assoc, hcancel, one_mul]

end GradedIso

/-! ### The converse: isomorphisms of Weil data in coordinates -/

namespace Iso

variable (e : Iso W W')

/-- The degreewise isomorphisms of cohomology of an isomorphism of data (D0)–(D3). -/
def toGradedIso : GradedIso W W' where
  e := e.gradeEquiv
  e_pull f n a := e.gradeEquiv_pullDeg f n a
  e_mul X _ _ _ _ := map_mul (e.equiv X) _ _
  e_one X := map_one (e.equiv X)

/-- The degreewise isomorphisms of `e.toGradedIso` are `e.gradeEquiv`. -/
@[simp]
theorem toGradedIso_e (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    e.toGradedIso.e X n = e.gradeEquiv X n :=
  rfl

/-- The ratio of the coordinates of `F(1)'` and `F(1)` along `e`: the image of the coordinate
vector of `F(1)` under `F(1) ≅ F(1)'`, read in the coordinate of `F(1)'`. -/
def coordRatio : Fˣ :=
  Units.mk0 (tateLineCoordinate W'.finrank_tate
      (e.tateEquiv ((tateLineCoordinate W.finrank_tate).symm 1)))
    (by simp)

/-- In the coordinates of the Tate lines, the isomorphism `F(1) ≅ F(1)'` of `e` is multiplication
by the coordinate ratio `e.coordRatio`. -/
theorem tateEquiv_trans_coordinate :
    e.tateEquiv.trans (tateLineCoordinate W'.finrank_tate) =
      (tateLineCoordinate W.finrank_tate).trans (LinearEquiv.smulOfUnit e.coordRatio) := by
  refine LinearEquiv.ext fun l ↦ ?_
  set c := tateLineCoordinate W.finrank_tate
  have hl : l = c l • c.symm 1 := by
    apply c.injective
    simp
  simp only [LinearEquiv.trans_apply, smulOfUnit_apply_eq_mul, coordRatio, Units.val_mk0]
  conv_lhs => rw [hl]
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]

/-- In coordinates, `e` on `H^n(X)(m)` is `e.gradeEquiv X n` scaled by the `m`th power of the
coordinate ratio. -/
theorem twCoord_twEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ)
    (x : W.Tw X n m) :
    W'.twCoord X n m (e.twEquiv X n m x) =
      ((e.coordRatio ^ m : Fˣ) : F) • e.gradeEquiv X n (W.twCoord X n m x) := by
  rw [twCoord, twEquiv, tateTwistCoordinates_tateTwistCongr, tateEquiv_trans_coordinate,
    tateTwistCoordinates_smulOfUnit, map_smul]
  rfl

/-- **An isomorphism of Weil data in coordinates**: with `κ` the inverse coordinate ratio,
`Θ(γ(α)) = κ^i γ'(α)` on `CH^i(X)` and `∫'_X Θ(a) = κ^d ∫_X a` on `H^{2d}(X)`. -/
theorem gradeEquiv_cycleClassCoord (hγ : e.PreservesCycleClass)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    e.gradeEquiv X (2 * i) (W.cycleClassCoord X i α) =
      ((e.coordRatio⁻¹ ^ i : Fˣ) : F) • W'.cycleClassCoord X i α := by
  rw [cycleClassCoord_apply, cycleClassCoord_apply, hγ, twCoord_twEquiv, smul_smul,
    val_inv_zpow_mul_val_zpow, one_smul]

/-- **`∫' ∘ e = κ^d ∫`** on `H^{2d}(X)` for `X` nonempty equidimensional of dimension `d`, with
`κ` the inverse coordinate ratio. -/
theorem traceCoord_gradeEquiv (htr : e.PreservesTrace)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (a : W.grade X (2 * (d : ℤ))) :
    W'.traceCoord X d hX (e.gradeEquiv X _ a) =
      ((e.coordRatio⁻¹ ^ (d : ℤ) : Fˣ) : F) * W.traceCoord X d hX a := by
  have h := htr X d hX ((W.twCoord X _ _).symm a)
  rw [trace_eq_traceCoord, trace_eq_traceCoord, twCoord_twEquiv, LinearEquiv.apply_symm_apply,
    map_smul, smul_eq_mul] at h
  rw [← h, ← mul_assoc, val_inv_zpow_mul_val_zpow, one_mul]

end Iso

end WeilData

end Stacks.WeilCohomology

end
