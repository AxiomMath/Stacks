module

public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EquidimensionalCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A family of zero-cycles which is not equidimensional

Let `k` be a field, let `S = Spec k[x, y]` and let `X = Spec k[x, y, t]` over `S`. Write `a, b`
for the images of `x, y` in the residue field `κ(s)` of a point `s` of `S`. The family `α` of
`0`-cycles on the fibres of `X/S` of Suslin--Voevodsky's example is

* `α_s = 0` when `b = 0`, and
* `α_s = [p] - [q]` otherwise, where `p`, resp. `q`, is the `κ(s)`-rational point of the fibre
  `Spec κ(s)[t]` with `t = a/b`, resp. `t = (a + b²)/b`.

This file constructs that family, shows that it is a relative `0`-cycle in the sense of
`Stacks.Chow.IsRelativeCycle`, and shows that it is not equidimensional in the sense of
`Stacks.Chow.IsEquidimensional`: the closure of its support contains the whole fibre over the
origin `(x, y)`, which is a line, so no closed subset of relative dimension `0` over `S`
carries the support. In particular there are relative `0`-cycles which are not
equidimensional.

## Main definitions

* `Stacks.Chow.NotEquidimensional.projection` — the morphism `Spec k[x, y, t] ⟶ Spec k[x, y]`.
* `Stacks.Chow.NotEquidimensional.evaluationPoint` — the point of `X` cut out by `t = c` over a
  point `s` of `S`, for a value `c` in the residue field of `s`.
* `Stacks.Chow.NotEquidimensional.firstPoint`,
  `Stacks.Chow.NotEquidimensional.secondPoint` — the two rational points `t = a/b` and
  `t = (a + b²)/b` of the fibre over `s`.
* `Stacks.Chow.NotEquidimensional.exampleFamily` — the family `α` above.

## Main results

* `Stacks.Chow.NotEquidimensional.exampleFamily_of_eq_zero`,
  `Stacks.Chow.NotEquidimensional.exampleFamily_of_ne_zero` — the two clauses of the example,
  giving the member of the family on every fibre.
* `Stacks.Chow.NotEquidimensional.mem_closure_supportOfFamily_exampleFamily` — every point of
  the fibre over the origin lies in the closure of the support of `α`.
* `Stacks.Chow.NotEquidimensional.isRelativeCycle_exampleFamily` — `α` is compatible with
  specializations, that is, `α` is a relative `0`-cycle.
* `Stacks.Chow.NotEquidimensional.not_isEquidimensional_exampleFamily` — `α` is not
  equidimensional.
* `Stacks.Chow.NotEquidimensional.exists_isRelativeCycle_not_isEquidimensional` — the conclusion
  of the example: there exist relative `0`-cycles which are not equidimensional.

## Implementation notes

A point of `S = Spec k[x, y]` is a prime `s` of `k[x, y]`, and the residue field in which the
fibrewise cycles are written down is the ideal-theoretic one, `s.asIdeal.ResidueField`; the
canonical isomorphism `AlgebraicGeometry.Scheme.Spec.residueFieldIso` identifies it with the
scheme-theoretic residue field that `Stacks.Chow.FiberCycleGroup` is stated with. The two
`κ(s)`-rational points of the fibre are produced as the images of the closed point under
sections `Spec κ(s) ⟶ X_s` of the fibre, built from the evaluation homomorphism
`k[x, y][t] → κ(s)` sending `t` to the prescribed value; they have relative dimension `0`
because such a section has residue degree `1`.

A point `z` of the fibre over the origin is reached from a point of the support by a
specialization: the homomorphism `k[x, y][t] → κ(z)[T]` sending `x ↦ c·T`, `y ↦ T` and
`t ↦ c`, where `c` is the image of the coordinate `t` in the residue field of `z`, has a prime
kernel `w` which lies on `y·t = x` and off `y = 0`, hence in the support, and evaluating `T` at
`0` shows `w ⊆ z`.

That `α` is compatible with specializations, that is that `α` is a relative `0`-cycle for the
definition `Stacks.Chow.IsRelativeCycle` of Stacks 0H50, is the one clause of the example whose
verification the source leaves to the reader. It is proved here, and the geometry behind it is
the source's own hint: the two parameter values `a/b` and `a/b + b` differ by `b`, so they come
together over any point where `b` vanishes. Accordingly the proof splits by where `b` vanishes
on a discrete valuation ring `R` mapping to `S` by `g`. If `b` already vanishes at the generic
point of `Spec R` it also vanishes at the closed point, so both members of the base change of
`α` are zero. If `b` vanishes only at the closed point, the translation `t ↦ t + y` of the
affine line is an automorphism over `S` which is the identity on the fibre over `g(0)` and
carries the first of the two rational points of the generic fibre to the second; so the two
scheme-theoretic closures are exchanged by it and have the same special fibre, their
fundamental cycles have the same specialization, and the difference specializes to `0`, which is
the vanishing member at the closed point. If `b` does not vanish at the closed point then `y` is
a unit of `R`, the value `a/b` lies in `R`, and the two points of the generic fibre extend to
closed sections of `X ×_S Spec R` over `Spec R`; the scheme-theoretic closure of the generic
point of such a section is the closed subscheme the section cuts out, whose special fibre is its
value at the closed point, so each fundamental cycle specializes to the prime cycle of that
value, and those two values are the two rational points of the special fibre.

## References

* [Stacks Project, Tag 0H5J](https://stacks.math.columbia.edu/tag/0H5J)
* [Stacks Project, Tag 0H5I](https://stacks.math.columbia.edu/tag/0H5I)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Suslin--Voevodsky, *Relative cycles and Chow sheaves*, Example 3.1.9]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.NotEquidimensional

/-! ### The affine line over the affine plane -/

/-- The coordinate ring `k[x, y]` of the base, as polynomials in two variables. -/
abbrev BaseRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k

/-- The base `S = Spec k[x, y]` of the example. -/
abbrev baseScheme (k : Type u) [Field k] : Scheme.{u} := Spec (.of (BaseRing k))

/-- The total space `X = Spec k[x, y, t]` of the example, written as the affine line over the
base. -/
abbrev totalScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (Polynomial (BaseRing k)))

/-- A point of the base is a prime ideal of `k[x, y]`. -/
local instance isPrime_asIdeal_base (k : Type u) [Field k] (s : baseScheme k) :
    s.asIdeal.IsPrime := s.isPrime

/-- A point of the total space is a prime ideal of `k[x, y, t]`. -/
local instance isPrime_asIdeal_total (k : Type u) [Field k] (w : totalScheme k) :
    w.asIdeal.IsPrime := w.isPrime

/-- The structure morphism `X = Spec k[x, y, t] ⟶ S = Spec k[x, y]` of the example. -/
def projection (k : Type u) [Field k] : totalScheme k ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The affine line over the affine plane is locally of finite type over it. -/
instance locallyOfFiniteType_projection (k : Type u) [Field k] :
    LocallyOfFiniteType (projection k) := by
  rw [projection, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (Polynomial.C : BaseRing k →+* Polynomial (BaseRing k)).FiniteType
  rw [← Polynomial.algebraMap_eq]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The origin `(x, y)` of the base, the point over which the support of the example family
accumulates. -/
def origin (k : Type u) [Field k] : baseScheme k :=
  ⟨RingHom.ker (MvPolynomial.constantCoeff : BaseRing k →+* k), RingHom.ker_isPrime _⟩

/-- The image `a` of the coordinate `x` in the residue field of a point of the base. -/
def xImage (k : Type u) [Field k] (s : baseScheme k) : s.asIdeal.ResidueField :=
  algebraMap (BaseRing k) s.asIdeal.ResidueField (MvPolynomial.X (0 : Fin 2))

/-- The image `b` of the coordinate `y` in the residue field of a point of the base. -/
def yImage (k : Type u) [Field k] (s : baseScheme k) : s.asIdeal.ResidueField :=
  algebraMap (BaseRing k) s.asIdeal.ResidueField (MvPolynomial.X (1 : Fin 2))

/-- The image of `y` in the residue field of `s` vanishes exactly when `y` lies in `s`. -/
theorem yImage_eq_zero_iff (k : Type u) [Field k] (s : baseScheme k) :
    yImage k s = 0 ↔ MvPolynomial.X (1 : Fin 2) ∈ s.asIdeal :=
  Ideal.algebraMap_residueField_eq_zero

/-! ### The rational points of a fibre cut out by a value of the coordinate -/

/-- The point of `X` over `s` at which the coordinate `t` takes the value `c` of the residue
field of `s`: the kernel of the evaluation homomorphism `k[x, y][t] → κ(s)` at `c`. -/
def evaluationPoint (k : Type u) [Field k] (s : baseScheme k) (c : s.asIdeal.ResidueField) :
    totalScheme k :=
  ⟨RingHom.ker (Polynomial.eval₂RingHom (algebraMap (BaseRing k) s.asIdeal.ResidueField) c),
    RingHom.ker_isPrime _⟩

/-- The point of `X` cut out by a value of the coordinate over `s` lies over `s`. -/
theorem projection_evaluationPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) : projection k (evaluationPoint k s c) = s := by
  apply PrimeSpectrum.ext
  change RingHom.ker ((Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c).comp Polynomial.C) = s.asIdeal
  rw [Polynomial.eval₂RingHom_comp_C, Ideal.ker_algebraMap_residueField]

/-- The two points `t = a/b` and `t = (a + b²)/b` of the fibre over `s` are distinct whenever
`b ≠ 0`: their difference is `b`. -/
theorem evaluationPoint_ne (k : Type u) [Field k] (s : baseScheme k)
    (a b : s.asIdeal.ResidueField)
    (ha : a = algebraMap (BaseRing k) s.asIdeal.ResidueField (MvPolynomial.X (0 : Fin 2)))
    (hb' : b = algebraMap (BaseRing k) s.asIdeal.ResidueField (MvPolynomial.X (1 : Fin 2)))
    (hb : b ≠ 0) :
    evaluationPoint k s (a / b) ≠ evaluationPoint k s ((a + b ^ 2) / b) := by
  intro h
  have hker := congrArg PrimeSpectrum.asIdeal h
  let P : Polynomial (BaseRing k) :=
    Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
      Polynomial.C (MvPolynomial.X (0 : Fin 2))
  have hP : P ∈ RingHom.ker (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) (a / b)) := by
    change Polynomial.eval₂ (algebraMap (BaseRing k) s.asIdeal.ResidueField) (a / b) P = 0
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    rw [← hb', ← ha]
    field_simp [hb]
    ring
  change RingHom.ker (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) (a / b)) =
    RingHom.ker (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) ((a + b ^ 2) / b)) at hker
  have hPd : P ∈ RingHom.ker (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) ((a + b ^ 2) / b)) := hker ▸ hP
  change Polynomial.eval₂ (algebraMap (BaseRing k) s.asIdeal.ResidueField)
    ((a + b ^ 2) / b) P = 0 at hPd
  have heval : b * ((a + b ^ 2) / b) - a = 0 := by
    simpa [P, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, ← ha, ← hb'] using hPd
  have hb2 : b ^ 2 = 0 := by
    field_simp [hb] at heval
    linear_combination heval
  exact hb (sq_eq_zero_iff.mp hb2)

/-- The morphism `Spec κ(s) ⟶ X` given by evaluating the coordinate `t` at `c`. -/
def evaluationPointMap (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) : Spec (.of s.asIdeal.ResidueField) ⟶ totalScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
    (algebraMap (BaseRing k) s.asIdeal.ResidueField) c))

/-- The evaluation morphism lies over the canonical morphism `Spec κ(s) ⟶ S`. -/
theorem evaluationPointMap_fac (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    evaluationPointMap k s c ≫ projection k =
      Spec.map (CommRingCat.ofHom (algebraMap (BaseRing k) s.asIdeal.ResidueField)) := by
  dsimp [evaluationPointMap, projection]
  rw [← Spec.map_comp, Spec.map_injective.eq_iff]
  change CommRingCat.ofHom ((Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c).comp Polynomial.C) =
    CommRingCat.ofHom (algebraMap (BaseRing k) s.asIdeal.ResidueField)
  congr 1
  exact Polynomial.eval₂RingHom_comp_C _ _

/-- The section `Spec κ(s) ⟶ X_s` of the fibre over `s` determined by the value `c` of the
coordinate `t`. -/
def evaluationSectionMap (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) : Spec (.of s.asIdeal.ResidueField) ⟶ (projection k).fiber s :=
  pullback.lift (evaluationPointMap k s c)
    (Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).hom)
    (by
      rw [evaluationPointMap_fac, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
      simp only [← Spec.map_comp]
      simp)

/-- The section of the fibre cut out by a value of the coordinate sits over the evaluation
morphism of the total space. -/
theorem evaluationSectionMap_fiberι (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    evaluationSectionMap k s c ≫ (projection k).fiberι s = evaluationPointMap k s c :=
  pullback.lift_fst _ _ _

/-- The `κ(s)`-rational point of the fibre over `s` at which the coordinate `t` takes the
value `c`. -/
def evaluationFiberPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) : (projection k).fiber s :=
  evaluationSectionMap k s c (IsLocalRing.closedPoint s.asIdeal.ResidueField)

/-- The rational point of the fibre at `t = c` maps to the point of `X` at `t = c`. -/
theorem fiberι_evaluationFiberPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    (projection k).fiberι s (evaluationFiberPoint k s c) = evaluationPoint k s c := by
  change (evaluationSectionMap k s c ≫ (projection k).fiberι s)
    (IsLocalRing.closedPoint s.asIdeal.ResidueField) = evaluationPoint k s c
  rw [evaluationSectionMap_fiberι]
  apply PrimeSpectrum.ext
  change Ideal.comap (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c)
      (IsLocalRing.closedPoint s.asIdeal.ResidueField).asIdeal =
    RingHom.ker (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c)
  rw [RingHom.ker_eq_comap_bot]
  change Ideal.comap (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c)
      (IsLocalRing.maximalIdeal s.asIdeal.ResidueField) =
    Ideal.comap (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) c) ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]

/-- The section of the fibre lies over the canonical isomorphism of residue fields. -/
theorem evaluationSectionMap_fiberToSpecResidueField (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    evaluationSectionMap k s c ≫ (projection k).fiberToSpecResidueField s =
      Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).hom := by
  dsimp [evaluationSectionMap, Scheme.Hom.fiberToSpecResidueField]
  exact pullback.lift_snd _ _ _

/-- If `u ≫ v` is an isomorphism then `v` has residue degree one at every point of the image
of `u`. -/
private theorem residueDegree_eq_one_of_comp_eq_iso {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z)
    (w : X ⟶ Z) [IsIso w] (h : u ≫ v = w) (x : X) : v.residueDegree (u x) = 1 := by
  have hcomp := residueDegree_comp u v x
  rw [h, residueDegree_iso w x] at hcomp
  exact Nat.eq_one_of_mul_eq_one_right hcomp.symm

/-- A `κ(s)`-rational point of the fibre has residue degree one over `Spec κ(s)`. -/
theorem residueDegree_evaluationFiberPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    ((projection k).fiberToSpecResidueField s).residueDegree
      (evaluationFiberPoint k s c) = 1 := by
  have : IsIso (Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).hom) :=
    (Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).op).isIso_hom
  exact residueDegree_eq_one_of_comp_eq_iso _ _ _
    (evaluationSectionMap_fiberToSpecResidueField k s c) _

/-- A point of nonzero residue degree over a base whose dimension function vanishes has
relative dimension zero: a finite residue field extension has transcendence degree zero. This
repeats `Stacks.Chow.relativeDimension_eq_zero_of_residueDegree_ne_zero`, whose only home is
the downstream file on products of punctured schemes; it is kept private here rather than
importing that file into this one. -/
private theorem relativeDimension_eq_zero_of_residueDegree_ne_zero {X S : Scheme.{u}}
    (δ : TopologicalSpace.DimensionFunction S) (hδ : ∀ x, δ x = 0) (f : X ⟶ S) (x : X)
    (hx : f.residueDegree x ≠ 0) : relativeDimension δ f x = 0 := by
  let _ : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hfinite : Module.Finite (S.residueField (f x)) (X.residueField x) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hx)
  simp [relativeDimension, hδ, trdeg_eq_zero]

/-- A `κ(s)`-rational point of the fibre over `s` has relative dimension zero, so it carries
`0`-cycles. -/
theorem relativeDimension_evaluationFiberPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    relativeDimension (fieldChowSituation ((baseScheme k).residueField s)).dimensionFunction
      ((projection k).fiberToSpecResidueField s) (evaluationFiberPoint k s c) = 0 := by
  apply relativeDimension_eq_zero_of_residueDegree_ne_zero
  · intro x
    exact fieldChowSituation_dimensionFunction_eq_zero _ x
  · rw [residueDegree_evaluationFiberPoint]
    norm_num

/-- The first of the two rational points of the fibre over `s`, at `t = a/b`. -/
def firstPoint (k : Type u) [Field k] (s : baseScheme k) : (projection k).fiber s :=
  evaluationFiberPoint k s (xImage k s / yImage k s)

/-- The second of the two rational points of the fibre over `s`, at `t = (a + b²)/b`. -/
def secondPoint (k : Type u) [Field k] (s : baseScheme k) : (projection k).fiber s :=
  evaluationFiberPoint k s ((xImage k s + yImage k s ^ 2) / yImage k s)

/-- The first rational point of the fibre lies over the point `t = a/b` of `X`. -/
theorem fiberι_firstPoint (k : Type u) [Field k] (s : baseScheme k) :
    (projection k).fiberι s (firstPoint k s) =
      evaluationPoint k s (xImage k s / yImage k s) :=
  fiberι_evaluationFiberPoint k s _

/-- The second rational point of the fibre lies over the point `t = (a + b²)/b` of `X`. -/
theorem fiberι_secondPoint (k : Type u) [Field k] (s : baseScheme k) :
    (projection k).fiberι s (secondPoint k s) =
      evaluationPoint k s ((xImage k s + yImage k s ^ 2) / yImage k s) :=
  fiberι_evaluationFiberPoint k s _

/-- The two rational points of the fibre over `s` are distinct when `b ≠ 0`. -/
theorem firstPoint_ne_secondPoint (k : Type u) [Field k] (s : baseScheme k)
    (hb : yImage k s ≠ 0) : firstPoint k s ≠ secondPoint k s := by
  intro h
  refine evaluationPoint_ne k s (xImage k s) (yImage k s) rfl rfl hb ?_
  rw [← fiberι_firstPoint, ← fiberι_secondPoint, h]

/-! ### The difference of two rational points -/

open Classical in
/-- The cycle `[p] - [q]` attached to a pair of points of a scheme. -/
def twoPointCycle {Y : Scheme.{u}} (p q : Y) : AlgebraicCycle Y ℤ :=
  ⟨(fun y : Y => (if y = p then (1 : ℤ) else 0) - (if y = q then (1 : ℤ) else 0)),
    (by intro y hy; trivial),
    (by
      intro y hy
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      apply (Set.Finite.insert p (Set.finite_singleton q)).subset
      intro z hz
      have hzsup : (if z = p then (1 : ℤ) else 0) - (if z = q then (1 : ℤ) else 0) ≠ 0 := hz.2
      by_cases hp : z = p
      · exact Set.mem_insert_iff.mpr (Or.inl hp)
      · by_cases hq : z = q
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hq))
        · simp [hp, hq] at hzsup)⟩

open Classical in
/-- The coefficient formula for the cycle `[p] - [q]`. -/
theorem twoPointCycle_apply {Y : Scheme.{u}} (p q y : Y) :
    twoPointCycle p q y = (if y = p then (1 : ℤ) else 0) - (if y = q then (1 : ℤ) else 0) :=
  rfl

/-- Away from the two points, the cycle `[p] - [q]` has coefficient zero. -/
theorem twoPointCycle_apply_of_ne {Y : Scheme.{u}} (p q y : Y) (hp : y ≠ p) (hq : y ≠ q) :
    twoPointCycle p q y = 0 := by
  classical
  change (if y = p then (1 : ℤ) else 0) - (if y = q then (1 : ℤ) else 0) = 0
  simp [hp, hq]

/-- At `p`, the cycle `[p] - [q]` has coefficient one, provided `p ≠ q`. -/
theorem twoPointCycle_apply_left {Y : Scheme.{u}} (p q : Y) (hpq : p ≠ q) :
    twoPointCycle p q p = 1 := by
  classical
  change (if p = p then (1 : ℤ) else 0) - (if p = q then (1 : ℤ) else 0) = 1
  simp [hpq]

/-- The difference of two points of the fibre, each of relative dimension zero, is a `0`-cycle
on the fibre. -/
theorem twoPointCycle_mem_cyclesOfDimension (k : Type u) [Field k] (s : baseScheme k)
    (p q : (projection k).fiber s)
    (hp : relativeDimension
      (fieldChowSituation ((baseScheme k).residueField s)).dimensionFunction
      ((projection k).fiberToSpecResidueField s) p = 0)
    (hq : relativeDimension
      (fieldChowSituation ((baseScheme k).residueField s)).dimensionFunction
      ((projection k).fiberToSpecResidueField s) q = 0) :
    twoPointCycle p q ∈ cyclesOfDimension (fieldChowSituation ((baseScheme k).residueField s))
      ((projection k).fiberToSpecResidueField s) 0 := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro z hz
  by_cases hp' : z = p
  · rw [hp']; exact hp
  · by_cases hq' : z = q
    · rw [hq']; exact hq
    · exact absurd (twoPointCycle_apply_of_ne p q z hp' hq') hz

/-! ### The example family -/

open Classical in
/-- The `0`-cycle on the fibre over `s` prescribed by the example: zero when the image `b` of
`y` vanishes, and otherwise the difference `[p] - [q]` of the rational points at `t = a/b` and
`t = (a + b²)/b`. -/
def exampleFiberCycle (k : Type u) [Field k] (s : baseScheme k) :
    FiberCycleGroup (projection k) s 0 :=
  if yImage k s = 0 then 0
  else ⟨twoPointCycle (firstPoint k s) (secondPoint k s),
    twoPointCycle_mem_cyclesOfDimension k s _ _
      (relativeDimension_evaluationFiberPoint k s _)
      (relativeDimension_evaluationFiberPoint k s _)⟩

/-- **Stacks Project, Tag 0H5J.** The family of `0`-cycles on the fibres of
`Spec k[x, y, t] ⟶ Spec k[x, y]` of Suslin--Voevodsky's example. -/
@[stacks 0H5J "the family of 0-cycles of the example"]
def exampleFamily (k : Type u) [Field k] : FamilyOfCycles (projection k) 0 :=
  fun s => exampleFiberCycle k s

/-- **Stacks Project, Tag 0H5J, first clause.** The example family vanishes on the fibre over
a point where the image of `y` is zero. -/
@[stacks 0H5J "the first clause: the member of the family is zero when b = 0"]
theorem exampleFamily_of_eq_zero (k : Type u) [Field k] (s : baseScheme k)
    (hb : yImage k s = 0) : exampleFamily k s = 0 := by
  classical
  simp only [exampleFamily, exampleFiberCycle, hb, ite_true]

/-- **Stacks Project, Tag 0H5J, second clause.** On a fibre where the image `b` of `y` is
nonzero the member of the example family is the difference `[p] - [q]` of the `κ(s)`-rational
points at `t = a/b` and at `t = (a + b²)/b`. -/
@[stacks 0H5J "the second clause: the member of the family is [p] - [q] when b is nonzero"]
theorem exampleFamily_of_ne_zero (k : Type u) [Field k] (s : baseScheme k)
    (hb : yImage k s ≠ 0) :
    (exampleFamily k s : AlgebraicCycle ((projection k).fiber s) ℤ) =
      twoPointCycle (firstPoint k s) (secondPoint k s) := by
  classical
  simp only [exampleFamily, exampleFiberCycle, hb, ite_false]

/-! ### The support of the example family -/

/-- A point of `X` lying on `y·t = x` but off `y = 0` is the point at `t = a/b` of its own
fibre. -/
theorem eq_evaluationPoint_of_mem_graph (k : Type u) [Field k] (w : totalScheme k)
    (hy : Polynomial.C (MvPolynomial.X (1 : Fin 2)) ∉ w.asIdeal)
    (hxy : Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) ∈ w.asIdeal) :
    w = evaluationPoint k (projection k w)
      (xImage k (projection k w) / yImage k (projection k w)) := by
  set s := projection k w with hs
  set ρ := algebraMap (Polynomial (BaseRing k)) w.asIdeal.ResidueField with hρ
  set m := Ideal.ResidueField.map s.asIdeal w.asIdeal Polynomial.C rfl with hm'
  have hm (r : BaseRing k) :
      m (algebraMap (BaseRing k) s.asIdeal.ResidueField r) = ρ (Polynomial.C r) :=
    Ideal.ResidueField.map_algebraMap _ _ _ _ r
  have hy' : ρ (Polynomial.C (MvPolynomial.X (1 : Fin 2))) ≠ 0 :=
    fun h => hy (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hxy' : ρ (Polynomial.C (MvPolynomial.X (1 : Fin 2))) * ρ Polynomial.X =
      ρ (Polynomial.C (MvPolynomial.X (0 : Fin 2))) := by
    have h : ρ (Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
        Polynomial.C (MvPolynomial.X (0 : Fin 2))) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hxy
    simpa only [map_sub, map_mul, sub_eq_zero] using h
  have hc : m (xImage k s / yImage k s) = ρ Polynomial.X := by
    rw [xImage, yImage, map_div₀, hm, hm, div_eq_iff hy']
    exact hxy'.symm.trans (mul_comm _ _)
  have he : m.comp (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField) (xImage k s / yImage k s)) = ρ := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using hm r
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hc
  apply PrimeSpectrum.ext
  change w.asIdeal = RingHom.ker (Polynomial.eval₂RingHom
    (algebraMap (BaseRing k) s.asIdeal.ResidueField) (xImage k s / yImage k s))
  calc
    w.asIdeal = RingHom.ker ρ := (Ideal.ker_algebraMap_residueField _).symm
    _ = RingHom.ker (m.comp (Polynomial.eval₂RingHom
      (algebraMap (BaseRing k) s.asIdeal.ResidueField)
      (xImage k s / yImage k s))) := congrArg RingHom.ker he.symm
    _ = _ := RingHom.ker_comp_of_injective _ m.injective

/-- Every point of `X` lying on `y·t = x` but off `y = 0` is in the support of the example
family: it is the first of the two rational points of its own fibre. -/
theorem mem_supportOfFamily_of_mem_graph (k : Type u) [Field k] (w : totalScheme k)
    (hy : Polynomial.C (MvPolynomial.X (1 : Fin 2)) ∉ w.asIdeal)
    (hxy : Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
      Polynomial.C (MvPolynomial.X (0 : Fin 2)) ∈ w.asIdeal) :
    w ∈ supportOfFamily (projection k) (exampleFamily k) := by
  have hmem : MvPolynomial.X (1 : Fin 2) ∉ (projection k w).asIdeal := hy
  have hb : yImage k (projection k w) ≠ 0 :=
    fun h => hmem ((yImage_eq_zero_iff k (projection k w)).mp h)
  have hw : w = evaluationPoint k (projection k w)
      (xImage k (projection k w) / yImage k (projection k w)) :=
    eq_evaluationPoint_of_mem_graph k w hy hxy
  refine (mem_supportOfFamily _ _ _).mpr
    ⟨projection k w, firstPoint k (projection k w), ?_,
      (fiberι_firstPoint k (projection k w)).trans hw.symm⟩
  apply subset_closure
  change (exampleFamily k (projection k w) :
      AlgebraicCycle ((projection k).fiber (projection k w)) ℤ)
    (firstPoint k (projection k w)) ≠ 0
  rw [exampleFamily_of_ne_zero k (projection k w) hb,
    twoPointCycle_apply_left _ _ (firstPoint_ne_secondPoint k (projection k w) hb)]
  exact one_ne_zero

/-- **Stacks Project, Tag 0H5J.** The closure of the support of the example family contains the
whole fibre over the origin, which is a line: the surface `y·t = x` lies in that closure and
contains the fibre over the origin. -/
@[stacks 0H5J "the closure of the support contains the whole fibre over the origin"]
theorem mem_closure_supportOfFamily_exampleFamily (k : Type u) [Field k] (z : totalScheme k)
    (hz : projection k z = origin k) :
    z ∈ closure (supportOfFamily (projection k) (exampleFamily k)) := by
  set L := z.asIdeal.ResidueField with hL
  set ρ := algebraMap (Polynomial (BaseRing k)) L with hρ
  set t := ρ Polynomial.X with ht
  set c : k →+* L := ρ.comp (Polynomial.C.comp MvPolynomial.C) with hc
  set B : BaseRing k →+* Polynomial L :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp c)
      (fun i => if i = 0 then Polynomial.C t * Polynomial.X else Polynomial.X) with hB
  set H : Polynomial (BaseRing k) →+* Polynomial L :=
    Polynomial.eval₂RingHom B (Polynomial.C t) with hH
  set w : totalScheme k := ⟨RingHom.ker H, RingHom.ker_isPrime H⟩ with hw'
  have hB0 : B (MvPolynomial.X (0 : Fin 2)) = Polynomial.C t * Polynomial.X := by simp [hB]
  have hB1 : B (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by simp [hB]
  have hw : w ∈ supportOfFamily (projection k) (exampleFamily k) := by
    apply mem_supportOfFamily_of_mem_graph k w
    · change H (Polynomial.C (MvPolynomial.X (1 : Fin 2))) ≠ 0
      simpa only [hH, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hB1] using
        (Polynomial.X_ne_zero (R := L))
    · change H (Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
        Polynomial.C (MvPolynomial.X (0 : Fin 2))) = 0
      simp only [map_sub, map_mul, hH, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.eval₂_X, hB0, hB1]
      ring
  have hzero (i : Fin 2) : ρ (Polynomial.C (MvPolynomial.X i)) = 0 := by
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    have hi : MvPolynomial.X i ∈ (origin k).asIdeal := by
      change MvPolynomial.constantCoeff (MvPolynomial.X i : BaseRing k) = 0
      simp
    rw [← hz] at hi
    exact hi
  have he : (Polynomial.evalRingHom (0 : L)).comp H = ρ := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        simp [hH, hB, hc]
      · intro i
        fin_cases i <;> simp [hH, hB, hzero]
    · simp [hH, ht]
  apply closure_mono (Set.singleton_subset_iff.mpr hw)
  change (z : PrimeSpectrum (Polynomial (BaseRing k))) ∈
    closure ({w} : Set (PrimeSpectrum (Polynomial (BaseRing k))))
  apply (PrimeSpectrum.le_iff_mem_closure (w : PrimeSpectrum (Polynomial (BaseRing k))) z).mp
  change w.asIdeal ≤ z.asIdeal
  intro P hP
  apply Ideal.algebraMap_residueField_eq_zero.mp
  change ρ P = 0
  rw [← he, RingHom.comp_apply]
  change H P = 0 at hP
  rw [hP, map_zero]

/-! ### The family is not equidimensional -/

/-- The local topological Krull dimension of a topological space at a point is nonnegative. -/
theorem nonneg_topologicalKrullDimAt {Y : Type*} [TopologicalSpace Y] (y : Y) :
    0 ≤ topologicalKrullDimAt Y y := by
  obtain ⟨⟨U, hy, _, hd⟩, _⟩ := topologicalKrullDimAt_isLeast Y y
  rw [hd]
  cases h : topologicalKrullDim U with
  | bot => exact False.elim (((topologicalKrullDim_eq_bot_iff_isEmpty U).mp h).false ⟨y, hy⟩)
  | coe n => simp

/-- A morphism of relative dimension zero has discrete fibres, so a specialization between two
points of one of its fibres is an equality. -/
theorem eq_of_specializes_of_relativeDimensionLE_zero {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (hf : RelativeDimensionLE f 0) (x y : Y) (hxy : x ⤳ y)
    (heq : f x = f y) : x = y := by
  have : LocallyQuasiFinite f :=
    ((AlgebraicGeometry.forall_quasiFiniteAt_iff f).mp (fun z =>
      (AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero f z).mpr
        (le_antisymm (hf z) (nonneg_topologicalKrullDimAt _)))).2
  have : DiscreteTopology (f ⁻¹' {f x}) :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f x))
  have h : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ (⟨y, heq.symm⟩ : f ⁻¹' {f x}) :=
    (subtype_specializes_iff _ _).mpr hxy
  exact congrArg Subtype.val h.eq

/-- The fibre over the origin carries a nontrivial specialization: the generic point of the
line `x = y = 0` specializes to the origin of that line. -/
theorem exists_specializes_over_origin (k : Type u) [Field k] :
    ∃ p q : totalScheme k, projection k p = origin k ∧ projection k q = origin k ∧
      p ⤳ q ∧ p ≠ q := by
  set H : Polynomial (BaseRing k) →+* Polynomial k :=
    Polynomial.mapRingHom MvPolynomial.constantCoeff with hH
  set E : Polynomial (BaseRing k) →+* k := (Polynomial.evalRingHom 0).comp H with hE
  set p : totalScheme k := ⟨RingHom.ker H, RingHom.ker_isPrime H⟩ with hp
  set q : totalScheme k := ⟨RingHom.ker E, RingHom.ker_isPrime E⟩ with hq
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · apply PrimeSpectrum.ext
    ext r
    change H (Polynomial.C r) = 0 ↔ MvPolynomial.constantCoeff r = 0
    simp [hH]
  · apply PrimeSpectrum.ext
    ext r
    change E (Polynomial.C r) = 0 ↔ MvPolynomial.constantCoeff r = 0
    simp [hE, hH]
  · apply (PrimeSpectrum.le_iff_specializes
      (p : PrimeSpectrum (Polynomial (BaseRing k))) q).mp
    intro r hr
    change E r = 0
    change H r = 0 at hr
    simp [hE, hr]
  · intro hpq
    have hX : Polynomial.X ∈ q.asIdeal := by
      change E Polynomial.X = 0
      simp [hE, hH]
    rw [← hpq] at hX
    change H Polynomial.X = 0 at hX
    simp [hH] at hX

/-- **Stacks Project, Tag 0H5J.** The example family of `0`-cycles on the fibres of
`Spec k[x, y, t] ⟶ Spec k[x, y]` is not equidimensional: a closed subset of `X` containing its
support contains the whole fibre over the origin, which is a line, so that closed subset
cannot have relative dimension `0` over the base. -/
@[stacks 0H5J "the example family is not equidimensional"]
theorem not_isEquidimensional_exampleFamily (k : Type u) [Field k] :
    ¬ IsEquidimensional (projection k) 0 (exampleFamily k) := by
  rintro ⟨W, hW, hdim⟩
  have hclosure := closure_minimal hW W.support.isClosed
  obtain ⟨p, q, hp, hq, hpq, hne⟩ := exists_specializes_over_origin k
  have hpW := hclosure (mem_closure_supportOfFamily_exampleFamily k p hp)
  have hqW := hclosure (mem_closure_supportOfFamily_exampleFamily k q hq)
  rw [← W.range_subschemeι] at hpW hqW
  obtain ⟨x, rfl⟩ := hpW
  obtain ⟨y, rfl⟩ := hqW
  refine hne ?_
  congr 1
  exact eq_of_specializes_of_relativeDimensionLE_zero (W.subschemeι ≫ projection k) hdim _ _
    (W.subschemeι.isEmbedding.isInducing.specializes_iff.mp hpq) (hp.trans hq.symm)

/-! ### Fundamental cycles of points of a fibre -/

open Classical in
/-- The fundamental cycle of the reduced closure of a point `ξ` of relative dimension `r` of a
fibre is the prime cycle of `ξ`: coefficient one at `ξ` and zero elsewhere. -/
private theorem fiberSubschemeCycle_integralComponentAt_apply {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (s : S) (r : ℕ) (ξ x : f.fiber s)
    (hξ : fiberPointDimension f s ξ = (r : ℤ)) :
    (fiberSubschemeCycle f s r (integralComponentAt ξ)).1 x =
      if x = ξ then (1 : ℤ) else 0 := by
  classical
  by_cases hx : x = ξ
  · subst hx
    rw [ite_eq_left rfl]
    exact fiberSubschemeCycle_integralComponentAt_self f s r x hξ
  · rw [ite_eq_right hx]
    exact fiberSubschemeCycle_integralComponentAt_of_ne f s r ξ x hx

/-! ### Reduced closures, kernels and sections -/

/-- The reduced closure of the image of a point is the scheme-theoretic image of its reduced
closure. -/
private theorem integralComponentAt_map {Y Z : Scheme.{u}} (f : Y ⟶ Z) (y : Y) :
    (integralComponentAt y).map f = integralComponentAt (f y) := by
  rw [integralComponentAt, integralComponentAt, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply SetLike.coe_injective
  change closure (f '' closure {y}) = closure {f y}
  rw [closure_image_closure f.continuous, Set.image_singleton]

/-- In a pullback square whose right edge is a closed immersion, the kernel of the left edge is
the inverse image of the kernel of the right edge. -/
private theorem ker_eq_comap_of_isPullback {P Y Z W : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z}
    {f : Y ⟶ W} {g : Z ⟶ W} (h : IsPullback a b f g) [IsClosedImmersion g] :
    a.ker = g.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion g f

/-- The kernel of a morphism out of an integral scheme is the reduced closure of the image of
its generic point. -/
private theorem ker_eq_integralComponentAt {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z) :
    f.ker = integralComponentAt (f (genericPoint Y)) := by
  rw [← integralComponentAt_map]
  have h : Closeds.closure ({genericPoint Y} : Set Y) = ⊤ :=
    SetLike.coe_injective (genericPoint_closure Y)
  rw [integralComponentAt, h, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot]

/-- The scheme-theoretic image of an ideal sheaf along an isomorphism is its inverse image along
the inverse isomorphism. -/
private theorem map_ideal_eq_comap_inv {Y Z : Scheme.{u}} (I : Y.IdealSheafData) (e : Y ≅ Z) :
    I.map e.hom = I.comap e.inv := by
  refine le_antisymm ?_ ?_
  · calc
      I.map e.hom = ((I.map e.hom).comap e.hom).comap e.inv := by
        simp only [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
          Scheme.IdealSheafData.comap_id]
      _ ≤ I.comap e.inv := Scheme.IdealSheafData.comap_mono _ (I.comap_map_le e.hom)
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp]
    simp

/-- The restriction to the fibre over `s` of a section `σ` of `f`: the `κ(s)`-rational point of
the fibre cut out by `σ`. -/
private def sectionOnFiber {Y S : Scheme.{u}} (f : Y ⟶ S) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S)
    (s : S) : Spec (S.residueField s) ⟶ f.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])

/-- The restriction of a section to a fibre lies over the section. -/
private theorem sectionOnFiber_fiberι {Y S : Scheme.{u}} (f : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (s : S) :
    sectionOnFiber f σ hσ s ≫ f.fiberι s = S.fromSpecResidueField s ≫ σ :=
  pullback.lift_fst _ _ _

/-- The restriction of a section to a fibre is a section of the fibre over `Spec κ(s)`. -/
private theorem sectionOnFiber_fiberToSpecResidueField {Y S : Scheme.{u}} (f : Y ⟶ S)
    (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) (s : S) :
    sectionOnFiber f σ hσ s ≫ f.fiberToSpecResidueField s = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The restriction of a section to a fibre exhibits that fibre point as the base change of the
section along `Spec κ(s) ⟶ S`. -/
private theorem sectionOnFiber_isPullback {Y S : Scheme.{u}} (f : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (s : S) :
    IsPullback (sectionOnFiber f σ hσ s) (S.fromSpecResidueField s) (f.fiberι s) σ := by
  refine IsPullback.of_right ?_ (sectionOnFiber_fiberι f σ hσ s)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
  change IsPullback (sectionOnFiber f σ hσ s ≫ f.fiberToSpecResidueField s)
    (S.fromSpecResidueField s) (S.fromSpecResidueField s) (σ ≫ f)
  rw [sectionOnFiber_fiberToSpecResidueField, hσ]
  exact IsPullback.id_horiz _

/-- A section of a separated morphism is a closed immersion. -/
private theorem isClosedImmersion_of_comp_eq_id {X Y : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ X)
    [IsSeparated v] (h : u ≫ v = 𝟙 X) : IsClosedImmersion u := by
  have : IsClosedImmersion (u ≫ v) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp u v

/-- The `κ(s)`-rational point of the fibre over `s` cut out by a section of `f`. -/
private def sectionFiberPoint {Y S : Scheme.{u}} (f : Y ⟶ S) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S)
    (s : S) : f.fiber s :=
  sectionOnFiber f σ hσ s (genericPoint (Spec (S.residueField s)))

/-- The point of the fibre cut out by a section maps to the value of the section. -/
private theorem sectionFiberPoint_fiberι {Y S : Scheme.{u}} (f : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (s : S) : f.fiberι s (sectionFiberPoint f σ hσ s) = σ s := by
  change (sectionOnFiber f σ hσ s ≫ f.fiberι s) _ = _
  rw [sectionOnFiber_fiberι]
  exact congrArg σ (Scheme.fromSpecResidueField_apply s _)

/-- The generic point of a section of the fibre over `Spec κ(s)` has relative dimension zero: it
is a `κ(s)`-rational point. -/
private theorem fiberPointDimension_section_eq_zero {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (s : S) (u : Spec (S.residueField s) ⟶ f.fiber s)
    (hu : u ≫ f.fiberToSpecResidueField s = 𝟙 _) :
    fiberPointDimension f s (u (genericPoint (Spec (S.residueField s)))) = 0 := by
  refine relativeDimension_eq_zero_of_residueDegree_ne_zero _
    (fun x ↦ fieldChowSituation_dimensionFunction_eq_zero _ x) _ _ ?_
  rw [residueDegree_eq_one_of_comp_eq_iso u _ _ hu]
  exact one_ne_zero

/-- The point of the fibre cut out by a section has relative dimension zero: it is a
`κ(s)`-rational point. -/
private theorem sectionFiberPoint_relativeDimension {Y S : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) (s : S) :
    fiberPointDimension f s (sectionFiberPoint f σ hσ s) = 0 :=
  fiberPointDimension_section_eq_zero f s _ (sectionOnFiber_fiberToSpecResidueField f σ hσ s)

/-! ### Specialization of the fundamental cycle of a rational point -/

section Dvr

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of R)) [LocallyOfFiniteType f]

/-- The spectrum of the residue field of a point is integral. -/
private theorem isIntegral_spec_residueField {S : Scheme.{u}} (s : S) :
    IsIntegral (Spec (S.residueField s)) := by
  have : IsDomain ↥(S.residueField s) := Field.isDomain
  infer_instance

open Classical in
/-- The specialization of the fundamental cycle of the point of the generic fibre cut out by a
closed section of `f` is the prime cycle of the point of the special fibre cut out by the same
section: the scheme-theoretic image of the closure of the generic point of the section is the
closed subscheme the section cuts out, whose special fibre is its closed point. -/
private theorem specializationIntegralCycle_sectionFiberPoint (σ : Spec (.of R) ⟶ Y)
    [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 _)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    (specializationIntegralCycle f 0
          (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R))))).1 x =
      if x = sectionFiberPoint f σ hσ (IsLocalRing.closedPoint R) then (1 : ℤ) else 0 := by
  have hclosure : specializationClosure f
      (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R)))) = σ.ker := by
    change (integralComponentAt (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R))))).map
      (f.fiberι (genericPoint (Spec (.of R)))) = σ.ker
    rw [integralComponentAt_map, sectionFiberPoint_fiberι, ker_eq_integralComponentAt]
  have hfibre : specializationSpecialFibre f
      (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R)))) =
      integralComponentAt (sectionFiberPoint f σ hσ (IsLocalRing.closedPoint R)) := by
    have : IsIntegral (Spec ((Spec (.of R)).residueField (IsLocalRing.closedPoint R))) :=
      isIntegral_spec_residueField (S := Spec (.of R)) (IsLocalRing.closedPoint R)
    change (specializationClosure f
      (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R))))).comap
        (f.fiberι (IsLocalRing.closedPoint R)) = _
    rw [hclosure, ← ker_eq_comap_of_isPullback
      (sectionOnFiber_isPullback f σ hσ (IsLocalRing.closedPoint R)),
      ker_eq_integralComponentAt]
    rfl
  change (fiberSubschemeCycle f (IsLocalRing.closedPoint R) 0 (specializationSpecialFibre f
    (sectionFiberPoint f σ hσ (genericPoint (Spec (.of R)))))).1 x = _
  rw [hfibre]
  exact fiberSubschemeCycle_integralComponentAt_apply f _ 0 _ x
    (by simpa using sectionFiberPoint_relativeDimension f σ hσ (IsLocalRing.closedPoint R))

/-- Two points of the generic fibre exchanged by an automorphism of `Y` which is the identity on
the special fibre have the same specialized fundamental cycle: the two scheme-theoretic images
are exchanged by the automorphism, hence have the same inverse image in the special fibre. -/
private theorem specializationIntegralCycle_eq_of_iso_fixed (r : ℕ) (e : Y ≅ Y)
    (he : f.fiberι (IsLocalRing.closedPoint R) ≫ e.hom = f.fiberι (IsLocalRing.closedPoint R))
    (ξ ξ' : f.fiber (genericPoint (Spec (.of R))))
    (hξ : e.hom (f.fiberι (genericPoint (Spec (.of R))) ξ) =
      f.fiberι (genericPoint (Spec (.of R))) ξ') :
    specializationIntegralCycle f r ξ = specializationIntegralCycle f r ξ' := by
  have hmap : (specializationClosure f ξ).map e.hom = specializationClosure f ξ' := by
    change ((integralComponentAt ξ).map (f.fiberι (genericPoint (Spec (.of R))))).map e.hom = _
    rw [integralComponentAt_map, integralComponentAt_map, hξ]
    exact (integralComponentAt_map _ ξ').symm
  have hinv : f.fiberι (IsLocalRing.closedPoint R) ≫ e.inv =
      f.fiberι (IsLocalRing.closedPoint R) := by
    calc
      f.fiberι (IsLocalRing.closedPoint R) ≫ e.inv =
          (f.fiberι (IsLocalRing.closedPoint R) ≫ e.hom) ≫ e.inv := by rw [he]
      _ = f.fiberι (IsLocalRing.closedPoint R) := by simp
  have hcomap : specializationSpecialFibre f ξ = specializationSpecialFibre f ξ' := by
    change (specializationClosure f ξ).comap (f.fiberι (IsLocalRing.closedPoint R)) =
      (specializationClosure f ξ').comap (f.fiberι (IsLocalRing.closedPoint R))
    rw [← hmap, map_ideal_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp, hinv]
  change fiberSubschemeCycle f (IsLocalRing.closedPoint R) r (specializationSpecialFibre f ξ) =
    fiberSubschemeCycle f (IsLocalRing.closedPoint R) r (specializationSpecialFibre f ξ')
  rw [hcomap]

/-- The difference of the fundamental cycles of two points of the generic fibre exchanged by an
automorphism which is the identity on the special fibre specializes to zero. -/
private theorem specializationCycle_sub_eq_zero_of_iso_fixed (r : ℕ) (e : Y ≅ Y)
    (he : f.fiberι (IsLocalRing.closedPoint R) ≫ e.hom = f.fiberι (IsLocalRing.closedPoint R))
    (ξ ξ' : f.fiber (genericPoint (Spec (.of R))))
    (hξ : e.hom (f.fiberι (genericPoint (Spec (.of R))) ξ) =
      f.fiberι (genericPoint (Spec (.of R))) ξ')
    (hdim : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (hdim' : fiberPointDimension f (genericPoint (Spec (.of R))) ξ' = (r : ℤ)) :
    specializationCycle f r (integralGenericCycle f r ξ - integralGenericCycle f r ξ') = 0 := by
  rw [← specializationCycleHom_apply, map_sub, specializationCycleHom_apply,
    specializationCycleHom_apply, specializationCycle_integralGenericCycle f r ξ hdim,
    specializationCycle_integralGenericCycle f r ξ' hdim',
    specializationIntegralCycle_eq_of_iso_fixed f r e he ξ ξ' hξ, sub_self]

omit [IsDiscreteValuationRing R] in
/-- The difference of the fundamental cycles of two points of relative dimension zero of the
generic fibre is the cycle `[p] - [q]`. -/
private theorem integralGenericCycle_sub_apply
    (p q : f.fiber (genericPoint (Spec (.of R))))
    (hp : fiberPointDimension f (genericPoint (Spec (.of R))) p = 0)
    (hq : fiberPointDimension f (genericPoint (Spec (.of R))) q = 0) :
    ((integralGenericCycle f 0 p - integralGenericCycle f 0 q :
          FiberCycleGroup f (genericPoint (Spec (.of R))) 0) :
        AlgebraicCycle (f.fiber (genericPoint (Spec (.of R)))) ℤ) = twoPointCycle p q := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (integralGenericCycle f 0 p).1 x - (integralGenericCycle f 0 q).1 x = _
  change (fiberSubschemeCycle f (genericPoint (Spec (.of R))) 0 (integralComponentAt p)).1 x -
    (fiberSubschemeCycle f (genericPoint (Spec (.of R))) 0 (integralComponentAt q)).1 x = _
  rw [fiberSubschemeCycle_integralComponentAt_apply f _ 0 p x (by simpa using hp),
    fiberSubschemeCycle_integralComponentAt_apply f _ 0 q x (by simpa using hq),
    twoPointCycle_apply]

end Dvr

/-! ### Base change of a family which is a difference of two rational points -/

/-- The base change of a family vanishing on the fibre over the image point vanishes. -/
private theorem baseChangeFamily_apply_eq_zero {Y S T : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : T)
    (hα : α (g t) = 0) : baseChangeFamily f g r α t = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [baseChangeFamily_apply, hα]
  change (0 : ℤ) * _ = _
  rw [zero_mul]
  rfl

/-- The base change of a family whose member over `g t` is the difference `[p] - [q]` of two
`κ(g t)`-rational points of relative dimension zero is the difference `[p'] - [q']` of the two
points of the fibre over `t` above them, provided each of `p'`, `q'` cuts out the inverse image
of the reduced closure of the point below it. -/
private theorem baseChangeFamily_eq_twoPointCycle {Y S T : Scheme.{u}} (f : Y ⟶ S)
    [LocallyOfFiniteType f] (g : T ⟶ S) (α : FamilyOfCycles f 0) (t : T)
    (p q : f.fiber (g t)) (p' q' : (pullback.snd f g).fiber t)
    (hα : (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) = twoPointCycle p q)
    (hp : restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t p' = p)
    (hq : restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t q' = q)
    (hIp : (integralComponentAt p).comap
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) =
      integralComponentAt p')
    (hIq : (integralComponentAt q).comap
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) =
      integralComponentAt q')
    (hdimp : fiberPointDimension (pullback.snd f g) t p' = 0)
    (hdimq : fiberPointDimension (pullback.snd f g) t q' = 0) :
    (baseChangeFamily f g 0 α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) =
      twoPointCycle p' q' := by
  classical
  set m := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t
    with hm
  have hcoeff (z : f.fiber (g t)) (z' : (pullback.snd f g).fiber t)
      (hI : (integralComponentAt z).comap m = integralComponentAt z')
      (hdim : fiberPointDimension (pullback.snd f g) t z' = 0) (x : (pullback.snd f g).fiber t) :
      closedSubschemeCycleCoeff (fieldChowSituation (T.residueField t))
          ((pullback.snd f g).fiberToSpecResidueField t)
          ((integralComponentAt z).comap m).subschemeι 0 x =
        if x = z' then (1 : ℤ) else 0 := by
    change (fiberSubschemeCycle (pullback.snd f g) t 0 ((integralComponentAt z).comap m)).1 x = _
    rw [hI]
    exact fiberSubschemeCycle_integralComponentAt_apply (pullback.snd f g) t 0 z' x
      (by simpa using hdim)
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [baseChangeFamily_apply, hα, twoPointCycle_apply, twoPointCycle_apply]
  change ((if m x = p then (1 : ℤ) else 0) - (if m x = q then (1 : ℤ) else 0)) *
    closedSubschemeCycleCoeff (fieldChowSituation (T.residueField t))
      ((pullback.snd f g).fiberToSpecResidueField t)
      ((integralComponentAt (m x)).comap m).subschemeι 0 x = _
  by_cases hxp : m x = p <;> by_cases hxq : m x = q
  · have heq : (if x = p' then (1 : ℤ) else 0) = if x = q' then (1 : ℤ) else 0 := by
      rw [← hcoeff p p' hIp hdimp x, ← hcoeff q q' hIq hdimq x, ← hxp, ← hxq]
    rw [ite_eq_left hxp, ite_eq_left hxq, sub_self, zero_mul, heq, sub_self]
  · have hxq' : x ≠ q' := fun h ↦ hxq (h ▸ hq)
    rw [ite_eq_left hxp, ite_eq_right hxq, sub_zero, one_mul, ite_eq_right hxq', sub_zero, hxp]
    exact hcoeff p p' hIp hdimp x
  · have hxp' : x ≠ p' := fun h ↦ hxp (h ▸ hp)
    rw [ite_eq_right hxp, ite_eq_left hxq, zero_sub, neg_mul, one_mul, ite_eq_right hxp', zero_sub,
      hxq]
    exact congrArg Neg.neg (hcoeff q q' hIq hdimq x)
  · have hxp' : x ≠ p' := fun h ↦ hxp (h ▸ hp)
    have hxq' : x ≠ q' := fun h ↦ hxq (h ▸ hq)
    rw [ite_eq_right hxp, ite_eq_right hxq, sub_self, zero_mul, ite_eq_right hxp',
      ite_eq_right hxq', sub_self]

/-! ### The two rational points of a fibre after a base change -/

/-- The base change of a section of `f` along a morphism of bases. -/
private def baseChangedSection {P Y T S : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ T} {f : Y ⟶ S}
    {g : T ⟶ S} (h : IsPullback a b f g) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) : T ⟶ P :=
  h.lift (g ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])

/-- The base change of a section lies over the section. -/
private theorem baseChangedSection_fst {P Y T S : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ T} {f : Y ⟶ S}
    {g : T ⟶ S} (h : IsPullback a b f g) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) :
    baseChangedSection h σ hσ ≫ a = g ≫ σ := h.lift_fst _ _ _

/-- The base change of a section is a section. -/
private theorem baseChangedSection_snd {P Y T S : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ T} {f : Y ⟶ S}
    {g : T ⟶ S} (h : IsPullback a b f g) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) :
    baseChangedSection h σ hσ ≫ b = 𝟙 _ := h.lift_snd _ _ _

/-- The base change of a section exhibits the closed subscheme it cuts out as the inverse image
of the one cut out by the section. -/
private theorem baseChangedSection_isPullback {P Y T S : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ T}
    {f : Y ⟶ S} {g : T ⟶ S} (h : IsPullback a b f g) (σ : S ⟶ Y) (hσ : σ ≫ f = 𝟙 S) :
    IsPullback (baseChangedSection h σ hσ) g a σ := by
  refine IsPullback.of_right ?_ (baseChangedSection_fst h σ hσ) h.flip
  rw [baseChangedSection_snd, hσ]
  exact IsPullback.id_horiz g

/-- The square exhibiting the fibre of a base change over `t` as the base change of the fibre
over `g t` along the residue field extension. -/
private theorem baseChangeFiber_isPullback {Y S T : Scheme.{u}} (f : Y ⟶ S) (g : T ⟶ S) (t : T) :
    IsPullback
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
      ((pullback.snd f g).fiberToSpecResidueField t) (f.fiberToSpecResidueField (g t))
      (Spec.map (g.residueFieldMap t)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) t

/-- The canonical morphism of fibres of a base change is compatible with the inclusions of the
fibres into the total spaces: the general square's compatibility, at the pullback square. -/
private theorem restrictedFiberMap_baseChange_fiberι {Y S T : Scheme.{u}} (f : Y ⟶ S) (g : T ⟶ S)
    (t : T) :
    restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t ≫
        f.fiberι (g t) =
      (pullback.snd f g).fiberι t ≫ pullback.fst f g :=
  restrictedFiberMap_fiberι ..

/-- The section `Spec κ(s) ⟶ X_s` of the fibre over `s` at `t = c`, written on the
scheme-theoretic residue field of `s`. -/
private def evaluationRationalSection (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    Spec ((baseScheme k).residueField s) ⟶ (projection k).fiber s :=
  Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).inv ≫ evaluationSectionMap k s c

/-- The rational section at `t = c` is a section of the fibre over `Spec κ(s)`. -/
private theorem evaluationRationalSection_fiberToSpecResidueField (k : Type u) [Field k]
    (s : baseScheme k) (c : s.asIdeal.ResidueField) :
    evaluationRationalSection k s c ≫ (projection k).fiberToSpecResidueField s = 𝟙 _ := by
  rw [evaluationRationalSection, Category.assoc,
    evaluationSectionMap_fiberToSpecResidueField, ← Spec.map_comp]
  simp

/-- The rational section at `t = c` cuts out the point of the fibre at `t = c`. -/
private theorem evaluationRationalSection_genericPoint (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) :
    evaluationRationalSection k s c (genericPoint (Spec ((baseScheme k).residueField s))) =
      evaluationFiberPoint k s c :=
  congrArg (evaluationSectionMap k s c) (Subsingleton.elim _ _)

/-- A section of a separated morphism is a closed immersion; here the fibre is affine over the
residue field, so the rational section at `t = c` is a closed immersion. -/
private theorem evaluationRationalSection_isClosedImmersion (k : Type u) [Field k]
    (s : baseScheme k) (c : s.asIdeal.ResidueField) :
    IsClosedImmersion (evaluationRationalSection k s c) :=
  isClosedImmersion_of_comp_eq_id _ _ (evaluationRationalSection_fiberToSpecResidueField k s c)

/-- The section of the fibre over a point `t` of a new base at the value `c` of the coordinate:
the base change of the rational section at `t = c` of the fibre over the image point. -/
private def baseChangedEvaluationSection (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    Spec (T.residueField t) ⟶ (pullback.snd (projection k) g).fiber t :=
  baseChangedSection (baseChangeFiber_isPullback (projection k) g t)
    (evaluationRationalSection k (g t) c) (evaluationRationalSection_fiberToSpecResidueField k _ c)

/-- The `κ(t)`-rational point of the fibre of the base change over `t` at which the coordinate
`t` takes the value `c`. -/
private def baseChangedEvaluationPoint (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    (pullback.snd (projection k) g).fiber t :=
  baseChangedEvaluationSection k g t c (genericPoint (Spec (T.residueField t)))

/-- The point at `t = c` of the fibre of a base change lies over the point at `t = c` of the
fibre below it. -/
private theorem baseChangedEvaluationPoint_map (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    restrictedFiberMap (projection k) (pullback.snd (projection k) g)
        (pullback.fst (projection k) g) g pullback.condition t
        (baseChangedEvaluationPoint k g t c) =
      evaluationFiberPoint k (g t) c := by
  change (baseChangedEvaluationSection k g t c ≫ restrictedFiberMap (projection k)
    (pullback.snd (projection k) g) (pullback.fst (projection k) g) g pullback.condition t) _ = _
  rw [baseChangedEvaluationSection, baseChangedSection_fst,
    ← evaluationRationalSection_genericPoint]
  exact congrArg (evaluationRationalSection k (g t) c) (Subsingleton.elim _ _)

/-- The point at `t = c` of the fibre of a base change cuts out the inverse image of the reduced
closure of the point at `t = c` below it: both are the inverse image of the closed subscheme cut
out by the rational section. -/
private theorem baseChangedEvaluationPoint_integralComponentAt (k : Type u) [Field k]
    {T : Scheme.{u}} (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    (integralComponentAt (evaluationFiberPoint k (g t) c)).comap
        (restrictedFiberMap (projection k) (pullback.snd (projection k) g)
          (pullback.fst (projection k) g) g pullback.condition t) =
      integralComponentAt (baseChangedEvaluationPoint k g t c) := by
  have := evaluationRationalSection_isClosedImmersion k (g t) c
  rw [← evaluationRationalSection_genericPoint, ← ker_eq_integralComponentAt,
    ← ker_eq_comap_of_isPullback (baseChangedSection_isPullback
      (baseChangeFiber_isPullback (projection k) g t) (evaluationRationalSection k (g t) c)
      (evaluationRationalSection_fiberToSpecResidueField k (g t) c)),
    ker_eq_integralComponentAt]
  rfl

/-- The point at `t = c` of the fibre of a base change has relative dimension zero. -/
private theorem baseChangedEvaluationPoint_relativeDimension (k : Type u) [Field k]
    {T : Scheme.{u}} (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    fiberPointDimension (pullback.snd (projection k) g) t
      (baseChangedEvaluationPoint k g t c) = 0 :=
  fiberPointDimension_section_eq_zero _ t _ (baseChangedSection_snd _ _ _)

/-- A point of the fibre of a base change whose image in `X` is the point at `t = c` is the
point at `t = c` of that fibre: the latter is closed in the fibre, and the former lies in its
closure. -/
private theorem eq_baseChangedEvaluationPoint (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField)
    (z : (pullback.snd (projection k) g).fiber t)
    (hz : pullback.fst (projection k) g ((pullback.snd (projection k) g).fiberι t z) =
      evaluationPoint k (g t) c) :
    z = baseChangedEvaluationPoint k g t c := by
  have hmap : restrictedFiberMap (projection k) (pullback.snd (projection k) g)
      (pullback.fst (projection k) g) g pullback.condition t z =
      evaluationFiberPoint k (g t) c := by
    apply ((projection k).fiberι (g t)).isEmbedding.injective
    rw [fiberι_evaluationFiberPoint]
    exact (congrArg (fun φ ↦ φ z)
      (restrictedFiberMap_baseChange_fiberι (projection k) g t)).trans hz
  have : IsSeparated (projection k) := by
    rw [projection]
    infer_instance
  have : IsSeparated ((pullback.snd (projection k) g).fiberToSpecResidueField t) := by
    change IsSeparated (pullback.snd (pullback.snd (projection k) g) _)
    infer_instance
  have : IsClosedImmersion (baseChangedEvaluationSection k g t c) :=
    isClosedImmersion_of_comp_eq_id _ _ (baseChangedSection_snd _ _ _)
  have hc : IsClosed ({baseChangedEvaluationPoint k g t c} :
      Set ((pullback.snd (projection k) g).fiber t)) := by
    simpa only [Set.image_singleton, baseChangedEvaluationPoint] using
      (baseChangedEvaluationSection k g t c).isClosedEmbedding.isClosedMap
        {genericPoint (Spec (T.residueField t))} isClosed_singleton
  have hsupp := congrArg
    (fun I : ((pullback.snd (projection k) g).fiber t).IdealSheafData ↦
      (I.support : Set ((pullback.snd (projection k) g).fiber t)))
    (baseChangedEvaluationPoint_integralComponentAt k g t c)
  simp only [Scheme.IdealSheafData.support_comap, coe_support_integralComponentAt,
    Closeds.coe_preimage] at hsupp
  have hz' : z ∈ closure ({baseChangedEvaluationPoint k g t c} :
      Set ((pullback.snd (projection k) g).fiber t)) := by
    rw [← hsupp]
    exact hmap ▸ subset_closure (Set.mem_singleton _)
  simpa only [hc.closure_eq, Set.mem_singleton_iff] using hz'

/-! ### Translation of the coordinate -/

/-- The automorphism `t ↦ t + b` of `X = Spec k[x, y, t]` over the base, for `b` in the
coordinate ring of the base. -/
private def translationIso (k : Type u) [Field k] (b : BaseRing k) :
    totalScheme k ≅ totalScheme k :=
  Scheme.Spec.mapIso (Polynomial.algEquivAevalXAddC b).toRingEquiv.toCommRingCatIso.op

/-- Translation of the coordinate is an automorphism over the base. -/
private theorem translationIso_projection (k : Type u) [Field k] (b : BaseRing k) :
    (translationIso k b).hom ≫ projection k = projection k := by
  change Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC b).toRingHom) ≫
    Spec.map (CommRingCat.ofHom Polynomial.C) = Spec.map (CommRingCat.ofHom Polynomial.C)
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
  simp [Polynomial.algEquivAevalXAddC_apply]

/-- Translation by `b` carries the point at `t = c` to the point at `t = c + b`. -/
private theorem evaluationPointMap_translation (k : Type u) [Field k] (s : baseScheme k)
    (c : s.asIdeal.ResidueField) (b : BaseRing k) :
    evaluationPointMap k s c ≫ (translationIso k b).hom =
      evaluationPointMap k s (c + algebraMap (BaseRing k) s.asIdeal.ResidueField b) := by
  change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
    (algebraMap (BaseRing k) s.asIdeal.ResidueField) c)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC b).toRingHom) = _
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (Polynomial.ringHom_ext ?_ ?_))
  · intro r
    simp [Polynomial.algEquivAevalXAddC_apply]
  · simp [Polynomial.algEquivAevalXAddC_apply]

/-- Translation by `b` is the identity on any affine scheme over `X` whose structure morphism to
the base factors through a residue field in which `b` vanishes. -/
private theorem translation_fixed_of_factorization (k : Type u) [Field k] {W : Scheme.{u}}
    [IsAffine W] (h : W ⟶ totalScheme k) (s : baseScheme k)
    (q : W ⟶ Spec (.of s.asIdeal.ResidueField)) (b : BaseRing k)
    (hfac : h ≫ projection k =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap (BaseRing k) s.asIdeal.ResidueField)))
    (hb : algebraMap (BaseRing k) s.asIdeal.ResidueField b = 0) :
    h ≫ (translationIso k b).hom = h := by
  obtain ⟨H, hH⟩ := Spec.map_surjective (W.isoSpec.inv ≫ h)
  obtain ⟨Q, hQ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ q)
  have hcomp : Spec.map H ≫ projection k =
      Spec.map Q ≫ Spec.map
        (CommRingCat.ofHom (algebraMap (BaseRing k) s.asIdeal.ResidueField)) := by
    rw [hH, hQ, Category.assoc, hfac, Category.assoc]
  change Spec.map H ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = _ at hcomp
  rw [← Spec.map_comp, ← Spec.map_comp] at hcomp
  have hr := congrArg (fun φ ↦ φ.hom) (Spec.map_injective hcomp)
  have hbH : H.hom (Polynomial.C b) = 0 := by
    have hrb := RingHom.congr_fun hr b
    change H.hom (Polynomial.C b) =
      Q.hom (algebraMap (BaseRing k) s.asIdeal.ResidueField b) at hrb
    simpa only [hb, map_zero] using hrb
  apply (cancel_epi W.isoSpec.inv).mp
  rw [← Category.assoc, ← hH]
  change Spec.map H ≫
    Spec.map (CommRingCat.ofHom (Polynomial.algEquivAevalXAddC b).toRingHom) = Spec.map H
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (Polynomial.ringHom_ext ?_ ?_))
  · intro r
    simp [Polynomial.algEquivAevalXAddC_apply]
  · simp [Polynomial.algEquivAevalXAddC_apply, hbH]

/-- Translation by `b` is the identity on the fibre over a point in whose residue field `b`
vanishes. -/
private theorem translation_fixed_on_fiber (k : Type u) [Field k] (s : baseScheme k)
    (b : BaseRing k) (hb : algebraMap (BaseRing k) s.asIdeal.ResidueField b = 0) :
    (projection k).fiberι s ≫ (translationIso k b).hom = (projection k).fiberι s := by
  refine translation_fixed_of_factorization k ((projection k).fiberι s) s
    ((projection k).fiberToSpecResidueField s ≫
      Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) s).inv) b ?_ hb
  change pullback.fst _ _ ≫ _ = _
  rw [pullback.condition]
  dsimp only [Scheme.Hom.fiberToSpecResidueField]
  exact (congrArg
    (fun φ ↦ pullback.snd (projection k) ((baseScheme k).fromSpecResidueField s) ≫ φ)
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of (BaseRing k))
      s)).symm.trans (Category.assoc _ _ _).symm

/-- Translation of the coordinate, carried along a base change `g : T ⟶ S`. -/
private def baseChangedTranslationIso (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (b : BaseRing k) :
    pullback (projection k) g ≅ pullback (projection k) g :=
  asIso (pullback.map (projection k) g (projection k) g (translationIso k b).hom (𝟙 _) (𝟙 _)
    (by simpa using (translationIso_projection k b).symm) (by simp))

/-- The base-changed translation is the translation on the first projection. -/
private theorem baseChangedTranslationIso_fst (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (b : BaseRing k) :
    (baseChangedTranslationIso k g b).hom ≫ pullback.fst (projection k) g =
      pullback.fst (projection k) g ≫ (translationIso k b).hom :=
  pullback.lift_fst _ _ _

/-- The base-changed translation is an automorphism over the new base. -/
private theorem baseChangedTranslationIso_snd (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (b : BaseRing k) :
    (baseChangedTranslationIso k g b).hom ≫ pullback.snd (projection k) g =
      pullback.snd (projection k) g := by
  dsimp only [baseChangedTranslationIso, asIso_hom, pullback.map]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The base-changed translation by `b` is the identity on the fibre over a point of the new base
in whose residue field the image of `b` vanishes. -/
private theorem baseChangedTranslation_fixed_on_fiber (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (b : BaseRing k)
    (hb : algebraMap (BaseRing k) (g t).asIdeal.ResidueField b = 0) :
    (pullback.snd (projection k) g).fiberι t ≫ (baseChangedTranslationIso k g b).hom =
      (pullback.snd (projection k) g).fiberι t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangedTranslationIso_fst, ← Category.assoc,
      ← restrictedFiberMap_baseChange_fiberι, Category.assoc,
      translation_fixed_on_fiber k (g t) b hb, restrictedFiberMap_baseChange_fiberι]
  · rw [Category.assoc, baseChangedTranslationIso_snd]

/-- The section at `t = c` of the fibre of a base change, read in the total space. -/
private theorem baseChangedEvaluationSection_fst (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) :
    baseChangedEvaluationSection k g t c ≫ (pullback.snd (projection k) g).fiberι t ≫
        pullback.fst (projection k) g =
      Spec.map (g.residueFieldMap t) ≫
        Spec.map (Scheme.Spec.residueFieldIso (.of (BaseRing k)) (g t)).inv ≫
          evaluationPointMap k (g t) c := by
  rw [← restrictedFiberMap_baseChange_fiberι, ← Category.assoc]
  change (baseChangedSection _ _ _ ≫ restrictedFiberMap (projection k)
    (pullback.snd (projection k) g) (pullback.fst (projection k) g) g pullback.condition t) ≫ _ = _
  rw [baseChangedSection_fst]
  simp only [evaluationRationalSection, Category.assoc, evaluationSectionMap_fiberι]

/-- Translation by `b` carries the section at `t = c` of the fibre of a base change to the
section at `t = c + b`. -/
private theorem baseChangedEvaluationSection_translation (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (c : (g t).asIdeal.ResidueField) (b : BaseRing k) :
    (baseChangedEvaluationSection k g t c ≫ (pullback.snd (projection k) g).fiberι t) ≫
        (baseChangedTranslationIso k g b).hom =
      baseChangedEvaluationSection k g t
          (c + algebraMap (BaseRing k) (g t).asIdeal.ResidueField b) ≫
        (pullback.snd (projection k) g).fiberι t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangedTranslationIso_fst, ← Category.assoc,
      Category.assoc (baseChangedEvaluationSection k g t c), baseChangedEvaluationSection_fst]
    simp only [Category.assoc, evaluationPointMap_translation, baseChangedEvaluationSection_fst]
  · rw [Category.assoc, baseChangedTranslationIso_snd]
    have h (d : (g t).asIdeal.ResidueField) :
        (baseChangedEvaluationSection k g t d ≫ (pullback.snd (projection k) g).fiberι t) ≫
          pullback.snd (projection k) g = T.fromSpecResidueField t := by
      rw [Category.assoc]
      rw [show (pullback.snd (projection k) g).fiberι t ≫ pullback.snd (projection k) g =
        (pullback.snd (projection k) g).fiberToSpecResidueField t ≫ T.fromSpecResidueField t from
        pullback.condition, ← Category.assoc]
      change (baseChangedSection _ _ _ ≫
        (pullback.snd (projection k) g).fiberToSpecResidueField t) ≫ _ = _
      rw [baseChangedSection_snd, Category.id_comp]
    rw [h, h]

/-! ### The example family is a relative `0`-cycle -/

/-- On the fibre of a base change over a point whose residue field has `b ≠ 0`, the base change
of the example family is the difference of the two rational points at `t = a/b` and
`t = (a + b²)/b`. -/
private theorem baseChange_exampleFamily_apply (k : Type u) [Field k] {T : Scheme.{u}}
    (g : T ⟶ baseScheme k) (t : T) (hb : yImage k (g t) ≠ 0) :
    (baseChangeFamily (projection k) g 0 (exampleFamily k) t :
        AlgebraicCycle ((pullback.snd (projection k) g).fiber t) ℤ) =
      twoPointCycle (baseChangedEvaluationPoint k g t (xImage k (g t) / yImage k (g t)))
        (baseChangedEvaluationPoint k g t
          ((xImage k (g t) + yImage k (g t) ^ 2) / yImage k (g t))) := by
  refine baseChangeFamily_eq_twoPointCycle (projection k) g (exampleFamily k) t
    (firstPoint k (g t)) (secondPoint k (g t)) _ _ (exampleFamily_of_ne_zero k (g t) hb)
    (baseChangedEvaluationPoint_map k g t _) (baseChangedEvaluationPoint_map k g t _)
    (baseChangedEvaluationPoint_integralComponentAt k g t _)
    (baseChangedEvaluationPoint_integralComponentAt k g t _)
    (baseChangedEvaluationPoint_relativeDimension k g t _)
    (baseChangedEvaluationPoint_relativeDimension k g t _)

/-- **Stacks Project, Tag 0H5J.** The family `α` of Suslin--Voevodsky's example is a relative
`0`-cycle: it is compatible with specializations. Over a discrete valuation ring `R` with a
morphism `g : Spec R ⟶ S` there are three cases. If `b = 0` in the residue field of the generic
point of `Spec R` then it also vanishes at the closed point, so both members of the base change
are zero. If `b ≠ 0` at the generic point but `b = 0` at the closed point, then the translation
`t ↦ t + y` of the affine line is the identity on the special fibre and carries the first of the
two rational points to the second, so their fundamental cycles have the same specialization and
the difference specializes to zero, which is the vanishing member at the closed point. If
`b ≠ 0` at the closed point then `y` is a unit of `R`, the value `a/b` lies in `R` and the two
points of the generic fibre extend to closed sections of `X ×_S Spec R` over `Spec R`, whose
values at the closed point are the two rational points of the special fibre; the specialization
of the fundamental cycle of a section is the prime cycle of its closed value. -/
@[stacks 0H5J "the example family is a relative 0-cycle, compatible with specializations"]
theorem isRelativeCycle_exampleFamily (k : Type u) [Field k] :
    IsRelativeCycle (projection k) 0 (exampleFamily k) := by
  classical
  intro R _ _ _ g
  set η : Spec (.of R) := genericPoint (Spec (.of R)) with hη
  set s : Spec (.of R) := IsLocalRing.closedPoint R with hs
  by_cases hy : MvPolynomial.X (1 : Fin 2) ∈ (g η).asIdeal
  · have hle : (g η).asIdeal ≤ (g s).asIdeal :=
      (PrimeSpectrum.le_iff_specializes (g η) (g s)).mpr
        ((specializes_iff_mem_closure.mpr (by rw [genericPoint_closure]; trivial)).map
          g.continuous)
    rw [baseChangeFamily_apply_eq_zero _ _ _ _ _
        (exampleFamily_of_eq_zero k (g η) ((yImage_eq_zero_iff k (g η)).mpr hy)),
      baseChangeFamily_apply_eq_zero _ _ _ _ _
        (exampleFamily_of_eq_zero k (g s) ((yImage_eq_zero_iff k (g s)).mpr (hle hy))),
      specializationCycle_zero]
  · have hne (z : Spec (.of R)) (hz : MvPolynomial.X (1 : Fin 2) ∉ (g z).asIdeal) :
        yImage k (g z) ≠ 0 := fun h ↦ hz ((yImage_eq_zero_iff k (g z)).mp h)
    have hb := hne η hy
    set p := baseChangedEvaluationPoint k g η (xImage k (g η) / yImage k (g η)) with hp
    set q := baseChangedEvaluationPoint k g η
      ((xImage k (g η) + yImage k (g η) ^ 2) / yImage k (g η)) with hq
    have hβ : baseChangeFamily (projection k) g 0 (exampleFamily k) η =
        integralGenericCycle (pullback.snd (projection k) g) 0 p -
          integralGenericCycle (pullback.snd (projection k) g) 0 q := by
      apply Subtype.ext
      rw [baseChange_exampleFamily_apply k g η hb, hp, hq,
        integralGenericCycle_sub_apply (pullback.snd (projection k) g) _ _
          (baseChangedEvaluationPoint_relativeDimension k g η _)
          (baseChangedEvaluationPoint_relativeDimension k g η _)]
    have htrans (z : Spec (.of R)) (hbz : yImage k (g z) ≠ 0) :
        (baseChangedTranslationIso k g (MvPolynomial.X (1 : Fin 2))).hom
          ((pullback.snd (projection k) g).fiberι z
            (baseChangedEvaluationPoint k g z (xImage k (g z) / yImage k (g z)))) =
        (pullback.snd (projection k) g).fiberι z (baseChangedEvaluationPoint k g z
          ((xImage k (g z) + yImage k (g z) ^ 2) / yImage k (g z))) := by
      have hc : xImage k (g z) / yImage k (g z) + yImage k (g z) =
          (xImage k (g z) + yImage k (g z) ^ 2) / yImage k (g z) := by field_simp [hbz]
      have he := baseChangedEvaluationSection_translation k g z
        (xImage k (g z) / yImage k (g z)) (MvPolynomial.X (1 : Fin 2))
      rw [show xImage k (g z) / yImage k (g z) +
          algebraMap (BaseRing k) (g z).asIdeal.ResidueField (MvPolynomial.X (1 : Fin 2)) =
            (xImage k (g z) + yImage k (g z) ^ 2) / yImage k (g z) from hc] at he
      exact congrArg (fun φ : Spec ((Spec (.of R)).residueField z) ⟶ _ ↦
        φ (genericPoint (Spec ((Spec (.of R)).residueField z)))) he
    by_cases hys : MvPolynomial.X (1 : Fin 2) ∈ (g s).asIdeal
    · rw [hβ, baseChangeFamily_apply_eq_zero _ _ _ _ _
        (exampleFamily_of_eq_zero k (g s) ((yImage_eq_zero_iff k (g s)).mpr hys))]
      exact specializationCycle_sub_eq_zero_of_iso_fixed (pullback.snd (projection k) g) 0
        (baseChangedTranslationIso k g (MvPolynomial.X (1 : Fin 2)))
        (baseChangedTranslation_fixed_on_fiber k g s _
          (Ideal.algebraMap_residueField_eq_zero.mpr hys))
        p q (htrans η hb)
        (by simpa using baseChangedEvaluationPoint_relativeDimension k g η _)
        (by simpa using baseChangedEvaluationPoint_relativeDimension k g η _)
    · obtain ⟨G, hG⟩ := Spec.map_surjective g
      have hu : IsUnit (G.hom (MvPolynomial.X (1 : Fin 2))) := by
        apply IsLocalRing.notMem_maximalIdeal.mp
        change MvPolynomial.X (1 : Fin 2) ∉ (Spec.map G s).asIdeal
        rwa [hG]
      obtain ⟨v, hv⟩ := hu
      set d : R := G.hom (MvPolynomial.X (0 : Fin 2)) * ↑(v⁻¹) with hd'
      have hd : G.hom (MvPolynomial.X (1 : Fin 2)) * d =
          G.hom (MvPolynomial.X (0 : Fin 2)) := by
        rw [hd', ← hv, mul_left_comm, Units.mul_inv, mul_one]
      set H : Spec (.of R) ⟶ totalScheme k :=
        Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom G.hom d)) with hH'
      have hH : H ≫ projection k = g := by
        rw [hH']
        change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom G.hom d)) ≫
          Spec.map (CommRingCat.ofHom Polynomial.C) = g
        rw [← Spec.map_comp, ← hG]
        exact congrArg Spec.map (CommRingCat.hom_ext (Polynomial.eval₂RingHom_comp_C _ _))
      set σ : Spec (.of R) ⟶ pullback (projection k) g :=
        pullback.lift H (𝟙 _) (by simpa using hH) with hσ'
      have hσ : σ ≫ pullback.snd (projection k) g = 𝟙 _ := pullback.lift_snd _ _ _
      have hσfst : σ ≫ pullback.fst (projection k) g = H := pullback.lift_fst _ _ _
      have hpσ (z : Spec (.of R)) (hz : MvPolynomial.X (1 : Fin 2) ∉ (g z).asIdeal) :
          sectionFiberPoint (pullback.snd (projection k) g) σ hσ z =
            baseChangedEvaluationPoint k g z (xImage k (g z) / yImage k (g z)) := by
        refine eq_baseChangedEvaluationPoint k g z _ _ ?_
        rw [sectionFiberPoint_fiberι]
        change (σ ≫ pullback.fst (projection k) g) z = _
        rw [hσfst]
        have hHz : projection k (H z) = g z := congrArg (fun φ ↦ φ z) hH
        have hyH : Polynomial.C (MvPolynomial.X (1 : Fin 2)) ∉ (H z).asIdeal := by
          change MvPolynomial.X (1 : Fin 2) ∉ (projection k (H z)).asIdeal
          rwa [hHz]
        have hxyH : Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
            Polynomial.C (MvPolynomial.X (0 : Fin 2)) ∈ (H z).asIdeal := by
          change Polynomial.eval₂ G.hom d
            (Polynomial.C (MvPolynomial.X (1 : Fin 2)) * Polynomial.X -
              Polynomial.C (MvPolynomial.X (0 : Fin 2))) ∈ z.asIdeal
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
            Polynomial.eval₂_X, hd, sub_self]
          exact z.asIdeal.zero_mem
        refine (eq_evaluationPoint_of_mem_graph k (H z) hyH hxyH).trans
          (congrArg (fun w : baseScheme k ↦ evaluationPoint k w (xImage k w / yImage k w)) hHz)
      set τ : Spec (.of R) ⟶ pullback (projection k) g :=
        σ ≫ (baseChangedTranslationIso k g (MvPolynomial.X (1 : Fin 2))).hom with hτ'
      have hτ : τ ≫ pullback.snd (projection k) g = 𝟙 _ := by
        rw [hτ', Category.assoc, baseChangedTranslationIso_snd, hσ]
      have hqτ (z : Spec (.of R)) (hz : MvPolynomial.X (1 : Fin 2) ∉ (g z).asIdeal) :
          sectionFiberPoint (pullback.snd (projection k) g) τ hτ z =
            baseChangedEvaluationPoint k g z
              ((xImage k (g z) + yImage k (g z) ^ 2) / yImage k (g z)) := by
        apply ((pullback.snd (projection k) g).fiberι z).isEmbedding.injective
        rw [sectionFiberPoint_fiberι]
        change (baseChangedTranslationIso k g (MvPolynomial.X (1 : Fin 2))).hom (σ z) = _
        rw [← sectionFiberPoint_fiberι (pullback.snd (projection k) g) σ hσ z, hpσ z hz]
        exact htrans z (hne z hz)
      have : IsSeparated (projection k) := by
        rw [projection]
        infer_instance
      have hσclosed : IsClosedImmersion σ := isClosedImmersion_of_comp_eq_id _ _ hσ
      have hτclosed : IsClosedImmersion τ := by rw [hτ']; infer_instance
      rw [hβ, ← specializationCycleHom_apply, map_sub, specializationCycleHom_apply,
        specializationCycleHom_apply,
        specializationCycle_integralGenericCycle _ 0 p
          (by simpa using baseChangedEvaluationPoint_relativeDimension k g η _),
        specializationCycle_integralGenericCycle _ 0 q
          (by simpa using baseChangedEvaluationPoint_relativeDimension k g η _)]
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro x
      rw [show p = sectionFiberPoint (pullback.snd (projection k) g) σ hσ η from (hpσ η hy).symm,
        show q = sectionFiberPoint (pullback.snd (projection k) g) τ hτ η from (hqτ η hy).symm]
      change (specializationIntegralCycle (pullback.snd (projection k) g) 0
          (sectionFiberPoint (pullback.snd (projection k) g) σ hσ η)).1 x -
        (specializationIntegralCycle (pullback.snd (projection k) g) 0
          (sectionFiberPoint (pullback.snd (projection k) g) τ hτ η)).1 x = _
      rw [specializationIntegralCycle_sectionFiberPoint _ σ hσ x,
        specializationIntegralCycle_sectionFiberPoint _ τ hτ x, hpσ s hys, hqτ s hys,
        ← twoPointCycle_apply, ← baseChange_exampleFamily_apply k g s (hne s hys)]

/-- **Stacks Project, Tag 0H5J.** There exist relative `0`-cycles which are not
equidimensional: Suslin--Voevodsky's family on `Spec k[x, y, t] ⟶ Spec k[x, y]` is one. -/
@[stacks 0H5J "there exist relative r-cycles which are not equidimensional"]
theorem exists_isRelativeCycle_not_isEquidimensional (k : Type u) [Field k] :
    ∃ α : FamilyOfCycles (projection k) 0,
      IsRelativeCycle (projection k) 0 α ∧ ¬ IsEquidimensional (projection k) 0 α :=
  ⟨exampleFamily k, isRelativeCycle_exampleFamily k, not_isEquidimensional_exampleFamily k⟩

end Stacks.Chow.NotEquidimensional

end
