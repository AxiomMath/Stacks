module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.Ideal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# An inseparable closed point admits no étale slice

Let `k` be an imperfect field of characteristic `p > 0` and let `a ∈ k` be an element which is
not a `p`-th power.  The ideal `𝔪 = (x, y^p - a)` of `k[x, y]` is maximal with residue field
`k[y]/(y^p - a) = k(a^{1/p})`, a purely inseparable extension of `k` of degree `p`, so `𝔪` is a
closed point `w` of `X = 𝐀²_k` lying on the one-dimensional fibre of the projection
`f : 𝐀²_k ⟶ 𝐀¹_k` over the closed point `(x)` of `𝐀¹_k`.  There is then no commutative diagram

```
S' --h--> X
 \        |
  g       f
   \      v
    ---> S
```

with `g` étale and `w` in the image of `h`.  So the separability hypothesis on `κ(x)/κ(s)` in
Stacks tag 057F cannot be dropped, not even when `x` is a closed point of a positive-dimensional
fibre.

## Main results

* `Stacks.AlgebraicGeometry.not_exists_etale_lift_through_inseparableClosedPoint`: for `a ∈ k`
  not a `p`-th power, no étale `g : S' ⟶ 𝐀¹_k` factors through the projection `𝐀²_k ⟶ 𝐀¹_k` by a
  morphism `h : S' ⟶ 𝐀²_k` whose image contains the closed point `(x, y^p - a)`.

## References

* [Stacks Project, Tag 057E](https://stacks.math.columbia.edu/tag/057E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace Stacks.AlgebraicGeometry

/-- **A separable extension in characteristic `p` contains no new `p`-th roots.**  If `E/F` is
separable, `F` has exponential characteristic `q` and `x ∈ E` has `x ^ q` in `F`, then `x` lies in
`F`. -/
private lemma mem_range_algebraMap_of_pow_mem_range {F E : Type*} [Field F] [Field E]
    [Algebra F E] (q : ℕ) [ExpChar F q] [Algebra.IsSeparable F E] {x : E}
    (hx : x ^ q ∈ (algebraMap F E).range) : x ∈ (algebraMap F E).range := by
  rw [← minpoly.natDegree_eq_one_iff,
    ← (Algebra.IsSeparable.isSeparable F x).natSepDegree_eq_natDegree,
    minpoly.natSepDegree_eq_one_iff_pow_mem q]
  exact ⟨1, by simpa using hx⟩

/-- **The evaluation map `R ⟶ κ(x)` at a point `x` of `Spec R`.**  It is the global evaluation
map of `Spec R` read through the identification of `R` with the global sections of `Spec R`. -/
private def specResidueEval (R : CommRingCat.{u}) (x : Spec R) :
    R ⟶ (Spec R).residueField x :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x

/-- **The evaluation map `R ⟶ κ(y)` along a morphism `φ : Y ⟶ Spec R`.** -/
private def residueEvalOfHom {Y : Scheme.{u}} {R : CommRingCat.{u}} (φ : Y ⟶ Spec R) (y : Y) :
    R ⟶ Y.residueField y :=
  (Scheme.ΓSpecIso R).inv ≫ Scheme.Hom.appTop φ ≫ Y.Γevaluation y

/-- **Evaluating along `φ` factors through the residue field of the image point.** -/
private lemma residueEvalOfHom_eq {Y : Scheme.{u}} {R : CommRingCat.{u}} (φ : Y ⟶ Spec R)
    (y : Y) :
    residueEvalOfHom φ y = specResidueEval R (φ.base y) ≫ φ.residueFieldMap y := by
  rw [specResidueEval, residueEvalOfHom, Category.assoc, ← Scheme.Γevaluation_naturality]

/-- **Evaluating along a composite `φ ≫ Spec.map ψ` is evaluating along `φ` after `ψ`.** -/
private lemma residueEvalOfHom_comp {Y : Scheme.{u}} {R S : CommRingCat.{u}} (ψ : R ⟶ S)
    (φ : Y ⟶ Spec S) (y : Y) :
    residueEvalOfHom (φ ≫ Spec.map ψ) y = ψ ≫ residueEvalOfHom φ y := by
  simp only [residueEvalOfHom, Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]

/-- **Pointwise form of `residueEvalOfHom_eq`.** -/
private lemma residueEvalOfHom_hom_apply {Y : Scheme.{u}} {R : CommRingCat.{u}} (φ : Y ⟶ Spec R)
    (y : Y) (r : R) :
    (residueEvalOfHom φ y).hom r =
      (φ.residueFieldMap y).hom ((specResidueEval R (φ.base y)).hom r) := by
  rw [residueEvalOfHom_eq]; rfl

/-- **The evaluation map at `x` is the structure map of the residue field of the prime `x`.** -/
private lemma specResidueEval_eq (R : CommRingCat.{u}) (x : Spec R) [x.asIdeal.IsPrime] :
    specResidueEval R x =
      CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R x).inv := by
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv, specResidueEval]
  rfl

/-- **Pointwise form of `specResidueEval_eq`.** -/
private lemma specResidueEval_apply (R : CommRingCat.{u}) (x : Spec R) [x.asIdeal.IsPrime]
    (r : R) :
    (specResidueEval R x).hom r =
      (Scheme.Spec.residueFieldIso R x).inv.hom (algebraMap R x.asIdeal.ResidueField r) := by
  rw [specResidueEval_eq]; rfl

/-- **A section of `Spec R` vanishes in `κ(x)` exactly on the prime `x`.** -/
private lemma specResidueEval_eq_zero_iff (R : CommRingCat.{u}) (x : Spec R) (r : R) :
    (specResidueEval R x).hom r = 0 ↔ r ∈ x.asIdeal := by
  have : x.asIdeal.IsPrime := x.isPrime
  rw [specResidueEval_apply,
    map_eq_zero_iff _ (Scheme.Spec.residueFieldIso R x).inv.hom.injective,
    Ideal.algebraMap_residueField_eq_zero]

/-- **At a closed point the residue field is generated by the global sections.** -/
private lemma specResidueEval_surjective (R : CommRingCat.{u}) (x : Spec R)
    (hx : x.asIdeal.IsMaximal) : Function.Surjective (specResidueEval R x).hom := by
  have : x.asIdeal.IsPrime := x.isPrime
  have : x.asIdeal.IsMaximal := hx
  intro y
  obtain ⟨z, hz⟩ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R x).inv).2 y
  obtain ⟨r, hr⟩ := Ideal.algebraMap_residueField_surjective x.asIdeal z
  exact ⟨r, by rw [specResidueEval_apply, hr]; exact hz⟩

namespace InseparableSlice

variable {k : Type u} [Field k] {p : ℕ} {a : k}

/-- **The ideal `𝔪 = (x, y^p - a)` of `k[x, y]`.**  The polynomial ring `k[x, y]` is spelled
`(k[x])[y]`, so that `x` is `C X` and `y` is `X`. -/
def pointIdeal (a : k) (p : ℕ) : Ideal ((k[X])[X]) :=
  Ideal.span {C X, X ^ p - C (C a)}

/-- **The map `k[x, y] → k[y]/(y^p - a)` sending `x` to `0` and `y` to a `p`-th root of `a`.**
It is the reduction of coefficients along `x ↦ 0` followed by the quotient map. -/
def residueHom (a : k) (p : ℕ) : (k[X])[X] →+* AdjoinRoot (X ^ p - C a) :=
  (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : k)))

/-- **On the coefficient subring `k[x]` the map `residueHom` is evaluation at `x = 0`.** -/
lemma residueHom_comp_C :
    (residueHom a p).comp (C : k[X] →+* (k[X])[X])
      = (AdjoinRoot.of (X ^ p - C a)).comp (Polynomial.evalRingHom (0 : k)) :=
  RingHom.ext fun q => by
    show AdjoinRoot.mk _ (Polynomial.map (Polynomial.evalRingHom (0 : k)) (C q)) = _
    rw [Polynomial.map_C]
    rfl

/-- **The kernel of `residueHom` is `(x, y^p - a)`.** -/
lemma ker_residueHom : RingHom.ker (residueHom a p) = pointIdeal a p := by
  rw [residueHom, ← RingHom.comap_ker]
  have h1 : RingHom.ker (AdjoinRoot.mk (X ^ p - C a)) = Ideal.span {(X ^ p - C a : k[X])} := by
    ext x; simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have h2 : Ideal.map (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : k)))
      (Ideal.span {(X ^ p - C (C a) : (k[X])[X])}) = Ideal.span {(X ^ p - C a : k[X])} := by
    rw [Ideal.map_span]; simp
  rw [h1, ← h2, Ideal.comap_map_of_surjective _
    (Polynomial.map_surjective _ fun y => ⟨C y, by simp⟩),
    ← RingHom.ker_eq_comap_bot, Polynomial.ker_mapRingHom, Polynomial.ker_evalRingHom,
    Ideal.map_span, pointIdeal, Set.pair_comm]
  simp [Ideal.span_insert]

section

variable (hirr : Irreducible (X ^ p - C a))
include hirr

/-- **`(x, y^p - a)` is a maximal ideal of `k[x, y]`** when `y^p - a` is irreducible over `k`. -/
lemma isMaximal_pointIdeal : (pointIdeal a p).IsMaximal := by
  have : Fact (Irreducible (X ^ p - C a)) := ⟨hirr⟩
  rw [← ker_residueHom]
  exact RingHom.ker_isMaximal_of_surjective _
    (AdjoinRoot.mk_surjective.comp (Polynomial.map_surjective _ fun y => ⟨C y, by simp⟩))

/-- **The image of `(x, y^p - a)` in `k[x]` is the ideal `(x)`** when `y^p - a` is irreducible
over `k`.  Equivalently, the closed point `(x, y^p - a)` of `𝐀²_k` lies over the closed point `(x)`
of `𝐀¹_k`. -/
lemma comap_C_pointIdeal :
    Ideal.comap (C : k[X] →+* (k[X])[X]) (pointIdeal a p) = Ideal.span {(X : k[X])} := by
  have : Fact (Irreducible (X ^ p - C a)) := ⟨hirr⟩
  rw [← ker_residueHom, RingHom.comap_ker, residueHom_comp_C, ← RingHom.comap_ker,
    (RingHom.ker_eq_bot_iff_eq_zero _).mpr
      fun x hx => (AdjoinRoot.of (X ^ p - C a)).injective (by simpa using hx),
    ← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom]
  simp

/-- **The point of `𝐀¹_k` below `(x, y^p - a)` is closed** when `y^p - a` is irreducible over
`k`. -/
lemma isMaximal_comap_C_pointIdeal :
    (Ideal.comap (C : k[X] →+* (k[X])[X]) (pointIdeal a p)).IsMaximal := by
  rw [comap_C_pointIdeal hirr,
    show Ideal.span {(X : k[X])} = RingHom.ker (Polynomial.evalRingHom (0 : k)) by
      rw [Polynomial.ker_evalRingHom]; simp]
  exact RingHom.ker_isMaximal_of_surjective _ fun y => ⟨C y, by simp⟩

end

/-- **The affine line `S = 𝐀¹_k = Spec k[x]`.** -/
def affineLine (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k[X])

/-- **The affine plane `X = 𝐀²_k = Spec k[x, y]`.** -/
def affinePlane (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of ((k[X])[X]))

/-- **The projection `f : 𝐀²_k ⟶ 𝐀¹_k`,** the morphism induced by the inclusion
`k[x] → k[x, y]` of the coefficient subring. -/
def projection (k : Type u) [Field k] : affinePlane k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (C : k[X] →+* (k[X])[X]))

/-- **The closed point `w` of `𝐀²_k` given by the maximal ideal `(x, y^p - a)`.** -/
def closedPoint [Fact p.Prime] (a : k) (ha : ∀ b : k, b ^ p ≠ a) : affinePlane k :=
  ⟨pointIdeal a p,
    (isMaximal_pointIdeal (X_pow_sub_C_irreducible_of_prime Fact.out ha)).isPrime⟩

/-- **No étale lift through the prime `(x, y^p - a)`, for the bare spectra.**  If `a ∈ k` is not
a `p`-th power, no étale `g : S' ⟶ Spec k[x]` equals `h ≫ Spec.map C` for a morphism
`h : S' ⟶ Spec k[x, y]` whose image contains the prime `(x, y^p - a)`. -/
private theorem not_exists_etale_lift_aux [Fact p.Prime] [CharP k p] (a : k)
    (ha : ∀ b : k, b ^ p ≠ a) (hpr : (pointIdeal a p).IsPrime) :
    ¬ ∃ (S' : Scheme.{u}) (g : S' ⟶ Spec (CommRingCat.of k[X]))
        (h : S' ⟶ Spec (CommRingCat.of ((k[X])[X]))),
        Etale g ∧ h ≫ Spec.map (CommRingCat.ofHom (C : k[X] →+* (k[X])[X])) = g ∧
          (⟨pointIdeal a p, hpr⟩ : Spec (CommRingCat.of ((k[X])[X]))) ∈ Set.range h.base := by
  rintro ⟨S', g, h, hg, hcomm, s', hs'⟩
  have hirr : Irreducible (X ^ p - C a) := X_pow_sub_C_irreducible_of_prime Fact.out ha
  have : Fact (Irreducible (X ^ p - C a)) := ⟨hirr⟩
  have _ : Etale g := hg
  have hw : (h.base s').asIdeal = pointIdeal a p := by rw [hs']
  have hbase : g.base s' =
      (Spec.map (CommRingCat.ofHom (C : k[X] →+* (k[X])[X]))).base (h.base s') := by
    rw [← hcomm]; rfl
  have hgt : (g.base s').asIdeal = Ideal.comap (C : k[X] →+* (k[X])[X]) (pointIdeal a p) := by
    rw [hbase, hs']; rfl
  have hmax : (g.base s').asIdeal.IsMaximal := by
    rw [hgt]; exact isMaximal_comap_C_pointIdeal hirr
  let _ : Algebra ((Spec (CommRingCat.of k[X])).residueField (g.base s'))
      (S'.residueField s') := (g.residueFieldMap s').hom.toAlgebra
  have _ : Unramified g := unramified_of_etale g
  have _ : Algebra.IsSeparable ((Spec (CommRingCat.of k[X])).residueField (g.base s'))
      (S'.residueField s') := isSeparable_residueField_of_unramified g s'
  have _ : CharP ((Spec (CommRingCat.of k[X])).residueField (g.base s')) p :=
    charP_of_injective_ringHom
      ((specResidueEval (CommRingCat.of k[X]) (g.base s')).hom.comp
        (C : k →+* k[X])).injective p
  have _ : ExpChar ((Spec (CommRingCat.of k[X])).residueField (g.base s')) p :=
    ExpChar.prime Fact.out
  have hF3 : residueEvalOfHom g s' =
      CommRingCat.ofHom (C : k[X] →+* (k[X])[X]) ≫ residueEvalOfHom h s' := by
    rw [← hcomm]; exact residueEvalOfHom_comp _ _ _
  have hCC : (residueEvalOfHom g s').hom (C a) = (residueEvalOfHom h s').hom (C (C a)) := by
    rw [hF3]; rfl
  have hmemI : (X ^ p - C (C a) : (k[X])[X]) ∈ (h.base s').asIdeal := by
    rw [hw]; exact Ideal.subset_span (by simp)
  have hkill : (residueEvalOfHom h s').hom (X ^ p - C (C a)) = 0 := by
    rw [residueEvalOfHom_hom_apply, (specResidueEval_eq_zero_iff _ _ _).2 hmemI, map_zero]
  have hbp : (residueEvalOfHom h s').hom X ^ p = (residueEvalOfHom g s').hom (C a) := by
    rw [map_sub, map_pow, sub_eq_zero] at hkill
    rw [hkill, hCC]
  have e2 : (g.residueFieldMap s').hom
      ((specResidueEval (CommRingCat.of k[X]) (g.base s')).hom (C a))
      = (residueEvalOfHom g s').hom (C a) := (residueEvalOfHom_hom_apply g s' _).symm
  have hrange : (residueEvalOfHom h s').hom X ^ p ∈
      (algebraMap ((Spec (CommRingCat.of k[X])).residueField (g.base s'))
        (S'.residueField s')).range := by
    refine ⟨(specResidueEval (CommRingCat.of k[X]) (g.base s')).hom (C a), ?_⟩
    rw [RingHom.algebraMap_toAlgebra, e2]
    exact hbp.symm
  obtain ⟨γ, hγ⟩ := mem_range_algebraMap_of_pow_mem_range p hrange
  rw [RingHom.algebraMap_toAlgebra] at hγ
  obtain ⟨q, hq⟩ :=
    specResidueEval_surjective (CommRingCat.of k[X]) (g.base s') hmax γ
  have hz : (specResidueEval (CommRingCat.of k[X]) (g.base s')).hom (q ^ p - C a) = 0 := by
    refine (g.residueFieldMap s').hom.injective ?_
    simp only [map_sub, map_pow, map_zero]
    rw [hq, hγ, e2, ← hbp, sub_self]
  have hmem2 : (q ^ p - C a : k[X]) ∈ (g.base s').asIdeal :=
    (specResidueEval_eq_zero_iff _ _ _).1 hz
  rw [hgt] at hmem2
  have hmem3 : (residueHom a p) (C (q ^ p - C a)) = 0 := by
    rw [← RingHom.mem_ker, ker_residueHom]; exact Ideal.mem_comap.1 hmem2
  rw [← RingHom.comp_apply, residueHom_comp_C, RingHom.comp_apply] at hmem3
  refine ha (q.eval 0) ?_
  have := (AdjoinRoot.of (X ^ p - C a)).injective
    (show AdjoinRoot.of (X ^ p - C a) ((q ^ p - C a).eval 0)
        = AdjoinRoot.of (X ^ p - C a) 0 by simpa using hmem3)
  simpa [sub_eq_zero] using this

end InseparableSlice

open InseparableSlice in
/-- **No étale lift through an inseparable closed point.**  Let `k` be a field of characteristic
`p > 0` and let `a ∈ k` not be a `p`-th power, so that `k` is imperfect.  For the closed point `w`
of `X = 𝐀²_k` given by the maximal ideal `(x, y^p - a)` and the projection `f : X ⟶ S = 𝐀¹_k`,
there is no commutative diagram `h : S' ⟶ X`, `g : S' ⟶ S` with `h ≫ f = g`, `g` étale, and `w`
in the image of `h`. -/
@[stacks 057E]
theorem not_exists_etale_lift_through_inseparableClosedPoint {k : Type u} [Field k] {p : ℕ}
    [Fact p.Prime] [CharP k p] (a : k) (ha : ∀ b : k, b ^ p ≠ a) :
    ¬ ∃ (S' : Scheme.{u}) (g : S' ⟶ affineLine k) (h : S' ⟶ affinePlane k),
        Etale g ∧ h ≫ projection k = g ∧ closedPoint a ha ∈ Set.range h.base :=
  not_exists_etale_lift_aux a ha _

end Stacks.AlgebraicGeometry

end
