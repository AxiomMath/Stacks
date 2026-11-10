module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardDivisor

/-!
# The degree of a principal divisor on a proper curve

Let `C = (S, δ)` be a Chow situation whose base is the spectrum of a field `K`, with `δ = 0`,
and let `c : X ⟶ S` be proper with `X` integral of delta-dimension one — a proper curve over
`K`. Stacks 02RU says that for a nonzero rational function `f` on `X`

  `∑_{x ∈ X closed} [κ(x) : K] · ord_{𝒪_{X,x}}(f) = 0`,

equivalently `c_*div(f) = 0`.

This file supplies the parts of that statement that do not need the graph construction of
Stacks 02RQ.

* The *equivalence of the two forms*. Over a one-point base the pushforward of a cycle has a
  single coefficient, the total weighted degree of the cycle, and at every point carrying a
  nonzero coefficient of `div(f)` the delta-dimension is preserved, so that the weight really
  is the residue-field degree. Hence `c_*div(f) = 0` if and only if the displayed sum vanishes
  (`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_iff`). The sum itself is named
  `Stacks.Chow.principalDivisorDegree`.
* That `f ↦ deg div(f)` is a *homomorphism*: the degree of a principal divisor is additive in
  the rational function (`Stacks.Chow.principalDivisorDegree_mul`), so Stacks 02RU need only be
  checked on a generating set of `R(X)^*`.
* The *reduction along a proper dominant morphism*, which is the step the Stacks proof takes
  after the graph construction. If `p : X ⟶ Y` is proper and dominant with `Y` integral, also
  of delta-dimension one over the base, then

    `deg div_X(f) = deg div_Y(Nm_{R(Y)}^{R(X)}(f))`

  (`Stacks.Chow.principalDivisorDegree_norm`), by the norm formula of Stacks 02RT and the
  functoriality of proper pushforward (Stacks 02R5). Consequently Stacks 02RU for `X` follows
  from Stacks 02RU for `Y`
  (`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant`). Taking `Y`
  to be the projective line is how Stacks 02RU is proved; see the implementation notes.

## Main definitions

* `Stacks.Chow.principalDivisorDegree` — the degree `∑_x ord_x(f) · [κ(x) : κ(c x)]` over the
  base of the principal divisor of a rational function.

## Main results

* `Stacks.Chow.relativeDimension_id` — the relative dimension function of the identity morphism
  is the dimension function of the base.
* `AlgebraicGeometry.Scheme.ord_one` — the order of vanishing of `1` is zero.
* `Stacks.Chow.properPushforward_principalDivisorCycle_apply` — over a one-point base with
  `δ = 0`, the unique coefficient of `c_*div(f)` is `principalDivisorDegree c f`.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_iff` — the two forms of Stacks
  02RU agree.
* `Stacks.Chow.principalDivisorDegree_mul` — additivity in the rational function.
* `Stacks.Chow.principalDivisorDegree_norm` — invariance under a proper dominant morphism of
  curves, through the norm of the function-field extension.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant` — Stacks 02RU
  descends along a proper dominant morphism of curves.

## Implementation notes

### Where Stacks 02RU itself is

Stacks 02RU is not proved in this file, and no declaration here carries its tag; it is
`Stacks.Chow.principalDivisorDegree_eq_zero` in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent`.

The source proves it by the graph construction of Stacks 02RQ, which is not in this repository.
The route actually taken avoids it: normalize, so that
`Stacks.Chow.principalDivisorDegree_norm` descends the degree from the normalization to `X` with
the norm acting trivially, because the normalization is birational
(`Stacks.Chow.bijective_dominantFunctionFieldMap_of_isBirational`); on the normal curve a
nonconstant regular function on a dense affine open is a rational map to `ℙ¹_K`
(`Stacks.Chow.exists_isDominant_partialMap_to_projectiveLine`) and extends to a morphism by
Stacks 0BXZ (`AlgebraicGeometry.toRationalMap_bijective`), which is proper because `X` is proper
over `K` and `ℙ¹_K` is separated over `K`; and the projective-line case is
`Stacks.Chow.principalDivisorDegree_projectiveLine_eq_zero`.

The norm formula of Stacks 02RT, which the Stacks proof uses for the second step, **is**
available in this repository as `Stacks.Chow.properPushforward_principalDivisorCycle`; that is
what `Stacks.Chow.principalDivisorDegree_norm` rests on.

### Local Noetherianity

`AlgebraicGeometry.Scheme.ord` is stated for a locally Noetherian integral scheme, so every
statement mentioning it carries `[IsLocallyNoetherian X]` as an instance hypothesis even where
that follows from the locally finite-type morphism to the locally Noetherian base; this is the
convention of `Stacks.Chow.principalDivisorCycle_apply`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The order of vanishing of the constant rational function `1` is zero at every point, the
companion of `AlgebraicGeometry.Scheme.ord_zero`. -/
@[simp]
theorem ord_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    X.ord (1 : X.functionField) x = 0 := by
  have h := X.ord_mul (x := x) (f := 1) (g := 1) one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

/-! ### The relative dimension function of the identity -/

/-- The dimension function propagated along the identity morphism is the dimension function
itself: the residue-field extension at a point is trivial, so its transcendence degree is
zero. -/
theorem relativeDimension_id {S : Scheme.{u}} (δ : DimensionFunction S) (s : S) :
    relativeDimension δ (𝟙 S) s = δ s := by
  let _ : Algebra ↑(S.residueField (((𝟙 S) : S ⟶ S) s)) ↑(S.residueField s) :=
    (Scheme.Hom.residueFieldMap (𝟙 S) s).hom.toAlgebra
  have : Algebra.IsAlgebraic ↑(S.residueField (((𝟙 S) : S ⟶ S) s)) ↑(S.residueField s) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, algebraMap ↑(S.residueField (((𝟙 S) : S ⟶ S) s))
        ↑(S.residueField s) y = x := ⟨x, by
      change ((Scheme.Hom.residueFieldMap (𝟙 S) s).hom) x = x
      rw [Scheme.residueFieldMap_id]
      rfl⟩
    exact isAlgebraic_algebraMap y
  rw [relativeDimension, trdeg_eq_zero]
  simp

/-! ### The degree of a principal divisor -/

/-- The degree over the base of the principal divisor of a rational function `f` on an integral
scheme `X` with structure morphism `c : X ⟶ S`:

  `deg div(f) = ∑_x ord_x(f) · [κ(x) : κ(c x)]`,

the displayed sum of Stacks 02RU. For a proper curve over a field the points contributing are
the closed points, and the weight there is `[κ(x) : K]`. -/
def principalDivisorDegree {X S : Scheme.{u}} (c : X ⟶ S) [IsIntegral X]
    [IsLocallyNoetherian X] (f : X.functionField) : ℤ :=
  ∑ᶠ x : X, X.ord f x * (c.residueDegree x : ℤ)

/-- On a compact scheme the prime divisors of a rational function are finite in number: local
finiteness of the support of `ord(f)`, which is Stacks 02RL, upgrades to finiteness. -/
theorem finite_support_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] (f : X.functionField) : (Function.support (X.ord f)).Finite := by
  simpa using (locallyFiniteSupport_ord X f).finite_inter_support_of_isCompact
    (W := (Set.univ : Set X)) isCompact_univ

/-- The degree of the principal divisor of `1` is zero. -/
@[simp]
theorem principalDivisorDegree_one {X S : Scheme.{u}} (c : X ⟶ S) [IsIntegral X]
    [IsLocallyNoetherian X] : principalDivisorDegree c (1 : X.functionField) = 0 := by
  simp [principalDivisorDegree]

/-- **Stacks 02RP, in degrees.** The degree of a principal divisor is additive in the rational
function: `deg div(fg) = deg div(f) + deg div(g)`. So the rational functions whose principal
divisor has degree zero form a subgroup of `R(X)^*`, and Stacks 02RU need only be checked on a
generating set of that group. -/
theorem principalDivisorDegree_mul {X S : Scheme.{u}} (c : X ⟶ S) [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisorDegree c (f * g) =
      principalDivisorDegree c f + principalDivisorDegree c g := by
  have hsupp : ∀ h : X.functionField,
      (Function.support fun x : X ↦ X.ord h x * (c.residueDegree x : ℤ)).Finite := fun h ↦
    (finite_support_ord h).subset fun x hx ↦ (mul_ne_zero_iff.mp hx).1
  unfold principalDivisorDegree
  rw [← finsum_add_distrib (hsupp f) (hsupp g)]
  exact finsum_congr fun x ↦ by rw [X.ord_mul hf hg, add_mul]

/-! ### The two forms of Stacks 02RU agree -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}}

/-- Over a one-point base with vanishing dimension function, the proper pushforward of the
principal divisor of a rational function on a curve has a single coefficient, namely the degree
`Stacks.Chow.principalDivisorDegree` of that principal divisor.

This is the computation behind the "in other words" of Stacks 02RU: the fibre of `c` is all of
`X`, and at a point of codimension one the delta-dimension over the base is `1 - 1 = 0`, which
is the delta-dimension of the base point, so the pushforward weight there is the residue-field
degree rather than zero. -/
theorem properPushforward_principalDivisorCycle_apply [Subsingleton C.S]
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : schemeDeltaDimension C c = ((1 : ℤ) : EInt))
    (f : X.functionField) (y : C.S) :
    (properPushforward C c (𝟙 C.S) c (by simp) 0
        (principalDivisorCycle C c hdim f) : AlgebraicCycle C.S ℤ) y =
      principalDivisorDegree c f := by
  change AlgebraicCycle.map c (relativeDimension C.dimensionFunction c)
      (relativeDimension C.dimensionFunction (𝟙 C.S))
      (principalDivisorCycle C c hdim f).1 y = _
  rw [AlgebraicCycle.map_apply_of_subsingleton, principalDivisorDegree]
  refine finsum_congr fun x ↦ ?_
  rw [principalDivisorCycle_apply]
  by_cases hx : coheight x = 1
  · have hdx : relativeDimension C.dimensionFunction c x = 0 := by
      have := relativeDimension_eq_sub_one_of_coheight_eq_one C c hdim hx
      omega
    have hdy : relativeDimension C.dimensionFunction (𝟙 C.S) (c.base x) = 0 := by
      rw [relativeDimension_id, hδ]
    simp [AlgebraicCycle.mapCoeff, hdx, hdy]
  · simp [Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- **The two forms of Stacks 02RU agree.** Over a one-point base with vanishing dimension
function, the proper pushforward `c_*div(f)` of the principal divisor of a rational function on
a curve vanishes exactly when the weighted sum `∑_x ord_x(f) · [κ(x) : K]` of Stacks 02RU
vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_iff [Subsingleton C.S] [Nonempty C.S]
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) (c : X ⟶ C.S) [IsProper c] [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : schemeDeltaDimension C c = ((1 : ℤ) : EInt))
    (f : X.functionField) :
    properPushforward C c (𝟙 C.S) c (by simp) 0 (principalDivisorCycle C c hdim f) = 0 ↔
      principalDivisorDegree c f = 0 := by
  obtain ⟨y⟩ := ‹Nonempty C.S›
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← properPushforward_principalDivisorCycle_apply C hδ c hdim f y, h]
    rfl
  · refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [show z = y from Subsingleton.elim z y,
      properPushforward_principalDivisorCycle_apply C hδ c hdim f y, h]
    rfl

/-- **The two forms of Stacks 02RU agree**, with the base presented as the spectrum of a field:
for a proper curve `c : X ⟶ Spec K` over a field and the zero dimension function, the proper
pushforward of the principal divisor of `f` vanishes exactly when the displayed sum
`∑_{x} [κ(x) : K] · ord_x(f)` of Stacks 02RU does. This is the hypothesis shape in which
Stacks 02RU is stated; what is missing for the vanishing itself is the graph construction of
Stacks 02RQ, see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic`. -/
theorem properPushforward_principalDivisorCycle_eq_zero_iff_of_eq_spec (k : Type u) [Field k]
    (hS : C.S = AlgebraicGeometry.Spec (.of k))
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) (c : X ⟶ C.S)
    [IsProper c] [IsIntegral X] [IsLocallyNoetherian X]
    (hdim : schemeDeltaDimension C c = (1 : EInt)) (f : X.functionField) :
    properPushforward C c (𝟙 C.S) c (by simp) 0 (principalDivisorCycle C c hdim f) = 0 ↔
      principalDivisorDegree c f = 0 := by
  have : Subsingleton C.S := by rw [hS]; infer_instance
  have : Nonempty C.S := by rw [hS]; infer_instance
  exact properPushforward_principalDivisorCycle_eq_zero_iff C hδ c hdim f

/-! ### Reduction along a proper dominant morphism -/

variable {Y : Scheme.{u}}

/-- **Stacks 02RT, in degrees.** Let `p : X ⟶ Y` be a proper dominant morphism of integral
schemes, both of delta-dimension one over a one-point base with vanishing dimension function.
Then the degree of the principal divisor of a nonzero rational function `f` on `X` equals the
degree of the principal divisor of its norm in the function-field extension `R(Y) ⊆ R(X)`:

  `deg div_X(f) = deg div_Y(Nm(f))`.

This is the step `c_*div_X(f) = c'_*p_*div_X(f) = c'_*div_Y(Nm(f))` of the proof of Stacks 02RU,
and it combines the norm formula of Stacks 02RT with the functoriality of proper pushforward
(Stacks 02R5). -/
theorem principalDivisorDegree_norm [Subsingleton C.S] [Nonempty C.S]
    (hδ : ∀ s : C.S, C.dimensionFunction s = 0) (sY : Y ⟶ C.S) [IsProper sY] [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Y) [IsProper p]
    [IsDominant p] (hnX : schemeDeltaDimension C (p ≫ sY) = ((1 : ℤ) : EInt))
    (hnY : schemeDeltaDimension C sY = ((1 : ℤ) : EInt))
    (f : X.functionField) (hf : f ≠ 0) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
    principalDivisorDegree (p ≫ sY) f =
      principalDivisorDegree sY (Algebra.norm Y.functionField f) := by
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
  obtain ⟨y⟩ := ‹Nonempty C.S›
  -- Stacks 02RT, read at the cycle index `0 = 1 - 1`
  have hnorm : properPushforward C (p ≫ sY) sY p rfl 0
      (principalDivisorCycle C (p ≫ sY) hnX f) =
        principalDivisorCycle C sY hnY (Algebra.norm Y.functionField f) :=
    properPushforward_principalDivisorCycle C (p ≫ sY) sY hnX hnY p rfl f hf
  rw [← properPushforward_principalDivisorCycle_apply C hδ (p ≫ sY) hnX f y,
    ← properPushforward_principalDivisorCycle_apply C hδ sY hnY _ y,
    ← properPushforward_properPushforward C (p ≫ sY) sY (𝟙 C.S) p sY rfl (by simp) 0, hnorm]

/-- **The reduction of Stacks 02RU along a proper dominant morphism.** If the degree of every
principal divisor on `Y` vanishes — Stacks 02RU for `Y` — and `p : X ⟶ Y` is proper and
dominant between integral schemes of delta-dimension one over a one-point base with vanishing
dimension function, then Stacks 02RU holds for `X`.

Together with the graph construction of Stacks 02RQ, which produces such a `p` with `Y` the
projective line, and the projective-line case
`Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero`, this proves Stacks 02RU. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_properDominant [Subsingleton C.S]
    [Nonempty C.S] (hδ : ∀ s : C.S, C.dimensionFunction s = 0) (sY : Y ⟶ C.S) [IsProper sY]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Y)
    [IsProper p] [IsDominant p] (hnX : schemeDeltaDimension C (p ≫ sY) = ((1 : ℤ) : EInt))
    (hnY : schemeDeltaDimension C sY = ((1 : ℤ) : EInt))
    (hY : ∀ g : Y.functionField, g ≠ 0 → principalDivisorDegree sY g = 0)
    (f : X.functionField) (hf : f ≠ 0) :
    properPushforward C (p ≫ sY) (𝟙 C.S) (p ≫ sY) (by simp) 0
      (principalDivisorCycle C (p ≫ sY) hnX f) = 0 := by
  let _ : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap p).toAlgebra
  rw [properPushforward_principalDivisorCycle_eq_zero_iff C hδ (p ≫ sY) hnX f,
    principalDivisorDegree_norm C hδ sY p hnX hnY f hf]
  exact hY _ ((isUnit_iff_ne_zero.mpr hf).map (Algebra.norm Y.functionField)).ne_zero

end Stacks.Chow

end
