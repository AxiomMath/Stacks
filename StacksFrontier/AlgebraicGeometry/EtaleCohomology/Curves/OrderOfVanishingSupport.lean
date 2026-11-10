module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The divisor of a rational function has finite support

The second map of the divisor sequence of Stacks 03RM,
`j_* 𝐆_{m,K} ⟶ ⨁_x i_{x,*} ℤ`,
sends an invertible rational function `g` to the family of its orders of vanishing. For that family
to be a section of a *coproduct* at all, only finitely many of its members may be nonzero: this is
the statement that a rational function has finitely many zeros and poles, and it is what this file
proves.

The argument needs no commutative algebra beyond what the function field already supplies. A
nonzero element of the function field is, by
`AlgebraicGeometry.Scheme.exists_isUnit_germ_eq`, the germ of a section that is *invertible* on
some nonempty affine open `U`; the order of vanishing is trivial wherever a function is invertible
(`AlgebraicGeometry.Scheme.ord_of_isUnit`), so the support of the divisor is contained in the
closed set `Uᶜ`, which misses the generic point. The whole content is therefore the following
topological fact about a proper closed subset `Z` of an irreducible Noetherian scheme: `Z` carries
only finitely many points of codimension one. Indeed `Z` is a finite union of irreducible closed
subsets, each of which has a generic point `z`, and a point `x` of codimension one lying in the
component of `z` satisfies `x ≤ z < genericPoint X`, which forces `x = z` — a point strictly below
`z` would have codimension at least two.

## Main definitions

* `AlgebraicGeometry.Scheme.principalDivisor`: the divisor of a rational function, as an
  algebraic cycle (`AlgebraicGeometry.AlgebraicCycle`) on a Noetherian integral scheme.
* `AlgebraicGeometry.Scheme.principalDivisorHom`: the divisor map on the units of the function
  field, as a homomorphism of groups. This is the second map of the divisor sequence of
  Stacks 03RM read on global sections.

## Main results

* `AlgebraicGeometry.finite_setOf_coheight_eq_one_of_isClosed`: a closed subset of an irreducible
  Noetherian scheme that misses the generic point contains only finitely many points of
  codimension one.
* `AlgebraicGeometry.Scheme.finite_support_ord`: **a rational function on a Noetherian integral
  scheme has finitely many zeros and poles.**
* `AlgebraicGeometry.Scheme.exists_opens_forall_ord_eq_zero`: **a codimension-one point has an
  open neighbourhood on which a given rational function has no other zero or pole.** This is the
  shrinking step of the local principality of a divisor, and the only input the right-hand
  exactness of Stacks 03RI needs beyond the existence of a function of prescribed order.
* `AlgebraicGeometry.Scheme.principalDivisor_mul`: the divisor of a product is the sum of the
  divisors.
* `AlgebraicGeometry.Scheme.principalDivisor_apply_of_isUnit` and
  `AlgebraicGeometry.Scheme.principalDivisor_eq_zero_of_isUnit`: a function invertible on an open
  has divisor coefficient zero there, so an invertible *global* function has divisor zero. The
  latter is the composite of the first two maps of the divisor sequence of Stacks 03RM being zero,
  read on global sections.
* `AlgebraicGeometry.IsCurve.finite_support_ord`: the same on a locally Noetherian curve, where
  the order of vanishing is `AlgebraicGeometry.IsCurve.ordHom` and is available at every
  non-generic point.
* `AlgebraicGeometry.IsCurve.ord_eq_zero_iff_ordHom_eq_one`: the coefficient of the divisor
  vanishes at a non-generic point of a curve exactly when the multiplicative order of vanishing
  there is trivial. This is what identifies the support of the divisor with the set of closed
  points at which the second map of the divisor sequence of Stacks 03RM is nonzero.

## Implementation notes

Noetherianity is imposed on the *space*, as `TopologicalSpace.NoetherianSpace`, rather than on the
scheme: that is all the proof uses, and it is the hypothesis that an étale `X`-scheme inherits from
a Noetherian `X` once it is quasi-compact. On a curve it is derived instead: a variety over a field
is quasi-compact over the field, hence has a compact space, and with local Noetherianity this is
`AlgebraicGeometry.IsNoetherian`.

The support is finite, not merely locally finite, so the algebraic cycle
`AlgebraicGeometry.Scheme.principalDivisor` is built with the whole space as the neighbourhood
witnessing local finiteness.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the divisor sequence,
  whose second map is the order of vanishing at the closed points.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- A proper specialization is a strict inequality in the specialization order. -/
private theorem lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : y ⤳ x) (hne : x ≠ y) :
    x < y :=
  ⟨le_iff_specializes.2 h, fun h' => hne (h.antisymm (le_iff_specializes.1 h')).eq.symm⟩

/-- A point strictly above a point of codimension one has codimension zero. -/
private theorem coheight_eq_zero_of_coheight_eq_one_of_lt {X : Scheme.{u}} {x y : X}
    (hx : coheight x = 1) (hxy : x < y) : coheight y = 0 := by
  have hx1 : coheight x ≤ ((1 : ℕ) : ℕ∞) := by rw [hx]; simp
  simpa using Order.coheight_le_coe_iff.1 hx1 y hxy

/-- **A closed subset of an irreducible Noetherian scheme that misses the generic point contains
only finitely many points of codimension one.**

The closed set is a finite union of irreducible closed subsets, and each of those contains at most
one point of codimension one, namely its own generic point: a point of the component that is
strictly below the component's generic point has that generic point and the generic point of the
whole scheme strictly above it, hence codimension at least two. -/
theorem finite_setOf_coheight_eq_one_of_isClosed {X : Scheme.{u}} [IrreducibleSpace X]
    [NoetherianSpace X] {Z : Set X} (hZ : IsClosed Z) (hZ' : genericPoint X ∉ Z) :
    {x : X | x ∈ Z ∧ coheight x = 1}.Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine Set.Finite.subset
    (hSfin.biUnion (t := fun t : Set X => {x : X | x ∈ t ∧ coheight x = 1}) ?_) ?_
  · intro t htS
    set z := (hSirr t htS).genericPoint with hzdef
    have hz : IsGenericPoint z t := (hSirr t htS).isGenericPoint_genericPoint (hScl t htS)
    have hzlt : z < genericPoint X :=
      lt_genericPoint fun h => hZ' (h ▸ hSU ▸ Set.mem_sUnion_of_mem hz.mem htS)
    have hz0 : coheight z ≠ 0 := Order.coheight_ne_zero.2 (not_isMax_of_lt hzlt)
    have key : ∀ x ∈ {x : X | x ∈ t ∧ coheight x = 1}, x = z := by
      rintro x ⟨hxt, hx1⟩
      by_contra hne
      exact hz0 (coheight_eq_zero_of_coheight_eq_one_of_lt hx1
        (lt_of_specializes_of_ne (hz.specializes hxt) hne))
    exact Set.Subsingleton.finite fun a ha b hb => (key a ha).trans (key b hb).symm
  · rintro x ⟨hxZ, hx1⟩
    obtain ⟨t, htS, hxt⟩ := hSU ▸ hxZ
    exact Set.mem_biUnion htS ⟨hxt, hx1⟩

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A rational function on a Noetherian integral scheme has finitely many zeros and poles.**

This is the finiteness that makes the family of orders of vanishing of a rational function a
section of the coproduct `⨁_x i_{x,*} ℤ`, hence the finiteness underlying the second map of the
divisor sequence of Stacks 03RM. -/
theorem finite_support_ord [NoetherianSpace X] (g : X.functionField) :
    {x : X | ord g x ≠ 0}.Finite := by
  by_cases hg : g = 0
  · subst hg
    simp
  obtain ⟨U, -, g', hUne, hgerm, hunit⟩ := exists_isUnit_germ_eq X g hg
  have : Nonempty U := hUne
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  refine Set.Finite.subset (finite_setOf_coheight_eq_one_of_isClosed (Z := (U : Set X)ᶜ)
    U.isOpen.isClosed_compl (by simpa using hgen)) ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  refine ⟨fun hxU => hx (hgerm ▸ ord_of_isUnit hunit hxU), ?_⟩
  by_contra hc
  exact hx (ord_eq_zero_of_coheight_neq_one hc g)

/-- **A rational function has no zeros or poles besides `x` on a neighbourhood of a
codimension-one point `x`.**

The zeros and poles are finite in number by `AlgebraicGeometry.Scheme.finite_support_ord`, so the
complement of the closures of those other than `x` is open; the content is that it still contains
`x`. Were `x` in the closure of another point `y` of the support, then `x < y` in the
specialization order, and a point strictly above a point of codimension one has codimension zero,
where the order of vanishing is zero by
`AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one`.

This is the shrinking step of the local principality of a divisor on a nonsingular curve; combined
with the existence of a function of prescribed order it gives
`AlgebraicGeometry.IsCurve.exists_ord_eq_and_forall_ord_eq_zero`, the local input to the
right-hand exactness of Stacks 03RI. Nothing about curves or smoothness is used here, only that
`x` has codimension one. -/
theorem exists_opens_forall_ord_eq_zero [NoetherianSpace X] {x : X} (hx : coheight x = 1)
    (g : X.functionField) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, y ≠ x → ord g y = 0 := by
  have hord : ∀ y : X, x < y → ord g y = 0 := fun y hxy =>
    ord_eq_zero_of_coheight_neq_one
      (by simp [coheight_eq_zero_of_coheight_eq_one_of_lt hx hxy]) g
  have hZ : IsClosed (⋃ y ∈ {y : X | ord g y ≠ 0} \ {x}, closure ({y} : Set X)) :=
    Set.Finite.isClosed_biUnion ((finite_support_ord g).subset Set.sdiff_subset)
      fun _ _ => isClosed_closure
  refine ⟨⟨_, hZ.isOpen_compl⟩, ?_, fun y hyU hyx => ?_⟩
  · intro hmem
    obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 hmem
    exact hyT.1 (hord y (lt_of_specializes_of_ne (specializes_iff_mem_closure.2 hxy)
      (Ne.symm hyT.2)))
  · by_contra hy
    exact hyU (Set.mem_biUnion (show y ∈ {y : X | ord g y ≠ 0} \ {x} from ⟨hy, hyx⟩)
      (subset_closure rfl))

/-- **The divisor of a rational function on a Noetherian integral scheme**, as an algebraic cycle:
the function assigning to each point the order of vanishing there, whose support is finite by
`AlgebraicGeometry.Scheme.finite_support_ord`. On a curve this is the value at the generic fibre of
the second map of the divisor sequence of Stacks 03RM. -/
def principalDivisor [NoetherianSpace X] (g : X.functionField) : AlgebraicCycle X ℤ where
  toFun x := ord g x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem, by rw [Set.univ_inter]; exact finite_support_ord g⟩

/-- The coefficient of the divisor of `g` at `x` is the order of vanishing of `g` at `x`. -/
@[simp]
theorem principalDivisor_apply [NoetherianSpace X] (g : X.functionField) (x : X) :
    principalDivisor g x = ord g x :=
  rfl

/-- The order of vanishing of the constant function `1` is zero at every point. -/
@[simp]
theorem ord_one (x : X) : ord (1 : X.functionField) x = 0 := by
  have h := ord_mul (x := x) (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

/-- The divisor of the constant rational function `1` is zero. -/
@[simp]
theorem principalDivisor_one [NoetherianSpace X] :
    principalDivisor (1 : X.functionField) = 0 :=
  Function.locallyFinsuppWithin.ext fun x => by simp

/-- **The divisor of a product is the sum of the divisors.** -/
theorem principalDivisor_mul [NoetherianSpace X] {g h : X.functionField} (hg : g ≠ 0)
    (hh : h ≠ 0) :
    principalDivisor (g * h) = principalDivisor g + principalDivisor h :=
  Function.locallyFinsuppWithin.ext fun x => by simp [ord_mul hg hh]

/-- **The divisor map on the units of the function field**, as a homomorphism from the
multiplicative group of the function field, written additively, to the group of algebraic cycles.

Over a curve this is the second map of the divisor sequence of Stacks 03RM evaluated on global
sections: the sections of `j_* 𝐆_{m,K}` over `X` itself are the units of the function field, and
the sections of `⨁_x i_{x,*} ℤ` over `X` are the divisors. -/
@[ega "IV 21.6.7" "special case"]
def principalDivisorHom [NoetherianSpace X] :
    Additive ((↥X.functionField)ˣ) →+ AlgebraicCycle X ℤ where
  toFun g := principalDivisor ((Additive.toMul g : (↥X.functionField)ˣ) : ↥X.functionField)
  map_zero' := by simp
  map_add' g h := by
    simpa [Units.val_mul] using principalDivisor_mul (X := X)
      (Additive.toMul g).ne_zero (Additive.toMul h).ne_zero

/-- The divisor map sends a unit of the function field to the divisor of that rational function. -/
@[simp]
theorem principalDivisorHom_apply [NoetherianSpace X] (g : Additive ((↥X.functionField)ˣ)) :
    principalDivisorHom g =
      principalDivisor ((Additive.toMul g : (↥X.functionField)ˣ) : ↥X.functionField) :=
  rfl

/-- **The divisor of a function invertible on an open has coefficient zero at every point of that
open.** The rational function is named as the germ of the section at the generic point rather than
through `AlgebraicGeometry.Scheme.germToFunctionField`, so that the statement asks only for the
containment `hgen` it uses: the restriction map to the function field is defined only for a
*nonempty* open, and `hgen` already witnesses nonemptiness. -/
theorem principalDivisor_apply_of_isUnit [NoetherianSpace X] {U : X.Opens}
    (hgen : genericPoint X ∈ U) {a : Γ(X, U)} (ha : IsUnit a) {x : X} (hx : x ∈ U) :
    principalDivisor (X.presheaf.germ U (genericPoint X) hgen a) x = 0 :=
  have : Nonempty U := ⟨⟨genericPoint X, hgen⟩⟩
  ord_of_isUnit ha hx

/-- **The divisor of an invertible global function is zero.** This is the statement that the
composite of the first two maps of the divisor sequence of Stacks 03RM is zero, read on global
sections: an invertible global function has neither zeros nor poles. -/
theorem principalDivisor_eq_zero_of_isUnit [NoetherianSpace X] {a : Γ(X, ⊤)} (ha : IsUnit a) :
    principalDivisor (X.presheaf.germ ⊤ (genericPoint X) trivial a) = 0 :=
  Function.locallyFinsuppWithin.ext fun _ =>
    (principalDivisor_apply_of_isUnit (U := ⊤) trivial ha trivial).trans rfl

end Scheme

namespace IsCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
  [IsLocallyNoetherian X]

/-- **The divisor of a nonzero rational function on a curve has coefficient zero at a point
exactly when the order of vanishing there is trivial.** The left-hand side is Mathlib's integer
valued `AlgebraicGeometry.Scheme.ord`, the right-hand side the multiplicative
`AlgebraicGeometry.IsCurve.ordHom`, which is defined at every non-generic point of a curve. -/
theorem ord_eq_zero_iff_ordHom_eq_one {x : X} (hx : x ≠ genericPoint X)
    {g : X.functionField} (hg : g ≠ 0) :
    ord g x = 0 ↔ ordHom f hx g = 1 := by
  rw [ord_eq_iff (coheight_eq_one f hx) hg]
  simp [ordHom]

/-- **A rational function on a locally Noetherian curve has finitely many zeros and poles.**

A curve is quasi-compact over its base field, so its space is compact, and with local
Noetherianity the space is Noetherian; the support of the divisor is then finite by
`AlgebraicGeometry.Scheme.finite_support_ord`. Together with
`AlgebraicGeometry.IsCurve.ord_eq_zero_iff_ordHom_eq_one` this says that
`AlgebraicGeometry.IsCurve.ordHom` is trivial at all but finitely many points of a curve, which is
the finiteness the second map of the divisor sequence of Stacks 03RM requires of its values. -/
theorem finite_support_ord (g : X.functionField) : {x : X | ord g x ≠ 0}.Finite := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := IsNoetherian.mk
  exact Scheme.finite_support_ord g

end IsCurve

end AlgebraicGeometry

end
