module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Inertia groups and base change

Let a group act on a commutative ring `R`. After an arbitrary base change from the invariant
subring, the inertia group of an ideal of `R` agrees with that of an ideal of the base-changed
ring lying above it. This applies in particular to the prime ideals in the source.

## Main definitions

* `MulSemiringAction.actionAlgHom`: a group element acting as an algebra endomorphism over the
  invariant subring.
* `MulSemiringAction.baseChangeAlgHom`: the induced endomorphism of the base-changed ring.
* `MulSemiringAction.baseChangeMulSemiringAction`: the canonical action on the base-changed
  ring, trivial on the new base and induced by the given action on `R`.

## Main results

* `MulSemiringAction.inertia_eq_inertia_baseChange`: inertia groups are unchanged by base
  change.

## Implementation notes

Mathlib's `Ideal.inertia` is the subgroup acting trivially modulo an ideal. Such an element
automatically preserves the ideal, so it expresses both conditions in the displayed definition
of the inertia group in the source. The finiteness of the acting group is not needed for this
base-change result.

## References

* [Stacks Project, Tag 0BSS](https://stacks.math.columbia.edu/tag/0BSS)
-/

@[expose] public section

open scoped Pointwise

namespace MulSemiringAction

variable {G R A : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- The action of `g` on `R`, regarded as an algebra endomorphism over the invariant subring. -/
public def actionAlgHom (g : G) : R →ₐ[FixedPoints.subring R G] R where
  __ := MulSemiringAction.toRingHom G R g
  commutes' x := x.property g

/-- The algebra endomorphism `actionAlgHom g` sends `r` to `g • r`. -/
@[simp]
public theorem actionAlgHom_apply (g : G) (r : R) : actionAlgHom g r = g • r := rfl

variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

/-- The algebra endomorphism of a base change induced by a group element acting on the second
tensor factor. -/
@[sga "1 V 1.9" "partial"]
public def baseChangeAlgHom (g : G) :
    TensorProduct (FixedPoints.subring R G) A R →ₐ[A]
      TensorProduct (FixedPoints.subring R G) A R :=
  Algebra.TensorProduct.map (AlgHom.id A A) (actionAlgHom g)

/-- The canonical group action on `A ⊗[Rᴳ] R`, trivial on `A` and induced by the given action
on `R`. -/
@[instance_reducible, sga "1 V 1.9" "special case"]
public def baseChangeMulSemiringAction :
    MulSemiringAction G (TensorProduct (FixedPoints.subring R G) A R) where
  smul g x := baseChangeAlgHom g x
  one_smul x := by
    change baseChangeAlgHom (1 : G) x = x
    induction x using TensorProduct.inductionOn with
    | tmul a r =>
      change a ⊗ₜ[FixedPoints.subring R G] ((1 : G) • r) = a ⊗ₜ r
      rw [one_smul]
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h x := by
    change baseChangeAlgHom (g * h) x = baseChangeAlgHom g (baseChangeAlgHom h x)
    induction x using TensorProduct.inductionOn with
    | tmul a r =>
      change a ⊗ₜ[FixedPoints.subring R G] ((g * h) • r) =
        a ⊗ₜ[FixedPoints.subring R G] (g • h • r)
      rw [mul_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  smul_zero g := map_zero (baseChangeAlgHom g)
  smul_add g := map_add (baseChangeAlgHom g)
  smul_one g := map_one (baseChangeAlgHom g)
  smul_mul g := map_mul (baseChangeAlgHom g)

/-- The canonical base-change action acts only on the second tensor factor. -/
@[simp]
public theorem baseChange_smul_tmul (g : G) (a : A) (r : R) :
    let := baseChangeMulSemiringAction (G := G) (R := R) (A := A)
    g • TensorProduct.tmul (R := FixedPoints.subring R G) a r =
      TensorProduct.tmul (R := FixedPoints.subring R G) a (g • r) := rfl

/-- The inertia group of an ideal is unchanged after arbitrary base change from the invariant
subring, for any ideal of the base change lying above it. -/
@[stacks 0BSS, sga "1 V 2.1" "special case"]
public theorem inertia_eq_inertia_baseChange
    (q : Ideal R)
    (q' : Ideal (TensorProduct (FixedPoints.subring R G) A R))
    (hq' : q = q'.comap Algebra.TensorProduct.includeRight) :
    let := baseChangeMulSemiringAction (G := G) (R := R) (A := A)
    q.inertia G = q'.inertia G := by
  let := baseChangeMulSemiringAction (G := G) (R := R) (A := A)
  change q.inertia G = q'.inertia G
  ext g
  simp only [Ideal.mem_inertia]
  refine ⟨fun hg x => ?_, fun hg r => ?_⟩
  · induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact add_mem hx hy
    | tmul a r =>
      rw [baseChange_smul_tmul, ← TensorProduct.tmul_sub]
      have hr : (1 : A) ⊗ₜ[FixedPoints.subring R G] (g • r - r) ∈ q' :=
        show g • r - r ∈ q'.comap Algebra.TensorProduct.includeRight from hq' ▸ hg r
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using
        q'.mul_mem_left (a ⊗ₜ[FixedPoints.subring R G] 1) hr
  · rw [hq', Ideal.mem_comap]
    simpa [Algebra.TensorProduct.includeRight_apply, ← TensorProduct.tmul_sub] using
      hg (Algebra.TensorProduct.includeRight r)

end MulSemiringAction
