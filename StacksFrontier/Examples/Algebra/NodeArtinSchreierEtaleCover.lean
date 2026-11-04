module

public import Mathlib.RingTheory.Etale.StandardEtale
public import StacksFrontier.Examples.Algebra.NodeRingArtinSchreier

/-!
# The Artin–Schreier étale double cover of the node

Let `k` be a field of characteristic `2`, let `A = {g ∈ k[t] ∣ g(0) = g(1)}` be the node and let
`B = k[t, 1/t]` be the affine line with `t = 0` removed, as in
`StacksFrontier/Examples/Algebra/NodeRingArtinSchreier.lean`. Put `a = t² + t ∈ A` and

`C = A[z]/(z² + z + a)`.

This file builds `C` as a *standard étale* `A`-algebra — the pair is `(z² + z + a, 1)`, and it is
standard étale because the derivative of `z² + z + a` in `z` is `2z + 1 = 1`, a unit, so no
localization is needed — and counts the `A`-algebra maps out of it: there are **none** into `A`,
and **exactly two** into `B`.

Geometrically `C` is the connected étale double cover `T = Spec C` of `S = Spec A`, an
`A`-algebra map `C → A` is a section of `T` over `S`, and an `A`-algebra map `C → B` is a section
of the base change `T ×_S X` over `X = Spec B`. The two counts are therefore the two sides of
the Stacks erratum: `Γ(S, h_T) = ∅` against two elements of `Γ(X, f⁻¹h_T)`.

## Implementation notes

Only the affine algebra of the counterexample is treated here, so no declaration carries a Stacks
tag. The scheme-theoretic side — that `Spec B ⟶ Spec A` is submersive with geometrically
connected fibres, and the identification of global sections of the representable sheaf and of its
inverse image with the two `AlgHom` sets counted here — is not part of this file. See the
docstring of `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso` for the erratum and
the full counterexample.

## Main results

* `Stacks.NodalCurve.artinSchreierPair` — the standard étale pair `(z² + z + a, 1)` over `A`;
  `Algebra.Etale A (artinSchreierPair k).Ring` holds by Mathlib's instance for
  `StandardEtalePair.Ring`.
* `Stacks.NodalCurve.artinSchreier_hasMap_iff` — a map out of `C` into an `A`-algebra `S` is the
  same thing as a solution of `z² + z = a` in `S`.
* `Stacks.NodalCurve.isEmpty_artinSchreier_algHom_nodeRing` — no section downstairs.
* `Stacks.NodalCurve.card_artinSchreier_algHom_localizationAway` — exactly two sections upstairs.

## References

* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.NodalCurve

variable (k : Type*) [Field k] [CharP k 2]

/-! ### Characteristic `2` passes to the node ring -/

omit [CharP k 2] in
/-- The structure map `k → A` is injective: it sends a scalar to the constant polynomial. -/
public theorem injective_algebraMap_nodeRing :
    Function.Injective (algebraMap k (nodeRing k)) := fun _ _ h =>
  C_injective (congrArg Subtype.val h)

/-- The node ring has characteristic `2`, being a `k`-algebra with `k` of characteristic `2`. -/
public instance charP_nodeRing : CharP (nodeRing k) 2 :=
  charP_of_injective_algebraMap (injective_algebraMap_nodeRing k) 2

/-- In any `A`-algebra, `2 = 0`: it is the image of `2 = 0` in `A`. -/
public theorem two_eq_zero_of_nodeRing_algebra (S : Type*) [CommRing S]
    [Algebra (nodeRing k) S] : (2 : S) = 0 := by
  have h : algebraMap (nodeRing k) S 2 = 0 := by rw [CharTwo.two_eq_zero, map_zero]
  rwa [map_ofNat] at h

/-! ### The standard étale pair -/

/-- `a = t² + t`, as an element of the node ring. -/
public def artinSchreierCoeff : nodeRing k := ⟨X ^ 2 + X, X_sq_add_X_mem_nodeRing k⟩

/-- The coercion of `a` to `k[t]` is `t² + t`. -/
@[simp]
public theorem coe_artinSchreierCoeff :
    ((artinSchreierCoeff k : nodeRing k) : Polynomial k) = X ^ 2 + X := rfl

/-- **The Artin–Schreier pair.** Over a node ring of characteristic `2` the pair
`(z² + z + a, 1)` is a standard étale pair: `z² + z + a` is monic, and the derivative
`2z + 1 = 1` is a unit, so the localizing polynomial can be taken to be `1`. -/
public def artinSchreierPair : StandardEtalePair (nodeRing k) where
  f := X ^ 2 + (X + C (artinSchreierCoeff k))
  monic_f := by
    refine monic_X_pow_add ?_
    compute_degree
    norm_num
  g := 1
  cond := ⟨1, 0, 0, by simp [CharTwo.add_self_eq_zero]⟩

/-- **Maps out of `C` are solutions of the Artin–Schreier equation.** For an `A`-algebra `S`, the
condition that `C` maps to `S` carrying `z` to `x` is exactly `x² + x = a`; the localizing
polynomial being `1`, its unit condition is vacuous. -/
public theorem artinSchreier_hasMap_iff {S : Type*} [CommRing S] [Algebra (nodeRing k) S]
    (x : S) :
    (artinSchreierPair k).HasMap x ↔
      x ^ 2 + x = algebraMap (nodeRing k) S (artinSchreierCoeff k) := by
  have h2 : (2 : S) = 0 := two_eq_zero_of_nodeRing_algebra k S
  rw [StandardEtalePair.HasMap]
  simp only [artinSchreierPair, map_one, isUnit_one, and_true, map_add, map_pow, aeval_X,
    aeval_C]
  constructor
  · intro h
    linear_combination h - algebraMap (nodeRing k) S (artinSchreierCoeff k) * h2
  · intro h
    linear_combination h + algebraMap (nodeRing k) S (artinSchreierCoeff k) * h2

/-! ### No section downstairs -/

/-- **No section downstairs.** There is no `A`-algebra map `C → A`: such a map is a solution of
`z² + z = a` in the node ring, and there is none. -/
public instance isEmpty_artinSchreier_algHom_nodeRing :
    IsEmpty ((artinSchreierPair k).Ring →ₐ[nodeRing k] nodeRing k) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨x, hx⟩ := (artinSchreierPair k).homEquiv φ
  rw [artinSchreier_hasMap_iff] at hx
  refine no_artinSchreier_root_nodeRing k x.1 x.2 ?_
  have h := congrArg (fun y : nodeRing k => (y : Polynomial k)) hx
  simp only [Algebra.algebraMap_self_apply, coe_artinSchreierCoeff] at h
  push_cast at h
  exact h

/-! ### Two sections upstairs -/

/-- The `A`-algebra structure of `B` factors through `k[t]`, so `a` acts as `t² + t`. -/
public theorem algebraMap_artinSchreierCoeff_localizationAway :
    algebraMap (nodeRing k) (Localization.Away (X : Polynomial k)) (artinSchreierCoeff k) =
      algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (X ^ 2 + X) := by
  rw [IsScalarTower.algebraMap_eq (nodeRing k) (Polynomial k)
    (Localization.Away (X : Polynomial k))]
  rfl

/-- **Two sections upstairs.** The `A`-algebra maps `C → B` correspond to the solutions of
`z² + z = a` in `B`, of which there are exactly the two, `t` and `t + 1`. -/
public theorem card_artinSchreier_algHom_localizationAway :
    Nat.card ((artinSchreierPair k).Ring →ₐ[nodeRing k]
      Localization.Away (X : Polynomial k)) = 2 := by
  have e : ((artinSchreierPair k).Ring →ₐ[nodeRing k] Localization.Away (X : Polynomial k)) ≃
      ↥({algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X,
          algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X + 1} :
          Set (Localization.Away (X : Polynomial k))) :=
    (artinSchreierPair k).homEquiv.trans
      (Equiv.subtypeEquivRight fun x => by
        rw [artinSchreier_hasMap_iff, algebraMap_artinSchreierCoeff_localizationAway,
          artinSchreier_root_localizationAway_iff]
        simp)
  rw [Nat.card_congr e, Nat.card_coe_set_eq,
    Set.ncard_pair (algebraMap_X_ne_algebraMap_X_add_one k)]

end Stacks.NodalCurve

end
