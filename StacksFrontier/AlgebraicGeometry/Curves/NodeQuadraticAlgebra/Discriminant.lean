module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.ConductorLocalization
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.DegreeSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.QuadraticRelationDeltaOne
public import StacksFrontier.RingTheory.Derivation.ConductorGlobal
public import StacksFrontier.RingTheory.Localization.RangeAlgebraLinearMap

/-!
# The discriminant of the quadratic relation is a unit at a node

Let `k` be a field, let `A` be a reduced Noetherian `k`-algebra, let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions, and suppose `A' = A + A t` for a single `t`, with `t ^ 2 = a + c t`. Then at every
prime `𝔪` of `A` at which `A` is a nodal `k`-algebra, the discriminant `4 a + c ^ 2` lies
*outside* `𝔪`.

Equivalently — since `(2 t - c) ^ 2` is the image of `4 a + c ^ 2`
(`Stacks.DerivationExtension.sq_two_mul_sub_algebraMap`) — the element `u = 2 t - c` is
invertible at every point of `Spec A'` above a node. This is the one geometric fact that item (2)
of Stacks 0E68 still owed: `u` is *not* globally invertible (on the nodal cubic
`y ^ 2 = x ^ 3 + x ^ 2`, with `A' = k[s]` and `A = {h : h 1 = h (-1)}`, one has `u = 2 s`, which
vanishes at the smooth point `s = 0`), but it is invertible where the conductor is not, and that
is what makes the conductor comaximal with it.

The proof is the separability of the closed fibre of the normalization at a node. In the closed
fibre `Stacks.Curves.quadraticAlgebra R` of a nodal local ring `R` the pair `1, t` spans, because
`R' = R + R t` does; the fibre having dimension two
(`Stacks.Curves.finrank_quadraticAlgebra_of_isNodalAlgebra`), that pair is a basis. The fibre is
separable over the residue field at a node
(`Stacks.Curves.isSeparable_quadraticAlgebra_of_isNodalAlgebra`), and a quadratic relation
satisfied by an element of a separable algebra independent from `1` has nonvanishing discriminant
(`Stacks.Curves.discrim_ne_zero_of_isSeparable`). That nonvanishing in the residue field is
`4 a + c ^ 2 ∉ 𝔪 R`.

The global statement follows by localizing at `𝔪`: `A' = A + A t` localizes to
`A'_𝔪 = A_𝔪 + A_𝔪 t` (`Submodule.localized'_range_algebraLinearMap` and
`Submodule.localized'_span`), and the localization of `A'` is the normalization of `A_𝔪`
(`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`).

## Main results

* `Stacks.Curves.four_mul_add_mul_self_notMem_maximalIdeal_of_isNodalAlgebra` — at a nodal local
  ring, the discriminant of the quadratic relation of a generator of the normalization is a unit.
* `Stacks.Curves.four_mul_add_mul_self_notMem_of_isNodalAlgebra` — globally: that discriminant
  lies outside every nodal prime.

## Implementation notes

The two statements are separated because the fibre computation must be carried out at an abstract
local ring: performed directly at `Localization.AtPrime 𝔪`, the instance
`Module (ResidueField (Localization.AtPrime 𝔪)) (quadraticAlgebra (Localization.AtPrime 𝔪))` is
not found within the `synthInstance` budget — there are two routes to it, this development's
`Stacks.Curves.instAlgebraResidueFieldQuadraticAlgebra` and Mathlib's
`Ideal.Quotient.algebraQuotientMapQuotient`, and the search has to unfold the localization. The
global statement mentions no fibre, so transporting into it costs nothing.

The generation hypothesis is taken in its module form `A + A t = A'`, since that is the form
localization computes with;
`Stacks.DerivationExtension.sup_span_eq_top_of_adjoin_eq_integralClosure` converts item (1)'s
`Algebra.adjoin A {t} = A'` into it.

No `@[stacks]` tag is carried here: this is one ingredient of item (2) of Stacks 0E68, not the
whole of any item.

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- An isomorphism of algebras carries the image of the base onto the image of the base. -/
private theorem map_range_algebra_linearMap {R B D : Type*} [CommRing R] [CommRing B]
    [CommRing D] [Algebra R B] [Algebra R D] (e : B ≃ₐ[R] D) :
    Submodule.map (e.toLinearEquiv : B →ₗ[R] D) (LinearMap.range (Algebra.linearMap R B)) =
      LinearMap.range (Algebra.linearMap R D) := by
  rw [← LinearMap.range_comp]
  exact congrArg LinearMap.range (LinearMap.ext e.commutes)

/-- **At a node, the discriminant of the quadratic relation is a unit.** Let `R` be a nodal local
`k`-algebra, let `R'` be its normalization inside its total ring of fractions, and suppose the
image of `R` together with a single `τ` spans `R'`, with `τ ^ 2 = a + c τ`. Then the discriminant
`4 a + c ^ 2` lies outside the maximal ideal of `R`, that is, it is a unit.

The closed fibre `R' / 𝔪 R'` is spanned by `1` and the class of `τ`, and has dimension two, so
those two are a basis of it; the fibre is separable over the residue field at a node, and the
discriminant of a quadratic relation satisfied in a separable algebra by an element independent
from `1` cannot vanish. -/
public theorem four_mul_add_mul_self_notMem_maximalIdeal_of_isNodalAlgebra (k : Type u)
    (R : Type v) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    (hnodal : IsNodalAlgebra k R) (τ : ↥(integralClosure R (FractionRing R))) (a c : R)
    (hspan : LinearMap.range (Algebra.linearMap R ↥(integralClosure R (FractionRing R))) ⊔
      Submodule.span R {τ} = ⊤)
    (hrel : τ * τ = algebraMap R ↥(integralClosure R (FractionRing R)) a +
      algebraMap R ↥(integralClosure R (FractionRing R)) c * τ) :
    4 * a + c * c ∉ maximalIdeal R := by
  classical
  have := isSeparable_quadraticAlgebra_of_isNodalAlgebra k R hnodal
  have hrank := finrank_quadraticAlgebra_of_isNodalAlgebra k R hnodal
  have : Nontrivial (quadraticAlgebra R) :=
    Module.nontrivial_of_finrank_pos (R := ResidueField R) (by omega)
  set s : quadraticAlgebra R :=
    Ideal.Quotient.mk ((maximalIdeal R).map
      (algebraMap R ↥(integralClosure R (FractionRing R)))) τ
  have hgen : ∀ a₀ a₁ : R, Ideal.Quotient.mk ((maximalIdeal R).map
      (algebraMap R ↥(integralClosure R (FractionRing R))))
      (algebraMap R ↥(integralClosure R (FractionRing R)) a₀ +
        algebraMap R ↥(integralClosure R (FractionRing R)) a₁ * τ) =
      residue R a₀ • (1 : quadraticAlgebra R) + residue R a₁ • s := fun a₀ a₁ => by
    rw [map_add, quotient_mk_algebraMap_integralClosure,
      quotient_mk_algebraMap_mul_integralClosure]
  -- `1` and the class of `τ` span the closed fibre, hence are a basis of it
  have hli : LinearIndependent (ResidueField R) ![(1 : quadraticAlgebra R), s] := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by rw [hrank]; rfl)
    intro z _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective
      (I := (maximalIdeal R).map (algebraMap R ↥(integralClosure R (FractionRing R)))) z
    obtain ⟨a₀, a₁, hx⟩ :=
      Stacks.DerivationExtension.exists_add_mul_of_sup_span_eq_top τ hspan x.2
    have hrange : Set.range ![(1 : quadraticAlgebra R), s] = {1, s} := by
      rw [show ({1, s} : Set (quadraticAlgebra R)) = {s, 1} from Set.pair_comm 1 s]
      simp [Matrix.range_cons, Matrix.range_empty]
    rw [hrange]
    exact Submodule.mem_span_pair.mpr ⟨residue R a₀, residue R a₁,
      (hgen a₀ a₁).symm.trans (congrArg _ (Subtype.ext (by simpa using hx.symm)))⟩
  -- the relation in the fibre, and its discriminant
  have hrelQ : s ^ 2 = residue R c • s + residue R a • (1 : quadraticAlgebra R) := by
    have h := hgen a c
    rw [← hrel, map_mul] at h
    rw [sq, h, add_comm]
  intro hmem
  refine discrim_ne_zero_of_isSeparable (quadraticAlgebra R) s _ _ hli hrelQ ?_
  have h0 : residue R (4 * a + c * c) = 0 := by
    rwa [residue_eq_zero_iff]
  rw [map_add, map_mul, map_mul, map_ofNat] at h0
  linear_combination h0

/-- **The discriminant of the quadratic relation is invertible at a node.** Let `A` be a reduced
Noetherian algebra over a field `k`, let `A'` be its integral closure in its total ring of
fractions, and suppose the image of `A` together with a single `t` spans `A'`, with
`t ^ 2 = a + c t`. Then at every prime `𝔪` of `A` whose local ring is a nodal `k`-algebra the
discriminant `4 a + c ^ 2` lies outside `𝔪`.

Since `(2 t - c) ^ 2` is the image of `4 a + c ^ 2`
(`Stacks.DerivationExtension.sq_two_mul_sub_algebraMap`), this says that `2 t - c` is invertible
at every maximal ideal of `A'` lying over a node — the fact that makes a conductor element
comaximal with `2 t - c` in item (2) of Stacks 0E68. -/
public theorem four_mul_add_mul_self_notMem_of_isNodalAlgebra (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsReduced A] [IsNoetherianRing A] [Algebra k A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (hnodal : IsNodalAlgebra k (Localization.AtPrime 𝔪))
    (t : ↥(integralClosure A (FractionRing A))) (a c : A)
    (hspan : LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
      Submodule.span A {t} = ⊤)
    (hrel : t * t = algebraMap A ↥(integralClosure A (FractionRing A)) a +
      algebraMap A ↥(integralClosure A (FractionRing A)) c * t) :
    4 * a + c * c ∉ 𝔪 := by
  classical
  let T := ↥(integralClosure A (FractionRing A))
  let Rl := Localization.AtPrime 𝔪
  let Tl := Localization (Algebra.algebraMapSubmonoid T 𝔪.primeCompl)
  let D := ↥(integralClosure Rl (FractionRing Rl))
  have : IsNoetherianRing Rl :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl Rl inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_localization_integralClosure_fractionRing A
    (minimalPrimes.finite_of_isNoetherianRing A) Rl 𝔪.primeCompl
  -- the image of the global generator in the normalization of the local ring
  let ψ : T →+* D := (e : Tl →+* D).comp (algebraMap T Tl)
  have hψ : ∀ b : A, ψ (algebraMap A T b) = algebraMap Rl D (algebraMap A Rl b) := fun b => by
    show e (algebraMap T Tl (algebraMap A T b)) = algebraMap Rl D (algebraMap A Rl b)
    rw [← IsScalarTower.algebraMap_apply A T Tl, IsScalarTower.algebraMap_apply A Rl Tl,
      e.commutes]
  -- `A' = A + A t` localizes to `A'_𝔪 = A_𝔪 + A_𝔪 t`
  have hspanTl : LinearMap.range (Algebra.linearMap Rl Tl) ⊔
      Submodule.span Rl {algebraMap T Tl t} = ⊤ := by
    have h := congrArg
      (fun N : Submodule A T => N.localized' Rl 𝔪.primeCompl
        (IsScalarTower.toAlgHom A T Tl).toLinearMap) hspan
    rwa [Submodule.localized'_sup, Submodule.localized'_range_algebraLinearMap,
      Submodule.localized'_span, Set.image_singleton, Submodule.localized'_top] at h
  have hspanD : LinearMap.range (Algebra.linearMap Rl D) ⊔ Submodule.span Rl {ψ t} = ⊤ := by
    have h := congrArg (Submodule.map (e.toLinearEquiv : Tl →ₗ[Rl] D)) hspanTl
    rwa [Submodule.map_sup, map_range_algebra_linearMap e, Submodule.map_span,
      Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h
  -- and carries the quadratic relation along
  have hrelD : ψ t * ψ t = algebraMap Rl D (algebraMap A Rl a) +
      algebraMap Rl D (algebraMap A Rl c) * ψ t := by
    rw [← map_mul, hrel, map_add, map_mul, hψ a, hψ c]
  -- so the local statement applies at the node
  intro hmem
  refine four_mul_add_mul_self_notMem_maximalIdeal_of_isNodalAlgebra k Rl hnodal (ψ t)
    (algebraMap A Rl a) (algebraMap A Rl c) hspanD hrelD ?_
  have hmap : algebraMap A Rl (4 * a + c * c) ∈ maximalIdeal Rl :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rl 𝔪 _).mpr hmem
  rwa [map_add, map_mul, map_mul, map_ofNat] at hmap

end Stacks.Curves

end
