module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverFieldProperties.FaithfullyFlatHom
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zero divisors in the local rings of a group scheme over a field

Let `G` be a group scheme over a field `k`.  We reduce the statement "every zero divisor of
every local ring `𝒪_{G, x}` is nilpotent" (Perrin's thesis, II 1.2; [SGA3, Exp. VI_A, 1.1.1] in
the finite type case) to the corresponding statement for the localizations at primes of
`K ⊗[k] L`, `K` and `L` zero-dimensional local `k`-algebras (Perrin, I 1.1–1.10).

## Main results

* `AlgebraicGeometry.zeroDivisorsNilpotent_stalk`: assuming the tensor
  statement, every zero divisor of every local ring of `G` is nilpotent.
* `ZeroDivisorsNilpotent.of_injective`: the property descends along injective ring maps.
* `AlgebraicGeometry.krullDimLE_zero_stalk_of_mem_irreducibleComponents`: the local ring of a
  scheme at a maximal point is zero-dimensional.

## Implementation notes

Write `x = μ u` with both projections `a, b` of `u` maximal points
(`AlgebraicGeometry.exists_mul_eq_of_maximal`).  Multiplication is flat (it is a base change of
the structure morphism, `GroupSchemeDifferentials.isPullback_mul`), so
`μ^♯ : 𝒪_{G, x} → 𝒪_{G ×_k G, u}` is a flat local, hence faithfully flat, hence injective, ring
map; and `𝒪_{G ×_k G, u}` is a localization of `𝒪_{G, a} ⊗[k] 𝒪_{G, b}` at a prime
(`AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct`), the two
factors being zero-dimensional local rings.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

universe u

/-- The property of a ring that **every zero divisor is nilpotent**. -/
def ZeroDivisorsNilpotent (R : Type*) [CommRing R] : Prop :=
  ∀ r : R, r ∉ nonZeroDivisors R → IsNilpotent r

/-- **Every zero divisor is nilpotent, descended along an injective ring map.** -/
theorem ZeroDivisorsNilpotent.of_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (hS : ZeroDivisorsNilpotent S) : ZeroDivisorsNilpotent R := by
  intro r hr
  rw [mem_nonZeroDivisors_iff_right] at hr
  push Not at hr
  obtain ⟨s, hsr, hs⟩ := hr
  have hφr : φ r ∉ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    push Not
    exact ⟨φ s, by rw [← map_mul, hsr, map_zero], fun h => hs (hφ (by rw [h, map_zero]))⟩
  obtain ⟨n, hn⟩ := hS (φ r) hφr
  exact ⟨n, hφ (by rw [map_pow, hn, map_zero])⟩

namespace AlgebraicGeometry

/-- **The local ring of a scheme at a maximal point is zero-dimensional**: its primes correspond
to the generizations of the point. -/
@[ega "I 2.4.3" "partial"]
theorem krullDimLE_zero_stalk_of_mem_irreducibleComponents {X : Scheme.{u}} (a : X)
    (ha : closure {a} ∈ irreducibleComponents X) : Ring.KrullDimLE 0 (X.presheaf.stalk a) := by
  rw [Ring.krullDimLE_zero_iff]
  intro q hq
  let q' : PrimeSpectrum (X.presheaf.stalk a) := ⟨q, hq⟩
  have hy : X.fromSpecStalk a q' ⤳ a := by
    have : X.fromSpecStalk a q' ∈ Set.range (X.fromSpecStalk a) := ⟨q', rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have hya : X.fromSpecStalk a q' = a := by
    have hsub : closure {X.fromSpecStalk a q'} ⊆ closure {a} :=
      ha.2 (isIrreducible_singleton.closure) (specializes_iff_closure_subset.mp hy)
    exact (hy.antisymm (specializes_iff_closure_subset.mpr hsub)).eq
  have hq' : q' = IsLocalRing.closedPoint (X.presheaf.stalk a) :=
    (X.fromSpecStalk a).isEmbedding.injective (hya.trans Scheme.fromSpecStalk_closedPoint.symm)
  have : q = IsLocalRing.maximalIdeal (X.presheaf.stalk a) := congrArg PrimeSpectrum.asIdeal hq'
  rw [this]
  infer_instance

/-- The `k`-algebra structure on the stalk at `p` of a scheme over `Spec k`. -/
private noncomputable abbrev stalkAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : X) : Algebra k (X.presheaf.stalk p) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ p trivial).hom.toAlgebra

open GroupSchemeDifferentials in
/-- **Zero divisors in the local rings of a group scheme over a field are nilpotent**, given the
corresponding statement for localizations at primes of tensor products of zero-dimensional local
`k`-algebras (Perrin, II 1.2 from I 1.1–1.10). -/
theorem zeroDivisorsNilpotent_stalk (k : Type u) [Field k]
    (H : ∀ (K L : Type u) [CommRing K] [CommRing L] [Algebra k K] [Algebra k L] [IsLocalRing K]
      [IsLocalRing L] [Ring.KrullDimLE 0 K] [Ring.KrullDimLE 0 L] (P : Ideal (K ⊗[k] L))
      [P.IsPrime], ZeroDivisorsNilpotent (Localization.AtPrime P))
    (G : Grp (Over (Spec (CommRingCat.of k)))) (x : G.X.left) :
    ZeroDivisorsNilpotent (G.X.left.presheaf.stalk x) := by
  obtain ⟨u, rfl, ha, hb⟩ := exists_mul_eq_of_maximal k G x
  let f := G.X.hom
  let : GrpObj (Over.mk f) := G.grp
  -- the multiplication is flat, so its map on local rings is injective
  have : Subsingleton (Spec (CommRingCat.of k)) := by
    change Subsingleton (PrimeSpectrum k)
    infer_instance
  have hflat : Flat (mul f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_mul f).flip
      (inferInstance : Flat f)
  let φ := (mul f).stalkMap u
  let : Algebra (G.X.left.presheaf.stalk (mul f u))
    ((pullback f f : Scheme.{u}).presheaf.stalk u) := φ.hom.toAlgebra
  have : Module.Flat (G.X.left.presheaf.stalk (mul f u))
      ((pullback f f : Scheme.{u}).presheaf.stalk u) := Flat.stalkMap (mul f) u
  have : IsLocalHom (algebraMap (G.X.left.presheaf.stalk (mul f u))
      ((pullback f f : Scheme.{u}).presheaf.stalk u)) := inferInstanceAs (IsLocalHom φ.hom)
  have : Module.FaithfullyFlat (G.X.left.presheaf.stalk (mul f u))
      ((pullback f f : Scheme.{u}).presheaf.stalk u) := .of_flat_of_isLocalHom
  have hinj : Function.Injective φ.hom :=
    FaithfulSMul.algebraMap_injective (G.X.left.presheaf.stalk (mul f u))
      ((pullback f f : Scheme.{u}).presheaf.stalk u)
  refine ZeroDivisorsNilpotent.of_injective φ.hom hinj ?_
  -- the local ring at `u` is a localization of the tensor product of zero-dimensional ones
  obtain ⟨ψ, -, -, hloc⟩ := exists_isLocalization_atPrime_stalk_pullback_tensorProduct k f f u
  let : Algebra k (G.X.left.presheaf.stalk (pullback.fst f f u)) := stalkAlgebra f _
  let : Algebra k (G.X.left.presheaf.stalk (pullback.snd f f u)) := stalkAlgebra f _
  let : Algebra (G.X.left.presheaf.stalk (pullback.fst f f u) ⊗[k]
      G.X.left.presheaf.stalk (pullback.snd f f u))
      ((pullback f f : Scheme.{u}).presheaf.stalk u) := ψ.toAlgebra
  have := krullDimLE_zero_stalk_of_mem_irreducibleComponents _ ha
  have := krullDimLE_zero_stalk_of_mem_irreducibleComponents _ hb
  let P := Ideal.comap ψ (IsLocalRing.maximalIdeal ((pullback f f : Scheme.{u}).presheaf.stalk u))
  let e := IsLocalization.algEquiv P.primeCompl ((pullback f f : Scheme.{u}).presheaf.stalk u)
    (Localization.AtPrime P)
  exact ZeroDivisorsNilpotent.of_injective e.toRingEquiv.toRingHom e.injective (H _ _ _)

end AlgebraicGeometry
