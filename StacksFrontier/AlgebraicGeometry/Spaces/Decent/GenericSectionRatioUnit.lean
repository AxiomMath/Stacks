module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericFreeGeneratorOfHonestChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericSectionRatio

/-!
# The ratio `s / s_ξ` is a unit of `𝒪^h_{X, ξ}` where `s` generates `ℒ_ξ`

Let `X` be a decent, locally Noetherian, integral algebraic space over `S`, let `Z ⊆ X` be a
prime divisor with generic point `ξ`, let `ℒ` be an invertible `𝒪_X`-module and let `t_ξ` be a
free generator of `ℒ_ξ`.  If the germ at `ξ` of a meromorphic section `s` of `ℒ` is the image of
a **free generator** of `ℒ_ξ` — the condition
`AlgebraicGeometry.Space.PrimeDivisor.GeneratesGenericModuleStalk` — then the ratio `s / s_ξ`
is the image of a **unit of `𝒪^h_{X, ξ}`**, and not merely a unit of the fraction ring.

This is the algebraic half of the step the second collection of Stacks 0EPS needs.  Its
geometric half is
`AlgebraicGeometry.Space.PrimeDivisor.generatesGenericModuleStalk_of_eval_eq_of_mem_range`, and
with the ratio read in `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing` the two
together give `ord_{Z, ℒ}(s) = 0` by
`AlgebraicGeometry.Space.orderOfVanishingSection_eq_zero_of_isUnit` — which is the hypothesis
`hord` of
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_of_isIntegral`.

## Main results

* `Space.PrimeDivisor.exists_isUnit_genericToMeromorphicFunctions_eq_of_generates`:
  **the statement above.**

## Implementation notes

The argument is three lines of algebra over step (i).  Two free generators of `ℒ_ξ` differ by a
factor `v ∈ 𝒪^h_{X, ξ}` which is a unit, because the two mutually inverse factors multiply to
`1` by the injectivity of either generator's multiplication map.  The comparison
`ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ` is `𝒪^h_{X, ξ}`-linear, so it carries `t' = v · t_ξ` to
`germ_ξ(s) = v · (t_ξ read in 𝒦_X(ℒ)_ξ)`; and the ratio is *unique* with that property, by step
(i) (`AlgebraicGeometry.Space.PrimeDivisor.bijective_smul_toMeromorphicSectionValue`), so it is
the image of `v`.

Nothing here needs regularity of `s`: generating `ℒ_ξ` is strictly stronger than being a unit
ratio, and it is what regularity is used for upstream, in the production of the generating
chart.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

include hX hdec hInt hN Z in
/-- **Where `s` generates `ℒ_ξ`, the ratio `s / s_ξ` is the image of a unit of `𝒪^h_{X, ξ}`.**
Let `t_ξ` be a free generator of `ℒ_ξ` and let `k` be the ratio of `s` against it, that is the
unique meromorphic function on `Spec(𝒪^h_{X, ξ})` with `k · t_ξ = germ_ξ(s)`.  If `germ_ξ(s)` is
the image of a free generator of `ℒ_ξ`, then `k` is the image of a unit of `𝒪^h_{X, ξ}` under
the structure map `𝒪^h_{X, ξ} ⟶ 𝒦(Spec(𝒪^h_{X, ξ}))`.

Two free generators differ by a unit, the comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ` is `𝒪^h_{X, ξ}`-linear,
and the ratio is unique; see the implementation notes of this module. -/
theorem PrimeDivisor.exists_isUnit_genericToMeromorphicFunctions_eq_of_generates
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (t : Z.genericModuleStalk B S hS hX hdec R hR L)
    (ht : Function.Bijective fun r : R => r • t)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hgen : Z.GeneratesGenericModuleStalk B S hS hX hdec R hR L s)
    (k : meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR))
    (hk : k • toMeromorphicSectionValue B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianPullback B S hS hX hdec R hR L)
        (Z.genericHenselianChart B S hS hX hdec R hR) t =
      Z.genericMeromorphicGerm B S hS hX hdec R hR L s) :
    ∃ v : R, IsUnit v ∧ k = Z.genericToMeromorphicFunctions B S hS hX hdec R hR v := by
  obtain ⟨t', ht'bij, ht'eq⟩ := hgen
  obtain ⟨v, hv : v • t = t'⟩ := ht.2 t'
  obtain ⟨w, hw : w • t' = t⟩ := ht'bij.2 t
  have hwv : w * v = 1 := ht.1 <| by
    change (w * v) • t = (1 : R) • t
    rw [mul_smul, hv, hw, one_smul]
  refine ⟨v, ⟨⟨v, w, (mul_comm v w).trans hwv, hwv⟩, rfl⟩,
    (Z.bijective_smul_toMeromorphicSectionValue B S hS hX hdec hInt hN R hR L hL t ht).1 ?_⟩
  beta_reduce
  rw [hk, ← ht'eq, ← hv]
  exact (Z.genericModuleStalkToMeromorphic B S hS hX hdec R hR L).map_smul v t

end Generic

end AlgebraicGeometry.Space

end
