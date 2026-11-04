module

public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictInjectivity
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCoreLowDegree

/-!
# Stacks 0G2H

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `(K_n)` be a Deligne system
with value `K` on `U`. [Stacks, Tag 0G2H] asserts that the canonical restriction map

`colim_n Hom_X(K_n, L) ⟶ Hom_U(K, L|_U)`

is bijective for every `L` in `D^b_{Coh}(𝒪_X)`.
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` proves this from one
hypothesis, `hcore`: the identification for a one-degree truncation of the system against a
target concentrated in a single degree. **This file proves `hcore`**, and with it the tag.

For `p ≤ q`, `hcore` for the pair of degrees `(p, q)` is
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`. For `q < p`, through
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree`, it is the
bijectivity of

`colim_n Ext^i_X(𝓘^n 𝓗, 𝓑) ⟶ Ext^i_U(𝓗|_U, 𝓑|_U)`, where `q + i = p`,

for `𝓗 = H^p(𝓕^•)` and `𝓑` coherent — the core case of the tag, and the third step of the
source's proof. Its two halves are
`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent` for surjectivity and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent`
for injectivity, the two hypotheses of
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem`.

## Main results

* `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`: **`hcore`**, the core case of
  [Stacks, Tag 0G2H].
* `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`: **[Stacks, Tag 0G2H].**

## Implementation notes

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance of raised priority,
as in `StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtEffacement`:
the import closure of the coherent effacement carries locally small models at universe `u` as
global instances, and with those in scope the shift functors of `D^b_{Coh}(𝒪_X)` are no longer
found to be additive.

The hypotheses of `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` are
supplied at the point of use rather than packaged into a lemma of their own: that lemma's
`CategoryTheory.RestrictionLifting` is elaborated with the `Hom`-universe of the derived category
left to the elaborator, and stating it in isolation fixes it one level too high for the `hext`
hypothesis of
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree` to accept.
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le` supplies its degree-zero
hypothesis in the same way, for the same reason.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.HasExt.standard

universe u

namespace AlgebraicGeometry.DeligneSystem

variable {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X]
  (D : DeligneSystem j)

/-- **The core case of [Stacks, Tag 0G2H].** The identification for the
one-degree truncation system `(τ^{≥p}τ^{≤p}K_n)` of a Deligne system against a target `L`
concentrated in a single degree `q`, for every pair `p`, `q`. This is the hypothesis `hcore` of
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`.

For `p ≤ q` it is `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_le`, where the
source's induction on the `Ext`-degree `i = p - q` has nothing to do. For `q < p` it is
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree` applied to the
`Ext`-colimit statement in degree `i = p - q` for the ideal powers of the coherent module
`H^p(𝓕^•)` (`AlgebraicGeometry.DeligneSystem.isCoherent_homology`), whose two halves are
`Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent` (surjectivity) and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent`
(injectivity). -/
public lemma restrictionLifting_truncGELE (p q : ℤ) (L : BoundedCoherentDerived X)
    (hGE : (boundedCoherentTStructure X).IsGE L q)
    (hLE : (boundedCoherentTStructure X).IsLE L q) :
    RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
      (restrictBoundedCoherent j) L := by
  rcases le_or_gt p q with h | h
  · exact D.restrictionLifting_truncGELE_of_le p q h L hGE hLE
  · refine D.restrictionLifting_truncGELE_of_single_degree p q L hGE hLE fun B hB => ?_
    have := D.isCoherent_homology p
    have := hB
    exact restrictionLifting_singleFunctor_idealPowerSystem j D.idealSheaf
      (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_support_of_eq_supportCompl
        D.opensRange_eq_supportCompl)
      (D.complex.homology p) B p q (p - q).toNat (by omega)
      (fun η => Stacks.ExtEffacement.exists_extIdealPowRestrict_eq_of_isCoherent D.idealSheaf
        j.opensRange D.opensRange_eq_supportCompl B ((p - q).toNat) (D.complex.homology p)
        inferInstance η)
      (fun _ ζ hζ =>
    Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_idealPowSmulMap_comp_eq_zero_of_isCoherent
      D.idealSheaf j.opensRange D.opensRange_eq_supportCompl ζ hζ)

/-- **Stacks Project, Tag 0G2H.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes and
let `(K_n)` be a Deligne system with value `K` on `U`. Then the canonical restriction
transformation

`colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)`

is an isomorphism: `colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)` for every `L` in
`D^b_{Coh}(𝒪_X)`.

This is `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` with its hypothesis
`hcore` supplied by `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`. -/
@[stacks 0G2H]
public theorem isIso_restrictionNatTrans (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K)) :
    IsIso (D.restrictionNatTrans K e) :=
  D.isIso_restrictionNatTrans_of_core K e fun p q L hq hq' =>
    D.restrictionLifting_truncGELE p q L hq hq'

end AlgebraicGeometry.DeligneSystem

end
