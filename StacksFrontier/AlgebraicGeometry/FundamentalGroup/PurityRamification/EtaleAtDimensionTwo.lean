module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.GorensteinRationalCase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SituationCohenMacaulay

/-!
# Étaleness at a normal point of dimension two over an excellent regular local ring

This is [Stacks, Tag 0EA3]: let `f : X ⟶ Spec A` be of finite type, `x ∈ X`, with `A` an excellent
regular local ring and `𝒪_{X, x}` normal of dimension two; if `f` is étale outside
`closure {x}`, then `f` is étale at `x`.

The proof is the source's. After replacing `X` by an affine Cohen–Macaulay open neighbourhood of
`x` (`Stacks.PurityRamification.exists_isAffineOpen_isCohenMacaulay`; `𝒪_{X, x}` is
Cohen–Macaulay, being normal of dimension two):

* `f^!𝒪_Y = 𝒪_X`, so `𝒪_{X, x}` is Gorenstein
  (`Stacks.PurityRamification.isGorensteinLocalRing_stalk_of_isCohenMacaulay`);
* `𝒪_{X, x}` defines a rational singularity: on a resolution `W ⟶ Spec 𝒪_{X, x}` spread out to a
  regular model `X' ⟶ X`, the fundamental class of the local complete intersection `X' ⟶ Spec A`
  ([Stacks, Tag 0E9Z]) gives `ω_{X'/Y} = 𝒪_{X'}(E)`, its restriction to `W` is `ω_W = 𝒪_W(E|_W)`,
  and [Stacks, Tag 0EA2] applies
  (`Stacks.PurityRamification.definesRationalSingularity_stalk_of_isCohenMacaulay`);
* a Gorenstein rational surface singularity has embedding dimension at most three, and then
  étaleness in codimension one forces étaleness at `x`
  (`AlgebraicGeometry.etaleAt_of_isGorensteinLocalRing_of_definesRationalSingularity`).

The source asks `f` to be of finite type; only local finiteness is used, étaleness at `x` being a
local property, so the statement below assumes `LocallyOfFiniteType f` alone. The normality of
`𝒪_{X, x}` is `IsNormalRing`, which for a local ring is being an integrally closed domain
(`IsNormalRing.of_isLocalRing`).

## Main results

* `AlgebraicGeometry.etaleAt_of_etaleAt_outside_closure_of_ringKrullDim_eq_two` —
  [Stacks, Tag 0EA3].
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EA3.** Let `f : X ⟶ Spec A` be a morphism (locally) of finite type and
`x ∈ X`. Assume `A` is an excellent regular local ring, `𝒪_{X, x}` is normal of dimension `2`,
and `f` is étale at every point outside `closure {x}`. Then `f` is étale at `x`. -/
@[stacks 0EA3]
theorem etaleAt_of_etaleAt_outside_closure_of_ringKrullDim_eq_two {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) : EtaleAt f x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨U, hU, hxU, hCMU⟩ := Stacks.PurityRamification.exists_isAffineOpen_isCohenMacaulay f x
    (isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two hX hdim)
  have : IsAffine U.toScheme := hU
  let xU : U.toScheme := ⟨x, hxU⟩
  let eU := (U.stalkIso xU).commRingCatIsoToRingEquiv
  have hn : IsNormalRing (U.toScheme.presheaf.stalk xU) := IsNormalRing.congr eU.symm hX
  have : IsNormalDomain (U.toScheme.presheaf.stalk xU) :=
    ⟨hn.of_isLocalRing.1, hn.of_isLocalRing.2⟩
  have hd : ringKrullDim (U.toScheme.presheaf.stalk xU) = 2 := eU.ringKrullDim.trans hdim
  have hetU : ∀ z : U.toScheme, z ∉ closure ({xU} : Set U.toScheme) → EtaleAt (U.ι ≫ f) z :=
    fun z hz => etaleAt_comp_of_etale U.ι f z (het z.1 fun hcl => hz <|
      specializes_iff_mem_closure.mp
        (U.ι.isEmbedding.specializes_iff.mp (specializes_iff_mem_closure.mpr hcl)))
  have hG := Stacks.PurityRamification.isGorensteinLocalRing_stalk_of_isCohenMacaulay (U.ι ≫ f)
    hCMU xU (by rw [hd]) hetU
  have hR := Stacks.PurityRamification.definesRationalSingularity_stalk_of_isCohenMacaulay hA
    (U.ι ≫ f) hCMU xU hd hetU
  exact etaleAt_of_open_precomp U.ι f xU
    (etaleAt_of_isGorensteinLocalRing_of_definesRationalSingularity hA (U.ι ≫ f) xU hd hG hR hetU)

end AlgebraicGeometry

end
