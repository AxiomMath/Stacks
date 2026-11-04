module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DerivedSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic

/-!
# `Rf_*ℱ[2]` lies in degrees `≤ -1` on a modification of a local surface

Let `(A, 𝔪, κ)` be a two-dimensional Noetherian normal local domain, let `f : X ⟶ Spec(A)` be a
modification with `X` normal — Situation [Stacks, Tag 0AX8] — and let `ℱ` be a quasi-coherent
`𝒪_X`-module. Then `RΓ(X, ℱ)` has no cohomology above degree one, that is `Rⁱf_*ℱ = 0` for
`i ≥ 2`; this is `AlgebraicGeometry.DualizingDivisor.isLE_derivedSections`, Grothendieck's
vanishing above the dimension of the fibres ([Stacks, Tag 02V7] at fibre dimension one, through
[Stacks, Tag 0B4X] clause (1)). This file records that bound after the shift by two:

`RΓ(X, ℱ)[2] ∈ D^{≤ -1}(A)`.

The shift is not cosmetic. It is the hypothesis `X.IsLE a` of
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` at `a = -1`, and shifting by two
is what converts `RΓ(X, ω_X)` into `Rf_*ω_X^•`, the dualizing complex of a normal surface being
its dualizing module in degree `-2`
(`Stacks.Duality.relativeDualizingComplexIsoShiftTwoOfIsNormalSurface`).

## Main results

* `AlgebraicGeometry.DualizingDivisor.isLE_neg_one_shiftTwo_derivedSections` — the bound.
* `AlgebraicGeometry.VanishingSituation.isLE_neg_one_shiftTwo_derivedSections` — the same in
  Situation [Stacks, Tag 0AX8], where the dimension and the modification come from the situation.
* `AlgebraicGeometry.VanishingSituation.isLE_neg_one_shiftTwo_derivedSections_of_isCoherent` — the
  same with coherence assumed instead of quasi-coherence, which is the hypothesis the dualizing
  module `ω_X` carries.

## Where this is used

`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` says that for `K ∈ D^{≤ a}` and
`L ∈ D^{≥ a}` taking degree-`a` cohomology is a bijection
`Hom_{D(A)}(K, L) ≅ Hom_A(Hᵃ(K), Hᵃ(L))`. At `a = -1`, `K = RΓ(X, ω_X)[2]` and `L = κ[1]` the
right-hand side is `Hom_A(H¹(X, ω_X), κ)`, so a nonzero `A`-linear functional
`φ : R¹f_*ω_X → κ` yields a nonzero `α : Rf_*ω_X^• ⟶ κ[1]` in the derived category. That is the
step which opens the proof of [Stacks, Tag 0AXD]: *"if the proposition is false, then we can find
a nonzero map `R¹f_*ω_X → κ`; in other words we obtain a nonzero map
`α : Rf_*ω_X^• → κ[1]`"*. The `IsGE (-1)` side at `κ[1]` is immediate, `κ[1]` being a module
placed in a single degree; the `IsLE (-1)` side is the one that needs the geometry of the fibres,
and is what is recorded here.

**Nothing of [Stacks, Tag 0AXD] is registered here.** The vanishing that tag asserts is
`R¹f_*ω_X = 0`, in degree *one*; the bound below is in degrees `≥ 2` and holds for every
quasi-coherent module, `ω_X` included. It is an input to that tag's proof, not a part of it.

## Implementation notes

The bound is `CategoryTheory.Triangulated.TStructure.isLE_shift` applied to
`AlgebraicGeometry.DualizingDivisor.isLE_derivedSections`, with `2 + (-1) = 1`. No new
mathematics enters; what the file adds is the spelling.

`AlgebraicGeometry.DualizingDivisor.derivedSections f ℱ` is an `abbrev` for
`(derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)`, and the
statements in the namespace `AlgebraicGeometry.VanishingSituation` below write it out, since that
is the form in which a consumer meets it.

The derived categories are read at the default instances — the locally small model of
[Stacks, Tag 079Q]. That is the model of `AlgebraicGeometry.DualizingDivisor.derivedSections`, and
also the model at which [Stacks, Tag 0AXC] and the existing applications of
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` are written in
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardStructureSheaf`;
that lemma's `[HasDerivedCategory C]` binder is universe-unconstrained, so it reads here.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **`RΓ(X, ℱ)[2] ∈ D^{≤ -1}(A)`** for `ℱ` quasi-coherent on a normal modification of a
two-dimensional Noetherian normal local domain.

`AlgebraicGeometry.DualizingDivisor.isLE_derivedSections` puts `RΓ(X, ℱ)` in `D^{≤ 1}`, the
fibres of the modification having dimension at most one; shifting by two moves the bound to `-1`,
because `2 + (-1) = 1`. -/
theorem DualizingDivisor.isLE_neg_one_shiftTwo_derivedSections {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((DualizingDivisor.derivedSections f ℱ)⟦(2 : ℤ)⟧).IsLE (-1) :=
  have := DualizingDivisor.isLE_derivedSections hdim f hf ℱ
  DerivedCategory.TStructure.t.isLE_shift _ 1 2 (-1) (by norm_num)

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- **`RΓ(X, ℱ)[2] ∈ D^{≤ -1}(A)` in Situation [Stacks, Tag 0AX8]** with `X` normal, for `ℱ` a
quasi-coherent `𝒪_X`-module: over the affine base this is `Rⁱf_*ℱ = 0` for `i ≥ 2`, written as a
bound on `RΓ(X, ℱ)[2]`.

This is `AlgebraicGeometry.DualizingDivisor.isLE_neg_one_shiftTwo_derivedSections` with the
dimension and the modification taken from the situation. It is the `IsLE (-1)` side condition of
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE` at `a = -1`, which at `ℱ = ω_X`
and target `κ[1]` turns a nonzero `A`-linear map `R¹f_*ω_X → κ` into a nonzero
`Rf_*ω_X^• ⟶ κ[1]`. -/
theorem isLE_neg_one_shiftTwo_derivedSections [IsNormal V.X] (ℱ : V.X.Modules)
    [ℱ.IsQuasicoherent] :
    (((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ℱ))⟦(2 : ℤ)⟧).IsLE (-1) :=
  DualizingDivisor.isLE_neg_one_shiftTwo_derivedSections V.dimension_two V.f V.modification ℱ

/-- **`RΓ(X, ω_X)[2] ∈ D^{≤ -1}(A)`.**
`AlgebraicGeometry.VanishingSituation.isLE_neg_one_shiftTwo_derivedSections` with coherence
assumed in place of quasi-coherence, which is the hypothesis the dualizing module of `X` carries:
the first component of `Stacks.Duality.IsDualizingModule` is `ℱ.IsCoherent`, and a coherent module
is quasi-coherent. -/
theorem isLE_neg_one_shiftTwo_derivedSections_of_isCoherent [IsNormal V.X] (ℱ : V.X.Modules)
    (hℱ : ℱ.IsCoherent) :
    (((derivedGlobalSectionsOver V.f).obj
      ((DerivedCategory.singleFunctor V.X.Modules 0).obj ℱ))⟦(2 : ℤ)⟧).IsLE (-1) := by
  have : ℱ.IsCoherent := hℱ
  have : ℱ.IsQuasicoherent := isQuasicoherent_of_isCoherent ℱ
  exact V.isLE_neg_one_shiftTwo_derivedSections ℱ

end VanishingSituation

end AlgebraicGeometry

end
