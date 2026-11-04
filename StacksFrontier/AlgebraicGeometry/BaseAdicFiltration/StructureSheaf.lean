module

public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FiltrationSequence

/-!
# The `𝔪`-adic filtration of the structure sheaf of a flat family over an Artinian local base

This file specializes the results of
`StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/GradedPiece.lean` and
`StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/FiltrationSequence.lean` to the case the
filtration argument of [Stacks, Tag 0E3X] runs them in: `ℱ = 𝒪_U` for a **flat** morphism
`p : U ⟶ Spec A` over an **Artinian local** base.

The only thing to supply is the flatness hypothesis `Stacks.BaseAdicFiltration.FlatStalks`, which
for the structure sheaf is a consequence of flatness of `p`: the stalk of `𝒪_U` as a module over
itself is the local ring `𝒪_{U,x}` (`Stacks.UnitStalk.unitStalkLinearEquiv`), which is flat
over `A` because it is a localization of a flat `A`-algebra
(`Stacks.BaseAdicFiltration.flat_stalk_of_flat`).

With that in hand the two statements of the tag read:

* the filtration `… ⊆ 𝔪²𝒪_U ⊆ 𝔪𝒪_U ⊆ 𝒪_U` has graded pieces
  `𝔪ⁿ𝒪_U/𝔪ⁿ⁺¹𝒪_U ≅ ⨁_{i<k} 𝒪_X`, with `k = dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹`, which is the source's
  `𝒪_X ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`; and
* for `f : U ⟶ V` with `R¹f_*𝒪_X = 0` the sequences
  `0 → ⨁_{i<k} f_*𝒪_X → f_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U) → f_*(𝒪_U/𝔪ⁿ𝒪_U) → 0` are short exact.

Here `𝒪_X` is `𝒪_U/𝔪𝒪_U`, the structure sheaf of the special fibre read on `U`; `U` and the
special fibre have the same underlying space because `𝔪` is nilpotent, which is the
identification the tag makes at the start of its proof and which is built into the fact that
every sheaf below lives on `U`.

## Main results

* `Stacks.BaseAdicFiltration.flatStalks_unit`: a flat `p` has flat stalks of `𝒪_U` over `A`.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_gradedPiece_unit`: the graded pieces of the
  `𝔪`-adic filtration of `𝒪_U`.
* `Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex_unit` and
  `Stacks.BaseAdicFiltration.exists_isoDirectSum_pushforward_gradedPiece_unit`: the direct image
  sequence and the decomposition of its first term.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.BaseAdicFiltration

attribute [local instance] hasFiniteBiproducts_schemeModules

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))

/-- **The structure sheaf of a flat family has flat stalks over the base.** The stalk of `𝒪_U`
viewed as a module over itself is the local ring `𝒪_{U,x}`, and that is a flat `A`-module for a
flat `p` by `Stacks.BaseAdicFiltration.flat_stalk_of_flat`.

The identification of the two is `Stacks.UnitStalk.unitStalkLinearEquiv`, multiplication by the
germ of the unit section; its target is the same object as
`(modulesStalkFunctor U x).obj 𝒪_U`, both being the `AddCommGrpCat`-valued stalk of the
underlying presheaf of abelian groups with the same module structure.  It is linear over
`𝒪_{U,x}`, hence over `A` after restricting scalars along
`Stacks.BaseAdicFiltration.stalkAlgebra`. -/
theorem flatStalks_unit [AlgebraicGeometry.Flat p] :
    FlatStalks p (SheafOfModules.unit U.ringCatSheaf) := by
  intro x
  let := stalkAlgebra p x
  let := stalkBaseModule p (SheafOfModules.unit U.ringCatSheaf) x
  have : Module.Flat A (U.presheaf.stalk x) := flat_stalk_of_flat p x
  have : IsScalarTower A (U.presheaf.stalk x)
      ((modulesStalkFunctor U x).obj (SheafOfModules.unit U.ringCatSheaf)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A (U.presheaf.stalk x) (U.presheaf.stalk x) := IsScalarTower.right
  exact Module.Flat.of_linearEquiv
    ({ (Stacks.UnitStalk.unitStalkLinearEquiv U x).symm.toAddEquiv with
        map_smul' := fun (a : A) m =>
          (Stacks.UnitStalk.unitStalkLinearEquiv U x).symm.map_smul
            (algebraMap A (U.presheaf.stalk x) a) m } :
      (modulesStalkFunctor U x).obj (SheafOfModules.unit U.ringCatSheaf) ≃ₗ[A]
        U.presheaf.stalk x)

section Artinian

variable [IsArtinianRing A] [IsLocalRing A] (n : ℕ)

/-- **The graded pieces of the `𝔪`-adic filtration of the structure sheaf of a flat family over
an Artinian local base.** For `p : U ⟶ Spec A` flat with `A` Artinian local, the graded piece
`𝔪ⁿ(𝒪_U/𝔪ⁿ⁺¹𝒪_U)` is a direct sum of `k = dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` copies of the structure sheaf
`𝒪_X = 𝒪_U/𝔪𝒪_U` of the special fibre.

This is the identification the proof of [Stacks, Tag 0E3X] makes by citing
[Stacks, Tag 063Y] or [Stacks, Tag 08LI]. -/
theorem exists_isoDirectSum_gradedPiece_unit [AlgebraicGeometry.Flat p] :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => specialFibre p (IsLocalRing.maximalIdeal A)
          (SheafOfModules.unit U.ringCatSheaf)) ≅
        (gradedPiece p (IsLocalRing.maximalIdeal A) n
          (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules) :=
  exists_isoDirectSum_gradedPiece_of_isArtinianRing p n
    (SheafOfModules.unit U.ringCatSheaf) (flatStalks_unit p)

variable {V : Scheme.{u}} (f : U ⟶ V)

/-- **`R¹f_*` annihilates every graded piece as soon as it annihilates `𝒪_X`.** This is the step
of [Stacks, Tag 0E3X] reading `R¹f_*(𝔪ⁿ𝒪_U/𝔪ⁿ⁺¹𝒪_U) = 0` off the hypothesis
`R¹f_*𝒪_X = 0`. -/
theorem isZero_rightDerived_one_gradedPiece_unit [AlgebraicGeometry.Flat p]
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (specialFibre p (IsLocalRing.maximalIdeal A) (SheafOfModules.unit U.ringCatSheaf)))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      ((gradedPiece p (IsLocalRing.maximalIdeal A) n
        (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules)) :=
  isZero_rightDerived_one_gradedPiece p (IsLocalRing.maximalIdeal A) n
    (SheafOfModules.unit U.ringCatSheaf) f (flatStalks_unit p) h

/-- **The direct image sequence of [Stacks, Tag 0E3X].** For `p : U ⟶ Spec A` flat over an
Artinian local base, `f : U ⟶ V`, and `R¹f_*𝒪_X = 0`, the sequence

```
0 ⟶ f_*(𝔪ⁿ(𝒪_U/𝔪ⁿ⁺¹𝒪_U)) ⟶ f_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U) ⟶ f_*(𝒪_U/𝔪ⁿ𝒪_U) ⟶ 0
```

is short exact; `Stacks.BaseAdicFiltration.exists_isoDirectSum_pushforward_gradedPiece_unit`
identifies its first term with `⨁_{i<k} f_*𝒪_X`, which is the source's
`(f_*𝒪_X) ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`. -/
theorem shortExact_map_pushforward_gradedShortComplex_unit [AlgebraicGeometry.Flat p]
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (specialFibre p (IsLocalRing.maximalIdeal A) (SheafOfModules.unit U.ringCatSheaf)))) :
    ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
      (SheafOfModules.unit U.ringCatSheaf)).map (Scheme.Modules.pushforward f)).ShortExact :=
  shortExact_map_pushforward_gradedShortComplex p (IsLocalRing.maximalIdeal A) n
    (SheafOfModules.unit U.ringCatSheaf) f (flatStalks_unit p) h

/-- **The first term of the direct image sequence is `(f_*𝒪_X) ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`**, presented as
`k = dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` copies of `f_*𝒪_X`. -/
theorem exists_isoDirectSum_pushforward_gradedPiece_unit [AlgebraicGeometry.Flat p] :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => (Scheme.Modules.pushforward f).obj
          (specialFibre p (IsLocalRing.maximalIdeal A)
            (SheafOfModules.unit U.ringCatSheaf))) ≅
        (Scheme.Modules.pushforward f).obj
          ((gradedPiece p (IsLocalRing.maximalIdeal A) n
            (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules)) :=
  exists_isoDirectSum_pushforward_gradedPiece p (IsLocalRing.maximalIdeal A) n
    (SheafOfModules.unit U.ringCatSheaf) f (flatStalks_unit p)

end Artinian

end Stacks.BaseAdicFiltration

end
