module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ContinuousMapPushforward
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.StructureSheaf

/-!
# The filtration sequence carried along a continuous map

`Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex_unit` pushes the
filtration sequence of `𝒪_U` forward along a **morphism of schemes** `f : U ⟶ V`.  The
essential-surjectivity direction of [Stacks, Tag 0E3X] cannot use it: there the scheme downstairs
is what is being constructed, so no morphism of schemes is available, and the only map in hand is
the continuous one obtained by composing the identification `|U| ≅ |X|` of a thickening with
`|X| → |Y|`.

A continuous map is all the sequence needs.  Direct image along `φ : |U| ⟶ Y` of sheaves of
modules over `𝒪_U`, landing in modules over `φ_*𝒪_U`, is a right adjoint and hence additive and
left exact (`Stacks.ContinuousMapPushforward.schemeModules`), and those are the only properties the
argument uses — `Stacks.BaseAdicFiltration.shortExact_map_gradedShortComplex` is stated for an
arbitrary such functor.  This file instantiates it.

## Main results

* `Stacks.BaseAdicFiltration.shortExact_map_continuousPushforward_gradedShortComplex` — **the
  sequence carried along a continuous map**, short exact under the vanishing of `R¹φ_*` on the
  special fibre.
* `Stacks.BaseAdicFiltration.isZero_rightDerived_one_continuousPushforward_gradedPiece` — that
  vanishing propagates from the special fibre to every graded piece.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_continuousPushforward_gradedPiece` — the first
  term is a finite direct sum of copies of `φ_*(ℱ/Iℱ)`.
* `Stacks.BaseAdicFiltration.shortExact_map_continuousPushforward_gradedShortComplex_unit` and
  `exists_isoDirectSum_continuousPushforward_gradedPiece_unit` — the same for `ℱ = 𝒪_U` over an
  Artinian local base, which is the form [Stacks, Tag 0E3X] consumes.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.BaseAdicFiltration

attribute [local instance] hasFiniteBiproducts_of_abelian

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ) (F : U.Modules) [F.IsQuasicoherent]
  {Y : TopCat.{u}} (φ : (U : TopCat) ⟶ Y)

/-- **`R¹φ_*` annihilates the graded piece as soon as it annihilates the special fibre**, for a
continuous map `φ` of the underlying spaces.  This is the step of [Stacks, Tag 0E3X] reading
`R¹φ_*(𝔪ⁿ𝒪_U/𝔪ⁿ⁺¹𝒪_U) = 0` off `R¹φ_*𝒪_X = 0`, with no morphism of schemes available. -/
theorem isZero_rightDerived_one_continuousPushforward_gradedPiece [IsNoetherianRing A]
    [I.IsMaximal] (hflat : FlatStalks p F)
    (h : IsZero (((ContinuousMapPushforward.schemeModules φ).rightDerived 1).obj
      (specialFibre p I F))) :
    IsZero (((ContinuousMapPushforward.schemeModules φ).rightDerived 1).obj
      ((gradedPiece p I n F).toSheafOfModules)) :=
  isZero_rightDerived_one_gradedPiece_of_additive p I n F
    (ContinuousMapPushforward.schemeModules φ) hflat h

/-- **The filtration sequence carried along a continuous map.**  For a continuous
`φ : |U| ⟶ Y` with `R¹φ_*` annihilating the special fibre `ℱ/Iℱ`, the sequence

```
0 ⟶ φ_*(Iⁿ(ℱ/Iⁿ⁺¹ℱ)) ⟶ φ_*(ℱ/Iⁿ⁺¹ℱ) ⟶ φ_*(ℱ/Iⁿℱ) ⟶ 0
```

of sheaves of `φ_*𝒪_U`-modules on `Y` is short exact.

This is the statement
`Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex` applies to a morphism of
schemes, made available when only a continuous map of the underlying spaces exists. -/
theorem shortExact_map_continuousPushforward_gradedShortComplex [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F)
    (h : IsZero (((ContinuousMapPushforward.schemeModules φ).rightDerived 1).obj
      (specialFibre p I F))) :
    ((gradedShortComplex p I n F).map (ContinuousMapPushforward.schemeModules φ)).ShortExact :=
  shortExact_map_gradedShortComplex p I n F (ContinuousMapPushforward.schemeModules φ) hflat h

/-- **The first term of the sequence carried along a continuous map is a finite direct sum of
copies of `φ_*(ℱ/Iℱ)`**, the number of copies being `dim_{A/I} Iⁿ/Iⁿ⁺¹`. -/
theorem exists_isoDirectSum_continuousPushforward_gradedPiece [IsNoetherianRing A] [I.IsMaximal]
    (hflat : FlatStalks p F) :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => (ContinuousMapPushforward.schemeModules φ).obj (specialFibre p I F)) ≅
        (ContinuousMapPushforward.schemeModules φ).obj ((gradedPiece p I n F).toSheafOfModules)) :=
  exists_isoDirectSum_map_gradedPiece p I n F (ContinuousMapPushforward.schemeModules φ) hflat

section Artinian

variable [IsArtinianRing A] [IsLocalRing A]

/-- **The sequence of [Stacks, Tag 0E3X] carried along a continuous map.**  For `p : U ⟶ Spec A`
flat over an Artinian local base, a continuous `φ : |U| ⟶ Y`, and `R¹φ_*𝒪_X = 0`, the sequence

```
0 ⟶ φ_*(𝔪ⁿ(𝒪_U/𝔪ⁿ⁺¹𝒪_U)) ⟶ φ_*(𝒪_U/𝔪ⁿ⁺¹𝒪_U) ⟶ φ_*(𝒪_U/𝔪ⁿ𝒪_U) ⟶ 0
```

is short exact.  This is
`Stacks.BaseAdicFiltration.shortExact_map_pushforward_gradedShortComplex_unit` with the morphism
of schemes replaced by a continuous map of the underlying spaces, which is what the
essential-surjectivity direction of the tag has. -/
theorem shortExact_map_continuousPushforward_gradedShortComplex_unit [AlgebraicGeometry.Flat p]
    (h : IsZero (((ContinuousMapPushforward.schemeModules φ).rightDerived 1).obj
      (specialFibre p (IsLocalRing.maximalIdeal A) (SheafOfModules.unit U.ringCatSheaf)))) :
    ((gradedShortComplex p (IsLocalRing.maximalIdeal A) n
        (SheafOfModules.unit U.ringCatSheaf)).map
      (ContinuousMapPushforward.schemeModules φ)).ShortExact :=
  shortExact_map_continuousPushforward_gradedShortComplex p (IsLocalRing.maximalIdeal A) n
    (SheafOfModules.unit U.ringCatSheaf) φ (flatStalks_unit p) h

/-- **The first term of that sequence is `(φ_*𝒪_X) ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`**, presented as
`k = dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹` copies of `φ_*𝒪_X`. -/
theorem exists_isoDirectSum_continuousPushforward_gradedPiece_unit [AlgebraicGeometry.Flat p] :
    ∃ k : ℕ, Nonempty
      ((⨁ fun _ : Fin k => (ContinuousMapPushforward.schemeModules φ).obj
          (specialFibre p (IsLocalRing.maximalIdeal A)
            (SheafOfModules.unit U.ringCatSheaf))) ≅
        (ContinuousMapPushforward.schemeModules φ).obj
          ((gradedPiece p (IsLocalRing.maximalIdeal A) n
            (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules)) :=
  exists_isoDirectSum_continuousPushforward_gradedPiece p (IsLocalRing.maximalIdeal A) n
    (SheafOfModules.unit U.ringCatSheaf) φ (flatStalks_unit p)

end Artinian

end Stacks.BaseAdicFiltration

end
