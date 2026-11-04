module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingComplexNagata
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DimensionFunctionTrdegCharts
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedAtClosedPointCharts
import StacksCore.Tactic.StacksAttribute

/-!
# Stalks and dimension functions of the normalized dualizing complex `ω_X^•`

Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, `p : X ⟶ S` of finite type and
`ω_X^•` the dualizing complex normalized relative to `ω_S^•` ([Stacks, Tag 0AUA],
`Stacks.Duality.normalizedDualizingComplex`). Its normalization isomorphisms
`α_U : ω_X^•|_U ≅ (U → S)^! ω_S^•`, read in `D(𝒪_U)` through `(U → X)^! = (-)|_U`
([Stacks, Tag 0AU0]), give an affine open around every point on which `ω_X^•` is
`(U → S)^! ω_S^•` for a compactification of `U` over `S`. Through this chart description:

* if `x ∈ X` is a closed point over a closed point `s` and `ω_{S,s}^•` is a normalized dualizing
  complex over `𝒪_{S,s}`, then `ω_{X,x}^•` is a normalized dualizing complex over `𝒪_{X,x}`
  ([Stacks, Tag 0AWL]);
* the dimension functions satisfy `δ_X(x) - δ_S(p x) = trdeg_{κ(p x)} κ(x)` ([Stacks, Tag 0AWM]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.exists_isAffine_restrict_iso_upperShriek`: the chart
  description of a complex normalized relative to `ω_S^•`.
* `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex`:
  [Stacks, Tag 0AWL].
* `Stacks.Duality.associatedShiftFunction_sub_eq_trdeg_normalizedDualizingComplex`:
  [Stacks, Tag 0AWM].

## References

* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 0AWM](https://stacks.math.columbia.edu/tag/0AWM)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **The chart description of a complex normalized relative to `ω_S^•`.** Every point `x` of
`X` has an affine open neighbourhood `U` with `K|_U ≅ (U → S)^! ω_S^•` in `D(𝒪_U)`, for a
compactification of `U` over `S`: the normalization isomorphism `α_U`, read through
`(U → X)^! = (-)|_U` ([Stacks, Tag 0AU0]). -/
theorem exists_isAffine_restrict_iso_upperShriek
    (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) (x : X) :
    haveI := hp.base_noetherian
    haveI := hp.locallyOfFiniteType
    ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (_ : x ∈ U)
      (j : CompactificationOf (Over.mk (ftsHomToBase (U.ι ≫ p)).left)),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj 𝒦.complex.obj.obj ≅
        ((upperShriek (ftsHomToBase (U.ι ≫ p)) j).obj ωS.obj).obj) := by
  have := hp.base_noetherian
  have := hp.locallyOfFiniteType
  obtain ⟨_, ⟨(U : X.Opens), hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsAffine U.toScheme := hU
  have := hp.opens_noetherian U
  have hW : IsShriekable (U.ι ≫ p) :=
    { target_noetherian := hp.base_noetherian
      separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩,
        quasiCompact_of_noetherianSpace_source _⟩ }
  exact ⟨U, hU, hxU, c (U.ι ≫ p) hW,
    ⟨(UpperShriek.shriekObjIsoDerivedRestrict c U.ι (hp.isShriekable_ι U) 𝒦.complex).symm ≪≫
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso (𝒦.localIso U hW)⟩⟩

end NormalizedOnOpens

variable {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
  (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
  (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

/-- **[Stacks, Tag 0AWL].** Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, let
`X` be of finite type over `S` and `ω_X^•` the dualizing complex normalized relative to `ω_S^•`.
If `x ∈ X` is a closed point lying over a closed point `s` of `S`, then `ω_{X,x}^•` is a
normalized dualizing complex over `𝒪_{X,x}` provided that `ω_{S,s}^•` is a normalized dualizing
complex over `𝒪_{S,s}`. Stalks are the derived stalks of representatives; the closedness of `s`
is not used. -/
@[stacks 0AWL]
theorem isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex
    (x : X) (hx : IsClosed ({x} : Set X))
    (hωSs : haveI := hp.base_noetherian
      ∃ E : CochainComplex S.Modules ℤ, Nonempty (DerivedCategory.Q.obj E ≅ ωS.obj.obj) ∧
      Dualizing.IsNormalizedDualizingComplex.{u, u}
        (@derivedStalkOfComplex S (p x) (HasDerivedCategory.standard _) E)) :
    haveI := hp.source_noetherian
    ∀ E : CochainComplex X.Modules ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ (normalizedDualizingComplex hp ωS hωS).complex.obj.obj) →
        Dualizing.IsNormalizedDualizingComplex.{u, u}
          (@derivedStalkOfComplex X x (HasDerivedCategory.standard _) E) :=
  have := hp.base_noetherian
  have := hp.locallyOfFiniteType
  isNormalizedDualizingComplex_derivedStalkOfComplex p ωS.obj hωS _
    (NormalizedOnOpens.exists_isAffine_restrict_iso_upperShriek nagataCompactification
      (normalizedDualizingComplex hp ωS hωS)) x hx hωSs

/-- **[Stacks, Tag 0AWM].** Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, let
`p : X ⟶ S` be of finite type and `ω_X^•` the dualizing complex normalized relative to `ω_S^•`.
For all `x ∈ X`, `δ_X(x) - δ_S(p x) = trdeg_{κ(p x)} κ(x)`, where `δ_S`, `δ_X` are the
dimension functions of `ω_S^•`, `ω_X^•` ([Stacks, Tag 0AWF]). -/
@[stacks 0AWM]
theorem associatedShiftFunction_sub_eq_trdeg_normalizedDualizingComplex (x : X) :
    haveI := hp.base_noetherian
    haveI := hp.source_noetherian
    letI := (p.residueFieldMap x).hom.toAlgebra
    associatedShiftFunction (normalizedDualizingComplex hp ωS hωS).complex.obj.obj x -
        associatedShiftFunction ωS.obj.obj (p x) =
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p x)) (X.residueField x)) : ℤ) :=
  have := hp.base_noetherian
  have := hp.locallyOfFiniteType
  associatedShiftFunction_sub_eq_trdeg_of_upperShriek p ωS.obj hωS _
    (NormalizedOnOpens.exists_isAffine_restrict_iso_upperShriek nagataCompactification
      (normalizedDualizingComplex hp ωS hωS)) x

end Stacks.Duality

end
