module

public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# The short exact sequence `0 → I ^ n ℱ → ℱ → ℱ / I ^ n ℱ → 0`

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `ℱ` a sheaf of modules. The
subsheaf `I ^ n ℱ` and the quotient `ℱ / I ^ n ℱ` sit in a short exact sequence of `𝒪_X`-modules,
and for `n ≤ m` the sequence for `m` maps to the sequence for `n` over the identity of `ℱ`.

That sequence and that ladder are the geometric input of the Artin--Rees step of the theorem on
formal functions. The long exact cohomology sequence of the first identifies
`Ker(H^p(X, ℱ) → H^p(X, ℱ / I ^ n ℱ))` with `Im(H^p(X, I ^ n ℱ) → H^p(X, ℱ))`, which is where
[Stacks, Tag 02OB] part (1) begins, and naturality of the connecting map along the second is the
diagram chase of [Stacks, Tag 02OB] part (3).

## Main definitions

* `Stacks.Algebraization.idealPowerQuotientShortComplex` — the short complex
  `I ^ n ℱ → ℱ → ℱ / I ^ n ℱ`, whose third term is `idealPowerQuotient`.
* `Stacks.Algebraization.idealPowerQuotientShortComplexMap` — for `n ≤ m`, the morphism from the
  short complex at `m` to the short complex at `n` which is the identity on `ℱ`.

## Main results

* `Stacks.Algebraization.idealPowerQuotientShortComplex_shortExact` — the short complex is short
  exact.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` and the two
presentations carry separately declared category instances, so the short complex is built with
`(C := X.Modules)` throughout: that is the presentation `idealPowerQuotient`,
`idealPowerQuotientDrop` and `adicQuotientSystem` live in, and the one whose cohomology is
computed by `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`. The monomorphism and epimorphism
instances do not cross the two presentations, and are taken from
`AlgebraicGeometry.Scheme.Modules.mono_submodule_ι` and
`Stacks.Algebraization.epi_cokernel_π_submodule_ι`, which state them at `X.Modules`.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)

/-- The short complex `I ^ n M → M → M / I ^ n M`, whose third term is
`Stacks.Algebraization.idealPowerQuotient`. -/
public def idealPowerQuotientShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (C := X.Modules) (idealPowerMultiple I n M).ι
    (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) (cokernel.condition _)

/-- The middle term of `idealPowerQuotientShortComplex I n M` is `M`. -/
@[simp]
public lemma idealPowerQuotientShortComplex_X₂ :
    (idealPowerQuotientShortComplex I n M).X₂ = M := rfl

/-- The third term of `idealPowerQuotientShortComplex I n M` is `idealPowerQuotient I n M`. -/
@[simp]
public lemma idealPowerQuotientShortComplex_X₃ :
    (idealPowerQuotientShortComplex I n M).X₃ = idealPowerQuotient I n M := rfl

/-- The first map of `idealPowerQuotientShortComplex I n M` is the inclusion of the subsheaf
`I ^ n M` into `M`. -/
@[simp]
public lemma idealPowerQuotientShortComplex_f :
    (idealPowerQuotientShortComplex I n M).f = (idealPowerMultiple I n M).ι := rfl

/-- The second map of `idealPowerQuotientShortComplex I n M` is the projection of `M` onto the
cokernel of the inclusion of `I ^ n M`. -/
@[simp]
public lemma idealPowerQuotientShortComplex_g :
    (idealPowerQuotientShortComplex I n M).g =
      cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι :=
  rfl

/-- The sequence `0 → I ^ n M → M → M / I ^ n M → 0` is short exact. -/
public lemma idealPowerQuotientShortComplex_shortExact :
    (idealPowerQuotientShortComplex I n M).ShortExact :=
  ShortComplex.shortExact_mk_cokernel_π (C := X.Modules) (idealPowerMultiple I n M).ι

variable {n}

/-- For `n ≤ m`, the morphism of short complexes from
`0 → I ^ m M → M → M / I ^ m M → 0` to `0 → I ^ n M → M → M / I ^ n M → 0` which is the
identity on `M`. -/
public def idealPowerQuotientShortComplexMap {m : ℕ} (h : n ≤ m) :
    idealPowerQuotientShortComplex I m M ⟶ idealPowerQuotientShortComplex I n M where
  τ₁ := submoduleInclusion (idealPowerMultiple_antitone I M h)
  τ₂ := 𝟙 M
  τ₃ := idealPowerQuotientDrop I h M
  comm₁₂ :=
    (submoduleInclusion_comp_ι (idealPowerMultiple_antitone I M h)).trans
      (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans (idealPowerQuotientDrop_π I h M).symm

/-- The component of `idealPowerQuotientShortComplexMap I M h` on first terms is the inclusion
`I ^ m M ⟶ I ^ n M`. -/
@[simp]
public lemma idealPowerQuotientShortComplexMap_τ₁ {m : ℕ} (h : n ≤ m) :
    (idealPowerQuotientShortComplexMap I M h).τ₁ =
      submoduleInclusion (idealPowerMultiple_antitone I M h) := rfl

/-- The component of `idealPowerQuotientShortComplexMap I M h` on middle terms is the identity
of `M`. -/
@[simp]
public lemma idealPowerQuotientShortComplexMap_τ₂ {m : ℕ} (h : n ≤ m) :
    (idealPowerQuotientShortComplexMap I M h).τ₂ = 𝟙 M := rfl

/-- The component of `idealPowerQuotientShortComplexMap I M h` on third terms is the map
`idealPowerQuotientDrop I h M : M / I ^ m M ⟶ M / I ^ n M`. -/
@[simp]
public lemma idealPowerQuotientShortComplexMap_τ₃ {m : ℕ} (h : n ≤ m) :
    (idealPowerQuotientShortComplexMap I M h).τ₃ = idealPowerQuotientDrop I h M := rfl

end Stacks.Algebraization

end
