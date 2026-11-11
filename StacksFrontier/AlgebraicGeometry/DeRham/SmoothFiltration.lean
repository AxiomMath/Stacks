module

public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration
import StacksCore.Tactic.StacksAttribute

/-!
# The filtration of the de Rham complex of a smooth morphism

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. Stacks Section 50.12 filters the relative de Rham complex `Ω^•_{X/S}` by
the forms pulled back from `Y`: the `k`-th step is

`F^kΩ^•_{X/S} = Im (Tot(f^{-1}σ^{≥k}Ω^•_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^•_{X/S}) ⟶ Ω^•_{X/S})`,

the image of the wedge map. Because the pulled-back forms are closed under the de Rham
differential, the source is a complex and the wedge map is a morphism of complexes, so each step
is automatically a subcomplex — this is the description Section 50.12 gives precisely so that the
Leibniz rule stays implicit.

This file instantiates the generic wedge filtration of
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration` at the canonical pullback map
`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` of
`StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex`, and records that the result is the
filtration of Section 50.12. Nothing is assumed: `ρ` is constructed there.

## Main definitions

* `Stacks.DeRhamSmooth.pulledBackDeRhamComplex`: the inverse image `f^{-1}Ω^•_{Y/S}`, a complex
  of `(f∘g)^{-1}𝒪_S`-modules on `X`.
* `Stacks.DeRhamSmooth.deRhamSmoothFiltration`: **the filtration of Section 50.12**, as a
  filtered complex whose underlying complex is `Ω^•_{X/S}`.

## Main results

* `Stacks.DeRhamSmooth.deRhamSmoothFiltration_spec`: **[Stacks, Section 0FMK]** — the
  construction is the filtration of Section 50.12: its underlying complex is `Ω^•_{X/S}`, its
  `(k+1)`-st step is the image of the wedge map out of
  `Tot(f^{-1}σ^{≥(k+1)}Ω^•_{Y/S} ⊗ Ω^•_{X/S})`, the steps decrease, and the filtration is
  exhaustive.

## Implementation notes

The step at `k ≤ 0` is `⊤` by definition rather than by a computation. This is faithful: Section
50.12 posits `F^0Ω^•_{X/S} = Ω^•_{X/S}` as part of the definition of the filtration, and the
image description agrees there, since the degree-zero summand of the wedge map is
`a ⊗ η ↦ ρ(a)·η` and `ρ` is unital.

The generic construction lives in its own module because the instances the tensor product of
complexes of sheaves of modules needs are found at the light import surface of
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct` and not under the heavier surface
this file imports.

The graded pieces `gr^kΩ^•_{X/S} ≅ f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` for `f` smooth,
and the computation of the filtration in each degree, are the other clauses of Section 0FMK; they
are stated in `StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltrationGradedPieces`
(`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSmooth` and
`Stacks.DeRhamSmooth.relativeDifferentialsExteriorFiltration_smooth_spec`).

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FKP](https://stacks.math.columbia.edu/tag/0FKP)
* [Stacks Project, Tag 012L](https://stacks.math.columbia.edu/tag/012L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The inverse image `f^{-1}Ω^•_{Y/S}` of the relative de Rham complex of the target, a complex
of `(f∘g)^{-1}𝒪_S`-modules on `X`. -/
abbrev pulledBackDeRhamComplex :=
  ((_root_.pullback (relativeBase f g)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Scheme.Hom.deRhamComplex g)

/-- **The filtration of `Ω^•_{X/S}` of Stacks Section 50.12**: its `k`-th step, for `k ≥ 1`, is
the image of the wedge map out of `Tot(f^{-1}σ^{≥k}Ω^•_{Y/S} ⊗ Ω^•_{X/S})`, and its steps in
degrees `≤ 0` are all of `Ω^•_{X/S}`. -/
abbrev deRhamSmoothFiltration :
    CochainComplex.Filtered (_root_.SheafOfModules.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))) :=
  AlgebraicGeometry.SheafOfModules.wedgeFiltered (X := X.toRingedSpace)
    (A := (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
    (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
    (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)

/-- **Stacks Project, Section 0FMK.** For `f : X ⟶ Y` over a base `S`, the canonical pullback map
`ρ : f^{-1}Ω^•_{Y/S} ⟶ Ω^•_{X/S}` of `(f∘g)^{-1}𝒪_S`-modules filters the relative de Rham complex
`Ω^•_{X/S}` by the forms pulled back from `Y`:

* the underlying complex of the filtration is `Ω^•_{X/S}`;
* its `(k+1)`-st step is the image of the wedge map out of
  `Tot(f^{-1}σ^{≥(k+1)}Ω^•_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^•_{X/S})`, so each step is a subcomplex;
* the steps decrease;
* and the filtration is exhaustive, its steps in degrees `≤ 0` being all of `Ω^•_{X/S}`. -/
@[stacks 0FMK "the filtered complex: F^kΩ^•_{X/S} is the image of the wedge map out of \
Tot(f^{-1}σ_{≥k}Ω^•_{Y/S} ⊗_{p^{-1}O_S} Ω^•_{X/S}), a decreasing filtration of Ω^•_{X/S} by \
subcomplexes with F^0Ω^•_{X/S} = Ω^•_{X/S}; it holds for every f, smooth or not"]
theorem deRhamSmoothFiltration_spec :
    (deRhamSmoothFiltration f g).X = deRhamCochainComplex (f ≫ g) ∧
      (∀ k : ℤ, (deRhamSmoothFiltration f g).filtration.subobject (op k) =
        AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep
          (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (f ≫ g)))
          (pulledBackDeRhamComplex f g)
          (Stacks.DeRhamPullback.deRhamPullbackChain f g) k) ∧
      Antitone (AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))
        (pulledBackDeRhamComplex f g)
        (Stacks.DeRhamPullback.deRhamPullbackChain f g)) ∧
      ∀ k : ℤ, k ≤ 0 → IsIso ((deRhamSmoothFiltration f g).filtration.ι.app (op k)) :=
  ⟨rfl,
    fun k => AlgebraicGeometry.SheafOfModules.wedgeFiltered_subobject _ _ _ _ k,
    AlgebraicGeometry.SheafOfModules.wedgeFiltrationStep_antitone _ _ _ _,
    fun k hk =>
      AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos _ _ _ _ k hk⟩

end Stacks.DeRhamSmooth

end
