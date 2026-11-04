module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented

/-!
# The comparison map of Stacks 04CX for a morphism of schemes of the site

Let `ψ : U ⟶ V` and `χ : V ⟶ W` be morphisms of the big fppf category over a scheme `S`.  There
are two comparison maps of relative differentials attached to the square they make up over the
identity of `W`:

* the Zariski one, `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` of Stacks 01UV, a
  morphism `ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of `𝒪_U`-modules on the scheme underlying `U`;
* the spaces-level one, `AlgebraicGeometry.Space.pullbackDifferentialsMap` of Stacks 04CX for the
  morphisms of represented algebraic spaces, a morphism on the small étale site of
  `yoneda.obj U`.

Stacks 04CS identifies the *objects* these two maps live between:
`AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso` identifies the targets and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` of Stacks 03LC (1) identifies
the sources.  This file records the square which says the two *maps* correspond under those
identifications, as
`AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality`, and draws the consequence
that then matters: monomorphy of the Zariski comparison map gives monomorphy of the
spaces-level one, for the morphism of represented algebraic spaces over the base `W` and — by
the étale-base step of Stacks 04CU — over any algebraic space `W` is étale over.

## Main definitions

* `AlgebraicGeometry.Space.schemeChartDifferentialsMap` is the Zariski comparison map of the
  square, in the spelling the two sides of the identification produce.
* `AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality` is **the naturality of
  the identification of Stacks 04CS for the comparison map of Stacks 04CX**: the square of the
  two comparison maps and the two identifications commutes.

## Main results

* `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso_hom_universalDerivation`: the
  identification of Stacks 04CS carries the universal derivation to the canonical derivation
  `d^a` of Stacks 04CS.  This is the compatibility of that identification with the *derivations*,
  which is what makes it canonical; it is not a compatibility with any comparison map.
* `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_schemeSpaceMap`: granted that
  naturality, a monomorphic Zariski comparison map gives a monomorphic spaces-level comparison
  map.  The associated-module functor is left exact by Stacks 08H8, so it preserves
  monomorphisms, and the other two factors of the square are isomorphisms.
* `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_etaleBase_schemeSpaceMap`: the same with
  the base `W` replaced by an algebraic space `Z` it is étale over, by
  `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_etaleBase`.

## What is granted and what is not

`AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality` is the only input of this
file which is not proved here or upstream.  It is a single equation of morphisms of
`𝒪`-modules, quantified over a morphism of schemes of the site and a structure morphism, with no
algebraic space, no chart, no étaleness and no monomorphy in it; the mono-transfer, the
invertibility of the two identifications and the passage to an étale base are all proved.  The
identifications it relates are `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso`,
which is a family of isomorphisms of objects asserting no compatibility with any morphism, and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, which is the `.app` of the
natural isomorphism `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` of
Stacks 03LC (1) — natural in the module, hence silent about a morphism out of a pullback.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SchemeComparison

variable {U V W : BigFppfOver B S hS}

/-- **The Zariski comparison map of Stacks 01UV of the square of a composable pair of morphisms
of schemes of the site over the identity of the target**, `ψ^*Ω_{V/W} ⟶ Ω_{U/W}`.  The left edge
is spelled as the composite of the morphisms of schemes underlying `ψ` and `χ`, which is the
morphism of schemes underlying `ψ ≫ χ`. -/
abbrev schemeChartDifferentialsMap (ψ : U ⟶ V) (χ : V ⟶ W) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ)).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ)) ⟶
      Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)) :=
  Scheme.Hom.relativeDifferentialsMap ((BigFppfOver.toScheme B S hS).map ψ)
    ((BigFppfOver.toScheme B S hS).map χ)
    ((BigFppfOver.toScheme B S hS).map ψ ≫ (BigFppfOver.toScheme B S hS).map χ)
    (𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (Category.comp_id _).symm

/-- **The identification of Stacks 04CS carries the universal derivation to the canonical
derivation `d^a`.**  For a morphism `ψ : U ⟶ V` of schemes of the site, the isomorphism
`Ω_{ψ} ≅ (Ω_{U/V})^a` of `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso` takes the
universal differential `d_{ψ}(x)` of a local section `x` of `𝒪` on the small étale site of
`yoneda.obj U` to the canonical differential `d^a(x)` of Stacks 04CS.

This is the compatibility of that identification with the *derivations*, which
`AlgebraicGeometry.Space.representedDifferentialsComparison_representedUniversalDerivation`
supplies for its inverse.  It is what makes the identification canonical, and it is all the
compatibility available: it says nothing about the comparison map of a square, which is the
content of `AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality` below. -/
theorem sheafOfDifferentialsRepresentedIso_hom_universalDerivation (ψ : U ⟶ V)
    (T : (SmallEtale B S hS (schemeSpace U).1)ᵒᵖ)
    (x : (structureSetSheaf B S hS (schemeSpace U)).obj.obj T) :
    (sheafOfDifferentialsRepresentedIso B S hS ψ).hom.val.app T
        ((universalDerivation B S hS (schemeSpaceMap ψ)).d x) =
      (representedUniversalDerivation B S hS ψ).d x := by
  refine Eq.trans (congrArg ((sheafOfDifferentialsRepresentedIso B S hS ψ).hom.val.app T)
    (representedDifferentialsComparison_representedUniversalDerivation B S hS ψ T x).symm) ?_
  exact congrArg (fun m : representedRelativeDifferentials B S hS ψ ⟶
      representedRelativeDifferentials B S hS ψ =>
      m.val.app T ((representedUniversalDerivation B S hS ψ).d x))
    (sheafOfDifferentialsRepresentedIso B S hS ψ).inv_hom_id

/-- **The naturality of the identification of Stacks 04CS for the comparison map of
Stacks 04CX.**  For every composable pair `ψ : U ⟶ V`, `χ : V ⟶ W` of morphisms of schemes of
the site, the square

```
ψ^*Ω_{(χ of spaces)} ------- c_ψ -------> Ω_{(ψ ≫ χ of spaces)}
          |                                        |
 04CS and 03LC (1)                               04CS
          v                                        v
   (ψ^*Ω_{V/W})^a ----- (Zariski c_ψ)^a -----> (Ω_{U/W})^a
```

commutes: the spaces-level comparison map of Stacks 04CX of the morphisms of represented
algebraic spaces, followed by the identification of Stacks 04CS of its target, is the
identification of Stacks 04CS of its source — through Stacks 03LC (1) — followed by the
associated module of the Zariski comparison map of Stacks 01UV.

This is the compatibility of Stacks 04CS with a *map* of differentials.  The isomorphisms it
relates are available: `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso` is
Stacks 04CS at an object and `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is
Stacks 03LC (1).  Neither asserts anything about a morphism, and the present equation does not
follow from them. -/
abbrev SchemeDifferentialsComparisonMapNaturality : Prop :=
  ∀ (U V W : BigFppfOver B S hS) (ψ : U ⟶ V) (χ : V ⟶ W),
    (modulePullback B S hS (schemeSpaceMap ψ)).map
          (sheafOfDifferentialsRepresentedIso B S hS χ).hom ≫
        (representedAssociatedModulePullbackIso B S hS ψ
            (relativelyRepresentable_yoneda_map B S hS ψ)
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))).hom ≫
        (representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ) =
      pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
        (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom

/-- A morphism preceded by two isomorphisms is monic when it is. -/
private theorem mono_iso_comp_iso_comp_of_mono {C : Type*} [Category C] {X Y Z T : C}
    (e : X ≅ Y) (e' : Y ≅ Z) (f : Z ⟶ T) (hf : Mono f) : Mono (e.hom ≫ e'.hom ≫ f) :=
  have := hf
  inferInstance

/-- **A monomorphic Zariski comparison map of Stacks 01UV gives a monomorphic spaces-level
comparison map of Stacks 04CX**, granted the naturality of Stacks 04CS for comparison maps.

The square of that naturality has three other factors.  Two of them are the isomorphisms of
Stacks 04CS and Stacks 03LC (1).  The third is the associated module of the Zariski comparison
map, and the associated-module functor of a represented algebraic space is left exact by
Stacks 08H8 — the instance
`AlgebraicGeometry.Space.preservesFiniteLimits_representedAssociatedModule` — hence preserves
monomorphisms. -/
theorem mono_pullbackDifferentialsMap_schemeSpaceMap
    (hnat : SchemeDifferentialsComparisonMapNaturality B S hS) (ψ : U ⟶ V) (χ : V ⟶ W)
    (hm : Mono (schemeChartDifferentialsMap B S hS ψ χ)) :
    Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ)) := by
  have : Limits.PreservesFiniteLimits
      (representedAssociatedModule B S hS U (schemeSpace U).property) :=
    preservesFiniteLimits_representedAssociatedModule B S hS U
      (isAlgebraicSpace_yoneda B S hS U)
  have : (representedAssociatedModule B S hS U
      (schemeSpace U).property).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have := hm
  have : Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
      (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom) := by
    rw [← hnat U V W ψ χ]
    exact mono_iso_comp_iso_comp_of_mono ((modulePullback B S hS (schemeSpaceMap ψ)).mapIso
      (sheafOfDifferentialsRepresentedIso B S hS χ)) _ _
      (Functor.map_mono (representedAssociatedModule B S hS U (schemeSpace U).property) _)
  exact mono_of_mono _ (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom

variable {Z : AlgebraicSpaces B S hS}

/-- **A monomorphic Zariski comparison map of Stacks 01UV gives a monomorphic spaces-level
comparison map of Stacks 04CX over an algebraic space the target is étale over**, granted the
naturality of Stacks 04CS for comparison maps.

`AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_schemeSpaceMap` gives it over the
represented algebraic space of `W`, and
`AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_etaleBase` — the étale-base step of
Stacks 04CU for the comparison map — carries it to the base `Z`. -/
theorem mono_pullbackDifferentialsMap_etaleBase_schemeSpaceMap
    (hnat : SchemeDifferentialsComparisonMapNaturality B S hS) (ψ : U ⟶ V) (χ : V ⟶ W)
    (cw : schemeSpace W ⟶ Z) (hcw : IsEtale B S hS cw.hom)
    (hm : Mono (schemeChartDifferentialsMap B S hS ψ χ)) :
    Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ ≫ cw)) :=
  mono_pullbackDifferentialsMap_of_etaleBase B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) cw hcw
    (mono_pullbackDifferentialsMap_schemeSpaceMap B S hS hnat ψ χ hm)

end SchemeComparison

end AlgebraicGeometry.Space

end
