module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAlmostCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# Right exactness of the direct image of modules along a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. The space-level analogue of [Stacks, Tag 08KS] asserts of the direct image
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` of `AlgebraicGeometry.Space.modulePushforward` that it is exact,
that it is fully faithful, and that its essential image is the class of `𝒪_X`-modules
annihilated by the ideal `ℐ = ker(i♯)` cutting out `Z`.

`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean` supplies
the left-exactness half of the exactness clause unconditionally, and obtains the right-exactness
half only from the hypothesis `hsurj` that every sheaf of `i_*𝒪_Z`-modules on the small étale
site of `X` is a Stacks 03D1 direct image — the essential-image assertion of Stacks 04E5, which
this development does not have. **This file discharges right exactness without `hsurj`.**

## The route, and why it avoids the universe obstruction

Right exactness is obtained from [Stacks, Tag 04BD], not from the essential-image clause. The
mathematical input is the space-level analogue of [Stacks, Tag 04DX], part (7),
`AlgebraicGeometry.Space.smallBaseChange_isAlmostCocontinuous_of_isClosedImmersion`: base change
of étale scheme charts along `i` is almost cocontinuous. By the core lemma of 04BD,
`CategoryTheory.Presheaf.isLocallySurjective_whiskerLeft_of_isAlmostCocontinuous`, direct image
along an almost cocontinuous functor of sites carries locally surjective morphisms of sheaves to
locally surjective morphisms; so it preserves epimorphisms, and an additive functor between
abelian categories preserving finite limits and epimorphisms preserves finite colimits.

The route does **not** pass through sheaves of sets or abelian sheaves at the coefficient
universe `u + 1`, which is why the universe mismatch that blocks the abelian Stacks 04E5 does
not arise here. The modules of `AlgebraicGeometry.Space.Modules` have their sections in the
universe `u` of the schemes, one below the objects `Type (u + 1)` of the small étale site, and
every step below is taken at that universe `u`: sheafification and the characterization of local
equivalences for `Type u`- and `AddCommGrpCat.{u}`-valued presheaves on the small étale site are
available by its essential smallness at `u`
(`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`,
`AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`), and the direct image of
sheaves of sets at that universe is `AlgebraicGeometry.Space.smallEtaleDirectImage`.

## Main results

All of the following are for a closed immersion `i : Z ⟶ X` of algebraic spaces over `S`, and
carry no hypothesis beyond `IsClosedImmersion`.

* `AlgebraicGeometry.Space.preservesEpimorphisms_modulePushforward_of_isClosedImmersion`: the
  direct image of modules carries surjections to surjections.
* `AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`: the
  right-exactness half of the exactness clause of Tag 08KS, unconditionally.
* `exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`, in the namespace
  `AlgebraicGeometry.Space`: **Tag 08KS, the exactness clause**, unconditionally. The route is in
  the name because left exactness needs no hypothesis on `i` while right exactness is obtained
  from almost cocontinuity.

The statements conditional on almost cocontinuity rather than on a closed immersion are
`AlgebraicGeometry.Space.preservesEpimorphisms_smallEtaleDirectImage_of_isAlmostCocontinuous`,
`…_modulePushforward_of_isAlmostCocontinuous` and
`preservesFiniteColimits_modulePushforward_of_isAlmostCocontinuous`; they hold for an arbitrary
representable morphism of algebraic spaces whose chart base change is almost cocontinuous.

## What is *not* delivered, and why

Two assertions of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardExactness.lean` keep the
hypothesis `hsurj` and are **not** made unconditional here.

* `AlgebraicGeometry.Space.isLeftAdjoint_modulePushforward_of_essSurj`: being a left adjoint is
  strictly more than preserving finite colimits, and the right adjoint it produces — the largest
  subsheaf annihilated by `ℐ` — is built *from* the essential-image description. Nothing here
  constructs it.
* `AlgebraicGeometry.Space.preservesColimitsOfShape_modulePushforward_of_essSurj`: its shape `K`
  is arbitrary, so it asks for *all* colimits; 04BD gives only finite ones.

The **reverse inclusion of the essential-image clause** — that every `ℐ`-annihilated module is a
direct image — is likewise not delivered. Exactness does not imply essential surjectivity onto
the annihilated modules: by
`AlgebraicGeometry.Space.essImage_restrictScalars_structureSharp_of_annihilatedByKerIdeal` such a
module is a module over `i_*𝒪_Z`, and what remains is exactly `hsurj`, that its underlying sheaf
of sets be a direct image along the small étale topos morphism. That is the essential-image
assertion of Stacks 04E5 for sheaves of sets, which no part of this route touches.

## Implementation notes

`AlgebraicGeometry.Space.modulePushforward` is *not* literally a
`CategoryTheory.SheafOfModules.pushforward` along a functor of sites, so 04BD cannot be
instantiated at it directly: it is restriction of scalars along `i♯` applied to the Stacks 03D1
direct image `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` of the abstract
finite-product-preserving functor `AlgebraicGeometry.Space.smallEtaleDirectImage`. Two
identifications bridge the gap, and both are already in the tree.

* On underlying sheaves of *sets*, the direct image of modules is the direct image of sheaves of
  sets: `CategoryTheory.Sheaf.moduleSheafFunctor` commutes with the two direct images, on objects
  and on morphisms, **by `rfl`** — the sections map of
  `Stacks.Sheaves.ToposPullback.pullbackModuleMap` is by definition the sections map of the image
  under `smallEtaleDirectImage`, and restriction of scalars does not change sections. This is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`, which is already in the
  tree in `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean` and is the
  functorial form of `AlgebraicGeometry.Space.moduleSheaf_modulePushforward`.
* For a representable morphism, `smallEtaleDirectImage` *is* restriction along chart base change,
  up to the natural isomorphism
  `AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`. Epimorphisms are stable
  under conjugation by a natural isomorphism, which is how almost cocontinuity reaches it.

Epimorphisms of sheaves of modules and of their underlying sheaves of sets correspond
(`AlgebraicGeometry.Space.epi_iff_epi_moduleSheafFunctor_map` below) through the
epimorphism/locally surjective dictionary of
`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`,
`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget` and
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`, the last of which needs sheafification of
`Type u`-valued presheaves on the small étale site.

No declaration here is an `instance`, and the three attributes used — continuity of chart base
change and Mathlib's abelian structure on sheaves of modules — are installed `local`, so nothing
of this file leaks into instance search of any module that imports it. `SheafOfModules.instAbelian`
is given a raised local priority because the generic abelian structure on sheaves of modules on a
site leaves the module universe as a join that is never the universe `u` of the schemes, and a
search reaching it first ends in an unsolvable universe constraint rather than a recoverable
failure.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 04DX](https://stacks.math.columbia.edu/tag/04DX)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### The underlying sheaf of sets of a direct image of modules -/

/-- A morphism of `𝒪`-modules on an algebraic space is an epimorphism exactly when the induced
morphism of underlying sheaves of sets is.

Both sides are local surjectivity of the same map on sections, read through the
epimorphism/locally surjective dictionary for sheaves of modules on one side and for sheaves of
sets on the other. -/
theorem epi_iff_epi_moduleSheafFunctor_map (W : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS W.1 W.2} (alpha : M ⟶ N) :
    Epi alpha ↔
      Epi ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map alpha) := by
  rw [← Sheaf.isLocallySurjective_iff_epi,
    Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective alpha,
    Presheaf.isLocallySurjective_iff_whisker_forget]
  rfl

/-! ### Preservation of epimorphisms from almost cocontinuity -/

/-- Direct image along an almost cocontinuous chart base change preserves epimorphisms of
sheaves of sets at the universe `u` of the schemes.

This is the core lemma of [Stacks, Tag 04BD] — almost cocontinuity transports local
surjectivity — together with the two halves of the epimorphism/locally surjective dictionary for
sheaves of sets. -/
theorem preservesEpimorphisms_sheafPushforward_smallBaseChange_of_isAlmostCocontinuous
    (f : Z ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (ha : IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)).PreservesEpimorphisms where
  preserves {M N} alpha halpha := by
    have h1 : Sheaf.IsLocallySurjective alpha :=
      (Sheaf.isLocallySurjective_iff_epi alpha).2 halpha
    have h2 : Sheaf.IsLocallySurjective
        (((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)).map alpha) :=
      Sheaf.isLocallySurjective_sheafPushforwardContinuous_map_of_isAlmostCocontinuous
        (A := Type u) _ _ _ ha h1
    infer_instance

/-- The direct image of sheaves of sets on the small étale sites, at the universe `u` of the
schemes, preserves epimorphisms as soon as chart base change is almost cocontinuous.

For a representable morphism that direct image is restriction along chart base change up to
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`, and epimorphisms are stable
under conjugation by a natural isomorphism. -/
theorem preservesEpimorphisms_smallEtaleDirectImage_of_isAlmostCocontinuous (f : Z ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (ha : IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    (smallEtaleDirectImage B S hS f).PreservesEpimorphisms where
  preserves {M N} alpha halpha := by
    have := halpha
    have := preservesEpimorphisms_sheafPushforward_smallBaseChange_of_isAlmostCocontinuous
      B S hS f hf ha
    have h2 : ((smallEtaleDirectImage B S hS f).map alpha ≫
          (smallEtaleDirectImageIsoSheafPushforward B S hS f hf).hom.app N) ≫
        (smallEtaleDirectImageIsoSheafPushforward B S hS f hf).inv.app N =
        (smallEtaleDirectImage B S hS f).map alpha := by
      simp
    rw [(smallEtaleDirectImageIsoSheafPushforward B S hS f hf).hom.naturality alpha] at h2
    rw [← h2]
    exact epi_comp _ _

/-- The direct image of `𝒪`-modules along a representable morphism of algebraic spaces preserves
epimorphisms as soon as chart base change is almost cocontinuous.

An epimorphism of modules is one of underlying sheaves of sets
(`AlgebraicGeometry.Space.epi_iff_epi_moduleSheafFunctor_map`), the direct image of modules is
the direct image of sheaves of sets on those
(`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`), and that preserves
epimorphisms. -/
theorem preservesEpimorphisms_modulePushforward_of_isAlmostCocontinuous (f : Z ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (ha : IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    (modulePushforward B S hS f).PreservesEpimorphisms where
  preserves {M N} alpha halpha := by
    have hdi := preservesEpimorphisms_smallEtaleDirectImage_of_isAlmostCocontinuous
      B S hS f hf ha
    have : Epi ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map alpha) :=
      (epi_iff_epi_moduleSheafFunctor_map B S hS Z alpha).1 halpha
    refine (epi_iff_epi_moduleSheafFunctor_map B S hS X
      ((modulePushforward B S hS f).map alpha)).2 ?_
    rw [moduleSheafFunctor_map_modulePushforward_map]
    exact hdi.preserves _

/-- The direct image of `𝒪`-modules along a representable morphism of algebraic spaces is right
exact as soon as chart base change is almost cocontinuous.

It is additive and preserves finite limits for an arbitrary morphism, being a right adjoint
(`AlgebraicGeometry.Space.modulePushforward_additive`,
`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`), and it preserves epimorphisms by
the previous statement; an additive functor between abelian categories preserving finite limits
and epimorphisms preserves finite colimits. -/
theorem preservesFiniteColimits_modulePushforward_of_isAlmostCocontinuous (f : Z ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (ha : IsAlmostCocontinuous (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) :
    PreservesFiniteColimits (modulePushforward B S hS f) := by
  have : (modulePushforward B S hS f).PreservesEpimorphisms :=
    preservesEpimorphisms_modulePushforward_of_isAlmostCocontinuous B S hS f hf ha
  exact Stacks.SheafOfModules.LocalCokernel.finiteColimits_of_finiteLimits_epi
    (modulePushforward B S hS f)

/-! ### The exactness clause of the space-level Stacks 08KS, unconditionally -/

/-- **The direct image of modules along a closed immersion of algebraic spaces preserves
surjections.** This is the form in which right exactness is usually consumed, and it carries no
hypothesis beyond `IsClosedImmersion`: chart base change along a closed immersion is almost
cocontinuous by the space-level [Stacks, Tag 04DX], part (7). -/
theorem preservesEpimorphisms_modulePushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (modulePushforward B S hS i).PreservesEpimorphisms :=
  preservesEpimorphisms_modulePushforward_of_isAlmostCocontinuous B S hS i hi.rep
    (smallBaseChange_isAlmostCocontinuous_of_isClosedImmersion B S hS i hi)

/-- The right-exactness half of the exactness clause of the space-level [Stacks, Tag 08KS],
unconditionally. The direct image `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` of Stacks 03LU along a closed
immersion of algebraic spaces preserves finite colimits.

This is [Stacks, Tag 04BD] fed the space-level analogue of [Stacks, Tag 04DX], part (7). It
replaces `AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_essSurj`, which
assumes the essential-image assertion of Stacks 04E5. The modules are those with sections in the
universe `u` of the schemes.

The tag is carried by the next statement, which is the exactness clause whole. -/
theorem preservesFiniteColimits_modulePushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    PreservesFiniteColimits (modulePushforward B S hS i) :=
  preservesFiniteColimits_modulePushforward_of_isAlmostCocontinuous B S hS i hi.rep
    (smallBaseChange_isAlmostCocontinuous_of_isClosedImmersion B S hS i hi)

/-- **[Stacks, Tag 08KS], the exactness clause, for algebraic spaces, unconditionally.** The
direct image `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` of Stacks 03LU along a closed immersion of algebraic
spaces is an exact functor.

Left exactness is `AlgebraicGeometry.Space.preservesFiniteLimits_modulePushforward` and needs no
hypothesis on `i`; right exactness is the previous statement. It replaces
`AlgebraicGeometry.Space.exactFunctor_modulePushforward_of_essSurj`, which assumes the
essential-image assertion of Stacks 04E5.

This is the one statement carrying the tag for the exactness clause on the algebraic-space
substrate: it states the clause as the source does, so neither half does.

The name records the route: right exactness comes from almost cocontinuity, the space-level
analogue of [Stacks, Tag 04DX], part (7), rather than from the finite case of
[Stacks, Tag 04C2]. -/
@[stacks 08KS "the exactness clause of the direct image, for algebraic spaces"]
theorem exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    exactFunctor (Modules.{u, u} B S hS Z.1 Z.2) (Modules.{u, u} B S hS X.1 X.2)
      (modulePushforward B S hS i) := by
  have hlim : PreservesFiniteLimits (modulePushforward B S hS i) := inferInstance
  rw [exactFunctor_iff]
  exact ⟨hlim, preservesFiniteColimits_modulePushforward_of_isClosedImmersion B S hS i hi⟩

end AlgebraicGeometry.Space

end
