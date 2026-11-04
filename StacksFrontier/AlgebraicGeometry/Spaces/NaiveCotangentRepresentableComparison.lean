module

public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex
public import StacksFrontier.Cotangent.Spaces.RepresentableComparison

/-!
# The naive cotangent complex of a morphism of representable algebraic spaces

Let `h : T₁ ⟶ T₂` be a morphism of the big fppf site over `S`, so that
`f : X = yoneda T₁ ⟶ Y = yoneda T₂` is a morphism of algebraic spaces represented by schemes,
with underlying morphism of schemes `f₀ : X₀ ⟶ Y₀`.  Stacks 0D0X identifies the naive cotangent
complex `NL_{X/Y}` of `f` with `ε^*NL_{X₀/Y₀}`, where
`ε : (X_étale, 𝒪_X) ⟶ (X₀,Zar, 𝒪_{X₀})` is the comparison morphism of Derived Categories of
Spaces, Section 071P.

This file carries out the first two steps of the source's proof, in the form

`ε⁻¹NL_{X₀/Y₀} ≅ NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ NL_{𝒪_X/f_small⁻¹𝒪_Y} = NL_{X/Y}`,

the isomorphism being Modules on Sites, Lemma 08TZ — the inverse image of the naive cotangent
complex is the naive cotangent complex of the inverse image — and the arrow being the canonical
chain map of Stacks 08TX attached to the square of Remark 08GH,
`AlgebraicGeometry.Space.representedBaseMap_square`.  The target is read in complexes of sheaves
of `ε⁻¹𝒪_{X₀}`-modules through restriction of scalars along `ε♯`, which is the adjoint form of a
map out of the pullback `ε^*NL_{X₀/Y₀} = ε⁻¹NL_{X₀/Y₀} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplex` is `NL_{X₀/Y₀}`, the naive
  cotangent complex of the Zariski structure map `f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_{X₀}` of `f₀`, its sections
  lifted to the universe of the small étale site.
* `AlgebraicGeometry.Space.representedInverseImageNaiveCotangentComplex` is
  `NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}}`, the naive cotangent complex of the inverse image along `ε` of
  that structure map.
* `AlgebraicGeometry.Space.representedNaiveCotangentComplexULift` is `NL_{X/Y}`, the naive
  cotangent complex of the structure map `f_small⁻¹𝒪_Y ⟶ 𝒪_X` of `f`, its sections lifted to the
  universe of the small étale site.
* `AlgebraicGeometry.Space.representedInverseImageNaiveCotangentComplexIso` is Lemma 08TZ at `ε`:
  the identification `ε⁻¹NL_{X₀/Y₀} ≅ NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}}`.
* `AlgebraicGeometry.Space.representedNaiveCotangentComparison` is the canonical chain map
  `NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ NL_{X/Y}` over the square of Remark 08GH.
* `AlgebraicGeometry.Space.representedPulledBackNaiveCotangentComparison` is the composite, the
  canonical map `ε⁻¹NL_{X₀/Y₀} ⟶ NL_{X/Y}` of the source's proof.

## Implementation notes

**Sections are lifted to `u + 1` throughout.**  The comparison `ε` is a morphism of ringed topoi
between `AlgebraicGeometry.Space.smallEtaleRingedToposULift` and
`AlgebraicGeometry.Space.representedZariskiRingedTopos`, both with sections in
`CommRingCat.{u + 1}`: the Zariski site of `X₀` has objects in `Type u` and the small étale site
of `X` has objects in `Type (u + 1)`, so the two can only be compared after the sections of the
structure sheaves are lifted to `u + 1`.  Accordingly the two ends of the comparison here are the
naive cotangent complexes of the *lifted* structure maps
`AlgebraicGeometry.Space.representedInverseImageStructureMap` and
`AlgebraicGeometry.Space.representedSpaceStructureMap`, and not
`AlgebraicGeometry.Space.naiveCotangentComplex` of Tag 0D0V, whose sections are in
`CommRingCat.{u}`.  Identifying a naive cotangent complex with that of its lifted structure map is
the analogue for `NL` of `AlgebraicGeometry.Scheme.Hom.cotangentComplexULiftIso`, which this
development has for the cotangent complex `L` and not for `NL`; that identification is the one
remaining input needed to read the comparison below at Tag 0D0V.

**The sheafification instances.**  `Stacks.SheafOfModules.naiveCotangentComplex` asks for
`HasWeakSheafify J CommRingCat.{w}` and `J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})`
with `w` the universe of the sections.  On the small étale site those are registered only at
`w = u` (`AlgebraicGeometry.Space.hasWeakSheafify_smallEtale_commRingCat`), and the general
instance has its section universe in `max`-normal form, which instance search cannot unify with
`u + 1`.  The same holds on the small Zariski site of `X₀`, where
`Stacks.Sites.FreeAlgebra.hasSheafifyOpensCommRingCat` is pinned to `w = u`.  They are therefore
supplied here as file-local instances at `w = u + 1`, from
`AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat`, whose section universe is a bare
universe variable rather than a `max`, and from `Stacks.hasSheafCompose_forget₂_commRingCat`,
which needs no size hypothesis at all; Lemma 08TZ additionally wants the sheaf condition for
abelian groups with sections in `u + 1` on both sites, which comes from
`CategoryTheory.hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall`.  Supplying these is
what makes Lemma 08TZ instantiable at `ε`.

**What is not done.**  The source's third step, that the canonical map is an isomorphism, is not
carried out.  It is checked in the source on stalks at geometric points, where the stalk maps of
`ε` and of
`AlgebraicGeometry.Space.representedBaseMap` are strict henselizations (Stacks 04K5, 04KF, 05V1)
and the conclusion is More on Algebra, Lemma 0D08.  Unlike the cotangent complex, `NL` has no
fundamental triangle, so the factorisation through two vanishing vertices that
`AlgebraicGeometry.Space.quasiIso_representedCotangentComparison` uses for Stacks 08VF is not
available, and nothing is asserted here in the derived category `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H), the naive cotangent
  complex of a morphism of schemes.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of the
  naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of the
  naive cotangent complex.
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH), the square relating `ε`
  to the structure maps.
* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF), the same identification
  for the cotangent complex, which this development proves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open CategoryTheory.Sheaf (inverseImageTargetModules)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Presheaves of commutative rings with sections in the universe `u + 1` of the small étale
site of a represented algebraic space admit sheafification.  The registered instance
`AlgebraicGeometry.Space.hasSheafify_smallEtale_commRingCat` is pinned to sections in `u`, and the
general instance has its section universe in `max`-normal form, which instance search cannot
unify with `u + 1`. -/
local instance hasSheafifySmallEtaleCommRingCatULift (T : BigFppfOver B S hS) :
    HasSheafify (SmallEtale.topology B S hS (yoneda.obj T)) CommRingCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat.{u + 1, u + 1, u}
    (SmallEtale.topology B S hS (yoneda.obj T))

/-- `AlgebraicGeometry.Space.hasSheafifySmallEtaleCommRingCatULift`, read as the existence of the
left adjoint of the inclusion of sheaves into presheaves. -/
local instance hasWeakSheafifySmallEtaleCommRingCatULift (T : BigFppfOver B S hS) :
    HasWeakSheafify (SmallEtale.topology B S hS (yoneda.obj T)) CommRingCat.{u + 1} :=
  HasSheafify.isRightAdjoint

/-- Forgetting commutativity preserves the sheaf condition on the small étale site of a
represented algebraic space, for sections in the universe `u + 1` of the site.  No size
hypothesis is needed: the forgetful functor creates limits and preserves them in every size. -/
local instance hasSheafComposeSmallEtaleForget₂ULift (T : BigFppfOver B S hS) :
    (SmallEtale.topology B S hS (yoneda.obj T)).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat.{u + 1, u, u + 1}
    (SmallEtale.topology B S hS (yoneda.obj T))

/-- Presheaves of commutative rings with sections in `u + 1` on the small Zariski site of a
scheme of the big fppf site admit sheafification.  The registered instance
`Stacks.Sites.FreeAlgebra.hasSheafifyOpensCommRingCat` is pinned to sections in `u`. -/
local instance hasWeakSheafifyOpensCommRingCatULift (T : BigFppfOver B S hS) :
    HasWeakSheafify (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      CommRingCat.{u + 1} :=
  (AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat.{u + 1, u, u}
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))).isRightAdjoint

/-- Forgetting commutativity preserves the sheaf condition on the small Zariski site of a scheme
of the big fppf site, for sections in `u + 1`. -/
local instance hasSheafComposeOpensForget₂ULift (T : BigFppfOver B S hS) :
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T)).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat.{u + 1, u, u}
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))

/-- On the small Zariski site of a scheme of the big fppf site, the presheaf of sections of a
sheaf of abelian groups with sections in `u + 1` is a sheaf of sets. -/
local instance hasSheafComposeOpensForgetAddCommGrpULift (T : BigFppfOver B S hS) :
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T)).HasSheafCompose
      (forget AddCommGrpCat.{u + 1}) :=
  CategoryTheory.hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall.{u + 1, u, u}
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))

/-- On the small étale site of a represented algebraic space, the presheaf of sections of a sheaf
of abelian groups with sections in `u + 1` is a sheaf of sets. -/
local instance hasSheafComposeSmallEtaleForgetAddCommGrpULift (T : BigFppfOver B S hS) :
    (SmallEtale.topology B S hS (yoneda.obj T)).HasSheafCompose
      (forget AddCommGrpCat.{u + 1}) :=
  CategoryTheory.hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall.{u + 1, u + 1, u}
    (SmallEtale.topology B S hS (yoneda.obj T))

variable {T₁ T₂ : BigFppfOver B S hS} (h : T₁ ⟶ T₂)

/-- **`NL_{X₀/Y₀}`.** The naive cotangent complex of the Zariski structure map
`f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_{X₀}` of the morphism of schemes `f₀` underlying `h`, its sections lifted to the
universe `u + 1` of the small étale site.  This is the complex that `ε^*` is applied to in
Stacks 0D0X. -/
noncomputable abbrev representedZariskiNaiveCotangentComplex :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u + 1, u + 1}
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁)) _ _
    ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage)

/-- **`NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}}`.** The naive cotangent complex, on the small étale site of
`X = yoneda T₁`, of the inverse image along `ε` of the Zariski structure map
`f₀⁻¹𝒪_{Y₀} ⟶ 𝒪_{X₀}` of the morphism of schemes `f₀` underlying `h`.  This is the complex that
Modules on Sites, Lemma 08TZ identifies with `ε⁻¹NL_{X₀/Y₀}`, and so the source of the canonical
map of Stacks 0D0X. -/
noncomputable abbrev representedInverseImageNaiveCotangentComplex :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u + 1, u + 1}
    (SmallEtale.topology B S hS (yoneda.obj T₁)) _ _
    (representedInverseImageStructureMap B S hS h)

/-- **`NL_{X/Y}`.** The naive cotangent complex of the structure map `f_small⁻¹𝒪_Y ⟶ 𝒪_X` of the
morphism `f` of algebraic spaces represented by `h`, its sections lifted to the universe `u + 1`
of the small étale site.  This is Tag 0D0V read at the lifted structure map. -/
noncomputable abbrev representedNaiveCotangentComplexULift :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u + 1, u + 1}
    (SmallEtale.topology B S hS (yoneda.obj T₁)) _ _
    (representedSpaceStructureMap B S hS h)

/-- **The canonical chain map `NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}} ⟶ NL_{X/Y}` of the proof of
Stacks 0D0X.**  It is the map of Stacks 08TX attached to the square of sheaves of commutative
rings on the small étale site of `X`
```
ε⁻¹𝒪_{X₀} ─────ε♯────▸ 𝒪_X
    ▲                    ▲
    │                    │
ε⁻¹f₀⁻¹𝒪_{Y₀} ─────────▸ f_small⁻¹𝒪_Y
```
whose bottom arrow is `AlgebraicGeometry.Space.representedBaseMap` and whose commutativity is
the square of Remark 08GH, `AlgebraicGeometry.Space.representedBaseMap_square`.  The target is
read in complexes of sheaves of `ε⁻¹𝒪_{X₀}`-modules through restriction of scalars along `ε♯`;
this is the adjoint form of a map out of `ε^*NL_{X₀/Y₀} = ε⁻¹NL_{X₀/Y₀} ⊗_{ε⁻¹𝒪_{X₀}} 𝒪_X`. -/
@[stacks 0D0X "the canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` of the source's proof, in its \
`ε⁻¹`-adjoint form, for the morphism of algebraic spaces represented by a morphism `T₁ ⟶ T₂` of \
the big fppf site over `S` (so `X`, `Y` are represented by the schemes `X₀`, `Y₀` underlying \
`T₁`, `T₂`); `ε` is the comparison of Section 071P (`representedToZariskiRingedToposHom`). WHAT \
IS PROVED IS THE SECOND STEP OF THE SOURCE'S PROOF: the canonical chain map of Tag 08TX attached \
to the square of Remark 08GH, `representedBaseMap_square`, from the naive cotangent complex of \
the inverse image along `ε` of the structure map of `f₀`. Its source is identified with \
`ε⁻¹NL_{X₀/Y₀}`, which is the source's FIRST step (Modules on Sites, Lemma 08TZ), separately by \
`representedInverseImageNaiveCotangentComplexIso`; the composite of the two is \
`representedPulledBackNaiveCotangentComparison`. THE SOURCE'S THIRD STEP IS NOT PROVED: the map \
is NOT shown to be an ISOMORPHISM; nothing is asserted in the derived category `D(O_X)`. The \
source checks that on stalks at geometric points, where the stalk maps of `ε` and of \
`representedBaseMap` are strict henselizations (Tags 04K5, 04KF, 05V1) and the conclusion is \
More on Algebra, Lemma 0D08; `NL` has no fundamental triangle, so the two-vanishing-vertices \
factorisation that `quasiIso_representedCotangentComparison` uses for Tag 08VF is unavailable. \
Carried beyond the source's statement: sections are lifted to `CommRingCat.{u + 1}` throughout, \
which is the only universe at which `ε` exists, so both ends are the naive cotangent complexes \
of the lifted structure maps and NOT `Space.naiveCotangentComplex` of Tag 0D0V, whose sections \
are in `CommRingCat.{u}`; an `NL` analogue of `Scheme.Hom.cotangentComplexULiftIso` is the one \
remaining input needed to read this at Tag 0D0V. The target is read in complexes of \
`ε⁻¹O_{X₀}`-modules through restriction of scalars along `ε♯`, the adjoint form of a map out of \
`ε^*NL_{X₀/Y₀}`"]
noncomputable def representedNaiveCotangentComparison :
    representedInverseImageNaiveCotangentComplex B S hS h ⟶
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
            (underlyingRingHomOfSite.{u, u + 1, u + 1}
              (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (representedNaiveCotangentComplexULift B S hS h) :=
  Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u + 1, u + 1, u + 1}
    (SmallEtale.topology B S hS (yoneda.obj T₁)) _ _
    (representedInverseImageStructureMap B S hS h) _ _
    (representedSpaceStructureMap B S hS h) (representedBaseMap B S hS h)
    (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage
    (representedBaseMap_square B S hS h)

/-- **Modules on Sites, Lemma 08TZ at `ε`.**  The inverse image along `ε` of the naive cotangent
complex of `f₀` is the naive cotangent complex of the inverse image along `ε` of the structure
map of `f₀`:

`ε⁻¹NL_{X₀/Y₀} ≅ NL_{ε⁻¹𝒪_{X₀}/ε⁻¹f₀⁻¹𝒪_{Y₀}}`.

This is the first step of the proof of Stacks 0D0X.  It is
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` at the universe instantiation that
`ε` admits: that lemma asks for the ambient section universe of each topos to be
`max` of the site's two universes with a third, and at `ε` both come out as `u + 1` — the small
étale site reaching it from objects in `Type (u + 1)` and the small Zariski site of `X₀` from
sections lifted to `CommRingCat.{u + 1}`.  This is the same universe instantiation
`{u + 1, u, u, u, u, u + 1}` that `StacksFrontier/Cotangent/Spaces/RepresentableComparison.lean`
uses for the cotangent-complex analogue, Stacks 08SV. -/
noncomputable def representedInverseImageNaiveCotangentComplexIso :
    ((inverseImageTargetModules.{u + 1, u, u, u, u, u + 1}
          (SmallEtale.topology B S hS (yoneda.obj T₁))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (representedToZariskiMorphismOfTopoi B S hS T₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (representedZariskiNaiveCotangentComplex B S hS h) ≅
      representedInverseImageNaiveCotangentComplex B S hS h :=
  Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso.{u + 1, u, u, u, u, u + 1}
    (SmallEtale.topology B S hS (yoneda.obj T₁))
    (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
    (representedToZariskiMorphismOfTopoi B S hS T₁)
    ((sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
      SheafOfModules.commRingCatULift.{u, u + 1}).map
      (Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map h)).fSharpInverseImage)

/-- **The canonical map `ε⁻¹NL_{X₀/Y₀} ⟶ NL_{X/Y}` of the proof of Stacks 0D0X.**  The
identification of Lemma 08TZ at `ε`
(`AlgebraicGeometry.Space.representedInverseImageNaiveCotangentComplexIso`) followed by the
canonical chain map of Stacks 08TX over the square of Remark 08GH
(`AlgebraicGeometry.Space.representedNaiveCotangentComparison`).  Read through restriction of
scalars along `ε♯`, this is the adjoint form of the map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` that
Stacks 0D0X asserts to be an isomorphism. -/
@[stacks 0D0X "the canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` of the source's proof, in its \
`ε⁻¹`-adjoint form, for the morphism of algebraic spaces represented by a morphism `T₁ ⟶ T₂` of \
the big fppf site over `S` (so `X`, `Y` are represented by the schemes `X₀`, `Y₀` underlying \
`T₁`, `T₂`); `ε` is the comparison of Section 071P (`representedToZariskiRingedToposHom`). THE \
FIRST TWO STEPS OF THE SOURCE'S PROOF ARE WHAT IS PROVED: the identification \
`ε⁻¹NL_{X₀/Y₀} = NL_{ε⁻¹O_{X₀}/ε⁻¹f₀⁻¹O_{Y₀}}` of Modules on Sites, Lemma 08TZ, instantiated at \
`ε` (`representedInverseImageNaiveCotangentComplexIso`), and then the canonical chain map of \
Tag 08TX attached to the square of Remark 08GH, `representedBaseMap_square` \
(`representedNaiveCotangentComparison`). THE THIRD STEP IS NOT PROVED: this map is NOT shown to \
be an ISOMORPHISM, and nothing is asserted in the derived category `D(O_X)`. The source checks \
that on stalks at geometric points, where the stalk maps of `ε` and of `representedBaseMap` are \
strict henselizations (Tags 04K5, 04KF, 05V1) and the conclusion is More on Algebra, \
Lemma 0D08; `NL` has no fundamental triangle, so the two-vanishing-vertices factorisation that \
`quasiIso_representedCotangentComparison` uses for Tag 08VF is unavailable. Carried beyond the \
source's statement: sections are lifted to `CommRingCat.{u + 1}` throughout, which is the only \
universe at which `ε` exists, so the two ends are the naive cotangent complexes of the lifted \
structure maps and NOT `Space.naiveCotangentComplex` of Tag 0D0V, whose sections are in \
`CommRingCat.{u}`, nor the scheme-level complex of Definition 0D0H at its own section universe; \
an `NL` analogue of `Scheme.Hom.cotangentComplexULiftIso` is the one remaining input needed to \
read this at Tag 0D0V. The target is read in complexes of `ε⁻¹O_{X₀}`-modules through \
restriction of scalars along `ε♯`, the adjoint form of a map out of `ε^*NL_{X₀/Y₀}`"]
noncomputable def representedPulledBackNaiveCotangentComparison :
    ((inverseImageTargetModules.{u + 1, u, u, u, u, u + 1}
          (SmallEtale.topology B S hS (yoneda.obj T₁))
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T₁))
          (representedToZariskiMorphismOfTopoi B S hS T₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (representedZariskiNaiveCotangentComplex B S hS h) ⟶
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
            (underlyingRingHomOfSite.{u, u + 1, u + 1}
              (representedToZariskiRingedToposHom B S hS T₁).fSharpInverseImage)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (representedNaiveCotangentComplexULift B S hS h) :=
  (representedInverseImageNaiveCotangentComplexIso B S hS h).hom ≫
    representedNaiveCotangentComparison B S hS h

end AlgebraicGeometry.Space

end
