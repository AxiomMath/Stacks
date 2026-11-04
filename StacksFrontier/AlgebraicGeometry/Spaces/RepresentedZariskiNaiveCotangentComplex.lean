module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.RingedStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSchemeZariskiRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.Cotangent.SchemeCotangentComplex

/-!
# `\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}}` for a morphism of represented algebraic spaces

Let `S` be a scheme, let `φ : U ⟶ V` be a morphism of objects of the big fppf site over `S`, let
`f₀ : X₀ ⟶ Y₀` be the morphism of the underlying schemes, and let `X = h_U` be the algebraic
space represented by `U`.  This module forms, on the small étale site of `X`, the naive cotangent
complex of the homomorphism of sheaves of commutative rings

`ε⁻¹(f_0^♯) : ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}`

obtained by applying `ε⁻¹` of `AlgebraicGeometry.Space.representedZariskiInverseImageCommRing`
(Stacks 071P, Equation 75.4.0.1, formalized in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSchemeZariskiRingedToposHom.lean`) to the
structure map of `f₀`, and the canonical chain map of Stacks 08TX out of it attached to `ε^♯`.

These are the pieces of the construction of the canonical map of Stacks 0D0X that do not need the
square of Derived Categories of Spaces, Remark 08GH.  That square is
`AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean:828`), and the chain
map into `\NL_{X/Y}` that it makes possible is
`AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexCompare` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentCompare.lean`; see the
scope section.

## Main definitions

* `AlgebraicGeometry.Space.representedZariskiInverseImageBaseRing`: `ε⁻¹f_0^{-1}𝒪_{Y₀}`, a sheaf
  of commutative rings on the small étale site of `X = h_U`.
* `AlgebraicGeometry.Space.representedZariskiInverseImageNaiveCotangentComplex`:
  `\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}}`.  This is the complex that Modules on Sites, Lemma 08TZ
  would identify with `ε⁻¹\NL_{X₀/Y₀}`.
* `AlgebraicGeometry.Space.representedZariskiBaseNaiveCotangentComplex`:
  `\NL_{𝒪_X / ε⁻¹f_0^{-1}𝒪_{Y₀}}`, the naive cotangent complex of the composite morphism of
  ringed topoi `f₀ ∘ ε : (X_étale, 𝒪_X) ⟶ (Y_{0, Zar}, 𝒪_{Y₀})`.
* `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexMap`: the canonical chain map
  of Stacks 08TX between the two, attached to `ε^♯ : ε⁻¹𝒪_{X₀} ⟶ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.representedZariskiBaseStructureMap_eq`: the homomorphism
  `ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ 𝒪_X` that the second complex is built from is the structure map, in
  inverse-image form, of the composite morphism of ringed topoi `f₀ ∘ ε`.  So the second complex
  really is the naive cotangent complex of that composite.

## Implementation notes

The square of sheaves of commutative rings on the small étale site of `X` that the chain map is
attached to is
```
ε⁻¹𝒪_{X₀} ────ε^♯────▸ 𝒪_X
   ▲                    ▲
   │                    │
ε⁻¹f_0^{-1}𝒪_{Y₀} ──𝟙──▸ ε⁻¹f_0^{-1}𝒪_{Y₀}
```
whose bottom edge is the identity, so that it commutes by `CategoryTheory.Category.id_comp` and
no input beyond `ε` itself is needed.  The target of the chain map is the image of the second
complex under termwise restriction of scalars along `ε^♯`, which is the Lean reading of the
source's assertion that the map of Stacks 08TX is linear over the ring of its *source*.

`AlgebraicGeometry.Space.structureUniverseHasWeakSheafifyCommRing` registers sheafification of
presheaves of commutative rings on the small étale site at the universe of the structure rings,
which the site's own low-priority instance supplies but instance search cannot reach past the
general `CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`; its docstring says why.

The universes do not move.  All of `ε⁻¹f_0^{-1}𝒪_{Y₀}`, `ε⁻¹𝒪_{X₀}` and `𝒪_X` are sheaves of
`CommRingCat.{u}` on a site whose objects form a `Type (u + 1)`, so both complexes are complexes
of sheaves of modules with sections in `Type (u + 1)` — the universe of
`AlgebraicGeometry.Space.naiveCotangentComplex`, whose implementation notes record why.

## Scope

**Stacks 0D0X is not proved here, and no tag is placed on anything in this file.**  The source
builds its canonical map `ε^*\NL_{X₀/Y₀} ⟶ \NL_{X/Y}` as the composite of three steps:

1. `ε⁻¹\NL_{X₀/Y₀} = \NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}}`, which is Modules on Sites,
   Lemma 08TZ.  The library has Tag 08TZ for sites, as
   `Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`, but its sheaves of rings are at
   the join `max u v w` of the two universes of the site
   (`StacksFrontier/CategoryTheory/Sites/Modules/NaiveCotangentInverseImageComplex.lean`, the
   variable block of its `InverseImageNaiveCotangentComplex` section), while the small étale site
   of an algebraic space has its objects one universe above its structure rings.  **That join is
   forced, not a pin that can be loosened**, so the library's form is not available here and no
   universe generalisation of the `NaiveCotangentInverseImage*` family would make it so.  The
   reason, with the declarations that force it, is in the implementation notes of that file:
   `ε⁻¹` of sheaves of modules exists only at the universe of the topos it is taken along, which
   here is the universe `u` of the structure rings, whereas the naive cotangent complex on this
   site is a complex of sheaves of modules with sections in `Type (u + 1)`.  Reading 08TZ here
   would need the small étale site replaced by an equivalent small site together with the
   transport of the naive cotangent complex along that equivalence, which the library does not
   carry.  What *is* available at these universes, and does apply to the complex built below, is
   the part of that file which does not mention the morphism of topoi: the universal property
   `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv` of the degree-`0` term with its
   section formula `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv_d`, and the term and
   differential identifications `Stacks.SheafOfModules.naiveCotangentComplexXNegOneIso`,
   `Stacks.SheafOfModules.naiveCotangentComplexXZeroIso` and
   `Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero_iso`.  The right-hand side of this
   step is `AlgebraicGeometry.Space.representedZariskiInverseImageNaiveCotangentComplex` below.
2. The chain map out of that complex, by functoriality of the naive cotangent complex (Tag 08TX)
   along the square of Derived Categories of Spaces, Remark 08GH.  **Only the `ε^♯` half of that
   square is built here**, as
   `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexMap` below.  The other half is
   the identification `ε⁻¹f_0^{-1}𝒪_{Y₀} ≅ f_{small}^{-1}ε_Y^{-1}𝒪_{Y₀}` coming from the
   commutation `f₀ ∘ ε_X = ε_Y ∘ f_{small}` of morphisms of ringed topoi, which is Remark 08GH
   itself; **it is no longer absent.**  Remark 08GH is
   `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`
   (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean:828`, the tag at
   `:820`), a `AlgebraicGeometry.RingedToposHom.TwoIso` between
   `AlgebraicGeometry.Space.representedZariskiEpsilonCompLeft` and
   `AlgebraicGeometry.Space.representedZariskiEpsilonCompRight`, and the identification it yields
   is `AlgebraicGeometry.Space.representedEpsilonBaseRingIso`.  The whole of step 2 — the chain
   map into `\NL_{X/Y}` — is
   `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexCompare` in
   `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentCompare.lean`, which is
   where the tag for this clause of Stacks 0D0X is registered.
3. That the resulting map is an isomorphism in `D(𝒪_X)`, which the source checks on stalks at
   geometric points using Properties of Spaces, Lemma 04KF and More on Algebra, Lemma 0D08.  This
   is not proved anywhere.

So steps 1 and 3 remain unavailable and Stacks 0D0X itself is still not proved.  The
quasi-coherence clause of Stacks 0D0Y, which the source deduces from Lemma 0D0X, is proved without
it, by a comparison on affine chart diagrams checked at geometric points:
`AlgebraicGeometry.Space.naiveCotangentComplex_homology` in
`StacksFrontier/AlgebraicGeometry/Spaces/NaiveCotangentHomologyQuasicoherent.lean`.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), the statement these are
  a step towards; not proved here, and not proved anywhere — step 2 of its proof is
  `AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexCompare` in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentCompare.lean`, and steps
  1 and 3 are unavailable.
* [Stacks Project, Tag 071P](https://stacks.math.columbia.edu/tag/071P), Section 75.4, whose
  Equation 75.4.0.1 is the `ε` used here.
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH), the square; proved, as
  `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso` in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean:828`.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), functoriality of the
  naive cotangent complex in a square of sheaves of rings.
* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ), the inverse image of the
  naive cotangent complex; not available at these universes.
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), composition of
  morphisms of ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

/-- Sheafification of presheaves of commutative rings on the small étale site of `F`, at the
universe of the structure rings of the site — which is one *below* the universe of its objects.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasSheafify`, which is registered at low
priority, while `CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat` is stated at the join
`max u v w` of the two universes of the site with a free coefficient universe and instance search
cannot solve the constraint `u =?= max (u + 1) ?w`, so the specialization has to be registered.
Being a `Prop`, it agrees with the general instance wherever both are available.

This is the companion, for sheaves of commutative rings at the universe of the structure rings,
of `AlgebraicGeometry.Space.objUniverseHasWeakSheafify`, which does the same for sheaves of
abelian groups at the universe of the objects of the site. -/
instance (priority := high) structureUniverseHasWeakSheafifyCommRing
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasWeakSheafify (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  (SmallEtale.instHasSheafify B S hS F CommRingCat.{u}).isRightAdjoint

include φ in
/-- The morphism of Zariski ringed topoi `(X_{0, Zar}, 𝒪_{X₀}) ⟶ (Y_{0, Zar}, 𝒪_{Y₀})` of the
morphism of schemes underlying `φ : U ⟶ V`. -/
noncomputable abbrev representedZariskiSchemeHom :
    AlgebraicGeometry.RingedToposHom
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos :=
  Scheme.Hom.zariskiRingedToposHom ((BigFppfOver.toScheme B S hS).map φ)

include φ in
/-- **`ε⁻¹f_0^{-1}𝒪_{Y₀}`**, a sheaf of commutative rings on the small étale site of the
algebraic space `X = h_U`: the inverse image along `ε` of the inverse image along `f₀` of the
structure sheaf of `Y₀`.

This is the bottom-left corner of the square of Stacks 08GH, and the coefficient ring of the
naive cotangent complex that Stacks 08TZ would identify with `ε⁻¹\NL_{X₀/Y₀}`. -/
noncomputable abbrev representedZariskiInverseImageBaseRing :
    Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} :=
  (representedZariskiInverseImageCommRing B S hS U).obj
    ((inverseImageCommRingFunctor.{u, u, u, u, u, u}
      (representedZariskiSchemeHom B S hS φ).toToposHom).obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)

/-- **`ε⁻¹(f_0^♯) : ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ ε⁻¹𝒪_{X₀}`**, the left-hand vertical map of the square of
Stacks 08GH: the inverse image along `ε` of the structure map of `f₀`, in inverse-image form. -/
noncomputable abbrev representedZariskiInverseImageSchemeSharp :
    representedZariskiInverseImageBaseRing B S hS φ ⟶
      (representedZariskiInverseImageCommRing B S hS U).obj
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O :=
  (representedZariskiInverseImageCommRing B S hS U).map
    (representedZariskiSchemeHom B S hS φ).fSharpInverseImage

include φ in
/-- **`\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}}`**, on the small étale site of the represented
algebraic space `X = h_U`: the naive cotangent complex of the inverse image along `ε` of the
structure map of `f₀`.

This is the complex that Modules on Sites, Lemma 08TZ would identify with the inverse image
`ε⁻¹\NL_{X₀/Y₀}` of the naive cotangent complex of `f₀`; that identification is not available at
these universes, see the scope section of this file. -/
noncomputable def representedZariskiInverseImageNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u + 1, u, u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        ((representedZariskiInverseImageCommRing B S hS U).obj
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O))) ℤ :=
  letI : HasWeakSheafify
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} :=
    structureUniverseHasWeakSheafifyCommRing B S hS _
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedZariskiInverseImageBaseRing B S hS φ)
    ((representedZariskiInverseImageCommRing B S hS U).obj
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)
    (representedZariskiInverseImageSchemeSharp B S hS φ)

/-- **The structure map `ε⁻¹f_0^{-1}𝒪_{Y₀} ⟶ 𝒪_X` of the composite `f₀ ∘ ε`**: the inverse image
along `ε` of the structure map of `f₀`, followed by `ε^♯`.

That it is the structure map of the composite morphism of ringed topoi is
`AlgebraicGeometry.Space.representedZariskiBaseStructureMap_eq`. -/
noncomputable abbrev representedZariskiBaseStructureMap :
    representedZariskiInverseImageBaseRing B S hS φ ⟶
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O :=
  representedZariskiInverseImageSchemeSharp B S hS φ ≫
    representedZariskiStructureSharpInverseImage B S hS U

include φ in
/-- **`\NL_{𝒪_X / ε⁻¹f_0^{-1}𝒪_{Y₀}}`**: the naive cotangent complex, on the small étale site of
`X = h_U`, of the composite morphism of ringed topoi
`f₀ ∘ ε : (X_étale, 𝒪_X) ⟶ (Y_{0, Zar}, 𝒪_{Y₀})`. -/
noncomputable def representedZariskiBaseNaiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u + 1, u, u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)) ℤ :=
  letI : HasWeakSheafify
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} :=
    structureUniverseHasWeakSheafifyCommRing B S hS _
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedZariskiInverseImageBaseRing B S hS φ)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (representedZariskiBaseStructureMap B S hS φ)

/-- **The coefficient ring and the structure map of
`AlgebraicGeometry.Space.representedZariskiBaseNaiveCotangentComplex` are those of the composite
morphism of ringed topoi `f₀ ∘ ε`.**  The structure map, in inverse-image form, of the composite
of `ε : (X_étale, 𝒪_X) ⟶ (X_{0, Zar}, 𝒪_{X₀})` with `f₀ : (X_{0, Zar}, 𝒪_{X₀}) ⟶ (Y_{0, Zar},
𝒪_{Y₀})` is the comparison of `(f₀ ∘ ε)^{-1}𝒪_{Y₀}` with the iterated inverse image
`ε⁻¹f_0^{-1}𝒪_{Y₀}`, followed by `ε⁻¹(f_0^♯) ≫ ε^♯`.

This is the composition law of Stacks 01D3 (3) in inverse-image form. -/
theorem representedZariskiBaseStructureMap_eq :
    (AlgebraicGeometry.RingedToposHom.comp (representedZariskiSchemeHom B S hS φ)
          (representedToSchemeZariskiRingedToposHom B S hS U)).fSharpInverseImage =
      (inverseImageCommRingComp (representedZariskiSchemeHom B S hS φ).toToposHom
            (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).inv.app
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O ≫
        representedZariskiBaseStructureMap B S hS φ :=
  AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_eq
    (representedZariskiSchemeHom B S hS φ) (representedToSchemeZariskiRingedToposHom B S hS U)

/-- **The canonical chain map of Stacks 08TX**
`\NL_{ε⁻¹𝒪_{X₀} / ε⁻¹f_0^{-1}𝒪_{Y₀}} ⟶ \NL_{𝒪_X / ε⁻¹f_0^{-1}𝒪_{Y₀}}`, attached to the square of
sheaves of commutative rings on the small étale site of `X = h_U` whose top edge is
`ε^♯ : ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` and whose bottom edge is the identity of `ε⁻¹f_0^{-1}𝒪_{Y₀}`.  The
target is read in complexes of sheaves of `ε⁻¹𝒪_{X₀}`-modules by restriction of scalars along
`ε^♯`.

This is the `ε^♯` half of step 2 of the proof of Stacks 0D0X.  The other half needs the square of
Remark 08GH, which is `AlgebraicGeometry.Space.representedEpsilonSquareTwoIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiEpsilonSquare.lean:828`); the full chain
map into `\NL_{X/Y}` built from it is
`AlgebraicGeometry.Space.representedZariskiNaiveCotangentComplexCompare` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiNaiveCotangentCompare.lean`.  See the
scope section of this file. -/
noncomputable def representedZariskiNaiveCotangentComplexMap :
    representedZariskiInverseImageNaiveCotangentComplex B S hS φ ⟶
      ((_root_.SheafOfModules.restrictScalars.{u + 1}
          (underlyingRingHomOfSite.{u, u + 1, u}
            (representedZariskiStructureSharpInverseImage B S hS U))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (representedZariskiBaseNaiveCotangentComplex B S hS φ) :=
  letI : HasWeakSheafify
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J CommRingCat.{u} :=
    structureUniverseHasWeakSheafifyCommRing B S hS _
  Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
    (representedZariskiInverseImageBaseRing B S hS φ)
    ((representedZariskiInverseImageCommRing B S hS U).obj
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O)
    (representedZariskiInverseImageSchemeSharp B S hS φ)
    (representedZariskiInverseImageBaseRing B S hS φ)
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O
    (representedZariskiBaseStructureMap B S hS φ)
    (𝟙 (representedZariskiInverseImageBaseRing B S hS φ))
    (representedZariskiStructureSharpInverseImage B S hS U)
    (Category.id_comp (representedZariskiBaseStructureMap B S hS φ)).symm

end AlgebraicGeometry.Space

end
