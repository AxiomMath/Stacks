module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The structure map of a composite factors through that of its first factor

Let `p' : X' ⟶ Y'` and `q : Y' ⟶ Y` be morphisms of algebraic spaces over a scheme `S`.  This
file proves that the structure map of the composite factors through the direct image of the
structure map of `p'`: there is a section of `(p' ≫ q)_*((p')⁻¹𝒪_{Y'})` whose image under the
direct image of the inverse-image form `(p')♯ : (p')⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` is
`(p' ≫ q)♯ : 𝒪_Y ⟶ (p' ≫ q)_*𝒪_{X'}`.

Transposed across the adjunction `(p' ≫ q)⁻¹ ⊣ (p' ≫ q)_*`, that is the statement that
`(p' ≫ q)♯ : (p' ≫ q)⁻¹𝒪_Y ⟶ 𝒪_{X'}` factors through `(p')♯ : (p')⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}`, and that
factorization is what makes the universal `Y'`-derivation `d_{X'/Y'}` a `Y`-derivation — the
`d_app` clause of a relative derivation.  It is consumed in that form by
`AlgebraicGeometry.Space.exists_structureSharpInverseImage_comp_factorization` of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeDifferentialsTriangle.lean`, which is where the
transposition is performed.

For morphisms of ringed *spaces* the statement is cheap: the direct image of a composite *is* the
composite of the direct images, so the two readings can be compared by substituting along an
equality of morphisms.  For algebraic spaces they are only isomorphic, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso`, and the composition law
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` of Stacks 03G8 is what the
substitution has to be replaced by.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardStructureCompIso` is the comparison of the iterated direct
  image of sheaves of commutative rings along `p'` and then `q` with the direct image along the
  composite morphism of ringed topoi, stated at the spelling the composite's own structure map
  uses.
* `AlgebraicGeometry.Space.inverseImageStructureSheafSection` is the section of
  `(p' ≫ q)_*((p')⁻¹𝒪_{Y'})` built from `q♯` and the unit of `(p')⁻¹ ⊣ (p')_*`.

## Main results

* `AlgebraicGeometry.Space.inverseImageStructureSheafSection_comp`: the factorization above, i.e.
  the section is carried to `(p' ≫ q)♯` by the direct image of `(p')♯`.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp_eq'`: the structure map of a
  composite of morphisms of small étale ringed topoi, written out through
  `pushforwardStructureCompIso` in the bracketing the substitution chain below consumes.
* `AlgebraicGeometry.Space.unit_comp_map_structureSharpInverseImage`: the unit of
  `(p')⁻¹ ⊣ (p')_*` followed by the direct image of `(p')♯` in inverse-image form is `(p')♯` in
  direct-image form.

## Implementation notes

No mate of `smallEtaleRingedToposHom_compRingIso` on inverse-image functors is used, and none is
needed.  What the consumer needs is only the *existence* of the factorization, and existence
transports across the adjunction by
`CategoryTheory.Adjunction.homEquiv_naturality_right` alone: the factorization is built here on
the direct-image side, where Stacks 03G8 is available in the form
`smallEtaleRingedToposHom_comp_fSharp`, and the consumer transposes it.  An *equation* between
the two inverse-image structure maps of the composite would need the mate; the factorization does
not.

Two features of the setting force the shape of the proof.

First, `AlgebraicGeometry.Space.structureSharpCommRing` — the `CommRingCat`-valued structure map,
and hence the `fSharp` field of `smallEtaleRingedToposHom` — is marked `irreducible`, so nothing
below may compute with it; only `smallEtaleRingedToposHom_comp_fSharp` and the definition of
`AlgebraicGeometry.RingedToposHom.comp` are used.

Second, the underlying morphism of topoi of a composite of morphisms of ringed topoi has two
spellings — `((smallEtaleRingedToposHom B S hS q).comp
(smallEtaleRingedToposHom B S hS p')).toToposHom` and the composite of the two
`toToposHom`s — which are definitionally but not syntactically equal, and
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso` is stated at the second spelling
while Stacks 03G8 and `RingedToposHom.comp` are stated at the first.  A `rewrite` whose motive
mentions both is not type-correct at the transparency `rw` unifies at.  So
`pushforwardStructureCompIso` is a `def` that fixes the first spelling once — a definition and not
a type ascription, because an ascription is discarded after elaboration while a definition fixes
the spelling for good — and everything downstream uses it.

The terms involved are large enough that assembling the substitution chain inside one declaration
exceeds the default heartbeat budget.  It is therefore extracted as the private lemma
`transportChain₂`, stated for arbitrary objects and morphisms of an arbitrary category, where
`rw` is cheap and cannot trip on transparency; it is applied once, at explicit arguments.  This
keeps every declaration inside the default budget, so no `maxHeartbeats` is raised anywhere in
this file.

No `@[stacks]` attribute is attached and no tag's content is stated here: the factorization is one
input to the sheaf of differentials of a composite, not a clause of a tag, and Stacks 03G8 is
consumed rather than proved.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces and its compatibility with composition.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials, whose universal derivation consumes this factorization.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), the adjunction
  `f⁻¹ ⊣ f_*`.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

section CategoricalChains

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- The substitution chain of `inverseImageStructureSheafSection_comp`: a four-factor composite
followed by `pmα`, rewritten by two naturality squares, the functoriality identity `h3`, and the
composition law `h4` and `h5`. -/
private theorem transportChain₂ {A Z1 Z2 Z3 Z4 W2 W3 W4 : C}
    (qS : A ⟶ Z1) (Qu : Z1 ⟶ Z2) (ihN : Z2 ⟶ Z3) (RhN : Z3 ⟶ Z4) (pmα : Z4 ⟶ W4)
    (pcα : Z3 ⟶ W3) (Rho : W3 ⟶ W4) (ppα : Z2 ⟶ W2) (iho : W2 ⟶ W3) (k : Z1 ⟶ W2)
    (cS' : A ⟶ W3) (fS' : A ⟶ W4)
    (h1 : RhN ≫ pmα = pcα ≫ Rho) (h2 : ihN ≫ pcα = ppα ≫ iho) (h3 : Qu ≫ ppα = k)
    (h4 : qS ≫ k ≫ iho = cS') (h5 : cS' ≫ Rho = fS') :
    (qS ≫ Qu ≫ ihN ≫ RhN) ≫ pmα = fS' := by
  rw [Category.assoc, Category.assoc, Category.assoc, h1, ← Category.assoc ihN pcα Rho, h2,
    Category.assoc, ← Category.assoc Qu ppα (iho ≫ Rho), h3, ← Category.assoc k iho Rho,
    ← Category.assoc qS (k ≫ iho) Rho, h4, h5]

end CategoricalChains

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}

/-- The comparison of the direct image of sheaves of commutative rings along `f` and then along
`p` with the direct image along the composite morphism of small étale ringed topoi.

This is `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso`, stated with its target at
the spelling `((smallEtaleRingedToposHom B S hS p).comp
(smallEtaleRingedToposHom B S hS f)).toToposHom`, which is the spelling the structure map of the
composite and Stacks 03G8 use. -/
noncomputable def pushforwardStructureCompIso (f : X' ⟶ X) (p : X ⟶ Y)
    (N : Sheaf (SmallEtale.topology B S hS X'.1) CommRingCat.{u}) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).obj
        ((pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).obj N) ≅
      (pushforwardCommRingFunctor
        ((smallEtaleRingedToposHom B S hS p).comp
          (smallEtaleRingedToposHom B S hS f)).toToposHom).obj N :=
  pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS f).toToposHom
    (smallEtaleRingedToposHom B S hS p).toToposHom N

/-- `AlgebraicGeometry.Space.pushforwardStructureCompIso` is natural in the sheaf of commutative
rings: it is `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafComp_naturality` for the two
direct-image functors. -/
theorem pushforwardStructureCompIso_naturality (f : X' ⟶ X) (p : X ⟶ Y)
    {N N' : Sheaf (SmallEtale.topology B S hS X'.1) CommRingCat.{u}} (a : N ⟶ N') :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS p).toToposHom).map
          ((pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS f).toToposHom).map a) ≫
        (pushforwardStructureCompIso B S hS f p N').hom =
      (pushforwardStructureCompIso B S hS f p N).hom ≫
        (pushforwardCommRingFunctor
          ((smallEtaleRingedToposHom B S hS p).comp
            (smallEtaleRingedToposHom B S hS f)).toToposHom).map a :=
  pullbackCommRingSheafComp_naturality (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS Y.1) _ _ a

/-- The structure map of a composite of morphisms of small étale ringed topoi, written out: the
structure map of the outer morphism, the direct image of the structure map of the inner one, and
the comparison of the iterated direct image with the direct image of the composite, bracketed to
the right, which is the bracketing `inverseImageStructureSheafSection_comp` consumes. -/
theorem smallEtaleRingedToposHom_comp_fSharp_eq' (f : X' ⟶ X) (p : X ⟶ Y) :
    ((smallEtaleRingedToposHom B S hS p).comp (smallEtaleRingedToposHom B S hS f)).fSharp =
      (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (pushforwardCommRingFunctor
            (smallEtaleRingedToposHom B S hS p).toToposHom).map
              (smallEtaleRingedToposHom B S hS f).fSharp ≫
        (pushforwardStructureCompIso B S hS f p
          (smallEtaleRingedTopos B S hS X').O).hom := rfl

/-- The unit of `(p')⁻¹ ⊣ (p')_*` at `𝒪_{Y'}`, followed by the direct image of the inverse-image
form `(p')♯ : (p')⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` of the structure map, is the direct-image form
`(p')♯ : 𝒪_{Y'} ⟶ (p')_*𝒪_{X'}`.  The inverse-image form is by definition the adjunct of the
direct-image form, and this is that statement read through
`CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem unit_comp_map_structureSharpInverseImage (p' : X' ⟶ Y') :
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS p').toToposHom).unit.app
          (smallEtaleRingedTopos B S hS Y').O ≫
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS p').toToposHom).map
            (structureSharpInverseImage B S hS p') =
      (smallEtaleRingedToposHom B S hS p').fSharp :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The section of `(p' ≫ q)_*((p')⁻¹𝒪_{Y'})` obtained from the structure map of `q` and the unit
of `(p')⁻¹ ⊣ (p')_*`, read through the comparisons of iterated direct images.  It is the
factorization of the structure map of `p' ≫ q` through the direct image of `(p')♯`. -/
noncomputable def inverseImageStructureSheafSection (p' : X' ⟶ Y') (q : Y' ⟶ Y) :
    (smallEtaleRingedTopos B S hS Y).O ⟶
      (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS (p' ≫ q)).toToposHom).obj
          (inverseImageStructureSheaf B S hS p') :=
  (smallEtaleRingedToposHom B S hS q).fSharp ≫
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).map
        ((commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS p').toToposHom).unit.app
            (smallEtaleRingedTopos B S hS Y').O) ≫
    (pushforwardStructureCompIso B S hS p' q
      (inverseImageStructureSheaf B S hS p')).hom ≫
    (smallEtaleRingedToposHom_compRingIso B S hS p' q).hom.app
      (inverseImageStructureSheaf B S hS p')

/-- `AlgebraicGeometry.Space.inverseImageStructureSheafSection` is a factorization of the
structure map of `p' ≫ q` through the direct image of the inverse-image form of the structure map
of `p'`. -/
theorem inverseImageStructureSheafSection_comp (p' : X' ⟶ Y') (q : Y' ⟶ Y) :
    inverseImageStructureSheafSection B S hS p' q ≫
        (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS (p' ≫ q)).toToposHom).map
            (structureSharpInverseImage B S hS p') =
      (smallEtaleRingedToposHom B S hS (p' ≫ q)).fSharp :=
  transportChain₂ _ _ _ _ _
    ((pushforwardCommRingFunctor
      ((smallEtaleRingedToposHom B S hS q).comp
        (smallEtaleRingedToposHom B S hS p')).toToposHom).map
          (structureSharpInverseImage B S hS p'))
    ((smallEtaleRingedToposHom_compRingIso B S hS p' q).hom.app
      (smallEtaleRingedTopos B S hS X').O)
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).map
      ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS p').toToposHom).map
          (structureSharpInverseImage B S hS p')))
    (pushforwardStructureCompIso B S hS p' q (smallEtaleRingedTopos B S hS X').O).hom
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).map
      (smallEtaleRingedToposHom B S hS p').fSharp)
    ((smallEtaleRingedToposHom B S hS q).comp
      (smallEtaleRingedToposHom B S hS p')).fSharp
    (smallEtaleRingedToposHom B S hS (p' ≫ q)).fSharp
    ((smallEtaleRingedToposHom_compRingIso B S hS p' q).hom.naturality _).symm
    (pushforwardStructureCompIso_naturality B S hS p' q _).symm
    ((((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).map_comp _ _).symm).trans
      (congrArg (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).map
        (unit_comp_map_structureSharpInverseImage B S hS p')))
    (smallEtaleRingedToposHom_comp_fSharp_eq' B S hS p' q).symm
    (smallEtaleRingedToposHom_comp_fSharp B S hS p' q)

end AlgebraicGeometry.Space

end
