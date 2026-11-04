module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Invariant functions for a pre-relation

Let `j : R ⟶ U ×_B U` be a pre-relation of algebraic spaces over an algebraic space `B`, with
target and source maps `t, s : R ⟶ U`, and let `φ : U ⟶ X` be an `R`-invariant morphism, so
that `φ' := t ≫ φ = s ≫ φ`.  Pulling functions back along `t` and along `s` gives two maps
`φ_*O_U ⟶ φ'_*O_R` of sheaves of rings on the small étale site of `X`, and the *sheaf of
`R`-invariant functions* is their equalizer.  The functions on `X` are the `R`-invariant
functions on `U` when the structure map `φ^♯ : O_X ⟶ φ_*O_U` exhibits `O_X` as that equalizer.

## Main definitions

* `AlgebraicGeometry.Space.relationFunctionMap` is the map `φ_*O_U ⟶ (p ≫ φ)_*O_R` of pulling
  functions back along a morphism `p : R ⟶ U`, for any morphism `φ` out of `U`.
* `AlgebraicGeometry.Space.invariantSourceFunctionMap` is the map obtained from the source map
  of an invariant morphism, read in the direct image along the target composite.
* `AlgebraicGeometry.Space.invariantFunctionSheaf` is **Stacks 04AA**, part (1), the sheaf of
  `R`-invariant functions, and `AlgebraicGeometry.Space.toInvariantFunctionSheaf` is the
  natural map to it from the structure sheaf of `X`.
* `AlgebraicGeometry.Space.HasInvariantFunctions` is **Stacks 04AA**, part (2): the functions
  on `X` are the `R`-invariant functions on `U`.

## Main results

* `AlgebraicGeometry.Space.fSharp_comp_relationFunctionMap`: the structure map of `φ` followed
  by pullback along `p` is the structure map of `p ≫ φ`.  This is the composition law of
  **Stacks 03G8** for the structure maps, and it is what makes the two pullback maps agree
  after `φ^♯` when `φ` is invariant
  (`AlgebraicGeometry.Space.fSharp_comp_invariantFunctionMap_eq`).

## Implementation notes

The direct images are those of the canonical morphisms of small étale ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` of **Stacks 03G8**, taken on sheaves of
commutative rings.  `AlgebraicGeometry.Space.relationFunctionMap` therefore has to compare
the iterated direct image along `p` and then `φ` with the direct image along `p ≫ φ`; it does
so in the two steps that are available: the comparison of iterated direct images with the
direct image of the composite *morphism of ringed topoi*
(`Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso`, the comparison in part (3) of
**Stacks 01D3**) followed by the comparison of that composite with the morphism of ringed
topoi of the composite morphism of algebraic spaces
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso`).

For an invariant `φ` the two pullback maps have *equal* but not syntactically identical
codomains, since `t ≫ φ` and `s ≫ φ` are equal morphisms rather than the same morphism.  The
identification is the identity, so it is an `CategoryTheory.eqToHom` along
`AlgebraicGeometry.Space.invariantPushforward_eq`; everything that has to be known about it is
`AlgebraicGeometry.Space.fSharp_comp_eqToHom`, which transports a structure map along such an
equality of morphisms.

Part (2) is stated as invertibility of the natural map
`AlgebraicGeometry.Space.toInvariantFunctionSheaf`, which is the source's formulation.  The
equation needed to build that map is not an assumption: it is
`AlgebraicGeometry.Space.fSharp_comp_invariantFunctionMap_eq`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 04AA](https://stacks.math.columbia.edu/tag/04AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)

/-! ### Pulling functions back along a morphism -/

/-- Pullback of functions along `p : R ⟶ U`, read in the direct images along a morphism `φ`
out of `U` and along the composite `p ≫ φ`: the direct image along `φ` of the structure map of
`p`, followed by the comparison of the iterated direct image with the direct image of the
composite. -/
noncomputable def relationFunctionMap {R U X : AlgebraicSpaces site S hS}
    (p : R ⟶ U) (φ : U ⟶ X) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS φ).toToposHom).obj
        (smallEtaleRingedTopos site S hS U).O ⟶
      (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom site S hS (p ≫ φ)).toToposHom).obj
        (smallEtaleRingedTopos site S hS R).O :=
  ((pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS φ).toToposHom).map
        (smallEtaleRingedToposHom site S hS p).fSharp ≫
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom site S hS p).toToposHom
        (smallEtaleRingedToposHom site S hS φ).toToposHom
        (smallEtaleRingedTopos site S hS R).O).hom) ≫
    (smallEtaleRingedToposHom_compRingIso site S hS p φ).hom.app
      (smallEtaleRingedTopos site S hS R).O

/-- The structure map of `φ` followed by pullback of functions along `p` is the structure map
of `p ≫ φ`.  This is the composition law of **Stacks 03G8** for the structure maps, read on
the direct images.

The left-hand side is, by definition of composition of morphisms of ringed topoi, the
structure map of the composite morphism of ringed topoi followed by the comparison of its
direct image with that of the morphism of ringed topoi of `p ≫ φ`. -/
theorem fSharp_comp_relationFunctionMap {R U X : AlgebraicSpaces site S hS}
    (p : R ⟶ U) (φ : U ⟶ X) :
    (smallEtaleRingedToposHom site S hS φ).fSharp ≫ relationFunctionMap site S hS p φ =
      (smallEtaleRingedToposHom site S hS (p ≫ φ)).fSharp :=
  Eq.trans
    (Category.assoc (smallEtaleRingedToposHom site S hS φ).fSharp
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS φ).toToposHom).map
            (smallEtaleRingedToposHom site S hS p).fSharp ≫
          (pushforwardCommRingCompIso (smallEtaleRingedToposHom site S hS p).toToposHom
            (smallEtaleRingedToposHom site S hS φ).toToposHom
            (smallEtaleRingedTopos site S hS R).O).hom)
        ((smallEtaleRingedToposHom_compRingIso site S hS p φ).hom.app
          (smallEtaleRingedTopos site S hS R).O)).symm
    (smallEtaleRingedToposHom_comp_fSharp site S hS p φ)

/-- The direct images of `O_R` along two equal morphisms agree. -/
theorem pushforwardCommRing_obj_eq {R X : AlgebraicSpaces site S hS} {ψ ψ' : R ⟶ X}
    (h : ψ = ψ') :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS ψ).toToposHom).obj
        (smallEtaleRingedTopos site S hS R).O =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS ψ').toToposHom).obj
        (smallEtaleRingedTopos site S hS R).O :=
  congrArg (fun χ : R ⟶ X =>
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS χ).toToposHom).obj
      (smallEtaleRingedTopos site S hS R).O) h

/-- Transport of a structure map along an equality of morphisms. -/
theorem fSharp_comp_eqToHom {R X : AlgebraicSpaces site S hS} {ψ ψ' : R ⟶ X} (h : ψ = ψ') :
    (smallEtaleRingedToposHom site S hS ψ).fSharp ≫
        eqToHom (pushforwardCommRing_obj_eq site S hS h) =
      (smallEtaleRingedToposHom site S hS ψ').fSharp := by
  subst h
  exact Category.comp_id _

/-! ### The sheaf of invariant functions -/

variable {B : AlgebraicSpaces site S hS}

/-- For an `R`-invariant morphism `φ` the direct image of `O_R` along `s ≫ φ` is its direct
image along `t ≫ φ`, the two morphisms being equal. -/
theorem invariantPushforward_eq {R U : Over B} {X : AlgebraicSpaces site S hS}
    (j : PreRelation R U) (φ : U.left ⟶ X) (hφ : IsInvariant j φ) :
    (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom site S hS (j.source.left ≫ φ)).toToposHom).obj
        (smallEtaleRingedTopos site S hS R.left).O =
      (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom site S hS (j.target.left ≫ φ)).toToposHom).obj
        (smallEtaleRingedTopos site S hS R.left).O :=
  pushforwardCommRing_obj_eq site S hS hφ.symm

/-- Pullback of functions along the source map of an `R`-invariant morphism, read in the direct
image along the target composite `t ≫ φ`. -/
noncomputable def invariantSourceFunctionMap {R U : Over B}
    {X : AlgebraicSpaces site S hS} (j : PreRelation R U) (φ : U.left ⟶ X)
    (hφ : IsInvariant j φ) :
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom site S hS φ).toToposHom).obj
        (smallEtaleRingedTopos site S hS U.left).O ⟶
      (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom site S hS (j.target.left ≫ φ)).toToposHom).obj
        (smallEtaleRingedTopos site S hS R.left).O :=
  relationFunctionMap site S hS j.source.left φ ≫
    eqToHom (invariantPushforward_eq site S hS j φ hφ)

/-- The structure map of an `R`-invariant morphism `φ` equalizes the two pullback maps of the
pre-relation: both composites are the structure map of `φ' = t ≫ φ = s ≫ φ`. -/
theorem fSharp_comp_invariantFunctionMap_eq {R U : Over B}
    {X : AlgebraicSpaces site S hS} (j : PreRelation R U) (φ : U.left ⟶ X)
    (hφ : IsInvariant j φ) :
    (smallEtaleRingedToposHom site S hS φ).fSharp ≫
        relationFunctionMap site S hS j.target.left φ =
      (smallEtaleRingedToposHom site S hS φ).fSharp ≫
        invariantSourceFunctionMap site S hS j φ hφ := by
  have h : (smallEtaleRingedToposHom site S hS φ).fSharp ≫
      invariantSourceFunctionMap site S hS j φ hφ =
      (smallEtaleRingedToposHom site S hS (j.target.left ≫ φ)).fSharp := by
    rw [invariantSourceFunctionMap, ← Category.assoc, fSharp_comp_relationFunctionMap,
      fSharp_comp_eqToHom site S hS hφ.symm]
  rw [fSharp_comp_relationFunctionMap, h]

/-- **Stacks 04AA**, part (1).  The *sheaf of `R`-invariant functions* `(φ_*O_U)^R` of an
`R`-invariant morphism `φ : U ⟶ X`: the equalizer, on the small étale site of `X`, of the two
maps `φ_*t^♯, φ_*s^♯ : φ_*O_U ⟶ φ'_*O_R` given by pulling functions back along the target and
the source of the pre-relation.

Its inclusion into `φ_*O_U` as an `O_X`-subalgebra is `CategoryTheory.Limits.equalizer.ι`,
which is a monomorphism. -/
@[stacks 04AA "part (1): the sheaf of invariant functions"]
noncomputable def invariantFunctionSheaf {R U : Over B} {X : AlgebraicSpaces site S hS}
    (j : PreRelation R U) (φ : U.left ⟶ X) (hφ : IsInvariant j φ) :
    Sheaf (SmallEtale.topology site S hS X.1) CommRingCat.{u} :=
  equalizer (relationFunctionMap site S hS j.target.left φ)
    (invariantSourceFunctionMap site S hS j φ hφ)

/-- The natural map from the structure sheaf of `X` to the sheaf of `R`-invariant functions,
induced by the structure map `φ^♯ : O_X ⟶ φ_*O_U`. -/
noncomputable def toInvariantFunctionSheaf {R U : Over B} {X : AlgebraicSpaces site S hS}
    (j : PreRelation R U) (φ : U.left ⟶ X) (hφ : IsInvariant j φ) :
    (smallEtaleRingedTopos site S hS X).O ⟶ invariantFunctionSheaf site S hS j φ hφ :=
  equalizer.lift (smallEtaleRingedToposHom site S hS φ).fSharp
    (fSharp_comp_invariantFunctionMap_eq site S hS j φ hφ)

/-- **Stacks 04AA**, part (2).  *The functions on `X` are the `R`-invariant functions on `U`*
when the natural map `O_X ⟶ (φ_*O_U)^R` is an isomorphism. -/
@[stacks 04AA "part (2): the functions on X are the invariant functions"]
noncomputable abbrev HasInvariantFunctions {R U : Over B} {X : AlgebraicSpaces site S hS}
    (j : PreRelation R U) (φ : U.left ⟶ X) (hφ : IsInvariant j φ) : Prop :=
  IsIso (toInvariantFunctionSheaf site S hS j φ hφ)

end AlgebraicGeometry.Space

end
