module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SplitSurjectionIdealDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalDirectImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompFactorization

/-!
# The split surjection and the base of the derivation of Stacks 02HP for a closed subspace

Let `Z ⊆ X` be a closed subspace of an algebraic space with inclusion `i`, and let `g : X ⟶ Z`
be a left inverse of `i`.  The derivation of Stacks 02HP that
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SplitSurjectionIdealDerivation.lean` produces
runs on the split surjection
```
  π = i_*(i♯) : i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z,   sec = i_*(s),
```
and is relative to a base map `ψ` whose image the section fixes.  This file supplies those two
data for the closed subspace, with the base taken to be `Z` itself through `g`.

## Main results

* `AlgebraicGeometry.Space.directImageInverseImageStructureSharpSection_comp_hom`: the split
  surjection, at the presheaf level the derivation consumes.
* `AlgebraicGeometry.Space.conormalSplitBase_comp` and
  `AlgebraicGeometry.Space.conormalSplitBase_comp_apply`: **the section fixes everything coming
  from the base**, as morphisms and on sections.

## Implementation notes

**Why the base is `Z` through `g`, and not an ambient `B`.**  The derivation of Stacks 02HP is a
relative derivation for any base map whose image the section fixes.  Over `Z` that hypothesis is
exactly `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` pushed forward along
`i_*` and transposed by the naturality of the unit of Stacks 00YV — no compatibility of `g` with
an ambient base is used, which is why the injectivity clause of Stacks 05ZB holds for *any* left
inverse of `i`, over the tag's base or not.

**The transposition is naturality of the unit, nothing more.**
`AlgebraicGeometry.Space.conormalSplitBase` is `g♯ : g⁻¹𝒪_Z ⟶ 𝒪_X` followed by the unit
`η : 𝒪_X ⟶ i_*i⁻¹𝒪_X`, and naturality of `η` at `g♯` rewrites it as `η` at `g⁻¹𝒪_Z` followed by
`i_*i⁻¹(g♯)` — which is the factor the pushed forward `_fixes` statement acts on.  The proof is in
term mode: `rw` with `CategoryTheory.Functor.map_comp` does not fire on these composites, and the
naturality square is stated at `(𝟭 _).map` and `(f⁻¹ ⋙ f_*).map`, neither of which `rw` matches
against the written-out spellings.

## References

* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the derivation.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), the adjunction whose
  unit `η` is.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the consumer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
  (g : X ⟶ subspaceSpace B S hS Z)
  (hg : subspaceInclusion B S hS X Z ≫ g = 𝟙 (subspaceSpace B S hS Z))

/-- The unit `η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` of the adjunction of Stacks 00YV on sheaves of commutative
rings, at the structure sheaf of `X`. -/
noncomputable abbrev directImageInverseImageStructureUnit :
    (smallEtaleRingedTopos B S hS X).O ⟶
      directImageInverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z) :=
  (commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.app
    (smallEtaleRingedTopos B S hS X).O

/-- **The split surjection of Stacks 02HP, at presheaf level.**  The direct image of the
section is a section of the direct image of the inverse-image form of the structure map. -/
theorem directImageInverseImageStructureSharpSection_comp_hom :
    (directImageInverseImageStructureSharpSection B S hS
          (subspaceInclusion B S hS X Z) g hg).hom ≫
        (directImageStructureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z)).hom =
      𝟙 ((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).obj
        (smallEtaleRingedTopos B S hS (subspaceSpace B S hS Z)).O).obj :=
  congrArg (fun m ↦ m.hom)
    (directImageInverseImageStructureSharpSection_comp B S hS
      (subspaceInclusion B S hS X Z) g hg)

/-- **The base map of the derivation of Stacks 02HP**: the structure map of `g` followed by the
unit `η`.  Taking the base to be `Z` itself, through the left inverse `g`, is what makes the
derivation a `Z`-derivation without any hypothesis relating `g` to a base `B`. -/
noncomputable abbrev conormalSplitBase :
    inverseImageStructureSheaf B S hS g ⟶
      directImageInverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z) :=
  structureSharpInverseImage B S hS g ≫
    directImageInverseImageStructureUnit B S hS X Z

/-- **The section fixes everything coming from the base**, pushed forward and composed with the
unit.  This is `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` carried along
`i_*` and transposed by the naturality of the unit of Stacks 00YV. -/
theorem conormalSplitBase_comp :
    conormalSplitBase B S hS X Z g ≫
        (directImageStructureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) ≫
          directImageInverseImageStructureSharpSection B S hS
            (subspaceInclusion B S hS X Z) g hg) =
      conormalSplitBase B S hS X Z g :=
  have hnat : conormalSplitBase B S hS X Z g =
      (commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.app
          (inverseImageStructureSheaf B S hS g) ≫
        (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
          ((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS X Z)).map
            (structureSharpInverseImage B S hS g)) :=
    (commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.naturality
      (structureSharpInverseImage B S hS g)
  have hkey : (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
        ((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS X Z)).map
          (structureSharpInverseImage B S hS g)) ≫
        (directImageStructureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) ≫
          directImageInverseImageStructureSharpSection B S hS
            (subspaceInclusion B S hS X Z) g hg) =
      (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
        ((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS X Z)).map
          (structureSharpInverseImage B S hS g)) :=
    Eq.trans
      (congrArg (fun t ↦ (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
          ((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS X Z)).map
            (structureSharpInverseImage B S hS g)) ≫ t)
        ((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map_comp
          (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z))
          (inverseImageStructureSharpSection B S hS
            (subspaceInclusion B S hS X Z) g hg)).symm)
      (Eq.trans
        ((pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map_comp
          ((smallEtaleInverseImageRing B S hS (subspaceInclusion B S hS X Z)).map
            (structureSharpInverseImage B S hS g))
          (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) ≫
            inverseImageStructureSharpSection B S hS
              (subspaceInclusion B S hS X Z) g hg)).symm
        (congrArg (pushforwardCommRingFunctor (subspaceToposHom B S hS X Z)).map
          (inverseImageStructureSharpSection_fixes B S hS
            (subspaceInclusion B S hS X Z) g hg)))
  Eq.trans
    (congrArg (fun t ↦ t ≫
        (directImageStructureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) ≫
          directImageInverseImageStructureSharpSection B S hS
            (subspaceInclusion B S hS X Z) g hg)) hnat)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun t ↦ (commRingImageAdjunction (subspaceToposHom B S hS X Z)).unit.app
            (inverseImageStructureSheaf B S hS g) ≫ t) hkey)
        hnat.symm))

/-- `AlgebraicGeometry.Space.conormalSplitBase_comp` on sections, in the shape the derivation
of Stacks 02HP consumes. -/
theorem conormalSplitBase_comp_apply (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((inverseImageStructureSheaf B S hS g).obj.obj U)) :
    ((directImageInverseImageStructureSharpSection B S hS
          (subspaceInclusion B S hS X Z) g hg).hom.app U).hom
        (((directImageStructureSharpInverseImage B S hS
            (subspaceInclusion B S hS X Z)).hom.app U).hom
          (((conormalSplitBase B S hS X Z g).hom.app U).hom t)) =
      ((conormalSplitBase B S hS X Z g).hom.app U).hom t :=
  congrArg (fun m ↦ (m.hom.app U).hom t) (conormalSplitBase_comp B S hS X Z g hg)

end AlgebraicGeometry.Space

end
