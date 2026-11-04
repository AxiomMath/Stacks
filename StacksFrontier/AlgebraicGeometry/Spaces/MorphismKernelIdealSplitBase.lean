module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SplitSurjectionIdealDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealDirectImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompFactorization

/-!
# The split surjection and the base of the derivation of Stacks 02HP, at a free morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `g : Y ⟶ X` be a left inverse of `f`.
The derivation of Stacks 02HP that
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SplitSurjectionIdealDerivation.lean` produces
runs on the split surjection
```
  π = f_*(f♯) : f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X,   sec = f_*(s),
```
and is relative to a base map `ψ` whose image the section fixes.  This file supplies those two
data at an arbitrary morphism with a left inverse, with the base taken to be `X` itself through
`g`.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSplitDerivation.lean` is the same file for the
inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`.  **Every declaration below is
a respelling**: `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` and
`AlgebraicGeometry.Space.directImageInverseImageStructureSharpSection_comp` are already stated
at an arbitrary morphism with a left inverse, and the rest is naturality of the unit of
Stacks 00YV and functoriality of `pushforwardCommRingFunctor`.

## Main results

* `AlgebraicGeometry.Space.directImageInverseImageStructureSharpSection_comp_hom_of_hom`: the
  split surjection, at the presheaf level the derivation consumes.
* `AlgebraicGeometry.Space.kernelSplitBase_comp` and
  `AlgebraicGeometry.Space.kernelSplitBase_comp_apply`: **the section fixes everything coming
  from the base**, as morphisms and on sections.

## Implementation notes

**Why the base is `X` through `g`, and not an ambient `B`.**  The derivation of Stacks 02HP is a
relative derivation for any base map whose image the section fixes.  Over `X` that hypothesis is
exactly `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` pushed forward along
`f_*` and transposed by the naturality of the unit of Stacks 00YV — no compatibility of `g` with
an ambient base is used, which is why the injectivity clause of Stacks 05ZB holds for *any* left
inverse of `f`, over the tag's base or not.

**The transposition is naturality of the unit, nothing more.**
`AlgebraicGeometry.Space.kernelSplitBase` is `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` followed by the unit
`η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y`, and naturality of `η` at `g♯` rewrites it as `η` at `g⁻¹𝒪_X` followed by
`f_*f⁻¹(g♯)` — which is the factor the pushed forward `_fixes` statement acts on.  The proof is
in term mode: `rw` with `CategoryTheory.Functor.map_comp` does not fire on these composites, and
the naturality square is stated at `(𝟭 _).map` and `(f⁻¹ ⋙ f_*).map`, neither of which `rw`
matches against the written-out spellings.

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
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ X) (hg : f ≫ g = 𝟙 X)

/-- The unit `η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y` of the adjunction of Stacks 00YV on sheaves of commutative
rings, at the structure sheaf of `Y`. -/
noncomputable abbrev directImageInverseImageStructureUnitOfHom :
    (smallEtaleRingedTopos B S hS Y).O ⟶ directImageInverseImageStructureSheaf B S hS f :=
  (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom).unit.app
    (smallEtaleRingedTopos B S hS Y).O

/-- **The split surjection of Stacks 02HP, at presheaf level.**  The direct image of the section
is a section of the direct image of the inverse-image form of the structure map. -/
theorem directImageInverseImageStructureSharpSection_comp_hom_of_hom :
    (directImageInverseImageStructureSharpSection B S hS f g hg).hom ≫
        (directImageStructureSharpInverseImage B S hS f).hom =
      𝟙 ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS f).toToposHom).obj
          (smallEtaleRingedTopos B S hS X).O).obj :=
  congrArg (fun m ↦ m.hom)
    (directImageInverseImageStructureSharpSection_comp B S hS f g hg)

/-- **The base map of the derivation of Stacks 02HP**: the structure map of `g` followed by the
unit `η`.  Taking the base to be `X` itself, through the left inverse `g`, is what makes the
derivation an `X`-derivation without any hypothesis relating `g` to a base `B`. -/
noncomputable abbrev kernelSplitBase :
    inverseImageStructureSheaf B S hS g ⟶ directImageInverseImageStructureSheaf B S hS f :=
  structureSharpInverseImage B S hS g ≫
    directImageInverseImageStructureUnitOfHom B S hS f

/-- **The section fixes everything coming from the base**, pushed forward and composed with the
unit.  This is `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` carried along
`f_*` and transposed by the naturality of the unit of Stacks 00YV. -/
theorem kernelSplitBase_comp :
    kernelSplitBase B S hS f g ≫
        (directImageStructureSharpInverseImage B S hS f ≫
          directImageInverseImageStructureSharpSection B S hS f g hg) =
      kernelSplitBase B S hS f g :=
  have hnat : kernelSplitBase B S hS f g =
      (commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS f).toToposHom).unit.app
          (inverseImageStructureSheaf B S hS g) ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
          ((smallEtaleInverseImageRing B S hS f).map
            (structureSharpInverseImage B S hS g)) :=
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom).unit.naturality
      (structureSharpInverseImage B S hS g)
  have hkey : (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS f).toToposHom).map
        ((smallEtaleInverseImageRing B S hS f).map
          (structureSharpInverseImage B S hS g)) ≫
        (directImageStructureSharpInverseImage B S hS f ≫
          directImageInverseImageStructureSharpSection B S hS f g hg) =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map
        ((smallEtaleInverseImageRing B S hS f).map
          (structureSharpInverseImage B S hS g)) :=
    Eq.trans
      (congrArg (fun t ↦ (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).map
          ((smallEtaleInverseImageRing B S hS f).map
            (structureSharpInverseImage B S hS g)) ≫ t)
        ((pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).map_comp
          (structureSharpInverseImage B S hS f)
          (inverseImageStructureSharpSection B S hS f g hg)).symm)
      (Eq.trans
        ((pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).map_comp
          ((smallEtaleInverseImageRing B S hS f).map
            (structureSharpInverseImage B S hS g))
          (structureSharpInverseImage B S hS f ≫
            inverseImageStructureSharpSection B S hS f g hg)).symm
        (congrArg (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS f).toToposHom).map
          (inverseImageStructureSharpSection_fixes B S hS f g hg)))
  Eq.trans
    (congrArg (fun t ↦ t ≫
        (directImageStructureSharpInverseImage B S hS f ≫
          directImageInverseImageStructureSharpSection B S hS f g hg)) hnat)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun t ↦ (commRingImageAdjunction
            (smallEtaleRingedToposHom B S hS f).toToposHom).unit.app
            (inverseImageStructureSheaf B S hS g) ≫ t) hkey)
        hnat.symm))

/-- `AlgebraicGeometry.Space.kernelSplitBase_comp` on sections, in the shape the derivation of
Stacks 02HP consumes. -/
theorem kernelSplitBase_comp_apply (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (t : ToType ((inverseImageStructureSheaf B S hS g).obj.obj U)) :
    ((directImageInverseImageStructureSharpSection B S hS f g hg).hom.app U).hom
        (((directImageStructureSharpInverseImage B S hS f).hom.app U).hom
          (((kernelSplitBase B S hS f g).hom.app U).hom t)) =
      ((kernelSplitBase B S hS f g).hom.app U).hom t :=
  congrArg (fun m ↦ (m.hom.app U).hom t) (kernelSplitBase_comp B S hS f g hg)

end AlgebraicGeometry.Space

end
