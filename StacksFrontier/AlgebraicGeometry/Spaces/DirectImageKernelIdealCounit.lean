module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCommRingCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealInverseImage
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The direct image of the counit, and the compatibility of the two structure maps

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdealInverseImage.lean` carries
the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` through the inverse image and then the direct image of
sheaves of modules; its third term is `f_*f⁻¹f_*𝒪_X`, while the third term of the sequence it
came from is `f_*𝒪_X`.  The comparison between the two is the direct image of the counit
`f⁻¹f_*𝒪_X ⟶ 𝒪_X` of `f⁻¹ ⊣ f_*`.

This file builds that comparison as a homomorphism of **sheaves of rings** and proves the one
identity that makes it a morphism over `𝒪_Y`, namely that the unit of `f⁻¹ ⊣ f_*` followed by
`f_*f⁻¹(f♯)` and then by it is the structure map `f♯` itself.

## Main definitions

* `AlgebraicGeometry.Space.directImageRingCounit`: the counit of `f⁻¹ ⊣ f_*` at `𝒪_X`, pushed
  forward, as a homomorphism `f_*f⁻¹f_*𝒪_X ⟶ f_*𝒪_X` of sheaves of rings on the small étale
  site of `Y`.

## Main results

* `AlgebraicGeometry.Space.ringUnit_comp_directImageRingCounit`: **the unit of `f⁻¹ ⊣ f_*` at
  `𝒪_Y`, followed by `f_*f⁻¹(f♯)` and then by the direct image of the counit, is the structure
  map `f♯ : 𝒪_Y ⟶ f_*𝒪_X`** of Stacks 03G8.  Every statement holds for an arbitrary morphism of
  algebraic spaces; no closed immersion is assumed.

## Implementation notes

The two sequences compared above are sequences of `𝒪_Y`-modules, and `𝒪_Y` acts on
`f_*f⁻¹f_*𝒪_X` through the unit followed by `f_*f⁻¹(f♯)`, while it acts on `f_*𝒪_X` through
`f♯`.  So this identity is exactly the hypothesis that the direct image of the counit is a
homomorphism of `𝒪_Y`-algebras; under it `SheafOfModules.unitRestrictScalarsMapOfComp` reads
a homomorphism of sheaves of rings as a morphism of `𝒪_Y`-modules between restrictions of
scalars of unit modules.  The proof is naturality of the unit at `f♯`, which turns the first
two factors into `f♯` followed by the unit at `f_*𝒪_X`, and then the triangle identity of the
adjunction, which collapses that unit against the direct image of the counit.

The type of the pushed-forward counit is not restated: writing it out makes the universe
parameters of `Stacks.Sheaves.ToposPullback.inverseImageRingSheaf` default, and the argument is
then rejected at `Sheaf.{0, 0, 0, 1}` with a message that reads as an unrelated type mismatch
about `AlgebraicGeometry.Space.structureRingSheafDirectImage`.  The same expression is accepted
with its type ascribed under other import sets, so the ascription is not reliable here; the type
is left to be inferred from the term.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image, and
  [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3), its adjunction.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map in
  its two forms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The counit of `f⁻¹ ⊣ f_*` at `𝒪_X`, pushed forward.**  The homomorphism
`f_*f⁻¹f_*𝒪_X ⟶ f_*𝒪_X` of sheaves of rings on the small étale site of `Y`, for an arbitrary
morphism `f` of algebraic spaces.

The type is left to be inferred; see the implementation notes. -/
noncomputable def directImageRingCounit (f : X ⟶ Y) :=
  pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
    (ringCounit (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS X))

/-- **The two structure maps agree.**  The unit of `f⁻¹ ⊣ f_*` at `𝒪_Y`, followed by
`f_*f⁻¹(f♯)` and then by the direct image of the counit, is the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8.  This holds for an arbitrary morphism of algebraic spaces.

The left-hand side is how `𝒪_Y` acts on `f_*f⁻¹f_*𝒪_X` and the right-hand side is how it acts
on `f_*𝒪_X`, so this says the direct image of the counit is a homomorphism of `𝒪_Y`-algebras;
see the implementation notes.  The proof is naturality of the unit at `f♯` followed by the
triangle identity of the adjunction. -/
theorem ringUnit_comp_directImageRingCounit (f : X ⟶ Y) :
    (ringUnit (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y) ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS Y.1)
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward
          (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
            (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
            (structureSharp B S hS f))) ≫
      directImageRingCounit B S hS f =
    structureSharp B S hS f := by
  have hnat := (ringImageAdjunction
    (smallEtaleRingedToposHom B S hS f).toToposHom).unit.naturality (structureSharp B S hS f)
  have htri := (ringImageAdjunction
    (smallEtaleRingedToposHom B S hS f).toToposHom).right_triangle_components
    (Y := structureRingSheaf B S hS X)
  exact Eq.trans (congrArg (fun m ↦ m ≫ directImageRingCounit B S hS f) hnat.symm)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun m ↦ structureSharp B S hS f ≫ m) htri) (Category.comp_id _)))

end AlgebraicGeometry.Space

end
