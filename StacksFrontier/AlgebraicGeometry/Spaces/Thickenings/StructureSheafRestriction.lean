module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# Restricting the inverse image of the structure sheaf along a square

Let `i : Z ⟶ X` and `φ : U ⟶ X` be morphisms of algebraic spaces over a scheme `S`, and let

    P --q--> U
    |        |
    p        φ
    v        v
    Z --i--> X

be a commuting square.  The inverse image `i^{-1}𝒪_X` of the structure sheaf is a sheaf of
rings on the small étale site of `Z`, and `q^{-1}𝒪_U` one on the small étale site of `P`.  This
file constructs the comparison

`κ : i^{-1}𝒪_X ⟶ p_*(q^{-1}𝒪_U)`

by which a regular function read on `Z` restricts to one read on `P`, and pins it by a proved
equation.

## Main definitions

* `AlgebraicGeometry.Space.pushRingComp` and `AlgebraicGeometry.Space.pushRingCompInv`: the
  comparison `g_*(f_* O) ≅ (f ≫ g)_* O` of iterated direct images of sheaves of rings, in its
  two directions.  These are the two steps
  `AlgebraicGeometry.Space.structureSharp_comp` is stated with, named so that a composite
  through them can be written in one line.
* `AlgebraicGeometry.Space.kappaPush`: the direct-image form `ψ : 𝒪_X ⟶ i_*(p_*(q^{-1}𝒪_U))`.
* `AlgebraicGeometry.Space.structureRingInverseImageRestrict`: `κ` itself, the adjunct of `ψ`.

## Main results

* `AlgebraicGeometry.Space.ringUnit_comp_map_structureRingInverseImageRestrict`: **the
  characterizing equation**, that the unit of `i^{-1} ⊣ i_*` followed by the direct image of
  `κ` is `ψ`.

## Implementation notes

**The functoriality this supplies.**  `AlgebraicGeometry.Space.structureRingSheafInverseImage`
is taken at one fixed morphism and comes with no comparison along a square.  Restricting a
thickening along an étale morphism, as in the descent of formal smoothness (step (II) of
[Stacks Project, Tag 04AM]), needs exactly `κ`: the two sheaves of rings in which the
comorphisms of two lifts are compared have the same index once the square's equation is used,
but different coefficient sheaves, `i^{-1}𝒪_X` against `q^{-1}𝒪_U`.

**`κ` is the adjunct, and carries no hypothesis.**  No thickening hypothesis is needed to define
it and none is imposed: only the square's equation `q ≫ φ = p ≫ i` enters, through the single
`eqToHom` built by `congrArg` on that equation — the device
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt` already uses for the same purpose.
`κ` is the transpose of `ψ` along the ring-level adjunction `i^{-1} ⊣ i_*` of
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, exactly as
`AlgebraicGeometry.Space.structureSharpRingInverseImage` is the transpose of
`AlgebraicGeometry.Space.structureSharp`; so the characterizing equation is the same
`ringImageAdjunction_homEquiv_apply` computation as
`AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage`.

**Why the characterizing equation, and not just the construction.**  `ψ` is a composite of five
morphisms, two of them comparisons of iterated direct images taken in opposite directions.  A
composite assembled the wrong way round has the same type; the equation below is what a
consumer should reason from, and it fails for any other composite.

**Only direct-image comparisons appear.**  Deliberately: the inverse-image analogue of
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` — an identification
`f^{-1} ⋙ g^{-1} ≅ (g ≫ f)^{-1}` — is **not** in this library, so a construction of `κ` that
transported `i^{-1}` through `p^{-1}` could not be assembled at all.  Going through `ψ` and the
adjunction avoids it: every comparison used is 03G2 (3) for the pushforward, which is proved.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), the
  compatibility of the small étale direct image with composition.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), the adjunction at an
  algebraic structure.
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM), the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X U P : AlgebraicSpaces B S hS}

/-- The comparison `g_*(f_* O) ⟶ (f ≫ g)_* O` of iterated direct images of sheaves of rings,
the one `AlgebraicGeometry.Space.structureSharp_comp` uses. -/
abbrev pushRingComp {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O) ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O :=
  (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1) (SmallEtale.topology B S hS V₃.1)
      (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).hom ≫
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g).hom

/-- The same comparison backwards, `(f ≫ g)_* O ⟶ g_*(f_* O)`. -/
abbrev pushRingCompInv {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g).inv ≫
    (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1) (SmallEtale.topology B S hS V₃.1)
      (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).inv

/-- `ψ`: the direct-image form of `κ`, a morphism `𝒪_X ⟶ i_*(p_*(q^{-1}𝒪_U))`. -/
def kappaPush {Zs : AlgebraicSpaces B S hS} (i : Zs ⟶ X) (φ : U ⟶ X) (q : P ⟶ U) (p : P ⟶ Zs)
    (hsq : q ≫ φ = p ≫ i) :
    structureRingSheaf B S hS X ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS i).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Zs.1)
          (smallToposMorphismTypeU B S hS p).pushforward
          (structureRingSheafInverseImage B S hS q)) :=
  structureSharp B S hS φ ≫
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS φ)).map
      (ringUnit (smallToposMorphismTypeU B S hS q) (structureRingSheaf B S hS U)) ≫
    pushRingComp B S hS q φ (structureRingSheafInverseImage B S hS q) ≫
    eqToHom (congrArg (fun m : P ⟶ X =>
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS q)) hsq) ≫
    pushRingCompInv B S hS p i (structureRingSheafInverseImage B S hS q)

/-- **`κ`**: the comparison `i^{-1}𝒪_X ⟶ p_*(q^{-1}𝒪_U)`, the adjunct of `ψ`. -/
def structureRingInverseImageRestrict {Zs : AlgebraicSpaces B S hS} (i : Zs ⟶ X) (φ : U ⟶ X)
    (q : P ⟶ U) (p : P ⟶ Zs) (hsq : q ≫ φ = p ≫ i) :
    structureRingSheafInverseImage B S hS i ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Zs.1)
        (smallToposMorphismTypeU B S hS p).pushforward
        (structureRingSheafInverseImage B S hS q) :=
  ((ringImageAdjunction (smallToposMorphismTypeU B S hS i)).homEquiv
    (structureRingSheaf B S hS X) _).symm (kappaPush B S hS i φ q p hsq)

/-- **The characterizing equation of `κ`**: the unit followed by the direct image of `κ` is
`ψ`.  A composite put together the wrong way round fails this. -/
theorem ringUnit_comp_map_structureRingInverseImageRestrict
    {Zs : AlgebraicSpaces B S hS} (i : Zs ⟶ X) (φ : U ⟶ X) (q : P ⟶ U) (p : P ⟶ Zs)
    (hsq : q ≫ φ = p ≫ i) :
    ringUnit (smallToposMorphismTypeU B S hS i) (structureRingSheaf B S hS X) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS i)).map
          (structureRingInverseImageRestrict B S hS i φ q p hsq) =
      kappaPush B S hS i φ q p hsq :=
  (ringImageAdjunction_homEquiv_apply (smallToposMorphismTypeU B S hS i)
      (structureRingSheaf B S hS X) _
      (structureRingInverseImageRestrict B S hS i φ q p hsq)).symm.trans
    (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Space

end
