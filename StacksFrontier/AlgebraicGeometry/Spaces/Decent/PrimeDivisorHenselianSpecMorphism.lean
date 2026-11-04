module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianSpecMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The canonical morphism at the generic point of a prime divisor

Let `X` be a decent algebraic space over `S` and let `Z ⊆ X` be a prime divisor with generic
point `ξ`.  Stacks 0ENK attaches to this situation the canonical morphism

`c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X`

and uses it to pull back an invertible module `ℒ` to `Spec(𝒪^h_{X, ξ})`, which is what makes
the ratio `s / s_ξ` of Stacks 0EPR canonical.  This file specializes the construction of
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom` to the chosen affine
elementary étale neighborhood `AlgebraicGeometry.Space.PrimeDivisor.genericChart` of `ξ`, which
makes `c_ξ` depend on nothing beyond the prime divisor and the henselization carried as a
parameter.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianSpace` is `Spec(𝒪^h_{X, ξ})` as an
  algebraic space over the base.
* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianMorphism` is
  `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianClosedPoint` is the closed point
  `𝔪^h_ξ` of `Spec(𝒪^h_{X, ξ})`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianPullback` is `c_ξ^*ℒ`, and
  `AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalk` is `ℒ_ξ`, its module of sections,
  as a module over the henselization carried as a parameter.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.pointsMap_genericHenselianMorphism_closedPoint`:
  `c_ξ` carries `𝔪^h_ξ` to the generic point `ξ` of the prime divisor.  This is the property
  that makes `c_ξ` the morphism of Stacks 0ENK rather than some other morphism to `X`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianMorphism_hom`: `c_ξ` factors through
  the generic chart.

## Implementation notes

As in `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpaceHom`, the henselian local
ring is carried as an abstract henselization `R` in `Type u` of the Zariski local ring of the
generic chart at its distinguished point, together with its containment in the chosen big site:
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing` is a `CommRingCat.{u + 1}` and
its spectrum is not an object of the site.  That the two agree is
`AlgebraicGeometry.Space.henselianLocalRing_isHenselization`, which exhibits
`𝒪^h_{X, ξ}` as a henselization of the very same local ring.

The containment `hR` is a hypothesis rather than a consequence, exactly as in
`AlgebraicGeometry.Space.ClosedPointNeighborhood.toSpaceHom`: a henselization in `Type u`
exists by `IsLocalRing.exists_isHenselization_residueField`, but bounding its cardinality below
the cutoff of the site is a separate question which this library does not settle.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- `Spec(𝒪^h_{X, ξ})` at the generic point of a prime divisor, as an algebraic space over the
base. -/
def PrimeDivisor.genericHenselianSpace : AlgebraicSpaces B S hS :=
  (Z.genericChart B S hS hX hdec).henselianSpace R hR

/-- **Stacks 0ENK.  The canonical morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X`** at the generic point
of a prime divisor, as a morphism of algebraic spaces over the base.

This is the morphism along which Stacks 0EPR pulls back a meromorphic section of `ℒ` in order
to compare it with a generator of `c_ξ^*ℒ`. -/
def PrimeDivisor.genericHenselianMorphism :
    Z.genericHenselianSpace B S hS hX hdec R hR ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  (Z.genericChart B S hS hX hdec).toSpaceHom R hR

/-- The closed point `𝔪^h_ξ` of `Spec(𝒪^h_{X, ξ})`, as a point of the algebraic space that
spectrum represents. -/
def PrimeDivisor.genericHenselianClosedPoint :
    points B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj :=
  (Z.genericChart B S hS hX hdec).henselianClosedPoint R hR

/-- **The canonical morphism `c_ξ` carries the closed point of `Spec(𝒪^h_{X, ξ})` to the
generic point `ξ` of the prime divisor.**

This is what identifies `c_ξ` as the morphism of Stacks 0ENK: it is a morphism to `X` whose
source is the spectrum of a henselization of a local ring of `X` at `ξ` and which lies over
`ξ`. -/
theorem PrimeDivisor.pointsMap_genericHenselianMorphism_closedPoint :
    pointsMap B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianMorphism B S hS hX hdec R hR).hom
        (Z.genericHenselianClosedPoint B S hS hX hdec R hR) =
      Z.genericPoint B S hS X :=
  (Z.genericChart B S hS hX hdec).pointsMap_toSpaceHom_henselianClosedPoint R hR

omit [IsLocalRing R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R] in
/-- The canonical morphism `c_ξ` factors through the generic chart. -/
theorem PrimeDivisor.genericHenselianMorphism_hom :
    (Z.genericHenselianMorphism B S hS hX hdec R hR).hom =
      yoneda.map ((Z.genericChart B S hS hX hdec).toSchemeHom R hR) ≫
        (Z.genericChart B S hS hX hdec).toSpace :=
  (Z.genericChart B S hS hX hdec).toSpaceHom_hom R hR

/-- **`c_ξ^*ℒ`, the pullback of an `𝒪_X`-module to `Spec(𝒪^h_{X, ξ})`.**

This is the module whose generator `s_ξ` the ratio `s / s_ξ` of Stacks 0EPR is taken against:
`ℒ_ξ` of the source is the module of sections of `c_ξ^*ℒ`, an `𝒪^h_{X, ξ}`-module because the
structure sheaf of `Spec(𝒪^h_{X, ξ})` has `𝒪^h_{X, ξ}` for its global sections. -/
def PrimeDivisor.genericHenselianPullback (L : Modules.{u, u} B S hS X hX) :
    Modules.{u, u} B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property :=
  (modulePullback B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR)).obj L

/-- **`ℒ_ξ`, the module of sections of `c_ξ^*ℒ`**, as a module over the henselization `R` of
Stacks 0ENK, that is over `𝒪^h_{X, ξ}`.

It is read over `Spec(𝒪^h_{X, ξ})` itself, taken as the identity étale chart of the algebraic
space it represents; the structure sheaf there has `Γ(Spec(R)) ≅ R` for its sections, and the
scalars are restricted along that isomorphism. -/
def PrimeDivisor.genericModuleStalk (L : Modules.{u, u} B S hS X hX) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).obj
    ((Z.genericHenselianPullback B S hS hX hdec R hR L).val.obj
      (op (idEtaleChart B S hS ((Z.genericChart B S hS hX hdec).henselianObj R hR))))

end Generic

end AlgebraicGeometry.Space

end
