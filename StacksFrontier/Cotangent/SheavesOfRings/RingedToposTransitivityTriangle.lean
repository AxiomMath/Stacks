module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposCotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The transitivity triangle of the cotangent complex for a composition of morphisms of ringed
topoi

Let `f : (Sh(C₁), 𝒪₁) ⟶ (Sh(C₂), 𝒪₂)` and `g : (Sh(C₂), 𝒪₂) ⟶ (Sh(C₃), 𝒪₃)` be morphisms of
ringed topoi. The source's proof of the transitivity triangle

`Lf^* L_g ⟶ L_{g ∘ f} ⟶ L_f ⟶ (Lf^* L_g)[1]`

reads it off the fundamental triangle of the tower of sheaves of rings

`f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁`

on the site of the source: it sets `h = g ∘ f`, identifies `h⁻¹𝒪₃` with `f⁻¹g⁻¹𝒪₃`, and then
runs the fundamental triangle with `𝒜 = h⁻¹𝒪₃`, `ℬ = f⁻¹𝒪₂`, `𝒞 = 𝒪₁`. Its three vertices are
`L_{ℬ/𝒜} ⊗_ℬ 𝒞`, `L_{𝒞/𝒜}` and `L_{𝒞/ℬ}`; the last two are `L_{g ∘ f}` and `L_f` on the nose,
and the first one is `Lf^* L_g` because `f⁻¹L_g = L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃}`, which is the inverse
image of the cotangent complex.

That last identification is what this file provides, from
`CategoryTheory.Sheaf.inverseImageCotangentComplexIso`, together with the tower and its
vertices. The triangle itself, Tag 08V1, is
`AlgebraicGeometry.RingedToposHom.exists_distTriang_transitivity` in
`StacksFrontier/Cotangent/SheavesOfRings/RingedToposTransitivityTriangleDerived.lean`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.towerBaseMap` is the base homomorphism
  `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂` of the tower, namely `f⁻¹` of the inverse-image form of the structure map
  of `g`.
* `AlgebraicGeometry.RingedToposHom.fSharpExtendScalars` is extension of scalars
  `- ⊗_{f⁻¹𝒪₂} 𝒪₁` along the inverse-image form of the structure map of `f`.
* `AlgebraicGeometry.RingedToposHom.inverseImageCotangentComplex` is `f⁻¹L_g`, the inverse image
  of the cotangent complex of `g`, and
  `AlgebraicGeometry.RingedToposHom.pullbackCotangentComplex` is `Lf^* L_g`: that inverse image
  with its scalars extended to `𝒪₁`.
* `AlgebraicGeometry.RingedToposHom.towerFirstVertex` is the first vertex
  `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` of the fundamental triangle of the tower, and
  `AlgebraicGeometry.RingedToposHom.compositeCotangentComplex` is its middle vertex
  `L_{𝒪₁/f⁻¹g⁻¹𝒪₃}`, which is `L_{g ∘ f}`.

## Main results

* `AlgebraicGeometry.RingedToposHom.inverseImageCotangentComplex_eq`: `f⁻¹L_g` is the inverse
  image of the cotangent complex of `g`.
* `AlgebraicGeometry.RingedToposHom.pullbackCotangentComplexIso`: `Lf^* L_g` is the first vertex
  of the fundamental triangle of the tower. This is the inverse-image comparison of the
  cotangent complex, with its scalars extended.
* `AlgebraicGeometry.RingedToposHom.compFSharpInverseImage_eq`: the structure map of a composite
  of morphisms of ringed topoi factors as the base homomorphism of the tower followed by the
  structure map of the inner morphism, after the canonical identification of `(g ∘ f)⁻¹𝒪₃` with
  `f⁻¹g⁻¹𝒪₃`. This is the source's `h⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`.

## The vertices

The two subsections below record how the vertices defined here compare with those of the
source. `StacksFrontier/Cotangent/SheavesOfRings/RingedToposTransitivityTriangleDerived.lean`
passes from them to the vertices of Tag 08V1.

### The first vertex carries the degreewise, not the derived, tensor product

`pullbackCotangentComplex` extends the scalars of `f⁻¹L_g` degreewise, so it is `f^* L_g` rather
than `Lf^* L_g`. The two agree because each term of `L_g` is locally a free `𝒪₂`-module, which
is not proved here. This is the same deviation as in the first vertex of
the fundamental triangle of
`StacksFrontier/Cotangent/SheavesOfRings/FundamentalTriangle.lean`.

### The base ring of the middle vertex

The middle vertex is the cotangent complex of `𝒪₁` over `f⁻¹g⁻¹𝒪₃`, which is where the source
puts it: its proof identifies `h⁻¹𝒪₃` with `f⁻¹g⁻¹𝒪₃` and takes the latter as the base of the
tower. `compFSharpInverseImage_eq` records that identification for a literal composite of
morphisms of ringed topoi. Transporting the cotangent complex along it would need the square
functoriality of the cotangent complex of sheaves of rings at an isomorphism of base rings,
which the tower-free presentation here does not use.

## Implementation notes

The tower is formed on the site of the source, from the inverse-image forms of the two structure
maps: `towerBaseMap` is `f⁻¹` of the structure map of `g` and needs no comparison isomorphism,
and the structure map of `f` is already a homomorphism out of `f⁻¹𝒪₂`. This is why the
inverse-image comparison of the cotangent complex applies to the first vertex on the nose: the
base ring of the tower is literally the iterated inverse image `f⁻¹g⁻¹𝒪₃` that comparison
produces.

Extension of scalars is additive because its right adjoint, restriction of scalars, is; that is
what lets it act on cochain complexes.

The three sites keep independent object and morphism universes, and the target ringed topos
keeps an independent universe of sections. The source and the middle ringed topos carry their
structure sheaves in the universe range of `CategoryTheory.Sheaf.cotangentComplex`, as they must
for their cotangent complexes to be defined. The section on the composite structure map is
stated at the universes of `AlgebraicGeometry.RingedToposHom.compFSharpInverseImage`, where the
three ringed topoi share one universe of sections.

## References

* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1), the triangle.
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the fundamental
  triangle of a tower of sheaves of rings.
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV), the inverse image of
  the cotangent complex.
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU), the cotangent complex
  of a morphism of ringed topoi.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars
  for sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction)

universe v u w v' u' w' v'' u'' w'' t

namespace AlgebraicGeometry.RingedToposHom

section Tower

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', max u' v' w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v' w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

/-! ## The tower `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁` -/

/-- The base homomorphism `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂` of the tower: the inverse image along `f` of the
inverse-image form `g⁻¹𝒪₃ ⟶ 𝒪₂` of the structure map of `g`. -/
abbrev towerBaseMap := G.toToposHom.inverseImageRing.map F.fSharpInverseImage

/-- Extension of scalars `- ⊗_{f⁻¹𝒪₂} 𝒪₁` along the inverse-image form of the structure map of
`f`, for sheaves of modules on the site of the source. This is the functor of Tag 03CZ. -/
def fSharpExtendScalars :
    Sheaf.targetModules.{u, v, w} X.J (G.toToposHom.inverseImageRing.obj Y.O) ⥤
      Sheaf.targetModules.{u, v, w} X.J X.O :=
  extendScalars X.J G.fSharpInverseImage.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
      (G.toToposHom.inverseImageRing.obj Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X.O).property

/-- Extension of scalars is additive: its right adjoint, restriction of scalars, is. -/
instance fSharpExtendScalars_additive : (fSharpExtendScalars G).Additive :=
  (extendRestrictScalarsAdjunction X.J G.fSharpInverseImage.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
      (G.toToposHom.inverseImageRing.obj Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X.O).property).left_adjoint_additive

/-- Extension of scalars along the structure map of `f`, acting on cochain complexes. -/
def fSharpExtendComplexes :
    CochainComplex
        (Sheaf.targetModules.{u, v, w} X.J (G.toToposHom.inverseImageRing.obj Y.O)) ℤ ⥤
      CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  (fSharpExtendScalars G).mapHomologicalComplex (ComplexShape.up ℤ)

/-! ## The three vertices -/

/-- `f⁻¹L_g`: the inverse image along `f` of the cotangent complex of `g`, a complex of sheaves
of `f⁻¹𝒪₂`-modules on the site of the source. -/
def inverseImageCotangentComplex :
    CochainComplex
      (Sheaf.targetModules.{u, v, w} X.J (G.toToposHom.inverseImageRing.obj Y.O)) ℤ :=
  ((Sheaf.inverseImageTargetModules.{u, v, w, u', v', w'} X.J Y.J G.toToposHom
      (B := Y.O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Sheaf.cotangentComplex.{u', v', w'} Y.J F.fSharpInverseImage)

/-- `f⁻¹L_g` is the inverse image of the cotangent complex `L_g` of `g`: the cotangent complex
of a morphism of ringed topoi is the cotangent complex of the inverse-image form of its
structure map. -/
lemma inverseImageCotangentComplex_eq :
    inverseImageCotangentComplex F G =
      ((Sheaf.inverseImageTargetModules.{u, v, w, u', v', w'} X.J Y.J G.toToposHom
          (B := Y.O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F.cotangentComplex := rfl

/-- **The first vertex of Tag 08V1.** `Lf^* L_g`: the inverse image of the cotangent complex of
`g`, with its scalars extended from `f⁻¹𝒪₂` to `𝒪₁`. The extension of scalars is the degreewise
one; see the module documentation. -/
def pullbackCotangentComplex :
    CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  (fSharpExtendComplexes G).obj (inverseImageCotangentComplex F G)

/-- The first vertex `L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` of the fundamental triangle of the
tower. -/
def towerFirstVertex :
    CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  (fSharpExtendComplexes G).obj (Sheaf.cotangentComplex.{u, v, w} X.J (towerBaseMap F G))

/-- **The middle vertex of Tag 08V1.** `L_{g ∘ f} = L_{𝒪₁/f⁻¹g⁻¹𝒪₃}`, the cotangent complex of
the composite homomorphism `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂ ⟶ 𝒪₁` of the tower. -/
def compositeCotangentComplex :
    CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  Sheaf.cotangentComplex.{u, v, w} X.J
    (towerBaseMap F G ≫ G.fSharpInverseImage)

/-! ## The first vertex is `Lf^* L_g` -/

/-- **Tag 08V1's identification of the first vertex.** `Lf^* L_g` is the first vertex
`L_{f⁻¹𝒪₂/f⁻¹g⁻¹𝒪₃} ⊗_{f⁻¹𝒪₂} 𝒪₁` of the fundamental triangle of the tower: the inverse image
of the cotangent complex of `g` is the cotangent complex of `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂` by Tag 08SV, and
extension of scalars carries that identification to the two first vertices. -/
def pullbackCotangentComplexIso :
    pullbackCotangentComplex F G ≅
      towerFirstVertex F G :=
  (fSharpExtendComplexes G).mapIso
    (Sheaf.inverseImageCotangentComplexIso.{u, v, w, u', v', w'} X.J Y.J G.toToposHom
      F.fSharpInverseImage)

end Tower

/-! ## The structure map of a literal composite -/

section Composite

open Stacks.Sheaves.ToposPushforward (inverseImageCommRingComp)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}} {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

/-- **The source's `h⁻¹𝒪₃ = f⁻¹g⁻¹𝒪₃`.** The inverse-image form of the structure map of a
composite of morphisms of ringed topoi is the canonical identification of `(g ∘ f)⁻¹𝒪₃` with the
iterated inverse image `f⁻¹g⁻¹𝒪₃`, followed by the base homomorphism `f⁻¹g⁻¹𝒪₃ ⟶ f⁻¹𝒪₂` of the
tower and then by the structure map of `f`. So the cotangent complex of the composite tower is
`L_{g ∘ f}` read over `f⁻¹g⁻¹𝒪₃`, which is where the source's proof puts it. -/
lemma compFSharpInverseImage_eq :
    compFSharpInverseImage F G =
      (inverseImageCommRingComp F.toToposHom G.toToposHom).inv.app Z.O ≫
        G.toToposHom.inverseImageRing.map F.fSharpInverseImage ≫ G.fSharpInverseImage :=
  rfl

end Composite

end AlgebraicGeometry.RingedToposHom

end
