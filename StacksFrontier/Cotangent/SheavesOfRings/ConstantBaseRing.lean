module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a morphism of ringed topoi over a constant base ring

Let `Λ` be a commutative ring and let `X` be an algebraic space over `Λ`, with structure
morphism `p : X ⟶ Spec(Λ)`. The cotangent complex `L_{X/Spec(Λ)}` agrees with the cotangent
complex `L_{𝒪_X/Λ̲}` of the homomorphism of sheaves of rings `Λ̲ ⟶ 𝒪_X`, where `Λ̲` is the
constant sheaf with value `Λ` on `X_{étale}`.

The source's proof is the transitivity triangle of Tag 08V1 for the composite
`X ⟶ Spec(Λ) ⟶ (*, Λ)`, whose first vertex is `Lp^* L_q` for `q : Spec(Λ)_{étale} ⟶ (*, Λ)`
the morphism to the punctual ringed topos: the middle vertex of that triangle is the cotangent
complex over the base `(q ∘ p)^{-1}Λ = Λ̲` and the third one is `L_p = L_{X/Spec(Λ)}`, so once
`L_q = 0` the triangle degenerates to an isomorphism between them.

Everything here is stated for a morphism of ringed topoi `G : X ⟶ Y` and a homomorphism of
sheaves of rings `b : Λ̲ ⟶ G⁻¹𝒪_Y` on the site of `X`, which is what "`X` is a space over `Λ`"
provides; the punctual topos itself does not appear, because the base of the tower is the
constant sheaf directly.

## Main definitions

* `AlgebraicGeometry.RingedTopos.constantRing` is the constant sheaf of commutative rings `Λ̲`
  with value `Λ` on the site of a ringed topos, that is, the sheafification of the constant
  presheaf.
* `AlgebraicGeometry.RingedToposHom.cotangentComplexOverBase` is `L_{𝒪_X/Λ̲}`, the cotangent
  complex of the composite `Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X`: the middle vertex of the tower.
* `AlgebraicGeometry.RingedToposHom.firstVertexOverBase` is its first vertex
  `L_{G⁻¹𝒪_Y/Λ̲} ⊗_{G⁻¹𝒪_Y} 𝒪_X`.

## Main results

* `AlgebraicGeometry.RingedToposHom.firstVertexOverInverseImageBaseIso`: when the base of the
  tower is an inverse image `G⁻¹Λ_Y`, the first vertex is `G^*` of `G⁻¹L_{𝒪_Y/Λ_Y}`. This is
  how the vanishing hypothesis below is the source's `L_q = 0`: with `Λ_Y = q^{-1}Λ` the
  complex `L_{𝒪_Y/Λ_Y}` is `L_q`.
* `AlgebraicGeometry.RingedToposHom.cotangentComplexOverBaseIso`: the degeneration of the
  tower's triangle when its first vertex is acyclic, for an arbitrary base.
* `AlgebraicGeometry.RingedToposHom.cotangentComplexOverConstantRingIso`: **Stacks 08VG**,
  `L_{X/Y} ≅ L_{𝒪_X/Λ̲}` in `D(𝒪_X)`.

## What is proved and what is carried

The identification is an isomorphism in the derived category of `𝒪_X`-modules, not an equality
of complexes: the two complexes are built from different standard resolutions and only their
images in `D(𝒪_X)` agree. That is also the shape the source's own proof produces, since it
reads the identification off a distinguished triangle.

Two hypotheses are carried, both inputs of the source's argument.

### The fundamental triangle of the tower

The short exact sequence `S`, `hS` with `e₁`, `e₂`, `e₃` identifying its three terms with the
three vertices of the fundamental triangle of Tag 08SZ for the tower `Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X` is
carried because the sheaf-level analogue of Tag 08SD is absent from this library, so the
fundamental triangle is taken as the short exact sequence of complexes its own proof produces.
It is an input and not the conclusion: a short exact sequence of complexes is strictly more
data than a distinguished triangle on its vertices, and the passage from one to the other is
part of what is proved here.

### The vanishing of the first vertex

`hv` says that the first vertex `L_{G⁻¹𝒪_Y/Λ̲} ⊗_{G⁻¹𝒪_Y} 𝒪_X` is acyclic. This is the source's
`L_q = 0`, pulled back to `X`: by `firstVertexOverInverseImageBaseIso` the first vertex of a
tower whose base is an inverse image `G⁻¹Λ_Y` is `G^*` of `G⁻¹L_{𝒪_Y/Λ_Y}`, and for
`Λ_Y = q^{-1}Λ` that complex is `L_q`. The source proves `L_q = 0` from the stalkwise criterion
of Properties of Spaces, Theorem 04K5, the stalk of the cotangent complex of Tag 08T0, the
description of the étale local rings of `Spec(Λ)` as strict henselizations of local rings of
`Λ` of Properties of Spaces, Lemma 04KF, and the vanishing of the cotangent complex of a strict
henselization of Tag 08R2; none of those four is available in this library in a form that
applies to the acyclicity of a complex of sheaves of modules on a site, so the composite
vanishing is carried as a single hypothesis at the one complex it is needed for. It is about
the morphism `q` out of `Y` and not about the two complexes the conclusion identifies, neither
of which occurs in it.

### The constant sheaf

`Λ̲` is `CategoryTheory.constantSheaf`, the sheafification of the constant presheaf with value
`Λ`, which is the source's `Λ̲`; no identification of it with an iterated inverse image
`p^{-1}q^{-1}Λ` is used or needed, since the tower is formed with `Λ̲` as its base from the
outset. The homomorphism `b : Λ̲ ⟶ G⁻¹𝒪_Y` is data, the `Λ`-algebra structure of the base; for
the structure morphism of an algebraic space over `Λ` it is the canonical one.

### The first vertex carries the degreewise extension of scalars

`firstVertexOverBase` extends scalars degreewise along `G⁻¹𝒪_Y ⟶ 𝒪_X`, through Tag 08V1's
`AlgebraicGeometry.RingedToposHom.fSharpExtendComplexes`, so it is `G^*` rather than `LG^*`.
This is the same deviation as in the first vertex of Tag 08V1 and of the fundamental triangle,
and it is harmless for the statement: the hypothesis is the vanishing of the vertex that
actually occurs in the triangle.

## References

* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG), the statement.
* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1), the transitivity
  triangle.
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV), the inverse image of
  the cotangent complex.
* [Stacks Project, Tag 08SU](https://stacks.math.columbia.edu/tag/08SU), the cotangent complex
  of a morphism of ringed topoi.
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the fundamental
  triangle of a tower of sheaves of rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u w v' u' w' t

namespace AlgebraicGeometry

namespace RingedTopos

/-- The constant sheaf of commutative rings `Λ̲` with value `Λ` on the site of a ringed topos:
the sheafification of the constant presheaf. This is the source's `Λ̲`. -/
def constantRing (X : RingedTopos.{v, u, max u v w}) (Λ : CommRingCat.{max u v w}) :
    Sheaf X.J CommRingCat.{max u v w} :=
  (constantSheaf X.J CommRingCat.{max u v w}).obj Λ

/-- `Λ̲` is the sheafification of the constant presheaf with value `Λ`. -/
lemma constantRing_eq (X : RingedTopos.{v, u, max u v w}) (Λ : CommRingCat.{max u v w}) :
    X.constantRing Λ =
      (presheafToSheaf X.J CommRingCat.{max u v w}).obj ((Functor.const X.Cᵒᵖ).obj Λ) :=
  rfl

end RingedTopos

namespace RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', max u' v' w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v' w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (G : RingedToposHom X Y)

/-! ## The tower `Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X` -/

section Base

variable {Λs : Sheaf X.J CommRingCat.{max u v w}}
  (b : Λs ⟶ G.toToposHom.inverseImageRing.obj Y.O)

/-- **The middle vertex.** `L_{𝒪_X/Λ̲}`, the cotangent complex of the composite
`Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X` of the tower, a complex of sheaves of `𝒪_X`-modules. -/
def cotangentComplexOverBase : CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  Sheaf.cotangentComplex.{u, v, w} X.J (b ≫ G.fSharpInverseImage)

/-- **The first vertex.** `L_{G⁻¹𝒪_Y/Λ̲} ⊗_{G⁻¹𝒪_Y} 𝒪_X`, the first vertex of the fundamental
triangle of the tower. The extension of scalars is the degreewise one of Tag 08V1. -/
def firstVertexOverBase : CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ :=
  (fSharpExtendComplexes G).obj (Sheaf.cotangentComplex.{u, v, w} X.J b)

end Base

/-- **The first vertex over an inverse-image base is `G^* G⁻¹L`.** When the base of the tower is
the inverse image `G⁻¹Λ_Y` of a sheaf of rings on the target, the first vertex is the inverse
image of the cotangent complex of `Λ_Y ⟶ 𝒪_Y`, with its scalars extended to `𝒪_X`. By Tag 08SV
the cotangent complex of `G⁻¹Λ_Y ⟶ G⁻¹𝒪_Y` is the inverse image of the cotangent complex of
`Λ_Y ⟶ 𝒪_Y`, and extension of scalars carries that identification to the two vertices.

With `Λ_Y` the inverse image of `Λ` along a morphism `q : Y ⟶ (*, Λ)` to the punctual ringed
topos, `L_{𝒪_Y/Λ_Y}` is `L_q` and this reads the first vertex as `G^* L_q`, which is the vertex
the source makes vanish. This generalizes
`AlgebraicGeometry.RingedToposHom.pullbackCotangentComplexIso` from the base `q⁻¹𝒪_Z` of a
morphism of ringed topoi to an arbitrary sheaf of rings over `𝒪_Y`. -/
def firstVertexOverInverseImageBaseIso {ΛY : Sheaf Y.J CommRingCat.{max u' v' w'}}
    (bY : ΛY ⟶ Y.O) :
    (fSharpExtendComplexes G).obj
        (((Sheaf.inverseImageTargetModules.{u, v, w, u', v', w'} X.J Y.J G.toToposHom
              (B := Y.O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Sheaf.cotangentComplex.{u', v', w'} Y.J bY)) ≅
      firstVertexOverBase G (G.toToposHom.inverseImageRing.map bY) :=
  (fSharpExtendComplexes G).mapIso
    (Sheaf.inverseImageCotangentComplexIso.{u, v, w, u', v', w'} X.J Y.J G.toToposHom bY)

/-! ## The degeneration of the triangle -/

section Iso

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]
  {Λs : Sheaf X.J CommRingCat.{max u v w}}
  (b : Λs ⟶ G.toToposHom.inverseImageRing.obj Y.O)

/-- **The tower's triangle degenerates when its first vertex is acyclic.** Let
`b : Λs ⟶ G⁻¹𝒪_Y` be a homomorphism of sheaves of rings on the site of `X`. Given the
fundamental triangle of the tower `Λs ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X` as a short exact sequence `S`, `hS` of
complexes with its three terms identified with the three vertices (`e₁`, `e₂`, `e₃`), and given
that the first vertex is acyclic (`hv`), the other two agree in `D(𝒪_X)`:
`L_{X/Y} ≅ L_{𝒪_X/Λs}`.

This is the step the source performs with Tag 08V1: the short exact sequence gives a
distinguished triangle on the three vertices, and a distinguished triangle whose first object
vanishes has its second map invertible. -/
def cotangentComplexOverBaseIso
    (S : ShortComplex (CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ firstVertexOverBase G b)
    (e₂ : S.X₂ ≅ cotangentComplexOverBase G b)
    (e₃ : S.X₃ ≅ G.cotangentComplex)
    (hv : IsZero (DerivedCategory.Q.obj (firstVertexOverBase G b))) :
    G.cotangentComplexDerived ≅ DerivedCategory.Q.obj (cotangentComplexOverBase G b) :=
  have hz : IsZero (DerivedCategory.Q.obj S.X₁) := hv.of_iso (DerivedCategory.Q.mapIso e₁)
  haveI : IsIso (DerivedCategory.Q.map S.g) :=
    ((DerivedCategory.triangleOfSES hS).isZero₁_iff_isIso₂
      (DerivedCategory.triangleOfSES_distinguished hS)).mp hz
  (DerivedCategory.Q.mapIso e₃).symm ≪≫ (asIso (DerivedCategory.Q.map S.g)).symm ≪≫
    DerivedCategory.Q.mapIso e₂

end Iso

/-! ## Stacks 08VG -/

section Constant

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]
  {Λ : CommRingCat.{max u v w}}

/-- **Stacks 08VG.** Let `Λ` be a commutative ring and let `X` be a space over `Λ`, with
structure morphism `G : X ⟶ Y` of ringed topoi and with `b : Λ̲ ⟶ G⁻¹𝒪_Y` the `Λ`-algebra
structure of its base, `Λ̲` being the constant sheaf with value `Λ` on the site of `X`. Then

`L_{X/Y} ≅ L_{𝒪_X/Λ̲}`

in `D(𝒪_X)`: the cotangent complex of the morphism agrees with the cotangent complex of the
homomorphism of sheaves of rings `Λ̲ ⟶ 𝒪_X`.

Two hypotheses are carried, both inputs of the source's proof: the fundamental triangle of the
tower `Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X`, in the shape Tag 08V1 carries it, and the acyclicity `hv` of its
first vertex, which is the source's `L_q = 0` pulled back to `X` by
`firstVertexOverInverseImageBaseIso`. See the module documentation. -/
@[stacks 08VG "an isomorphism in `D(𝒪_X)` rather than an equality of complexes, as the source's \
own proof produces. `L_{X/Spec(Λ)}` is the cotangent complex of the morphism of ringed topoi \
(Tag 08SU) and `L_{𝒪_X/Λ̲}` is the cotangent complex of `Λ̲ ⟶ 𝒪_X` with `Λ̲` the constant sheaf \
of Mathlib's `constantSheaf`, so no identification of `Λ̲` with an iterated inverse image is \
used. TWO carried hypotheses, both inputs of the source's argument and neither the conclusion: \
(1) the short exact sequence `S`, `hS`, `e₁`, `e₂`, `e₃` giving the fundamental triangle of \
Tag 08SZ for the tower `Λ̲ ⟶ G⁻¹𝒪_Y ⟶ 𝒪_X`, carried in the same shape and for the same reason \
as in Tag 08V1 (the sheaf-level analogue of Tag 08SD is absent here); (2) `hv`, the acyclicity \
of the FIRST vertex `L_{G⁻¹𝒪_Y/Λ̲} ⊗ 𝒪_X`, which is the source's `L_q = 0` for \
`q : Spec(Λ)_étale ⟶ (*, Λ)` pulled back to `X` — `firstVertexOverInverseImageBaseIso` proves \
that a first vertex over an inverse-image base is `G^*G⁻¹L_{𝒪_Y/Λ_Y}` — and which the source \
obtains from Tags 04K5, 08T0, 04KF and 08R2, none of which this library has in a form \
applying to acyclicity of a complex of sheaves of modules on a site. The conclusion's two \
objects do not occur in either hypothesis. What is proved: the passage from the short exact \
sequence to a distinguished triangle, the identification of the first vertex over an \
inverse-image base through Tag 08SV, and the degeneration of the triangle. The first vertex \
carries the DEGREEWISE extension of scalars, as in Tag 08V1"]
def cotangentComplexOverConstantRingIso
    (b : X.constantRing Λ ⟶ G.toToposHom.inverseImageRing.obj Y.O)
    (S : ShortComplex (CochainComplex (Sheaf.targetModules.{u, v, w} X.J X.O) ℤ))
    (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ firstVertexOverBase G b)
    (e₂ : S.X₂ ≅ cotangentComplexOverBase G b)
    (e₃ : S.X₃ ≅ G.cotangentComplex)
    (hv : IsZero (DerivedCategory.Q.obj (firstVertexOverBase G b))) :
    G.cotangentComplexDerived ≅ DerivedCategory.Q.obj (cotangentComplexOverBase G b) :=
  cotangentComplexOverBaseIso G b S hS e₁ e₂ e₃ hv

end Constant

end RingedToposHom

end AlgebraicGeometry

end
