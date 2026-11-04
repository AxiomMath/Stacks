module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.IsomRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsSiteSize

/-!
# The big fppf site contains the object representing a relative isomorphism functor

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an object of the big fppf site
of `S`, and let `z : Z ⟶ V` and `x : X ⟶ V` be two morphisms of the site whose underlying
morphisms of schemes are finite locally free. The relative isomorphism functor `Isom_V(Z, X)` is
then represented by an object of the category of schemes over the scheme underlying `V`
(`Stacks.Morphisms.relativeIsomObj`), and this file proves that the scheme underlying that
object lies in the site.

Two steps. The four relative morphism functors of the square of
`Stacks.Morphisms.relativeIsomObj` have sources and targets among `Z` and `X`, both finite
locally free over `V` and hence affine over `V`; so each of their representing objects lies in
the site by `AlgebraicGeometry.Space.contains_relativeHomRepresenting`, whose hypothesis on the
target is exactly the fibrewise one an affine morphism supplies
(`Stacks.Morphisms.exists_isAffineOpen_fibre_of_isAffineHom`). And the scheme underlying the
fibre product of the square is a fibre product of schemes
(`Stacks.Morphisms.relativeIsomObjLeftIso`), so it stays in the site by closure of the cutoff
under fibre products, Stacks 000R (1).

The consequence is that `Isom_V(Z, X)` is *represented by an object of the site over `V`*, and
not merely an algebraic space over `S`: the sections of the representing object over a test
object of the site are the isomorphisms of the two base changes to it.

## Main results

* `AlgebraicGeometry.Space.contains_relativeHomRepresenting_of_isAffineHom`: the site contains
  every object representing `Mor_V(Z, X)` when the morphism of schemes underlying `z` is finite
  locally free and the one underlying `x` is affine.
* `AlgebraicGeometry.Space.contains_relativeIsomObj_left`: the site contains the scheme
  underlying `Stacks.Morphisms.relativeIsomObj`.
* `AlgebraicGeometry.Space.exists_contains_isom_representing_prodOverBase`: for two morphisms of
  the site which are finite locally free, there is an object of the category of schemes over the
  scheme underlying `V` whose underlying scheme lies in the site and whose sections over a test
  object are the isomorphisms of the two base changes to it.

## Implementation notes

No `@[stacks]` attribute is placed here: the containment is a statement about the size cutoff of
the site, which is Stacks 000Q and Stacks 000R, already registered where those bounds are proved.

The terminal object of the category of schemes over the scheme underlying `V` appears as the
second corner of the square, and its underlying scheme is only *isomorphic* to the scheme
underlying `V`, not equal to it; `CategoryTheory.Over.mkIdTerminal` identifies the two and
`AlgebraicGeometry.Scheme.size_congr` transports the bound.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The big fppf site of `S` contains every object representing `Mor_V(Z, X)` for a finite
locally free `z` and an affine `x`.** An affine morphism satisfies the fibrewise hypothesis on
the target of Stacks 0BL4, by
`Stacks.Morphisms.exists_isAffineOpen_fibre_of_isAffineHom`. -/
theorem contains_relativeHomRepresenting_of_isAffineHom {V Zs Xs : BigFppfOver B S hS}
    (z : Zs ⟶ V) (x : Xs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    [AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map x)]
    (W : Over ((BigFppfOver.toScheme B S hS).obj V))
    (e : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
        (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W) :
    B.Contains W.left :=
  contains_relativeHomRepresenting z x
    (Stacks.Morphisms.exists_isAffineOpen_fibre_of_isAffineHom
      ((BigFppfOver.toScheme B S hS).map x)) W e

/-- **The big fppf site of `S` contains the scheme underlying the object representing
`Isom_V(Z, X)`.** The four corners of the square are in the site, and the cutoff is closed under
fibre products. -/
theorem contains_relativeIsomObj_left {V Zs Xs : BigFppfOver B S hS}
    (z : Zs ⟶ V) (x : Xs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map x)]
    {W₁ W₂ V₁ V₂ : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (e₁ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
      (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy W₁)
    (e₂ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map x))
      (Over.mk ((BigFppfOver.toScheme B S hS).map z))).RepresentableBy W₂)
    (e₃ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map z))
      (Over.mk ((BigFppfOver.toScheme B S hS).map z))).RepresentableBy V₁)
    (e₄ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map x))
      (Over.mk ((BigFppfOver.toScheme B S hS).map x))).RepresentableBy V₂) :
    B.Contains (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).left := by
  have h₁ : B.Contains W₁.left := contains_relativeHomRepresenting_of_isAffineHom z x W₁ e₁
  have h₂ : B.Contains W₂.left := contains_relativeHomRepresenting_of_isAffineHom x z W₂ e₂
  have eT : (⊤_ (Over ((BigFppfOver.toScheme B S hS).obj V))).left ≅
      (BigFppfOver.toScheme B S hS).obj V :=
    (Over.forget ((BigFppfOver.toScheme B S hS).obj V)).mapIso
      (terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal)
  have hT : B.Contains (⊤_ (Over ((BigFppfOver.toScheme B S hS).obj V))).left :=
    (Scheme.size_congr eT).trans_lt V.left.property
  refine (Scheme.size_congr
    (Stacks.Morphisms.relativeIsomObjLeftIso e₁ e₂ e₃ e₄)).trans_lt ?_
  exact Scheme.size_pullback_lt _ _ (B.contains_prod_left W₁ W₂ h₁ h₂) hT

/-- **`Isom_V(Z, X)` is represented by an object of the site over `V`.** For two morphisms `z`
and `x` of the big fppf site of `S` whose underlying morphisms of schemes are finite locally
free, there is an object `I` of the category of schemes over the scheme underlying `V` whose
underlying scheme lies in the site, and whose sections over a test object `T` are the
isomorphisms `Z ×_V T ≅ X ×_V T` over `T`.

This is the form criterion (2) of Stacks 045G asks for, with the isomorphism functor represented
inside the site rather than merely an algebraic space over `S`. -/
theorem exists_contains_isom_representing_prodOverBase {V Zs Xs : BigFppfOver B S hS}
    (z : Zs ⟶ V) (x : Xs ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map z)]
    [Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map x)] :
    ∃ I : Over ((BigFppfOver.toScheme B S hS).obj V), B.Contains I.left ∧
      ∀ T : Over ((BigFppfOver.toScheme B S hS).obj V),
        Nonempty ((T ⟶ I) ≃
          (prodOverBase (Over.mk ((BigFppfOver.toScheme B S hS).map z)) T ≅
            prodOverBase (Over.mk ((BigFppfOver.toScheme B S hS).map x)) T)) := by
  obtain ⟨W₁, W₂, V₁, V₂, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, ⟨e₄⟩⟩ :=
    Stacks.Morphisms.exists_representableBy_four
      ((BigFppfOver.toScheme B S hS).map z) ((BigFppfOver.toScheme B S hS).map x)
  exact ⟨Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄,
    contains_relativeIsomObj_left z x e₁ e₂ e₃ e₄,
    fun T => ⟨Stacks.Morphisms.relativeIsomObjEquivIso e₁ e₂ e₃ e₄ T⟩⟩

end AlgebraicGeometry.Space

end
