module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# Formal properties of morphisms of algebraic spaces

Composition and base change preserve formal smoothness, formal étaleness and formal
unramifiedness of morphisms of algebraic spaces.

## Main results

An algebraic space over a scheme is presented here by its functor of points, and a morphism
of algebraic spaces is a natural transformation of such functors; the formal properties of
such a morphism are the affine square-zero lifting properties of that transformation. That is
what Tag 04GC says, so the statements for transformations of arbitrary set-valued functors on
the big fppf site already give the corresponding statements for morphisms of algebraic spaces,
in greater generality and with no additional algebraic-space hypothesis.

* `AlgebraicGeometry.Space.formallyUnramified_comp`,
  `AlgebraicGeometry.Space.formallyEtale_comp` and
  `AlgebraicGeometry.Space.FormallySmooth.comp` are the composition statements.
* `AlgebraicGeometry.Space.FormallySmooth.baseChange` is the base-change statement for formal
  smoothness.
* `AlgebraicGeometry.Space.FormallyEtale.isoComp`: formal étaleness of a transformation is
  unchanged by precomposition with an isomorphism of its source.
* `AlgebraicGeometry.Space.formallyEtale_of_isPullback` is **Stacks 0613**: a base change of a
  formally étale morphism of algebraic spaces over `S` is formally étale.

## Implementation notes

Base change is the one place where the geometric statement is not merely an instance of the
transformation-level one. Tag 0613 is about a cartesian square in the category of algebraic
spaces over `S`, whereas Tag 049U is about the canonical fibre product of presheaves, and what
separates them is that the fibre product of algebraic spaces is computed in presheaves. That
is `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`, which identifies the top-left corner of
the given square with
`AlgebraicGeometry.Space.FppfFunctorPullbackSituation.fibreProduct`, over which the formally
étale clause of Tag 049U, `AlgebraicGeometry.Space.formallyEtale_baseChange`, applies.
Transporting the conclusion along that identification needs only that formal étaleness is
unchanged by precomposition with an isomorphism, which is
`AlgebraicGeometry.Space.FormallyEtale.isoComp`, the counterpart for unique lifts of
`AlgebraicGeometry.Space.FormallySmooth.isoComp`.

The corresponding statement for morphisms of schemes is Tag 02HJ,
`AlgebraicGeometry.FormallyEtale.pullback_snd`, proved directly from the scheme-level lifting
property `AlgebraicGeometry.FormallyEtale` of Tag 02HG and independent of this file.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049U](https://stacks.math.columbia.edu/tag/049U)
* [Stacks Project, Tag 04GC](https://stacks.math.columbia.edu/tag/04GC)
* [Stacks Project, Tag 05ZZ](https://stacks.math.columbia.edu/tag/05ZZ)
* [Stacks Project, Tag 0612](https://stacks.math.columbia.edu/tag/0612)
* [Stacks Project, Tag 0613](https://stacks.math.columbia.edu/tag/0613)
* [Stacks Project, Tag 061E](https://stacks.math.columbia.edu/tag/061E)
* [Stacks Project, Tag 061F](https://stacks.math.columbia.edu/tag/061F)
-/

add_to_stacks 05ZZ AlgebraicGeometry.Space.formallyUnramified_comp

add_to_stacks 0612 AlgebraicGeometry.Space.formallyEtale_comp

add_to_stacks 061E AlgebraicGeometry.Space.FormallySmooth.comp

add_to_stacks 0613 AlgebraicGeometry.Space.formallyEtale_baseChange

add_to_stacks 061F AlgebraicGeometry.Space.FormallySmooth.baseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- Formal étaleness of a transformation of set-valued functors on the big fppf site of `S` is
unchanged by precomposition with an isomorphism of its source: the unique lift of a square for
the isomorphic source is the image under the isomorphism of the unique lift of the original
square, and back. -/
public theorem FormallyEtale.isoComp {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (e : F' ≅ F) {a : F ⟶ G}
    (ha : FormallyEtale a) : FormallyEtale (e.hom ≫ a) := by
  intro T T' hT hT' i hi x t hxt
  obtain ⟨z, ⟨hz₁, hz₂⟩, hzu⟩ :=
    ha T T' hT hT' i hi (e.hom.app (op T) x) t (by simpa using hxt)
  refine ⟨e.inv.app (op T') z, ⟨?_, ?_⟩, ?_⟩
  · have hn := NatTrans.naturality_apply e.inv i.op z
    rw [hz₁] at hn
    simpa using hn.symm
  · simpa using hz₂
  · rintro w ⟨hw₁, hw₂⟩
    have hwz : e.hom.app (op T') w = z := by
      refine hzu _ ⟨?_, ?_⟩
      · have hn := NatTrans.naturality_apply e.hom i.op w
        rw [hw₁] at hn
        exact hn.symm
      · simpa using hw₂
    rw [← hwz]
    simp

/-- **Stacks 0613.** A base change of a formally étale morphism of algebraic spaces over `S` is
formally étale: if `fst, snd, f, g` is a cartesian square of algebraic spaces over `S` and `f`
is formally étale, then so is `snd`. -/
@[stacks 0613]
public theorem formallyEtale_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z W : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst : W ⟶ X} {snd : W ⟶ Y} (sq : IsPullback fst snd f g)
    (hf : FormallyEtale f.hom) : FormallyEtale snd.hom := by
  let D : FppfFunctorPullbackSituation.{u, u} :=
    { B := B, S := S, hS := hS, F := X.1, G := Z.1, H := Y.1, a := f.hom, b := g.hom }
  have hsq : IsPullback snd.hom fst.hom g.hom f.hom :=
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_hom B S hS sq).flip
  rw [← D.isPullback.isoIsPullback_inv_fst _ _ hsq]
  exact FormallyEtale.isoComp (D.isPullback.isoIsPullback _ _ hsq).symm
    (formallyEtale_baseChange D hf)

end AlgebraicGeometry.Space

end
