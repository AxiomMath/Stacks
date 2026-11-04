module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# The slice fibre of an algebraic space over a scheme of the site (Stacks 03I5 (1), 04SG)

Let `V` be a scheme of the big fppf site of `S` and let `q : P ⟶ h_V` be a morphism of presheaves
with `P` an algebraic space over `S`. Reading the fibre of `q` over the tautological section of
`h_V` on the big fppf site of `V` itself — that is,
`(Over.iteratedSliceBackward V).op ⋙ CategoryTheory.OverShriek.fiber (𝟙 h_V) q` — produces an
*algebraic space over `V`*. This is the direction of the equivalence of **Stacks 04SG** that
carries an algebraic space over `S` with a morphism to `V` to an algebraic space over `V`, in the
only form this library can state it: the quasi-inverse functor of that equivalence is not
assembled (see `StacksFrontier/AlgebraicGeometry/Spaces/SmallerBase.lean`), but the value of the
quasi-inverse on an object *is* available, because the slice fibre is a fibre product of three
algebraic spaces over `V`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_iteratedSliceFiber`: the slice fibre of an algebraic space
  over `S` along a morphism to the representable presheaf of a scheme `V` of the site is an
  algebraic space over `V`.

## Implementation notes

The slice fibre `F` sits in a cartesian square

```text
  F ---------------> R P
  |                   |
  |                   | R q
  v                   v
  h_{V/V} ---------> R h_V
```

over the big fppf site of `V`, where `R = CategoryTheory.OverShriek.relocalizeRestrict V.hom` is
restriction along `CategoryTheory.Over.map V.hom` and the bottom arrow is the tautological
section: a section of `F` over `W ⟶ V` is a section of `P` over `W ⟶ V ⟶ S` whose image under
`q` is the structure morphism `W ⟶ V`, which is exactly a section of `R P` over `W` agreeing with
the tautological section of `R h_V`. The two right-hand presheaves are algebraic spaces over `V`
by **Stacks 03I5 part (1)**, `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict`, and
`V / V` is a final object of the big fppf site of `V`, so the fibre product is an algebraic space
by the special case of Stacks 02X2 with a final factor,
`AlgebraicGeometry.isAlgebraicSpace_of_isPullback_isTerminal` — no part of the full Stacks 02X2 is
needed.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The slice fibre of an algebraic space is an algebraic space over the slice base.** For a
scheme `V` of the big fppf site of `S` and a morphism `q : P ⟶ h_V` out of an algebraic space `P`
over `S`, the fibre of `q` over the tautological section of `h_V`, read on the big fppf site of
`V`, is an algebraic space over `V`.

This is the value on an object of the quasi-inverse of the equivalence of **Stacks 04SG**. -/
theorem isAlgebraicSpace_iteratedSliceFiber
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : P ⟶ yoneda.obj V)
    (hP : IsAlgebraicSpace B S hS P) :
    IsAlgebraicSpace B V.left.1 V.left.2
      ((Over.iteratedSliceBackward V).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj V)) q) := by
  let R := OverShriek.relocalizeRestrict V.hom
  let T : BigFppfOver B V.left.1 V.left.2 := Over.mk (𝟙 _)
  let F := (Over.iteratedSliceBackward V).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj V)) q
  let a : yoneda.obj T ⟶ R.obj (yoneda.obj V) :=
    { app := fun W => ↾fun _ => Over.homMk W.unop.hom
      naturality := by
        intro W W' g
        ext z
        apply Over.OverMorphism.ext
        exact (Over.w g.unop).symm }
  let hT : IsTerminal (yoneda.obj T) := IsTerminal.isTerminalObj yoneda T Over.mkIdTerminal
  let b : F ⟶ yoneda.obj T := hT.from F
  let i : F ⟶ R.obj P :=
    { app := fun _ => ↾fun z => z.1
      naturality := by intros; rfl }
  have hi : i ≫ R.map q = b ≫ a := by
    ext W z
    exact z.2
  have hp : IsPullback i b (R.map q) a := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk i b hi)
    refine PullbackCone.IsLimit.mk hi
      (fun s => { app := fun W => ↾fun z => ⟨s.fst.app W z, ?_⟩, naturality := ?_ }) ?_ ?_ ?_
    · exact congrArg (fun k => k.app W z) s.condition
    · intro W W' g
      ext z
      apply Subtype.ext
      exact s.fst.naturality_apply g z
    · intro s
      rfl
    · intro s
      exact hT.hom_ext _ _
    · intro s m hm₁ _
      ext W z
      apply Subtype.ext
      exact congrArg (fun k => k.app W z) hm₁
  exact isAlgebraicSpace_of_isPullback_isTerminal
    (isAlgebraicSpace_relocalizeRestrict B V.left.1 S V.left.2 hS V.hom P hP)
    (isAlgebraicSpace_relocalizeRestrict B V.left.1 S V.left.2 hS V.hom (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V))
    Over.mkIdTerminal hp

end AlgebraicGeometry

end
