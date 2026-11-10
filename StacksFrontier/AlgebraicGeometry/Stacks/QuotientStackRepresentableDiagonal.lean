module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable

/-!
# The diagonal of a quotient stack is representable

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `[U/R]` be its quotient stack (**Stacks 044Q**). Stacks
04WZ says that the diagonal of `[U/R]` is representable by algebraic spaces, and its proof is a
one-step reduction: the diagonal criterion of **Stacks 045G** identifies representability of the
diagonal with algebraicity of every isomorphism sheaf `Isom(x, y)` of a fibre, and for a quotient
stack that algebraicity is **Stacks 04TB**.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_pointwiseEquiv`: condition (2) of
  Stacks 045G from a pointwise natural bijection between the isomorphism sheaf and a small
  algebraic-space presheaf.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic`:
  the reduction of **Stacks 04WZ** to **Stacks 04TB**.
* `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom_of_isomPresheafAlgebraic`:
  what that buys — the projection of Stacks 044R is representable by algebraic spaces on the
  strength of Stacks 04TB alone.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack`: **Stacks 04WZ**.
* `AlgebraicGeometry.Stack.representable_quotientStackProjectionHom`: the projection of
  Stacks 044R is representable by algebraic spaces.

## Implementation notes

Condition (2) of Stacks 045G,
`AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`, compares the isomorphism sheaf with the
representing presheaf *after universe lifts on both sides*, because the fibre morphisms of a
category fibred in groupoids over the site may live in any universe while an algebraic space is a
presheaf of `Type u`. A source statement asserting that `Isom(x, y)` "is" an algebraic space
produces instead a bijection `Isom(x, y)(V) ≃ F(V)` for each `V`, natural in `V`, with no `ULift`
anywhere — that is all a quotient stack supplies, since the hom sets of a stackification are not
small. The first result below is the passage between the two packagings: the pointwise bijections
are assembled by `CategoryTheory.NatIso.ofComponents` after `ULift.up`/`ULift.down`, and the
naturality square is the given naturality transported along the injectivity of one bijection. It is
stated for an arbitrary category fibred in groupoids over the site, not just for a quotient stack,
because nothing about the quotient enters it.

The second result is the first composed with
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`, the
equivalence of conditions (1) and (2) of Stacks 045G.

The quotient stack appears as `CategoryTheory.CatFiberedInGroupoids.mk (quotientStack G) …`, the
same spelling `AlgebraicGeometry.Stack.quotientStackProjectionHom` uses for the target of the
projection, so that the two meet without a comparison.

The third result composes the second with the implication (1) ⟹ (7) of Stacks 045G,
`AlgebraicGeometry.Stack.representable_quotientStackProjection_of_hasRepresentableDiagonal`, and
with the transport of representability along the universe lift of the object space,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackProjectionHom`. It is the
hypothesis `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_baseChange`
(Stacks 045D) and `AlgebraicGeometry.Stack.hasRelativeProperty_comp` (Stacks 045B) call `hf`; with
it, the only hypothesis either of those still wants about the projection is the single base change.

The last two results discharge the Stacks 04TB input of the first three by
`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, and the first of them carries
`@[stacks 04WZ]`.

No `@[stacks]` attribute is placed on the first three declarations, which carry the Stacks 04TB
input as a hypothesis. The first of them is a repackaging of condition (2) of Stacks 045G, whose
parts (1) and (2) already carry their site on
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Condition (2) of **Stacks 045G** holds as soon as every isomorphism sheaf of a fibre admits a
pointwise bijection, natural in the slice, with a presheaf of `Type u` which is an algebraic
space.

The conclusion compares the two presheaves after a universe lift on each side; the hypothesis is
the `ULift`-free form a source statement produces. -/
theorem isAlgebraicSpaceIsomPresheaf_of_pointwiseEquiv
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U),
        ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
          IsAlgebraicSpace B U.left.1 U.left.2 F ∧
            ∃ e : ∀ V, ((Over.iteratedSliceBackward U).op ⋙
                𝒳.val.p.isomPresheaf x y).obj V ≃ F.obj V,
              ∀ ⦃V W⦄ (f : V ⟶ W) (z : ((Over.iteratedSliceBackward U).op ⋙
                  𝒳.val.p.isomPresheaf x y).obj V),
                e W (((Over.iteratedSliceBackward U).op ⋙
                  𝒳.val.p.isomPresheaf x y).map f z) = F.map f (e V z)) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro U x y
  obtain ⟨F, hF, e, he⟩ := h U x y
  refine ⟨F, hF, ⟨NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun z => ULift.up ((e V).symm z.down)
      invFun := fun z => ULift.up (e V z.down)
      left_inv := by intro z; cases z; simp; rfl
      right_inv := by intro z; cases z; simp; rfl }) ?_⟩⟩
  intro V W f
  ext z
  change ULift.up ((e W).symm ((F.map f) z.down)) =
    ULift.up (((Over.iteratedSliceBackward U).op ⋙
      𝒳.val.p.isomPresheaf x y).map f ((e V).symm z.down))
  congr 1
  apply (e W).injective
  simpa using (he f ((e V).symm z.down)).symm

section Quotient

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- **Stacks 04WZ, reduced to Stacks 04TB.** The diagonal of the quotient stack of a groupoid in
algebraic spaces is representable by algebraic spaces, provided every isomorphism sheaf of a fibre
of the quotient stack is an algebraic space over the scheme the fibre sits over.

The hypothesis is the conclusion of **Stacks 04TB**, in the `ULift`-free shape that statement has:
a presheaf of `Type u` which is an algebraic space, together with a bijection with the isomorphism
sheaf over each object of the slice site, natural in that object. -/
theorem hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (h : ∀ (T : BigFppfOver C S hS) (x y : (quotientStack G).p.Fiber T),
      ∃ F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace C T.left.1 T.left.2 F ∧
          ∃ e : ∀ U, ((Over.iteratedSliceBackward T).op ⋙
              (quotientStack G).p.isomPresheaf x y).obj U ≃ F.obj U,
            ∀ ⦃U V⦄ (f : U ⟶ V) (z : ((Over.iteratedSliceBackward T).op ⋙
                (quotientStack G).p.isomPresheaf x y).obj U),
              e V (((Over.iteratedSliceBackward T).op ⋙
                (quotientStack G).p.isomPresheaf x y).map f z) = F.map f (e U z)) :
    HasRepresentableDiagonal C S hS
      (CatFiberedInGroupoids.mk (quotientStack G)
        (isFiberedInGroupoids_quotientStack G)) :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf C S hS _).mpr
    (isAlgebraicSpaceIsomPresheaf_of_pointwiseEquiv C S hS _ h)

/-- The canonical projection `S_U ⟶ [U/R]` of **Stacks 044R** is representable by algebraic
spaces, provided every isomorphism sheaf of a fibre of the quotient stack is an algebraic space
over the scheme the fibre sits over.

The 1-morphism is `AlgebraicGeometry.Stack.quotientStackProjectionHom`, the form in which the
relative-property results of Stacks 045B and 045D take their 1-morphism, so this is the
representability hypothesis those results ask for, resting on **Stacks 04TB** alone. -/
theorem representable_quotientStackProjectionHom_of_isomPresheafAlgebraic
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (h : ∀ (T : BigFppfOver C S hS) (x y : (quotientStack G).p.Fiber T),
      ∃ F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace C T.left.1 T.left.2 F ∧
          ∃ e : ∀ U, ((Over.iteratedSliceBackward T).op ⋙
              (quotientStack G).p.isomPresheaf x y).obj U ≃ F.obj U,
            ∀ ⦃U V⦄ (f : U ⟶ V) (z : ((Over.iteratedSliceBackward T).op ⋙
                (quotientStack G).p.isomPresheaf x y).obj U),
              e V (((Over.iteratedSliceBackward T).op ⋙
                (quotientStack G).p.isomPresheaf x y).map f z) = F.map f (e U z)) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom :=
  isRepresentableByAlgebraicSpaces_quotientStackProjectionHom G
    (representable_quotientStackProjection_of_hasRepresentableDiagonal C S hS G
      (hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic G h))

end Quotient


/-- The instance of **Stacks 04S6** part (3) that Stacks 04TB consumes, over every object of the
big fppf site of `S`: a sheaf which receives a representable, surjective, flat, locally finitely
presented morphism from an algebraic space is an algebraic space. -/
abbrev Bootstrap04S6 (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S) : Prop :=
  ∀ (T : BigFppfOver C S hS) (F' : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
    Presheaf.IsSheaf (BigFppfOver.topology C T.left.1 T.left.2) F' →
    ∀ G' : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace C T.left.1 T.left.2 G' →
    ∀ g : G' ⟶ F', yoneda.relativelyRepresentable g →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
          MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C T.left.1 T.left.2))) g →
      IsAlgebraicSpace C T.left.1 T.left.2 F'

/-- **Stacks 04WZ.** The diagonal of the quotient stack of a groupoid in algebraic spaces over a
scheme of a big fppf site is representable by algebraic spaces.

The diagonal criterion of **Stacks 045G** reduces this to algebraicity of every isomorphism sheaf
of a fibre, which is **Stacks 04TB**; that result in turn rests on Stacks 04SK, whose last step is
the bootstrap theorem. -/
@[stacks 04WZ]
theorem hasRepresentableDiagonal_quotientStack
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    HasRepresentableDiagonal C S hS
      (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G)) :=
  hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic G
    (fun T x y => isAlgebraicSpace_isomPresheaf C S hS A G T x y)

/-- The canonical projection `S_U ⟶ [U/R]` of **Stacks 044R** is representable by algebraic
spaces: the diagonal of the quotient stack is (Stacks 04WZ). -/
theorem representable_quotientStackProjectionHom
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom :=
  representable_quotientStackProjectionHom_of_isomPresheafAlgebraic G
    (fun T x y => isAlgebraicSpace_isomPresheaf C S hS A G T x y)

end AlgebraicGeometry.Stack

end
