module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty

/-!
# Base change of a relative property of a representable 1-morphism (Stacks 045C)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S` which is stable under base change and local on the target for the fppf
precoverage. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` which is representable by algebraic spaces and has `P` relatively, in the sense of
Stacks 03YK. Stacks 045C says that in a 2-fibre product square over the cospan `(g, f)`, for any
`g : 𝒵 ⟶ 𝒴`, the projection to `𝒵` again has `P` relatively.

The proof is formal, and is the relative-property half of the argument that proves Stacks 0302.
Fix a scheme `U` over `S` and a scheme-valued point `z` of `𝒵` over the big fppf site of `U`.
Writing `R` for the apex of the given square and `Q = 𝒵 ×_𝒴 𝒳` for the canonical 2-fibre product
(`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`), which is a 2-fibre product of the
same cospan, the comparison 1-morphisms between `R` and `Q` supplied by terminality give an
equivalence `U ×_𝒵 R ≃ U ×_𝒵 Q` over the site of `U`
(`CategoryTheory.TwoFibreProductOver.mapSndEquivalenceOver`), and cancelling the middle factor
gives `U ×_𝒵 (𝒵 ×_𝒴 𝒳) ≃ U ×_𝒴 X`
(`CategoryTheory.TwoFibreProductOver.cancelMiddleEquivalenceOver`). The composite is
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`. So an algebraic space representing
the base change of the projection along `z` also represents the base change of `f` along
`z ⋙ g`, and the relative property of `f` applies to it verbatim: the two instances of Stacks
03YK have *the same*
conclusion `P (algebraicSpaceMap …)` for the same algebraic space, so no transport of `P` along
the equivalence is needed, and in particular neither hypothesis on `P` is used.

## Main results

* `AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`: the base change of a 2-fibre
  product square along a scheme-valued point of its first factor is equivalent, over the site of
  that scheme, to the base change of the cospan's second leg.
* `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`: **Stacks 045C**.

## Implementation notes

The universes are those of `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`
(Stacks 0302), whose conclusion is the representability witness that the statement of Stacks 045C
has to feed to `AlgebraicGeometry.Stack.HasRelativeProperty`: the three categories fibred in
groupoids have morphism universe `max u v` and object universe `max (max (u + 1) w) v` for the
site's universe `u` and arbitrary `v`, `w`, so that both are closed under the operations the
canonical 2-fibre product performs. The statement of Stacks 045C could be read at the unconstrained
`CatFiberedInGroupoids.{u, v, u + 1, w}`, but that universe assignment is defective for
Stacks 0302; this module follows the corrected one.

`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` is the construction performed inline
in the proof of Stacks 0302; that proof carries its own copy, which
should be replaced by an application of this lemma. It is stated as an inhabitation rather than as
a bare equivalence because the comparison 1-morphisms are extracted from the terminality of the
two apexes through `Quotient.exact`, which is an existential statement in `Prop`; both consumers
need only the inhabitation.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

/-- The base change of a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of
categories fibred in groupoids along a scheme-valued point `z` of `𝒵` is equivalent, over the big
fppf site of that scheme, to the base change of `f` along `z ⋙ g`.

This identifies `U ×_𝒵 (𝒵 ×_𝒴 𝒳)` with `U ×_𝒴 𝒳`, after replacing the given apex by the canonical
2-fibre product using terminality. -/
theorem nonempty_baseChangeEquivalenceOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f)
    (hR : Bicategory.IsTwoFibreProduct R)
    (U : BigFppfOver B S hS)
    (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
    (hz : z ⋙ 𝒵.val.p = Over.map U.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) R.pt.val.p 𝒵.val.p z R.fst.hom.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p (z ⋙ g.hom.toFunctor)
        f.hom.toFunctor)) := by
  let Q : Bicategory.TwoCommSq g f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, w} g f
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, v, u + 1, w} g f
  let a : Bicategory.TwoCommSq.PreHom R Q := Quotient.out (hQ.from R)
  let b : Bicategory.TwoCommSq.PreHom Q R := Quotient.out (hR.from Q)
  obtain ⟨e₁, h11, -⟩ :=
    Quotient.exact (hR.hom_ext (Quotient.mk _ (a.comp b)) (𝟙 R))
  obtain ⟨e₂, h21, -⟩ :=
    Quotient.exact (hQ.hom_ext (Quotient.mk _ (b.comp a)) (𝟙 Q))
  have hcomp₁ : ∀ x, ((CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app x ≫
      (CatFiberedInGroupoids.underlyingIso b.isoFst).hom.app (a.hom.hom.toFunctor.obj x)) ≫
      R.fst.hom.toFunctor.map
        ((CatFiberedInGroupoids.underlyingIso e₁).hom.app x) = 𝟙 _ := fun x =>
    cancel_inner_id (a.isoFst.hom.hom.toNatTrans.app x)
      (b.isoFst.hom.hom.toNatTrans.app (a.hom.hom.toFunctor.obj x))
      (R.fst.hom.toFunctor.map (e₁.hom.hom.toNatTrans.app x))
      (congrArg (fun t => t.hom.toNatTrans.app x) h11)
  have hcomp₂ : ∀ x, ((CatFiberedInGroupoids.underlyingIso b.isoFst).hom.app x ≫
      (CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app (b.hom.hom.toFunctor.obj x)) ≫
      Q.fst.hom.toFunctor.map
        ((CatFiberedInGroupoids.underlyingIso e₂).hom.app x) = 𝟙 _ := fun x =>
    cancel_inner_id (b.isoFst.hom.hom.toNatTrans.app x)
      (a.isoFst.hom.hom.toNatTrans.app (b.hom.hom.toFunctor.obj x))
      (Q.fst.hom.toFunctor.map (e₂.hom.hom.toNatTrans.app x))
      (congrArg (fun t => t.hom.toNatTrans.app x) h21)
  have E1 : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) R.pt.val.p 𝒵.val.p z R.fst.hom.toFunctor)
      (TwoFibreProductOver.fst (Over.map U.hom) Q.pt.val.p 𝒵.val.p z Q.fst.hom.toFunctor) :=
    TwoFibreProductOver.mapSndEquivalenceOver (Over.map U.hom) R.pt.val.p Q.pt.val.p
      𝒵.val.p z R.fst.hom.toFunctor Q.fst.hom.toFunctor a.hom.hom.toFunctor a.hom.hom.w
      (CatFiberedInGroupoids.underlyingIso a.isoFst) (fun x => a.isoFst.hom.hom.isHomLift' x)
      b.hom.hom.toFunctor b.hom.hom.w (CatFiberedInGroupoids.underlyingIso b.isoFst)
      (fun x => b.isoFst.hom.hom.isHomLift' x)
      (CatFiberedInGroupoids.underlyingIso e₁) (CatFiberedInGroupoids.underlyingIso e₂)
      (fun x => e₁.hom.hom.isHomLift' x) (fun x => e₂.hom.hom.isHomLift' x) hcomp₁ hcomp₂
  exact ⟨E1.trans <| TwoFibreProductOver.cancelMiddleEquivalenceOver (Over.map U.hom) 𝒳.val.p
    𝒴.val.p 𝒵.val.p z f.hom.toFunctor g.hom.toFunctor hz g.hom.w⟩

/-- **Stacks 045C.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change and local on the target for the fppf precoverage. In a 2-fibre product
square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf site of `S`, the projection to `𝒵` has the relative property `P` of Stacks 03YK as soon as
`f` does. -/
@[stacks 045C]
theorem hasRelativeProperty_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f)
    (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : HasRelativeProperty B S hS P f hf) :
    HasRelativeProperty B S hS P R.fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR hf) := by
  intro U z hz F hF he
  refine hPf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

end AlgebraicGeometry.Stack

end
