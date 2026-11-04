module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartPresieves
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward

/-!
# Faithfulness of the direct-image functor of Stacks 081V

Let `X` be an algebraic space over a scheme `S` of a big fppf site.  Stacks 081V asserts an
anti-equivalence between the algebraic spaces affine over `X` and the quasi-coherent sheaves of
commutative `𝒪_X`-algebras, sending `f : Y ⟶ X` to `f_* 𝒪_Y`.  This file proves the content of
the *faithfulness* half of that assertion.

By `AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor_iff` (in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence`, which this file does
not import) faithfulness of the direct-image functor is injectivity of
`AlgebraicGeometry.Space.pushforwardRingMap` on the morphisms of `CategoryTheory.Over X` between
objects affine over `X`, and that injectivity is what is proved here.  The functor-level statement
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor` is drawn from it in
`StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFunctorFullyFaithful`.

## Main results

* `AlgebraicGeometry.Space.hom_ext_of_affineChartBaseChange`: **the descent step.**  A morphism
  from an algebraic space `Y` representable over `X` to a sheaf is determined by its
  restrictions along the cartesian projections `Y ×_X V ⟶ Y` at the *affine* étale charts `V`
  of `X`.
* `AlgebraicGeometry.Space.smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq`: **the affine
  step.**  Two morphisms over `X` between objects affine over `X` with the same direct-image map
  have the same base change to every affine étale chart of `X`.
* `AlgebraicGeometry.Space.eq_of_pushforwardRingMap_eq`: **the two steps composed**, which is
  the right-hand side of `faithful_affinePushforwardAlgebraFunctor_iff`.

## Implementation notes

The argument is the one the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence` record, and it is the
scheme-level proof `Stacks.AffineAlgebraEquivalence.left_eq_of_pushforwardAlgebraMap_eq` run over
étale charts instead of affine opens.  Its three inputs are:

* the chart value of the direct-image map is pullback of regular functions along the base-changed
  morphism of schemes `Y ×_X V ⟶ Z ×_X V`, by
  `AlgebraicGeometry.Space.pushforwardRingMap_app_eq`.  Equal direct-image maps therefore have
  equal `AlgebraicGeometry.Scheme.Hom.appTop` there;
* over an *affine* chart `V` the base change `Z ×_X V` of the **target** is an affine scheme, by
  `AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`, so `AlgebraicGeometry.ext_of_isAffine`
  identifies the two morphisms of schemes.  It is affineness of the *target* that the
  extensionality asks for, which is why affineness of `Y` is never used below — matching
  `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`, which asks it of the target only;
* `AlgebraicGeometry.BigFppfOver.toScheme` is faithful, so the two base-changed morphisms of the
  site agree, and `AlgebraicGeometry.Space.yoneda_map_smallBaseChangeOverMap_fst` turns that into
  agreement of the two morphisms after the cartesian projection `Y ×_X V ⟶ Y`.

What is left is descent from the affine charts, and the affine charts of `X` only *cover*: no
affine surjective chart is available, the surjective chart of
`AlgebraicGeometry.Space.exists_isSurjective_chart` not being affine.  So the single-atlas
cancellation `AlgebraicGeometry.Space.hom_ext_of_etale_atlas` does not apply and the covering has
to be used as a covering.  The one that serves is
`AlgebraicGeometry.Space.generate_affineChartPresieve_mem`: a point of `X` with values in any
object `T` of the big fppf site factors, locally on `T` for the fppf topology and over affine
objects, through an *affine* étale chart of `X`.  Pulling a point of `Y` back to such an object
and pairing it with that factorization gives, by the universal property of `Y ×_X V`, a
factorization of the point of `Y` through the cartesian projection, where the two morphisms are
assumed to agree; separatedness of the target finishes.

`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj` is consumed at the spelling
`CategoryTheory.Functor.relativelyRepresentable.pullback`, which is the one
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` produces, rather than at the étale chart
`(smallBaseChange …).obj V` of its own statement; the two agree by unfolding
`AlgebraicGeometry.Space.smallBaseChange`, and the `have` below is stated at the former so that
no term of the proof carries the latter.

**What is delivered for Stacks 081V.**  Faithfulness is one half of the anti-equivalence clause
of the tag; fullness is `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFunctorFullyFaithful`, and neither
the tag's essential surjectivity nor its base-change assertion is proved by these files;
`AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence` remains a hypothesis.  Clause (a)
of `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective` asks
that `f ↦ f_*` be *bijective*, and it is its injectivity that is delivered here.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descent along the base changes of the affine charts -/

/-- **A morphism out of an algebraic space representable over `X` is determined by its
restrictions to the base changes of the affine étale charts of `X`.**

Let `Y` be an algebraic space over `X` whose structure morphism is representable, and let `W` be
a sheaf on the big fppf site.  Two morphisms `Y ⟶ W` agreeing after each cartesian projection
`Y ×_X V ⟶ Y`, for `V` an étale chart of `X` whose underlying scheme is affine, are equal.

A point of `Y` with values in an object `T` of the site has an image point of `X`, which by
`AlgebraicGeometry.Space.generate_affineChartPresieve_mem` factors, on a covering sieve of `T`
and over affine objects, through an affine étale chart `V` of `X`.  Over such an object the point
of `Y` and that factorization are a cone on the cartesian square, so the point factors through
`Y ×_X V ⟶ Y`, where the two morphisms agree by hypothesis; `W` being a sheaf, agreement on a
covering sieve is agreement. -/
theorem hom_ext_of_affineChartBaseChange {X : AlgebraicSpaces B S hS} (Y : Over X)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W) {a b : Y.left.1 ⟶ W}
    (hab : ∀ V : SmallEtale B S hS X.1,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) →
        hY.fst V.obj.hom ≫ a = hY.fst V.obj.hom ≫ b) :
    a = b := by
  have hWt : Presieve.IsSheaf (BigFppfOver.topology B S hS) W :=
    (isSheaf_iff_isSheaf_of_type _ W).mp hW
  ext ⟨T⟩ x
  refine (hWt _ (generate_affineChartPresieve_mem B S hS X
    (Y.hom.hom.app (op T) x))).isSeparatedFor.ext ?_
  rintro T' f ⟨Z, p, q, ⟨-, V, hV, g, hgfac⟩, rfl⟩
  -- The point of `Y` restricted to `Z`, and its factorization through `Y ×_X V`.
  have hnat : Y.hom.hom.app (op Z) (Y.left.1.map q.op x) =
      X.1.map q.op (Y.hom.hom.app (op T) x) :=
    NatTrans.naturality_apply Y.hom.hom q.op x
  have hcone : yonedaEquiv.symm (Y.left.1.map q.op x) ≫ Y.hom.hom =
      yoneda.map g ≫ V.obj.hom := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, hnat, hgfac, yonedaEquiv_naturality]
  have hfac : yoneda.map (hY.lift _ g hcone) ≫ hY.fst V.obj.hom =
      yonedaEquiv.symm (Y.left.1.map q.op x) :=
    hY.lift_fst _ _ hcone
  have hpt : yonedaEquiv.symm (Y.left.1.map q.op x) ≫ a =
      yonedaEquiv.symm (Y.left.1.map q.op x) ≫ b := by
    rw [← hfac, Category.assoc, Category.assoc, hab V hV]
  -- Transport that agreement back to the section `x` restricted along `q`, then along `p`.
  have hsec : a.app (op Z) (Y.left.1.map q.op x) = b.app (op Z) (Y.left.1.map q.op x) := by
    have h := congrArg yonedaEquiv hpt
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  have hq : W.map q.op (a.app (op T) x) = W.map q.op (b.app (op T) x) :=
    ((NatTrans.naturality_apply a q.op x).symm.trans hsec).trans
      (NatTrans.naturality_apply b q.op x)
  rw [op_comp, W.map_comp, types_comp_apply, types_comp_apply]
  exact congrArg _ hq

/-! ### The affine step -/

/-- **Two morphisms over `X` with the same direct-image map induce the same map on the regular
functions of the base-changed schemes, at every étale chart of `X`.**

By `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` both sides are the component at `V` of the
direct-image map read through `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at source
and target, so the equality is that reading conjugated by the hypothesis.  No affineness and no
chart condition is used.

This is a separate statement from
`AlgebraicGeometry.Space.smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq` below only because
of the heartbeat budget: the two instances of
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq` are long terms, and elaborating them together
with the affineness of the base-changed target in one declaration exhausts it, the budget being
cumulative over a declaration's elaboration. -/
theorem appTop_smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq
    {X : AlgebraicSpaces B S hS} {Y Z : Over X} (f g : Y ⟶ Z)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (e : pushforwardRingMap B S hS f = pushforwardRingMap B S hS g)
    (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS f hY hZ V)).appTop =
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS g hY hZ V)).appTop := by
  have hf := pushforwardRingMap_app_eq B S hS f hY hZ V
  rw [e] at hf
  exact hf.symm.trans (pushforwardRingMap_app_eq B S hS g hY hZ V)

/-- **Two morphisms over `X` between objects affine over `X` with the same direct-image map have
the same base change to every affine étale chart of `X`.**

At an affine chart the *target* `Z ×_X V` is an affine scheme, by
`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`, so the equality of
`AlgebraicGeometry.Space.appTop_smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq` is enough for
`AlgebraicGeometry.ext_of_isAffine` to identify the two morphisms of schemes, and
`AlgebraicGeometry.BigFppfOver.toScheme` being faithful identifies the two morphisms of the
site.  Affineness of the source `Y` is not used. -/
theorem smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq {X : AlgebraicSpaces B S hS}
    {Y : Over X} (Z : AffineOver B S hS X) (f g : Y ⟶ Z.obj)
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.obj.hom.hom)
    (e : pushforwardRingMap B S hS f = pushforwardRingMap B S hS g)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffineOver B S hS ((SmallEtale.toOver B S hS X.1).obj V)) :
    smallBaseChangeOverMap B S hS f hY hZ V = smallBaseChangeOverMap B S hS g hY hZ V := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hZ.pullback V.obj.hom)) :=
    isAffine_smallBaseChange_obj B S hS Z.obj.hom hZ Z.property V hV
  exact (BigFppfOver.toScheme B S hS).map_injective (AlgebraicGeometry.ext_of_isAffine
    (appTop_smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq B S hS f g hY hZ e V))

/-! ### Faithfulness -/

/-- **The direct-image map of Stacks 081V is injective on the morphisms over `X` between objects
affine over `X`.**

This is the right-hand side of
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor_iff`, and the two steps above
composed: the two morphisms have the same base change to every affine étale chart of `X`, by
`AlgebraicGeometry.Space.smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq`; by
`AlgebraicGeometry.Space.yoneda_map_smallBaseChangeOverMap_fst` they therefore agree after each
cartesian projection `Y ×_X V ⟶ Y`; and the affine charts of `X` suffice to descend that, by
`AlgebraicGeometry.Space.hom_ext_of_affineChartBaseChange`.

Affineness of the source `Y` is used only to know that its structure morphism is representable,
which is what makes `Y ×_X V` a scheme; affineness of it as a *scheme* is never needed. -/
theorem eq_of_pushforwardRingMap_eq {X : AlgebraicSpaces B S hS} (Y Z : AffineOver B S hS X)
    (f g : Y.obj ⟶ Z.obj)
    (e : pushforwardRingMap B S hS f = pushforwardRingMap B S hS g) : f = g := by
  have hY : yoneda.relativelyRepresentable Y.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS Y.obj.hom Y.property
  have hZ : yoneda.relativelyRepresentable Z.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS Z.obj.hom Z.property
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  refine hom_ext_of_affineChartBaseChange B S hS Y.obj hY Z.obj.left.property.isSheaf ?_
  intro V hV
  refine (yoneda_map_smallBaseChangeOverMap_fst B S hS f hY hZ V).symm.trans ?_
  refine Eq.trans ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ V)
  exact congrArg (fun m => yoneda.map m ≫ hZ.fst V.obj.hom)
    (smallBaseChangeOverMap_eq_of_pushforwardRingMap_eq B S hS Z f g hY hZ e V hV)

end AlgebraicGeometry.Space

end
