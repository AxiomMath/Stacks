module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.TransitionSwap

/-!
# The descended algebra of an affine descent datum along a flat surjection of affines

Let `Q : Sc ⟶ Sa` be a surjective flat morphism of affine schemes and let `(V, φ)` be a descent
datum relative to `Q` — an `AlgebraicGeometry.DescentDatum` — whose structure morphism
`V ⟶ Sc` is affine. The ring-theoretic content of effective descent for such a datum is
already available as `AlgebraicGeometry.exists_descentPushout_of_isPullback`: it produces a
`Γ(Sa)`-algebra `C`, injectively embedded in `Γ(V)`, presenting `Γ(V)` as
`Γ(Sc) ⊗_{Γ(Sa)} C`. That theorem, however, does not take a descent datum as input. It asks for
the datum *presented by its action*: three Cartesian squares naming `V ×_{Sa} Sc`, `Sc ×_{Sa} V`
and `Sc ×_{Sa} (Sc ×_{Sa} V)`, a morphism `s : Sc ×_{Sa} V ⟶ V` identified with the first
component of `φ⁻¹`, and the cocycle identity in the form `l ≫ s = l' ≫ s` for two specific
morphisms out of the triple product. That is the shape in which the proof of Stacks 041Z meets
a datum coming from a Cartesian square of presheaves on a big fppf site, and it is *not* the
shape of a `AlgebraicGeometry.DescentDatum`, whose cocycle condition is a diagram of binary
products in `Over Sa`.

This file supplies the missing passage, so that the descended algebra can be obtained from a
descent datum in the sense of Stacks 023V.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.DescentDatum.transition_inv_left_comp_fst` and
  `AlgebraicGeometry.DescentDatum.transition_inv_left_comp_snd`: **the inverse gluing
  isomorphism, read on generalized points.** The two components of `φ⁻¹` are the action of a
  descent datum and the structure morphism; this is the counterpart for `φ⁻¹` of
  `AlgebraicGeometry.DescentDatum.transition_hom_left_eq`.
* `AlgebraicGeometry.DescentDatum.exists_isPushout_appTop`: **the descended algebra of a
  descent datum.** For a surjective flat morphism `Q : Sc ⟶ Sa` of affine schemes and a descent
  datum relative to `Q` whose structure morphism is affine, there is a `Γ(Sa)`-algebra `C`
  injecting into `Γ(V)` and presenting `Γ(V)` as the pushout of `Γ(Sc) ← Γ(Sa) → C`.

## Implementation notes

*Why the three Cartesian squares cost nothing.* The products that
`AlgebraicGeometry.DescentData` is stated with are binary products in `Over Sa`, and
`CategoryTheory.Over.isPullback_of_binaryFan_isLimit` says that such a product square is a
Cartesian square of the underlying schemes. So `V ×_{Sa} Sc`, `Sc ×_{Sa} V` and the triple
product are taken to be the underlying schemes of `V ⨯ Sc`, `Sc ⨯ V` and `Sc ⨯ (Sc ⨯ V)` in
`Over Sa`, and all three squares are that lemma applied to
`CategoryTheory.Limits.prodIsProd`. No comparison with `CategoryTheory.Limits.pullback` is
needed anywhere, and in particular `AlgebraicGeometry.DescentDatum.transitionPullbackIso` is
not used: the gluing isomorphism is transported to the underlying schemes by the forgetful
functor instead.

*Where the cocycle condition comes from.* The action `s` of the consumed theorem is the first
component of `φ⁻¹`, whereas `AlgebraicGeometry.DescentDatum.act` is the second component of
`φ`. The two are the same operation with its arguments swapped, which is
`AlgebraicGeometry.DescentDatum.swapTransitionHom_eq_inv` — the identity `σ^*φ = φ⁻¹`, already
available — and that is the content of `transition_inv_left_comp_fst`. With `s` identified with
`act` in this way, the cocycle identity `l ≫ s = l' ≫ s` becomes `(v · x₂) · x₁ = v · x₁`,
which is `AlgebraicGeometry.DescentDatum.act_act` verbatim. Nothing has to be proved about
triple products: the two morphisms `l` and `l'` out of `Sc ⨯ (Sc ⨯ V)` are
`CategoryTheory.Limits.prod.lift`s, and their four defining equations are
`CategoryTheory.Limits.prod.lift_fst` and `CategoryTheory.Limits.prod.lift_snd` read through
the forgetful functor.

*How this sits inside Stacks 0245.* Two further passages separate the descended algebra from
the tag. Effectivity of the datum — that it is isomorphic to a canonical one,
`AlgebraicGeometry.DescentData.IsEffective` — reads the pushout of rings back as an isomorphism
of *descent data*, producing the descended scheme `Spec C` together with the identification of
the gluing isomorphism of its canonical datum with `φ`; the invariance of `C` under the action,
which is the third conclusion of
`AlgebraicGeometry.exists_descentPushout_of_isPullback` and is passed over here, is what that
identification consumes, and the passage itself is
`AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_surjective_of_flat` in
`StacksFrontier.AlgebraicGeometry.Descent.AffineStandardFpqcDescent`. Stacks 0245 then speaks of
an arbitrary fpqc covering of an arbitrary scheme, and the reduction of that to a single
surjective flat morphism of affines is Stacks 02W3.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentDatum

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **The `V`-component of the inverse gluing isomorphism is the action.** For a descent datum
`(V, φ)` relative to `f : X ⟶ S`, the first component of `φ⁻¹ : X ×_S V ⟶ V ×_S X` sends a pair
`(x, v)` to `v · x`. This is `AlgebraicGeometry.DescentDatum.swapTransitionHom_eq_inv` read on
generalized points. -/
lemma transition_inv_left_comp_fst :
    D.transition.inv.left ≫ (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _) =
      D.act prod.snd prod.fst := by
  rw [← D.swapTransitionHom_eq_inv]
  simp [swapTransitionHom, act, gluingAction, prod.braiding_hom]

/-- **The `X`-component of the inverse gluing isomorphism is the structure morphism.** The
second component of `φ⁻¹ : X ×_S V ⟶ V ×_S X` sends a pair `(x, v)` to the point of `X` under
`v`. This is the statement that `φ⁻¹` lies over `X ×_S X`. -/
lemma transition_inv_left_comp_snd :
    D.transition.inv.left ≫ (prod.snd : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _) =
      prod.snd ≫ structureMap f D.over := by
  have h := congrArg (fun g ↦ g ≫ (prod.snd : Over.mk f ⨯ Over.mk f ⟶ Over.mk f))
    (Over.w D.transition.inv)
  simpa using h

variable {Sa Sc : Scheme.{u}} [IsAffine Sa] [IsAffine Sc] {Q : Sc ⟶ Sa}

/-- The product of two objects of `Over S` is a Cartesian square of the underlying schemes. -/
private theorem isPullback_prod_left {S : Scheme.{u}} (A B : Over S) :
    IsPullback (prod.fst : A ⨯ B ⟶ A).left (prod.snd : A ⨯ B ⟶ B).left A.hom B.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd A B)

/-- **The descended algebra of an affine descent datum along a flat surjection of affines.**
Let `Q : Sc ⟶ Sa` be a surjective flat morphism of affine schemes and let `(V, φ)` be a descent
datum relative to `Q` whose structure morphism `V ⟶ Sc` is affine. Then there is a ring `C`
under `Γ(Sa)`, injecting into `Γ(V)`, such that `Γ(V)` is the pushout of `Γ(Sc) ← Γ(Sa) → C`.

This is the ring-theoretic content of Stacks 0245 for a single chart, obtained from a descent
datum in the sense of Stacks 023V. The statement proved is
`AlgebraicGeometry.exists_descentPushout_of_isPullback`; what is done here is to produce its
input — the three Cartesian squares, the action and the cocycle identity — from the descent
datum. -/
theorem exists_isPushout_appTop (hQs : Surjective Q) (hQf : Flat Q) (D : DescentDatum Q)
    [IsAffineHom D.over.hom] :
    ∃ (C : CommRingCat.{u}) (k : Γ(Sa, ⊤) ⟶ C) (p : C ⟶ Γ(D.over.left, ⊤)),
      Function.Injective p.hom ∧ IsPushout Q.appTop k D.over.hom.appTop p := by
  have : IsAffine D.over.left := isAffine_of_isAffineHom D.over.hom
  set A : Over Sa := (Over.map Q).obj D.over with hA
  set Xo : Over Sa := Over.mk Q with hXo
  have sq₁ : IsPullback (prod.fst : A ⨯ Xo ⟶ A).left (prod.snd : A ⨯ Xo ⟶ Xo).left
      (D.over.hom ≫ Q) Q := isPullback_prod_left A Xo
  have sq₂ : IsPullback (prod.fst : Xo ⨯ A ⟶ Xo).left (prod.snd : Xo ⨯ A ⟶ A).left
      Q (D.over.hom ≫ Q) := isPullback_prod_left Xo A
  have sq₃ : IsPullback (prod.fst : Xo ⨯ (Xo ⨯ A) ⟶ Xo).left
      (prod.snd : Xo ⨯ (Xo ⨯ A) ⟶ Xo ⨯ A).left Q
      ((prod.fst : Xo ⨯ A ⟶ Xo).left ≫ Q) := by
    have h := isPullback_prod_left Xo (Xo ⨯ A)
    rwa [← Over.w (prod.fst : Xo ⨯ A ⟶ Xo)] at h
  have hcoc : (prod.lift prod.fst (prod.snd ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst) :
        Xo ⨯ (Xo ⨯ A) ⟶ Xo ⨯ A) ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst =
      (prod.lift prod.fst (prod.snd ≫ (prod.snd : Xo ⨯ A ⟶ A)) :
        Xo ⨯ (Xo ⨯ A) ⟶ Xo ⨯ A) ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst := by
    simp [act_act]
  obtain ⟨C, k, p, hinj, -, hpush⟩ :=
    exists_descentPushout_of_isPullback (Sv := D.over.left) (w := D.over.hom) hQs hQf sq₁ sq₂ sq₃
      (s := (D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst).left)
      (φ := (Over.forget Sa).mapIso (D.gluingIso () ()))
      (l := (prod.lift prod.fst (prod.snd ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst) :
        Xo ⨯ (Xo ⨯ A) ⟶ Xo ⨯ A).left)
      (l' := (prod.lift prod.fst (prod.snd ≫ (prod.snd : Xo ⨯ A ⟶ A)) :
        Xo ⨯ (Xo ⨯ A) ⟶ Xo ⨯ A).left)
      (congrArg Over.Hom.left (D.act_comp_structureMap (prod.snd : Xo ⨯ A ⟶ A) prod.fst))
      (congrArg Over.Hom.left D.transition_inv_left_comp_fst)
      (congrArg Over.Hom.left D.transition_inv_left_comp_snd)
      (congrArg Over.Hom.left (prod.lift_fst (prod.fst : Xo ⨯ (Xo ⨯ A) ⟶ Xo)
        (prod.snd ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst)))
      (congrArg Over.Hom.left (prod.lift_snd (prod.fst : Xo ⨯ (Xo ⨯ A) ⟶ Xo)
        (prod.snd ≫ D.act (prod.snd : Xo ⨯ A ⟶ A) prod.fst)))
      (congrArg Over.Hom.left (prod.lift_fst (prod.fst : Xo ⨯ (Xo ⨯ A) ⟶ Xo)
        (prod.snd ≫ (prod.snd : Xo ⨯ A ⟶ A))))
      (congrArg Over.Hom.left (prod.lift_snd (prod.fst : Xo ⨯ (Xo ⨯ A) ⟶ Xo)
        (prod.snd ≫ (prod.snd : Xo ⨯ A ⟶ A))))
      (congrArg Over.Hom.left hcoc)
  exact ⟨C, k, p, hinj, hpush⟩

end AlgebraicGeometry.DescentDatum
