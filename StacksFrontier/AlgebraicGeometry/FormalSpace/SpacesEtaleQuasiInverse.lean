module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# The quasi-inverse `U_{V, ψ}` of Stacks 0DEG

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with reduction `X_red`, and let `ψ : V ⟶ X_red` be an object of `X_{spaces, étale}`, that is
an algebraic space étale over `X_red`. Stacks 0DEG identifies `X_{spaces, étale}` with the
category of formal algebraic spaces representable étale over `X`; the comparison functor
`(U ⟶ X) ↦ U ×_X X_red` is built in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleIdentification.lean`, and the quasi-inverse
is the functor

    U_{V, ψ}(T) = {(a, b) | a : T ⟶ X, b : T ×_{a, X} X_red ⟶ V, ψ ∘ b = a|_{T ×_{a,X} X_red}}

which the source writes down. This file constructs it.

The construction is carried out for an arbitrary pair of morphisms of fppf sheaves `i : I ⟶ X`
and `p : W ⟶ I`, the case of Stacks 0DEG being `i = X_red ⟶ X` and `p = ψ`; nothing about
reductions or étaleness is used until the last section. In the language of a topos,
`U_{V, ψ}` is the dependent product (Weil restriction) of `p` along `i`, so what is proved here
is that this dependent product exists in fppf sheaves on the big fppf site and that its counit
is an isomorphism when `i` is injective on sections.

## Main definitions

* `AlgebraicGeometry.FormalSpace.LiftAlong` is a section of `U_{V, ψ}` over an object of the
  site: a section `a` of `X` together with the rule `b`, given on points, with its two
  conditions. Equality of two such is `AlgebraicGeometry.FormalSpace.LiftAlong.ext`, and
  restriction along a morphism of the site is
  `AlgebraicGeometry.FormalSpace.LiftAlong.restrict`.
* `AlgebraicGeometry.FormalSpace.liftAlongPresheaf` and
  `AlgebraicGeometry.FormalSpace.liftAlong` are `U_{V, ψ}` as a presheaf and as an fppf sheaf,
  and `AlgebraicGeometry.FormalSpace.liftAlongBase` is the transformation `U_{V, ψ} ⟶ X`,
  `(a, b) ↦ a`.
* `AlgebraicGeometry.FormalSpace.liftAlongSection` is the comparison `W ⟶ U_{V, ψ}`, defined
  when `i` is injective on sections.
* `AlgebraicGeometry.FormalSpace.spacesEtaleQuasiInverse`,
  `AlgebraicGeometry.FormalSpace.spacesEtaleQuasiInverseBase` and
  `AlgebraicGeometry.FormalSpace.spacesEtaleQuasiInverseSection` are the three of them at the
  inclusion of a reduction, which is the situation of **Stacks 0DEG**.
* `AlgebraicGeometry.FormalSpace.liftAlongId` is the inverse of `U_{I, 𝟙} ⟶ X`: the dependent
  product of the identity of `I` along `i` is `X` itself, the dependent product being a right
  adjoint and so carrying the terminal object of the sheaves over `I` to the terminal object of
  the sheaves over `X` (`AlgebraicGeometry.FormalSpace.isIso_liftAlongBase_id`).
* `AlgebraicGeometry.FormalSpace.liftAlongMap` is the quasi-inverse on morphisms,
  postcomposition on the second component, and
  `AlgebraicGeometry.FormalSpace.spacesEtaleQuasiInverseFunctor` assembles it into the functor
  `X_{spaces, étale} ⥤ Over X` which is what the source produces: "thus we obtain our functor
  `(V, ψ) ↦ (U_{V, ψ} ⟶ X)` in the other direction".

## Main results

* `AlgebraicGeometry.FormalSpace.isSheaf_liftAlongPresheaf`: `U_{V, ψ}` is a sheaf for the fppf
  topology. This is the step the source states as "observe that `U_{V, ψ}` is a sheaf for the
  fppf topology (some details omitted)". The morphism `a` glues because `X` is a sheaf; the
  rule `b` glues because `W` is a sheaf and a covering sieve of `T` pulls back to a covering
  sieve of every object over `T`, the fppf topology being stable under base change.
* `AlgebraicGeometry.FormalSpace.isPullback_liftAlongSection` and its instance
  `AlgebraicGeometry.FormalSpace.isPullback_spacesEtaleQuasiInverseSection`: the square
  exhibiting `W` as the fibre product `U_{V, ψ} ×_X I`. At the inclusion of a reduction this
  says `U_{V, ψ} ×_X X_red = V` over `X_red`, that is: the comparison functor of Stacks 0DEG,
  applied to the quasi-inverse at `(V, ψ)`, returns `(V, ψ)`. This is the half of the source's
  "we omit the verification that the constructions are mutually inverse to each other" that
  does not need the lifting of morphisms along the thickening `X_red ⟶ X`.
* `AlgebraicGeometry.FormalSpace.Reduction.injective_app_inclusion`: the inclusion of a
  reduction is injective on sections, so the two results above apply to it unconditionally.

## What is *not* proved here

Of the two assertions the source makes about `U_{V, ψ}` — that `U_{V, ψ} ⟶ X` is representable
by algebraic spaces and étale ("we omit the verification"), and that `U_{V, ψ}` is a formal
algebraic space — the first is proved, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverseRepresentable.lean`, as
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_spacesEtaleQuasiInverseBase`; it is not in
this file only because its proof needs the base-change invariance of the construction, which
sits above this module in import order. The second is proved too, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/LiftAlongAffineBase.lean`, as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong`: its affine case is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace`
and the reduction to an affine étale chart of `X` is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_affine`, so the comparison
functor of Stacks 0DEG is an equivalence with nothing assumed. The other verification the
source omits, that the comparison functor is bijective on morphisms, is proved — it is
`AlgebraicGeometry.FormalSpace.bijective_spacesEtaleComparison_map`, resting on the sheaf-level
general-thickening case of Stacks 05ZH,
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening`.

* **representable étale**, proved. After base change along a scheme-valued point `T ⟶ X` the
  construction becomes, by
  `AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange`, the dependent product along
  the thickening `T_0 = T ×_X X_red ⟶ T` of schemes of the site, and that dependent product is
  the algebraic space étale over `T` which essential surjectivity in Stacks 05ZH for a general
  thickening — `AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, which
  carries no order hypothesis — lifts out of `V ×_{X_red} T_0`.
* **formal algebraic space**, proved. Being a formal algebraic space means carrying an atlas of
  *affine* formal algebraic spaces, Definition 0AIM, and the source produces one by base
  changing to an affine étale chart `X_i ⟶ X`, where `U_{V, ψ} ×_X X_i = U_{V_i, ψ_i}` — which
  is `AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange` — and appealing to the
  proof of Stacks 0DEE over the affine formal algebraic space `X_i`. That reduction is
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_affine`, and the affine
  case itself is
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace`:
  the atlas of `U_{V_i, ψ_i}` is the family of dependent products of the affine étale charts of
  `V_i` over the stages of a presentation of `X_i`, each of which is an affine formal algebraic
  space by `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit`, the version of
  Stacks 0GVM assuming the set-theoretic condition (Stacks 0GVM itself is
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_iff` and
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_of_cofinal`), applied to
  its own stagewise base changes. The affine étale lift across a thickening of schemes of the site
  (`AlgebraicGeometry.FormalSpace.exists_affine_etale_lift_of_isThickening`, out of Stacks 039R
  and Stacks 06AD) is what makes those base changes affine, and the set-theoretic condition of
  Stacks 0AIS descends to `U_{V, ψ}` from `X` along the representable morphism
  `U_{V, ψ} ⟶ X` by
  `FormalSpace.SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over`.
  Stacks 07VT is *not* an input: the affineness the argument needs is Stacks 06AD,
  `Stacks.Thickenings.isAffine_of_isThickening`.

## Implementation notes

A section of `U_{V, ψ}` over `T` is recorded as a structure rather than as a morphism out of a
fibre product of presheaves, because the fibre product `T ×_{a, X} I` depends on `a` and would
have to be chosen. The rule `b` is therefore a dependent function whose domain mentions the
section `a`, and comparing the rules of two sections needs a congruence lemma that moves the
section, the morphism and the point of `I` at once; that is
`AlgebraicGeometry.FormalSpace.LiftAlong.lift_congr`, with
`AlgebraicGeometry.FormalSpace.LiftAlong.lift_eq_of_eq_restrict` for the case of two sections
over different objects of the site. Every proof below goes through these two, which is what
keeps the proof irrelevance of the compatibility conditions invisible.

The sheaf condition is proved in the `Presieve.FamilyOfElements.SieveCompatible` form rather
than the `Compatible` form: compatibility then involves a single morphism instead of a pair of
them, which halves the bookkeeping.

The cartesian square is produced from `CategoryTheory.Limits.PullbackCone.IsLimit.mk` directly
in the category of fppf sheaves: the lift of a cone is "evaluate the rule `b` at the identity",
so no description of the fibre product of sheaves is needed.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DED](https://stacks.math.columbia.edu/tag/0DED)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X I W : FppfSheaf B S hS}

namespace LiftAlong

variable {B S hS} {i : I ⟶ X} {p : W ⟶ I} {T : BigFppfOver B S hS}

end LiftAlong

/-! ### `U_{V, ψ}` is a sheaf for the fppf topology -/

variable {i : I ⟶ X} {p : W ⟶ I}

/-! ### `U_{V, ψ}` as an fppf sheaf over `X` -/

section Construction

variable (i : I ⟶ X) (p : W ⟶ I)

variable {i p} (hi : ∀ T : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op T)))

section Cone

variable {Z : FppfSheaf B S hS} (a : Z ⟶ liftAlong B S hS i p) (b : Z ⟶ I)
  (hab : a ≫ liftAlongBase B S hS i p = b ≫ i)

end Cone

/-! ### The quasi-inverse at the inclusion of a reduction -/

/-- The inclusion of a reduction is injective on sections: it is a representable thickening,
hence a monomorphism of the underlying presheaves, and a monomorphism of presheaves of types is
injective on sections over every object. This is the hypothesis `hi` under which the
construction above applies to `i = X_red ⟶ X`. -/
theorem Reduction.injective_app_inclusion {X : FppfSheaf B S hS} (R : Reduction B S hS X)
    (T : BigFppfOver B S hS) :
    Function.Injective (R.inclusion.hom.app (Opposite.op T)) :=
  (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
    (mono_of_isRepresentableThickeningULift B S hS
      R.isReduction.isRepresentableThickening) (Opposite.op T))

/-! ### Stacks 0DEG: the quasi-inverse `U_{V, ψ}` -/

/-- **Stacks 0DEG.** The quasi-inverse of the proof, at an object `ψ : V ⟶ X_red` of
`X_{spaces, étale}`: the fppf sheaf `U_{V, ψ}` whose sections over `T` are the pairs `(a, b)`
with `a : T ⟶ X` a morphism of formal algebraic spaces and
`b : T ×_{a, X} X_red ⟶ V` a morphism over `X_red`.

This is the functor the source writes down, as an fppf sheaf. That it is a sheaf is
`AlgebraicGeometry.FormalSpace.isSheaf_liftAlongPresheaf`. -/
@[stacks 0DEG "the quasi-inverse `U_{V, ψ}` of the proof, as an fppf sheaf; that
  `U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale is proved in
  StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverseRepresentable.lean, that
  `U_{V, ψ}` is a formal algebraic space is not, see the implementation notes"]
def spacesEtaleQuasiInverse {X : FppfSheaf B S hS} (R : Reduction B S hS X)
    (V : R.SpacesEtale) : FppfSheaf B S hS :=
  liftAlong B S hS R.inclusion (liftSheafMap B S hS V.obj.hom)

/-- **Stacks 0DEG.** The transformation `U_{V, ψ} ⟶ X`, `(a, b) ↦ a`, which the source claims
defines an object of the category of formal algebraic spaces representable étale over `X`. -/
@[stacks 0DEG "the transformation `U_{V, ψ} ⟶ X`, `(a, b) ↦ a`"]
def spacesEtaleQuasiInverseBase {X : FppfSheaf B S hS} (R : Reduction B S hS X)
    (V : R.SpacesEtale) : spacesEtaleQuasiInverse B S hS R V ⟶ X :=
  liftAlongBase B S hS R.inclusion (liftSheafMap B S hS V.obj.hom)

/-- **Stacks 0DEG.** The comparison `V ⟶ U_{V, ψ}` over `X`, which exhibits `V` as the fibre
product `U_{V, ψ} ×_X X_red`. -/
def spacesEtaleQuasiInverseSection {X : FppfSheaf B S hS} (R : Reduction B S hS X)
    (V : R.SpacesEtale) :
    liftSheaf B S hS V.obj.left ⟶ spacesEtaleQuasiInverse B S hS R V :=
  liftAlongSection B S hS (R.injective_app_inclusion)

/-- **Stacks 0DEG.** `V` is the fibre product `U_{V, ψ} ×_X X_red`.

Since the comparison functor of Stacks 0DEG sends `φ : U ⟶ X` to `U ×_X X_red` — which is
`AlgebraicGeometry.FormalSpace.isPullback_inclusion_liftSheafMap_map` — this says that the
comparison functor applied to the quasi-inverse at `(V, ψ)` returns `(V, ψ)`. It is the half of
the source's "the constructions are mutually inverse to each other" that does not need the
lifting of morphisms along the thickening `X_red ⟶ X`. -/
@[stacks 0DEG "the quasi-inverse is a right inverse: `U_{V, ψ} ×_X X_red = V` over `X_red`,
  which is one half of the source's 'the constructions are mutually inverse to each other'"]
theorem isPullback_spacesEtaleQuasiInverseSection {X : FppfSheaf B S hS}
    (R : Reduction B S hS X) (V : R.SpacesEtale) :
    IsPullback (spacesEtaleQuasiInverseSection B S hS R V)
      (liftSheafMap B S hS V.obj.hom) (spacesEtaleQuasiInverseBase B S hS R V) R.inclusion :=
  isPullback_liftAlongSection B S hS (R.injective_app_inclusion)

end Construction


/-! ### Functoriality of the quasi-inverse -/

section Map

variable {W' : FppfSheaf B S hS} (i : I ⟶ X) {p : W ⟶ I} {p' : W' ⟶ I}
  (q : W ⟶ W') (hq : q ≫ p' = p)

end Map

/-! ### The dependent product of the identity -/

section Identity

variable (i : I ⟶ X)

end Identity

/-- **Stacks 0DEG.** The quasi-inverse as a functor, which is what the source produces: an
object `ψ : V ⟶ X_red` of `X_{spaces, étale}` goes to the formal-space-shaped sheaf
`U_{V, ψ}` with its morphism to `X`, and a morphism of `X_{spaces, étale}` goes to the
morphism over `X` obtained by postcomposition on the second component.

It lands in the slice `Over X` rather than in the category of Stacks 0DEG for a reason of import
order only. Both of the source's assertions about its values are proved: that the structure
morphism is representable by algebraic spaces and étale is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_spacesEtaleQuasiInverseBase`, and that
`U_{V, ψ}` is a formal algebraic space is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong`, which lives further down the
import order, in `StacksFrontier/AlgebraicGeometry/FormalSpace/LiftAlongAffineBase.lean`. The
equivalence assembled from them is there as well,
`AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`. See the module
documentation. -/
@[stacks 0DEG "the quasi-inverse as a functor into the slice over `X` — the source's 'thus we
  obtain our functor `(V, ψ) ↦ (U_{V, ψ} ⟶ X)` in the other direction'. That its values lie in
  the subcategory of the formal algebraic spaces representable étale over `X` is proved, in both
  of the source's assertions: `isRepresentableEtale_spacesEtaleQuasiInverseBase` here and
  `isFormalAlgebraicSpace_liftAlong` further down the import order; the codomain restriction and
  the equivalence assembled from them are `spacesEtaleComparison_isEquivalence`. The slice is an
  import-order artefact, not a missing step"]
def spacesEtaleQuasiInverseFunctor {X : FppfSheaf B S hS} (R : Reduction B S hS X) :
    R.SpacesEtale ⥤ Over X where
  obj V := Over.mk (spacesEtaleQuasiInverseBase B S hS R V)
  map {_ V'} f := Over.homMk
    (liftAlongMap B S hS R.inclusion (liftSheafMap B S hS f.hom.left)
      ((liftSheafMap_comp B S hS f.hom.left V'.obj.hom).symm.trans
        (congrArg (liftSheafMap B S hS) (Over.w f.hom))))
    (liftAlongMap_comp_base B S hS R.inclusion _ _)
  map_id V := Over.OverMorphism.ext
    ((liftAlongMap_congr B S hS R.inclusion (liftSheafMap_id B S hS V.obj.left) _ _).trans
      (liftAlongMap_id B S hS R.inclusion))
  map_comp f g := Over.OverMorphism.ext
    ((liftAlongMap_congr B S hS R.inclusion
        (liftSheafMap_comp B S hS f.hom.left g.hom.left) _ _).trans
      (liftAlongMap_comp B S hS R.inclusion _ _ _ _).symm)


end AlgebraicGeometry.FormalSpace

end
