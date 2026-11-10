module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.ToposRelocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a relocalization is base change

Let `X` be a ringed topos presented by a site `(C, J)` and let `a : H ⟶ K` be a morphism of
sheaves of sets on `C`. Stacks 04J4 asserts that the relocalization morphism
`Sh(C/H) ⟶ Sh(C/K)` — restriction along postcomposition of sections with `a` — becomes, once
the two localizations are identified with the slice topoi `Sh(C)/H` and `Sh(C)/K` by Stacks
04IE, base change along `a`. This file proves that assertion.

The identifications of Stacks 04IE are not abstract: Stacks 0791 pins down the inverse of each
of them on underlying presheaves as the *fibre construction*, sending an object `φ : G ⟶ K` of
`Sh(C)/K` to the presheaf `(U, t) ↦ {x ∈ G(U) | φ(x) = t}` on the site of elements of `K`. So
the assertion reduces to a computation with those fibres, which is what is carried out here: a
section of `G` over `(U, t)` in the site of elements of `H`, read through postcomposition with
`a`, is a section of `G` over `(U, t ≫ a)`, and that is the same thing as a section over `(U, t)`
of the base change `G ×_K H`. That last step is exactly the adjunction `a_* ⊣ a^*` between
`CategoryTheory.Over.map` and `CategoryTheory.Over.pullback` evaluated at the representable
object `(U, t)`, which is how it is proved below.

## Main definitions

* `CategoryTheory.OverPresheafAux.overArrowsEquivOverHom`: a section of `η : F ⟶ A` over a
  representable element `s : h_U ⟶ A` is a morphism `(h_U, s) ⟶ (F, η)` of `PSh(C)/A`.
* `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv`: the fibres of a base change
  `G ×_{K} H ⟶ H` over `(U, t)` are the fibres of `G ⟶ K` over `(U, t ≫ a)`.
* `CategoryTheory.restrictedYonedaCompPullbackIso`: the fibre construction turns base change
  along `a : H ⟶ K` into restriction along postcomposition with `a`, as an isomorphism of
  functors `PSh(C)/K ⥤ PSh(C/H)`.

## Main results

* `CategoryTheory.forget_map_toOverCompPullbackIso_hom_app`: the counit of the identification
  `toOver K ⋙ Over.pullback a ≅ toOver H`, needed to read a comparison with base change through
  the projections `G × H ⟶ G` and `G × K ⟶ G`.
* `AlgebraicGeometry.RingedTopos.relocalizationFibreIso`: **Stacks 04J4** in the form the fibre
  description gives it: the inverse of Stacks 04IE's identification at `K`, followed by the
  inverse image of the relocalization, is base change along `a` followed by the inverse of the
  identification at `H`.
* `AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso`: **Stacks 04J4**, the
  inverse image of the relocalization morphism along `a : H ⟶ K`, read through Stacks 04IE's
  identifications of the two localizations with their slice topoi, is base change along `a`.
* `AlgebraicGeometry.RingedTopos.forget_map_relocalizationInverseImageSliceIso_hom_app`:
  **Stacks 04J4** on the objects pulled back from `Sh(C)`. Read through `Over.forget H` and
  followed by the projection to `G`, the comparison composes with the lower shriek counit at `K`
  to give the lower shriek counit at `H`. This is what connects a comparison built from the fibre
  description with the characterisation of Stacks 04IE's inverse-image identification by the
  lower shriek counit.
* `AlgebraicGeometry.RingedTopos.fst_app_val_fibrePullbackComparison`: the fibre comparison of a
  base change is the first projection.
* `AlgebraicGeometry.RingedTopos.relocalizationFibreIso_hom_app_map` and
  `AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso_hom_app`: the components of
  the two comparisons, the first on underlying presheaves. Together they evaluate every
  component of the comparison, the fibre computation
  `AlgebraicGeometry.RingedTopos.relocalizationFibrePresheafIso` being the only non-formal
  ingredient.

## Implementation notes

**Why the fibre description is needed.** Whiskering a comparison isomorphism with the inverse
image of the localization at `K` is injective but not surjective
(`Stacks.Sheaves.LocalizedRingedTopos.relocalization_inverseImage_unique`, and the counterexample
in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RelocalizationSliceComparison.lean`), so the
comparison cannot be obtained from its restriction to the objects pulled back from `Sh(C)`. It
has to be built from the actual description of the identifications, which is
`AlgebraicGeometry.RingedTopos.localizationEquivalence_fibers`.

**Why the computation happens on presheaves.** The fibre description of Stacks 0791 is a
statement about underlying presheaves, and `sheafToPresheaf` is fully faithful, so an
isomorphism of functors into a category of sheaves may be built from an isomorphism of the
composites with it (`CategoryTheory.Functor.fullyFaithfulCancelRight`). The two steps that cross
between sheaves and presheaves are then: that restriction along a continuous functor is
precomposition on underlying presheaves, which is
`CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso` and holds on the nose;
and that `sheafToPresheaf` preserves the pullback defining base change, which is
`CategoryTheory.Over.postPullbackIso`.

The fibre computation itself is stated for arbitrary presheaves `H`, `K` on an arbitrary
category, with no topology in sight: it is a property of `CostructuredArrow.map` and
`Over.pullback`, not of sheaves.

Universes follow `SliceEquivalence.lean`: site morphisms and sections of `O` are taken in one
universe `v`, which is what Stacks 0791 needs in order to return a sheaf equivalence, and site
objects in a universe `u` of their own; the smallness `Stacks 0791` needs of the site is then the
hypothesis `EssentiallySmall.{v} X.C`, automatic when `u = v`.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

open OverPresheafAux

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

/-- **A fibre is a morphism of the slice category.** A section of `η : F ⟶ A` over a
representable element `s : h_U ⟶ A` of `A` is the same thing as a morphism `(h_U, s) ⟶ (F, η)`
in `PSh(C)/A`: the Yoneda lemma turns the section into a map `h_U ⟶ F`, and lying in the fibre
over `s` is exactly commutativity of the triangle over `A`. -/
@[sga "3 I 1.3" "partial"]
noncomputable def OverPresheafAux.overArrowsEquivOverHom {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {U : C}
    (s : yoneda.obj U ⟶ A) : OverArrows η s ≃ (Over.mk s ⟶ Over.mk η) where
  toFun x := Over.homMk (yonedaEquiv.symm x.val) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    simpa using x.app_val)
  invFun f := ⟨yonedaEquiv f.left, MakesOverArrow.of_arrow (by simpa using f.w)⟩
  left_inv x := by ext; simp
  right_inv f := by ext; simp

/-- The underlying map of a morphism of `PSh(C)/A` produced by
`CategoryTheory.OverPresheafAux.overArrowsEquivOverHom`. -/
lemma OverPresheafAux.overArrowsEquivOverHom_left {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {U : C}
    (s : yoneda.obj U ⟶ A) (x : OverArrows η s) :
    (overArrowsEquivOverHom η s x).left = yonedaEquiv.symm x.val :=
  rfl

/-- The section of `η` recovered from a morphism of `PSh(C)/A` by
`CategoryTheory.OverPresheafAux.overArrowsEquivOverHom`. -/
lemma OverPresheafAux.overArrowsEquivOverHom_symm_val {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {U : C}
    (s : yoneda.obj U ⟶ A) (f : Over.mk s ⟶ Over.mk η) :
    ((overArrowsEquivOverHom η s).symm f).val = yonedaEquiv f.left :=
  rfl

variable {H K : Cᵒᵖ ⥤ Type v}

/-- **The fibres of a base change.** For `α : H ⟶ K` and an object `S` of `PSh(C)/K`, the
sections of the base change `S ×_K H ⟶ H` over an element `(U, t)` of `H` are the sections of
`S ⟶ K` over the element `(U, t ≫ α)` of `K`.

Both sides are morphisms out of the representable object `(U, t)` — on the left into the base
change, on the right out of its image under `Over.map α`, which is `(U, t ≫ α)` — so this is the
adjunction `CategoryTheory.Over.mapPullbackAdj` and nothing more. -/
noncomputable def OverPresheafAux.overArrowsPullbackEquiv (α : H ⟶ K) (S : Over K)
    (s : CostructuredArrow yoneda H) :
    OverArrows ((Over.pullback α).obj S).hom s.hom ≃
      OverArrows S.hom ((CostructuredArrow.map α).obj s).hom :=
  (overArrowsEquivOverHom ((Over.pullback α).obj S).hom s.hom).trans
    ((((Over.mapPullbackAdj α).homEquiv (Over.mk s.hom) S).symm).trans
      (overArrowsEquivOverHom S.hom _).symm)

/-- `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv` is the first projection of the base
change. -/
@[simp]
lemma OverPresheafAux.overArrowsPullbackEquiv_val (α : H ⟶ K) (S : Over K)
    (s : CostructuredArrow yoneda H) (x : OverArrows ((Over.pullback α).obj S).hom s.hom) :
    (overArrowsPullbackEquiv α S s x).val = (pullback.fst S.hom α).app (op s.left) x.val := by
  have h : overArrowsPullbackEquiv α S s x =
      (overArrowsEquivOverHom S.hom ((CostructuredArrow.map α).obj s).hom).symm
        (((Over.mapPullbackAdj α).homEquiv (Over.mk s.hom) S).symm
          (overArrowsEquivOverHom ((Over.pullback α).obj S).hom s.hom x)) := rfl
  rw [h, overArrowsEquivOverHom_symm_val]
  simp [Over.mapPullbackAdj, overArrowsEquivOverHom_left, yonedaEquiv_comp]

/-- `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv` is natural in the element of `H`. -/
lemma OverPresheafAux.overArrowsPullbackEquiv_map₂ (α : H ⟶ K) (S : Over K)
    {Z W : CostructuredArrow yoneda H} (g : W ⟶ Z)
    (x : OverArrows ((Over.pullback α).obj S).hom Z.hom) :
    overArrowsPullbackEquiv α S W (x.map₂ g.left g.w) =
      (overArrowsPullbackEquiv α S Z x).map₂ g.left (by
        change yoneda.map g.left ≫ Z.hom ≫ α = W.hom ≫ α
        rw [← Category.assoc, g.w]) := by
  apply OverArrows.ext
  simp only [overArrowsPullbackEquiv_val, OverArrows.map₂_val]
  exact NatTrans.naturality_apply (pullback.fst S.hom α) g.left.op x.val

/-- `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv` is natural in the object of
`PSh(C)/K`. -/
lemma OverPresheafAux.overArrowsPullbackEquiv_map₁ (α : H ⟶ K) {S T : Over K} (f : S ⟶ T)
    (s : CostructuredArrow yoneda H) (x : OverArrows ((Over.pullback α).obj S).hom s.hom) :
    overArrowsPullbackEquiv α T s
        (x.map₁ ((Over.pullback α).map f).left ((Over.pullback α).map f).w) =
      (overArrowsPullbackEquiv α S s x).map₁ f.left f.w := by
  apply OverArrows.ext
  simp only [overArrowsPullbackEquiv_val, OverArrows.map₁_val]
  have h : ((Over.pullback α).map f).left ≫ pullback.fst T.hom α
      = pullback.fst S.hom α ≫ f.left := pullback.lift_fst _ _ _
  change (((Over.pullback α).map f).left ≫ pullback.fst T.hom α).app (op s.left) x.val
      = (pullback.fst S.hom α ≫ f.left).app (op s.left) x.val
  rw [h]

/-- **The fibre construction turns base change into restriction.** For `α : H ⟶ K`, taking the
base change along `α` of an object of `PSh(C)/K` and then its fibre presheaf on the category of
elements of `H` is the same as taking its fibre presheaf on the category of elements of `K` and
restricting along postcomposition with `α`.

This is `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv`, natural in both variables by
`overArrowsPullbackEquiv_map₂` and `overArrowsPullbackEquiv_map₁`. -/
noncomputable def restrictedYonedaCompPullbackIso (α : H ⟶ K) :
    Over.pullback α ⋙ (overEquivPresheafCostructuredArrow H).functor ≅
      (overEquivPresheafCostructuredArrow K).functor ⋙
        (Functor.whiskeringLeft _ _ (Type v)).obj (CostructuredArrow.map α).op :=
  NatIso.ofComponents
    (fun S => NatIso.ofComponents
      (fun s => (OverPresheafAux.overArrowsPullbackEquiv α S s.unop).toIso)
      (fun {_ _} f => by
        ext x
        exact OverPresheafAux.overArrowsPullbackEquiv_map₂ α S f.unop x))
    (fun {_ _} f => by
      ext s x
      exact OverPresheafAux.overArrowsPullbackEquiv_map₁ α f s.unop x)

section ToOverPullback

universe v' u'

variable {E : Type u'} [Category.{v'} E] [CartesianMonoidalCategory E] [HasPullbacks E]

/-- The adjunction `Over.forget H ⊣ toOver K ⋙ Over.pullback a` of which
`CategoryTheory.toOverCompPullbackIso` compares the right adjoint with `toOver H`, with its left
adjoint written as `Over.forget H` from the start.

`toOverCompPullbackIso` transports the composite `Over.mapPullbackAdj a ∘ forgetAdjToOver K`
along `CategoryTheory.Over.mapForget_eq`; that equality of functors is `rfl`, so the transport is
the identity, but leaving it in place makes `Adjunction.rightAdjointUniq_hom_app_counit`
unusable — unifying a freshly elaborated transported adjunction with the one inside the
definition exhausts the elaborator. Naming the transport-free adjunction, and identifying it
with the transported one by `rfl`, is what makes the counit of `toOverCompPullbackIso`
reachable. -/
@[sga "4 IV 5.2" "j_{H!} ⊣ j_H^*"]
private noncomputable def forgetAdjToOverCompPullback {H K : E} (a : H ⟶ K) :
    Over.forget H ⊣ toOver K ⋙ Over.pullback a :=
  (Over.mapPullbackAdj a).comp (forgetAdjToOver K)

/-- `CategoryTheory.toOverCompPullbackIso` compares the right adjoint of
`forgetAdjToOverCompPullback` with that of `forgetAdjToOver`. -/
private theorem toOverCompPullbackIso_eq {H K : E} (a : H ⟶ K) :
    toOverCompPullbackIso a =
      Adjunction.rightAdjointUniq (forgetAdjToOverCompPullback a) (forgetAdjToOver H) :=
  rfl

/-- **The counit of `toOverCompPullbackIso`.** Reading the identification
`toOver K ⋙ Over.pullback a ≅ toOver H` through `Over.forget H` and following it by the
projection `G × H ⟶ G` is the projection `(G × K) ×_K H ⟶ G × K` followed by the projection
`G × K ⟶ G`.

Both composites are the counit of `forgetAdjToOverCompPullback`: the left-hand one because
`toOverCompPullbackIso` is uniqueness of right adjoints, and the right-hand one because the
counit of a composite adjunction is the composite of the counits. -/
theorem forget_map_toOverCompPullbackIso_hom_app {H K : E} (a : H ⟶ K) (G : E) :
    (Over.forget H).map ((toOverCompPullbackIso a).hom.app G) ≫
        (forgetAdjToOver H).counit.app G =
      pullback.fst ((toOver K).obj G).hom a ≫ (forgetAdjToOver K).counit.app G := by
  rw [toOverCompPullbackIso_eq, Adjunction.rightAdjointUniq_hom_app_counit,
    forgetAdjToOverCompPullback, Adjunction.comp_counit_app]
  congr 1
  simp [Over.mapPullbackAdj_counit_app]

end ToOverPullback

end CategoryTheory

namespace AlgebraicGeometry.RingedTopos

open Stacks.Sheaves.LocalizedRingedTopos

variable (X : RingedTopos.{v, u, v}) [EssentiallySmall.{v} X.C] {H K : X.Topos}

/-- **Stacks 04J4** in fibre form, on underlying presheaves: the fibre presheaf of an object of
`Sh(C)/K` on the site of elements of `K`, restricted along postcomposition with `a : H ⟶ K`, is
the fibre presheaf of its base change along `a` on the site of elements of `H`.

The two identifications of Stacks 04IE are the fibre construction
(`localizationEquivalence_fibers`), the inverse image of the relocalization is restriction along
postcomposition with `a`, and `CategoryTheory.restrictedYonedaCompPullbackIso` says that the
fibre construction carries base change along `a` to that restriction. -/
noncomputable def relocalizationFibrePresheafIso (a : H ⟶ K) :
    ((localizationEquivalence X K).inverse ⋙
          (X.relocalizationMorphismOfTopoi a).inverseImage) ⋙
        sheafToPresheaf (elementTopology X H) (Type v) ≅
      (Over.pullback a ⋙ (localizationEquivalence X H).inverse) ⋙
        sheafToPresheaf (elementTopology X H) (Type v) :=
  Functor.isoWhiskerRight (localizationEquivalence_fibers X K)
      ((Functor.whiskeringLeft _ _ (Type v)).obj
        (CostructuredArrow.map a.hom).op) ≪≫
    Functor.isoWhiskerLeft (Over.post (X := K) (sheafToPresheaf X.J (Type v)))
      (restrictedYonedaCompPullbackIso ((sheafToPresheaf X.J (Type v)).map a)).symm ≪≫
    Functor.isoWhiskerRight
      (Over.postPullbackIso (sheafToPresheaf X.J (Type v)) a).symm
      (overEquivPresheafCostructuredArrow H.obj).functor ≪≫
    Functor.isoWhiskerLeft (Over.pullback a) (localizationEquivalence_fibers X H).symm

omit [EssentiallySmall.{v} X.C] in
/-- **The fibre comparison of a base change is the first projection.** The last two factors of
`relocalizationFibrePresheafIso` turn a section of `S ⟶ K` over the element `(U, t ≫ a)` of `K`
into a section of the base change `S ×_K H ⟶ H` over `(U, t)`; this says that the first
projection `S ×_K H ⟶ S` sends the latter back to the former.

The two factors are `CategoryTheory.OverPresheafAux.overArrowsPullbackEquiv`, whose value is the
first projection by `overArrowsPullbackEquiv_val`, and the Beck–Chevalley isomorphism
`CategoryTheory.Over.postPullbackIso`, which is `Limits.PreservesPullback.iso` on underlying
presheaves and therefore commutes with the first projection by
`Limits.PreservesPullback.iso_inv_fst`. -/
theorem fst_app_val_fibrePullbackComparison (a : H ⟶ K) (S : Over K)
    (Z : CostructuredArrow yoneda H.obj)
    (q : OverPresheafAux.OverArrows
      ((Over.post (X := K) (sheafToPresheaf X.J (Type v))).obj S).hom
      ((CostructuredArrow.map ((sheafToPresheaf X.J (Type v)).map a)).obj Z).hom) :
    (pullback.fst S.hom a).hom.app (op Z.left)
        (((Functor.isoWhiskerLeft (Over.post (X := K) (sheafToPresheaf X.J (Type v)))
                (restrictedYonedaCompPullbackIso ((sheafToPresheaf X.J (Type v)).map a)).symm ≪≫
              Functor.isoWhiskerRight
                (Over.postPullbackIso (sheafToPresheaf X.J (Type v)) a).symm
                (overEquivPresheafCostructuredArrow H.obj).functor).hom.app S).app (op Z) q).val =
      q.val := by
  have h := OverPresheafAux.overArrowsPullbackEquiv_val ((sheafToPresheaf X.J (Type v)).map a)
    ((Over.post (X := K) (sheafToPresheaf X.J (Type v))).obj S) Z
    ((OverPresheafAux.overArrowsPullbackEquiv ((sheafToPresheaf X.J (Type v)).map a)
      ((Over.post (X := K) (sheafToPresheaf X.J (Type v))).obj S) Z).symm q)
  rw [Equiv.apply_symm_apply] at h
  change (pullback.fst S.hom a).hom.app (op Z.left)
      ((PreservesPullback.iso (sheafToPresheaf X.J (Type v)) S.hom a).inv.app (op Z.left)
        ((OverPresheafAux.overArrowsPullbackEquiv ((sheafToPresheaf X.J (Type v)).map a)
          ((Over.post (X := K) (sheafToPresheaf X.J (Type v))).obj S) Z).symm q).val) = q.val
  rw [h]
  exact congrArg (fun g => (ConcreteCategory.hom g)
      ((OverPresheafAux.overArrowsPullbackEquiv ((sheafToPresheaf X.J (Type v)).map a)
        ((Over.post (X := K) (sheafToPresheaf X.J (Type v))).obj S) Z).symm q).val)
    (NatTrans.congr_app
      (PreservesPullback.iso_inv_fst (sheafToPresheaf X.J (Type v)) S.hom a) (op Z.left))

/-- **Stacks 04J4** in fibre form: the inverse of Stacks 04IE's identification of the
localization of `X` at `K` with `Sh(C)/K`, followed by the inverse image of the relocalization
along `a : H ⟶ K`, is base change along `a` followed by the inverse of the identification at
`H`.

Since `sheafToPresheaf` is fully faithful, the computation of the underlying presheaves
(`relocalizationFibrePresheafIso`) is the statement. -/
noncomputable def relocalizationFibreIso (a : H ⟶ K) :
    (localizationEquivalence X K).inverse ⋙
        (X.relocalizationMorphismOfTopoi a).inverseImage ≅
      Over.pullback a ⋙ (localizationEquivalence X H).inverse :=
  @Functor.fullyFaithfulCancelRight _ _ _ _ _ _ _ _
    (sheafToPresheaf (elementTopology X H) (Type v))
    (ObjectProperty.fullyFaithfulι _).full (ObjectProperty.fullyFaithfulι _).faithful
    (X.relocalizationFibrePresheafIso a)

/-- **The component of `relocalizationFibreIso` is reachable**: on underlying presheaves it is
the component of the fibre computation `relocalizationFibrePresheafIso`.

`relocalizationFibreIso` is produced by `CategoryTheory.Functor.fullyFaithfulCancelRight`, so
its components are `sheafToPresheaf`-preimages, which no `simp` set can evaluate. This is the
only handle on them, and since `sheafToPresheaf` is faithful it is a complete one: an equation
between morphisms of sheaves built from these components holds as soon as it holds on underlying
presheaves. -/
theorem relocalizationFibreIso_hom_app_map (a : H ⟶ K) (S : Over K) :
    (sheafToPresheaf (elementTopology X H) (Type v)).map
        ((X.relocalizationFibreIso a).hom.app S) =
      (X.relocalizationFibrePresheafIso a).hom.app S :=
  have : (sheafToPresheaf (elementTopology X H) (Type v)).Full :=
    (fullyFaithfulSheafToPresheaf _ _).full
  Functor.map_preimage _ _

/-- `relocalizationFibreIso_hom_app_map` for the inverse. -/
theorem relocalizationFibreIso_inv_app_map (a : H ⟶ K) (S : Over K) :
    (sheafToPresheaf (elementTopology X H) (Type v)).map
        ((X.relocalizationFibreIso a).inv.app S) =
      (X.relocalizationFibrePresheafIso a).inv.app S :=
  have : (sheafToPresheaf (elementTopology X H) (Type v)).Full :=
    (fullyFaithfulSheafToPresheaf _ _).full
  Functor.map_preimage _ _

/-- **Stacks 04J4.** The inverse image of the relocalization morphism along a morphism
`a : H ⟶ K` of sheaves of sets, read through Stacks 04IE's identifications of the localization
of `X` at `H` and at `K` with the slice topoi `Sh(C)/H` and `Sh(C)/K`, is base change along
`a`.

This is `relocalizationFibreIso` transported across the two equivalences. -/
@[stacks 04J4 "the inverse image of the relocalization is base change on slice topoi"]
noncomputable def relocalizationInverseImageSliceIso (a : H ⟶ K) :
    (X.relocalizationMorphism a).toToposHom.inverseImage ⋙
        (localizationEquivalence X H).functor ≅
      (localizationEquivalence X K).functor ⋙ Over.pullback a :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (localizationEquivalence X K).unitIso
      ((X.relocalizationMorphism a).toToposHom.inverseImage ⋙
        (localizationEquivalence X H).functor) ≪≫
    Functor.isoWhiskerLeft (localizationEquivalence X K).functor
      (Functor.isoWhiskerRight (X.relocalizationFibreIso a)
        (localizationEquivalence X H).functor) ≪≫
    Functor.isoWhiskerLeft ((localizationEquivalence X K).functor ⋙ Over.pullback a)
      (localizationEquivalence X H).counitIso ≪≫
    Functor.rightUnitor _

/-- **Stacks 04J4's comparison, componentwise.** The component of
`relocalizationInverseImageSliceIso` at an object `W` of the localization at `K` is the fibre
comparison at `W` read in `Sh(C)/K`, conjugated by the unit of the equivalence at `K` and its
counit at `H`.

Together with `relocalizationFibreIso_hom_app_map` this makes every component of the comparison
reachable: the fibre comparison is the only non-formal ingredient, and that lemma evaluates it
on underlying presheaves. -/
theorem relocalizationInverseImageSliceIso_hom_app (a : H ⟶ K)
    (W : (localizedRingedTopos X K).Topos) :
    (X.relocalizationInverseImageSliceIso a).hom.app W =
      (localizationEquivalence X H).functor.map
          ((X.relocalizationMorphismOfTopoi a).inverseImage.map
            ((localizationEquivalence X K).unitIso.hom.app W)) ≫
        (localizationEquivalence X H).functor.map
            ((X.relocalizationFibreIso a).hom.app
              ((localizationEquivalence X K).functor.obj W)) ≫
          (localizationEquivalence X H).counitIso.hom.app
            ((Over.pullback a).obj ((localizationEquivalence X K).functor.obj W)) := by
  simp only [relocalizationInverseImageSliceIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp]
  rfl

private theorem key_relocalizationFibre (a : H ⟶ K) (G : X.Topos) :
    (X.relocalizationMorphismOfTopoi a).inverseImage.map
          ((localizationEquivalence X K).unit.app
            ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫
        (X.relocalizationFibreIso a).hom.app
            ((localizationEquivalence X K).functor.obj
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫
          fibreTranspose X H ((Over.pullback a).obj
              ((localizationEquivalence X K).functor.obj
                ((X.localizationMorphism K).toToposHom.inverseImage.obj G))) G
            (pullback.fst ((localizationEquivalence X K).functor.obj
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
                (X.localizationShriekAdjunction K).counit.app G) =
      𝟙 ((X.localizationMorphism H).toToposHom.inverseImage.obj G) := by
  refine Sheaf.homEquiv.injective ?_
  change _ ≫ (sheafToPresheaf (elementTopology X H) (Type v)).map
      ((X.relocalizationFibreIso a).hom.app _) ≫ _ = _
  rw [X.relocalizationFibreIso_hom_app_map a]
  ext Z y
  obtain ⟨Z⟩ := Z
  refine Eq.trans (app_fibreTranspose X H ((Over.pullback a).obj
        ((localizationEquivalence X K).functor.obj
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G))) G
      (pullback.fst ((localizationEquivalence X K).functor.obj
        ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
          (X.localizationShriekAdjunction K).counit.app G) Z
      ((((Functor.isoWhiskerLeft (Over.post (X := K) (sheafToPresheaf X.J (Type v)))
                (restrictedYonedaCompPullbackIso ((sheafToPresheaf X.J (Type v)).map a)).symm ≪≫
              Functor.isoWhiskerRight
                (Over.postPullbackIso (sheafToPresheaf X.J (Type v)) a).symm
                (overEquivPresheafCostructuredArrow H.obj).functor).hom.app
            ((localizationEquivalence X K).functor.obj
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G))).app (op Z)
        (((localizationEquivalence_fibers X K).hom.app
              ((localizationEquivalence X K).functor.obj
                ((X.localizationMorphism K).toToposHom.inverseImage.obj G))).app
            (op ((CostructuredArrow.map ((sheafToPresheaf X.J (Type v)).map a)).obj Z))
          (((localizationEquivalence X K).unit.app
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom.app
            (op ((CostructuredArrow.map ((sheafToPresheaf X.J (Type v)).map a)).obj Z)) y))))) ?_
  refine Eq.trans (congrArg (fun v => ((X.localizationShriekAdjunction K).counit.app G).hom.app
      (op Z.left) v) (X.fst_app_val_fibrePullbackComparison a _ Z _)) ?_
  exact X.counit_app_val_app_fibers_hom_unit K G
    ((CostructuredArrow.map ((sheafToPresheaf X.J (Type v)).map a)).obj Z) y

/-- **Stacks 04J4 on the objects pulled back from `Sh(C)`.** The comparison of the inverse
image of the relocalization with base change, read through `Over.forget H` and followed by the
projection to `G`, composes with the lower shriek counit at `K` to give the lower shriek counit
at `H`.

This is the whole content of the base lemma: the comparison is built from the *fibre*
description of the two identifications, while the identification of the inverse image of a
localization with a product is characterised by the *counit* of the lower shriek, so the two have
to be connected once. `AlgebraicGeometry.RingedTopos.fibreTranspose_shriek_counit` does the
formal half and `key_relocalizationFibre` the fibre computation. -/
theorem forget_map_relocalizationInverseImageSliceIso_hom_app (a : H ⟶ K) (G : X.Topos) :
    (Over.forget H).map ((X.relocalizationInverseImageSliceIso a).hom.app
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫
        (pullback.fst ((localizationEquivalence X K).functor.obj
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
          (X.localizationShriekAdjunction K).counit.app G) =
      (X.localizationShriekAdjunction H).counit.app G := by
  refine fibreTranspose_injective X H ((localizationEquivalence X H).functor.obj
    ((X.relocalizationMorphismOfTopoi a).inverseImage.obj
      ((X.localizationMorphism K).toToposHom.inverseImage.obj G))) G ?_
  refine Eq.trans (fibreTranspose_forget_map_comp X H G
    ((X.relocalizationInverseImageSliceIso a).hom.app
      ((X.localizationMorphism K).toToposHom.inverseImage.obj G))
    (pullback.fst ((localizationEquivalence X K).functor.obj
      ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
        (X.localizationShriekAdjunction K).counit.app G)) ?_
  refine Eq.trans ?_ (fibreTranspose_shriek_counit X H G).symm
  rw [show (localizationEquivalence X H).inverse.map
        ((X.relocalizationInverseImageSliceIso a).hom.app
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) =
      (localizationEquivalence X H).unitInv.app
          ((X.relocalizationMorphismOfTopoi a).inverseImage.obj
            ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫
        ((X.relocalizationMorphismOfTopoi a).inverseImage.map
            ((localizationEquivalence X K).unit.app
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫
          (X.relocalizationFibreIso a).hom.app
            ((localizationEquivalence X K).functor.obj
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G))) from by
    rw [X.relocalizationInverseImageSliceIso_hom_app a, ← Category.assoc, ← Functor.map_comp]
    exact Equivalence.inverse_map_functor_map_comp_counit _ _]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (localizationEquivalence X H).unitInv.app
        ((X.relocalizationMorphismOfTopoi a).inverseImage.obj
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫ z)
      ((Category.assoc _ _ _).trans (X.key_relocalizationFibre a G))).trans (Category.comp_id _))


/-- **Stacks 04J4: the comparison with base change is the one the localization comparisons
prescribe.** Stacks 04IE identifies the inverse image of the localization at `H` with
`toOver H`; that identification is `localizationInverseImageIso X H`, and this says it is the
comparison with base change along `a`, whiskered with the inverse image of the localization at
`K`, followed by Stacks 04IE at `K` and by the identification
`toOver K ⋙ Over.pullback a ≅ toOver H` of Stacks 03EH.

With `Stacks.Sheaves.LocalizedRingedTopos.relocalization_inverseImage_unique` this is the full
`∃!` of the source: uniqueness holds for every choice of the two identifications, and here is the
one solution for the canonical choice. The proof is
`localizationInverseImageIso_eq` — the comparison is determined by its lower shriek counits —
fed with `forget_map_relocalizationInverseImageSliceIso_hom_app` for the relocalization half,
`CategoryTheory.forget_map_toOverCompPullbackIso_hom_app` for the Stacks 03EH half, and
`localizationInverseImageIso`'s own counit description at `K`. -/
@[stacks 04J4 "the comparison with base change is the one the localization comparisons of 04IE
  prescribe"]
theorem localizationInverseImageIso_eq_relocalization (a : H ⟶ K) :
    localizationInverseImageIso X H =
      Functor.isoWhiskerLeft (X.localizationMorphism K).toToposHom.inverseImage
          (X.relocalizationInverseImageSliceIso a) ≪≫
        Functor.isoWhiskerRight (localizationInverseImageIso X K) (Over.pullback a) ≪≫
          toOverCompPullbackIso a := by
  refine (localizationInverseImageIso_eq X H _ ?_).symm
  intro G
  have hglue : (Over.forget H).map ((Over.pullback a).map
          ((localizationInverseImageIso X K).hom.app G)) ≫
        (Over.forget H).map ((toOverCompPullbackIso a).hom.app G) ≫
          (forgetAdjToOver H).counit.app G =
      pullback.fst ((localizationEquivalence X K).functor.obj
          ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
        (X.localizationShriekAdjunction K).counit.app G := by
    rw [forget_map_toOverCompPullbackIso_hom_app, ← Category.assoc,
      show (Over.forget H).map ((Over.pullback a).map
              ((localizationInverseImageIso X K).hom.app G)) ≫
            pullback.fst ((toOver K).obj G).hom a =
          pullback.fst ((localizationEquivalence X K).functor.obj
              ((X.localizationMorphism K).toToposHom.inverseImage.obj G)).hom a ≫
            (Over.forget K).map ((localizationInverseImageIso X K).hom.app G) from
        pullback.lift_fst _ _ _,
      Category.assoc, forget_localizationInverseImageIso_hom_app]
  rw [← X.forget_map_relocalizationInverseImageSliceIso_hom_app a G]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  exact congrArg (fun z => (Over.forget H).map ((X.relocalizationInverseImageSliceIso a).hom.app
      ((X.localizationMorphism K).toToposHom.inverseImage.obj G)) ≫ z) hglue

end AlgebraicGeometry.RingedTopos

end
