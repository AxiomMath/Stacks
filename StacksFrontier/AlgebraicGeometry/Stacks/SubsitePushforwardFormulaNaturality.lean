module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula

/-!
# The pushforward formula on a subsite, componentwise and naturally in the presheaf

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a base, let `𝒳' ⊆ 𝒳` and `𝒴' ⊆ 𝒴` be full
subcategories with `f` carrying `𝒳'` into `𝒴'`, and let `f' : 𝒳' ⥤ 𝒴'` be the restriction. For a
presheaf `ℋ` on `𝒳'` and an object `y` of `𝒴'` lying over `V`,
`CategoryTheory.SubsitePushforward.subsitePushforwardSectionsEquiv` is the bijection

`f'_*ℋ(y) ≃ Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℋ)`.

This file computes that bijection on components and deduces that it is natural in `ℋ`.

## Main results

* `CategoryTheory.SubsitePushforward.ranObjEquiv_apply`: the comparison of the two right Kan
  extensions — the one along `f'` and the one along `𝒳' ⥤ 𝒳 ⥤ 𝒴` — is the identity on
  components, in the sense that it matches the counits of the two Kan extensions.
* `CategoryTheory.SubsitePushforward.subsitePushforwardSectionsEquiv_apply`: at an object of the
  primed 2-fibre product, the section corresponding to an element of `f'_*ℋ(y)` is obtained by
  restricting along the comparison arrow to `y` and applying the counit of the right Kan
  extension along `f'`.
* `CategoryTheory.SubsitePushforward.subsitePushforwardSectionsEquiv_naturality`: the bijection
  commutes with morphisms of presheaves.
* `AlgebraicGeometry.Stack.FlatFppf.primedPushforwardSectionsEquiv_apply`,
  `AlgebraicGeometry.Stack.FlatFppf.primedPushforwardSectionsEquiv_naturality` and their
  lisse-étale counterparts: the same two statements for the two sites of an algebraic stack.

## Implementation notes

The chain of five comparisons making up `subsitePushforwardSectionsEquiv` is componentwise
understood already except for the comparison of right Kan extensions
`CategoryTheory.SubsitePushforward.ranObjEquiv`, which passes through
`CategoryTheory.Functor.ranObjObjIsoLimit` in both directions. The identification is extracted
here by evaluating both of `CategoryTheory.Functor.ranObjObjIsoLimit_hom_π` and
`CategoryTheory.Functor.ranObjObjIsoLimit_inv_π` at a structured arrow of the shape
`StructuredArrow.mk a.op`; the three intervening comparisons of compatible families are
`CategoryTheory.Functor.sectionsPrecomp`, whose values are given by reindexing, so no transport
appears.

Naturality is then formal: both sides of each comparison are determined by their components, and
`CategoryTheory.SubsitePushforward.ranObjObj_ext` turns that into an extensionality principle for
the value of a right Kan extension.

Naturality is stated as a commuting square rather than as an isomorphism of functors in `ℋ`,
because the two sides of the formula live in different universes: the value of the Kan extension
is in `Type w`, while the compatible families over the primed 2-fibre product are indexed by its
objects and so land in `Type (max u w)`. This is the same reason the formula itself is an `Equiv`
rather than an isomorphism, as it already is for **Stacks 06W6**.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AU](https://stacks.math.columbia.edu/tag/07AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

attribute [local implicit_reducible] Functor.Fiber

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

section Generic

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

/-- Two elements of the value at `op Y` of a right Kan extension along `L.op` agree as soon as
all their restrictions along arrows `L.obj x ⟶ Y`, read through the counit, agree. -/
lemma ranObjObj_ext (L : C ⥤ D) (ℋ : Cᵒᵖ ⥤ Type w)
    [∀ G : Cᵒᵖ ⥤ Type w, L.op.HasPointwiseRightKanExtension G] {Y : D}
    {t t' : (L.op.ran.obj ℋ).obj (op Y)}
    (h : ∀ (x : C) (a : L.obj x ⟶ Y),
      (L.op.ranCounit.app ℋ).app (op x) ((L.op.ran.obj ℋ).map a.op t) =
        (L.op.ranCounit.app ℋ).app (op x) ((L.op.ran.obj ℋ).map a.op t')) :
    t = t' := by
  apply (L.op.ranObjObjIsoLimit ℋ (op Y)).toEquiv.injective
  apply Limits.Types.limit_ext
  intro j
  have hπ := Functor.ranObjObjIsoLimit_hom_π L.op ℋ (op Y) j
  have ht := congrArg (fun g : (L.op.ran.obj ℋ).obj (op Y) ⟶ _ => g t) hπ
  have ht' := congrArg (fun g : (L.op.ran.obj ℋ).obj (op Y) ⟶ _ => g t') hπ
  simp only [CategoryTheory.comp_apply] at ht ht'
  simp only [Iso.toEquiv_fun]
  rw [ht, ht']
  exact h j.right.unop j.hom.unop

/-- Restricting an element of a right Kan extension along an arrow out of `L.obj x` and reading
it through the counit commutes with the map induced by a morphism of presheaves. -/
lemma ranCounit_ran_map_apply (L : C ⥤ D) (ℋ 𝒢 : Cᵒᵖ ⥤ Type w)
    [∀ G : Cᵒᵖ ⥤ Type w, L.op.HasPointwiseRightKanExtension G] (η : ℋ ⟶ 𝒢) {Y : D}
    (t : (L.op.ran.obj ℋ).obj (op Y)) (x : C) (a : L.obj x ⟶ Y) :
    (L.op.ranCounit.app 𝒢).app (op x)
        ((L.op.ran.obj 𝒢).map a.op ((L.op.ran.map η).app (op Y) t)) =
      η.app (op x) ((L.op.ranCounit.app ℋ).app (op x) ((L.op.ran.obj ℋ).map a.op t)) := by
  have hnat := congrArg (fun g : (L.op.ran.obj ℋ).obj (op Y) ⟶ _ => g t)
    ((L.op.ran.map η).naturality a.op)
  simp only [CategoryTheory.comp_apply] at hnat
  rw [← hnat]
  exact congrArg (fun g : (L.op.ran.obj ℋ).obj (L.op.obj (op x)) ⟶ _ => g
    ((L.op.ran.obj ℋ).map a.op t)) (congr_app (L.op.ranCounit.naturality η) (op x))

/-- The value at an arrow `b : g.obj c ⟶ Y` of the compatible family transported from the index
category of structured arrows to the opposite of the index category of costructured arrows. -/
lemma pushforwardCostrSectionsEquiv_val (g : C ⥤ D) (Y : D) (ℱ : Cᵒᵖ ⥤ Type w)
    (σ : (StructuredArrow.proj (op Y) g.op ⋙ ℱ).sections) (c : C) (b : g.obj c ⟶ Y) :
    (Presheaf.pushforwardCostrSectionsEquiv g Y ℱ σ).1 (op (CostructuredArrow.mk b)) =
      σ.1 (StructuredArrow.mk (Y := op c) b.op) :=
  rfl

/-- The inverse transport, read at an arrow `b : g.obj c ⟶ Y`. -/
lemma pushforwardCostrSectionsEquiv_symm_val (g : C ⥤ D) (Y : D) (ℱ : Cᵒᵖ ⥤ Type w)
    (τ : ((CostructuredArrow.proj g Y).op ⋙ ℱ).sections) (c : C) (b : g.obj c ⟶ Y) :
    ((Presheaf.pushforwardCostrSectionsEquiv g Y ℱ).symm τ).1
        (StructuredArrow.mk (Y := op c) b.op) = τ.1 (op (CostructuredArrow.mk b)) := by
  conv_rhs => rw [← Equiv.apply_symm_apply (Presheaf.pushforwardCostrSectionsEquiv g Y ℱ) τ]
  exact (pushforwardCostrSectionsEquiv_val g Y ℱ _ c b).symm

end Generic

section Index

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) (y : Q.FullSubcategory)
  (ℋ 𝒢 : (P.FullSubcategory)ᵒᵖ ⥤ Type w)
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]

/-- The comparison of the two right Kan extensions matches their counits: restricting along an
arrow `f x' ⟶ y` of `𝒴` and reading the counit of the Kan extension along `𝒳' ⥤ 𝒳 ⥤ 𝒴` gives the
same element as restricting along the corresponding arrow `f' x' ⟶ y` of the subsite of `𝒴` and
reading the counit of the Kan extension along `f'`. -/
theorem ranObjEquiv_apply (s : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y))
    (x : P.FullSubcategory) (a : f.obj x.obj ⟶ y.obj) :
    ((P.ι ⋙ f).op.ranCounit.app ℋ).app (op x)
        (((P.ι ⋙ f).op.ran.obj ℋ).map a.op (ranObjEquiv f P hPQ y ℋ s)) =
      ((subsiteFunctor f P hPQ).op.ranCounit.app ℋ).app (op x)
        (((subsiteFunctor f P hPQ).op.ran.obj ℋ).map
          (ObjectProperty.homMk (P := Q) a).op s) := by
  have h₁ := Functor.ranObjObjIsoLimit_inv_π (P.ι ⋙ f).op ℋ (op y.obj)
    (StructuredArrow.mk (Y := op x) a.op)
  simp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self] at h₁
  have h₁' : ∀ z, ((P.ι ⋙ f).op.ranCounit.app ℋ).app (op x)
      (((P.ι ⋙ f).op.ran.obj ℋ).map a.op
        (((P.ι ⋙ f).op.ranObjObjIsoLimit ℋ (op y.obj)).inv z)) =
      limit.π (StructuredArrow.proj (op y.obj) (P.ι ⋙ f).op ⋙ ℋ)
        (StructuredArrow.mk (Y := op x) a.op) z := by
    intro z
    simpa only [CategoryTheory.comp_apply] using
      congrArg (fun g : limit (StructuredArrow.proj (op y.obj) (P.ι ⋙ f).op ⋙ ℋ) ⟶
        ℋ.obj (op x) => g z) h₁
  have h₂ := Functor.ranObjObjIsoLimit_hom_π (subsiteFunctor f P hPQ).op ℋ (op y)
    (StructuredArrow.mk (Y := op x) (ObjectProperty.homMk (P := Q) a).op)
  simp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self] at h₂
  have h₂' := congrArg (fun g : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y) ⟶
    ℋ.obj (op x) => g s) h₂
  simp only [CategoryTheory.comp_apply] at h₂'
  simp only [ranObjEquiv, Equiv.trans_apply, Iso.toEquiv_fun, Iso.symm_hom, h₁',
    Types.limitEquivSections_symm_apply, pushforwardCostrSectionsEquiv_symm_val,
    indexSectionsEquiv]
  exact h₂'

/-- The comparison of the two right Kan extensions is natural in the presheaf. -/
theorem ranObjEquiv_naturality (η : ℋ ⟶ 𝒢)
    (s : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y)) :
    ranObjEquiv f P hPQ y 𝒢 (((subsiteFunctor f P hPQ).op.ran.map η).app (op y) s) =
      ((P.ι ⋙ f).op.ran.map η).app (op y.obj) (ranObjEquiv f P hPQ y ℋ s) := by
  refine ranObjObj_ext (P.ι ⋙ f) 𝒢 fun x a => ?_
  rw [ranObjEquiv_apply, ranCounit_ran_map_apply, ranCounit_ran_map_apply,
    ranObjEquiv_apply]

end Index

section TwoFibreProduct

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
  {Q : ObjectProperty 𝒴} (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
  (y : Q.FullSubcategory) (ℋ 𝒢 : (P.FullSubcategory)ᵒᵖ ⥤ Type w)
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]

/-- **Stacks 07AU on components.** At an object `T` of the primed 2-fibre product, the section
corresponding to an element of `f'_*ℋ(y)` is obtained by restricting along the comparison arrow
from the `𝒳`-component of `T` to `y` and applying the counit of the right Kan extension
along `f'`. -/
theorem subsitePushforwardSectionsEquiv_apply
    (s : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y))
    (T : primedTwoFibreProduct p𝒳 p𝒴 f P c y) :
    ((Presheaf.globalSectionsEquivSections ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ))
        (subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y ℋ s)).1 (op T) =
      ((subsiteFunctor f P hPQ).op.ranCounit.app ℋ).app
          (op ((primedProjection p𝒳 p𝒴 f P c y).obj T))
        (((subsiteFunctor f P hPQ).op.ran.obj ℋ).map
          (ObjectProperty.homMk (P := Q)
            (T.obj.iso.inv ≫ c.map T.obj.x.hom ⟨y.obj, rfl⟩)).op s) := by
  have hP := Presheaf.pushforwardSectionsEquiv_apply (P.ι ⋙ p𝒳) p𝒴 (P.ι ⋙ f) h𝒴
    (ι_comp_comp_structure_eq p𝒳 p𝒴 f P hf) c ⟨y.obj, rfl⟩ ℋ (ranObjEquiv f P hPQ y ℋ s)
    ((primedToSub p𝒳 p𝒴 f P c y).obj T)
  refine Eq.trans ?_ (ranObjEquiv_apply f P hPQ y ℋ s ((primedProjection p𝒳 p𝒴 f P c y).obj T)
    (T.obj.iso.inv ≫ c.map T.obj.x.hom ⟨y.obj, rfl⟩))
  simp only [subsitePushforwardSectionsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact hP

/-- **Stacks 07AU is natural in the presheaf.** -/
theorem subsitePushforwardSectionsEquiv_naturality (η : ℋ ⟶ 𝒢)
    (s : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y)) :
    subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y 𝒢
        (((subsiteFunctor f P hPQ).op.ran.map η).app (op y) s) =
      subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y ℋ s ≫
        Functor.whiskerLeft (primedProjection p𝒳 p𝒴 f P c y).op η := by
  apply (Presheaf.globalSectionsEquivSections
    ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ 𝒢)).injective
  apply Functor.sections_ext_iff.mpr
  intro T
  rw [subsitePushforwardSectionsEquiv_apply (T := T.unop),
    Presheaf.globalSectionsEquivSections_naturality]
  show _ = ((primedProjection p𝒳 p𝒴 f P c y).op.whiskerLeft η).app T
    (((Presheaf.globalSectionsEquivSections ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ ℋ))
      (subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y ℋ s)).1 T)
  rw [subsitePushforwardSectionsEquiv_apply]
  exact ranCounit_ran_map_apply (subsiteFunctor f P hPQ) ℋ 𝒢 η s _ _

end TwoFibreProduct

end CategoryTheory.SubsitePushforward

namespace AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace FlatFppf

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f) (y : FlatFppf B S hS 𝒴)
  (ℋ 𝒢 : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a)
  [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
    (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension F]
  [∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
    (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F]

/-- **Stacks 07AU on components, the flat-fppf case.** At an object `T` of the primed 2-fibre
product, the section corresponding to an element of `f'_*ℋ(y)` is the restriction of that element
along the comparison arrow from the `𝒳`-component of `T` to `y`, read through the counit of the
right Kan extension along `f'`. -/
theorem primedPushforwardSectionsEquiv_apply
    (s : ((primedSiteFunctor B S hS f hf).op.ran.obj ℋ).obj (op y))
    (T : primedTwoFibreProduct B S hS f y) :
    ((Presheaf.globalSectionsEquivSections ((primedProjection B S hS f y).op ⋙ ℋ))
        (primedPushforwardSectionsEquiv B S hS f hf y ℋ s)).1 (op T) =
      ((primedSiteFunctor B S hS f hf).op.ranCounit.app ℋ).app
          (op ((primedProjection B S hS f y).obj T))
        (((primedSiteFunctor B S hS f hf).op.ran.obj ℋ).map
          (ObjectProperty.homMk (P := flatObject B S hS 𝒴.val)
            (T.obj.iso.inv ≫
              (ambientChoiceOfPullbacks B S hS 𝒴).map T.obj.x.hom ⟨y.obj, rfl⟩)).op s) :=
  SubsitePushforward.subsitePushforwardSectionsEquiv_apply 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ s T

/-- **Stacks 07AU is natural in the presheaf, the flat-fppf case.** -/
theorem primedPushforwardSectionsEquiv_naturality (η : ℋ ⟶ 𝒢)
    (s : ((primedSiteFunctor B S hS f hf).op.ran.obj ℋ).obj (op y)) :
    primedPushforwardSectionsEquiv B S hS f hf y 𝒢
        (((primedSiteFunctor B S hS f hf).op.ran.map η).app (op y) s) =
      primedPushforwardSectionsEquiv B S hS f hf y ℋ s ≫
        Functor.whiskerLeft (primedProjection B S hS f y).op η :=
  SubsitePushforward.subsitePushforwardSectionsEquiv_naturality 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ 𝒢 η s

end FlatFppf

namespace LisseEtale

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f) (y : LisseEtale.{u, w} B S hS 𝒴)
  (ℋ 𝒢 : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a)
  [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
    (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension F]
  [∀ F : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
    (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension F]

/-- **Stacks 07AU on components, the lisse-étale case.** At an object `T` of the primed 2-fibre
product, the section corresponding to an element of `f'_*ℋ(y)` is the restriction of that element
along the comparison arrow from the `𝒳`-component of `T` to `y`, read through the counit of the
right Kan extension along `f'`. -/
theorem primedPushforwardSectionsEquiv_apply
    (s : ((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj ℋ).obj (op y))
    (T : primedTwoFibreProduct B S hS f y) :
    ((Presheaf.globalSectionsEquivSections ((primedProjection B S hS f y).op ⋙ ℋ))
        (primedPushforwardSectionsEquiv B S hS f hf y ℋ s)).1 (op T) =
      ((primedSiteFunctor.{u, w} B S hS f hf).op.ranCounit.app ℋ).app
          (op ((primedProjection B S hS f y).obj T))
        (((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj ℋ).map
          (ObjectProperty.homMk (P := smoothObject.{u, w} B S hS 𝒴)
            (T.obj.iso.inv ≫
              (ambientChoiceOfPullbacks B S hS 𝒴).map T.obj.x.hom ⟨y.obj, rfl⟩)).op s) :=
  SubsitePushforward.subsitePushforwardSectionsEquiv_apply 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ s T

/-- **Stacks 07AU is natural in the presheaf, the lisse-étale case.** -/
theorem primedPushforwardSectionsEquiv_naturality (η : ℋ ⟶ 𝒢)
    (s : ((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj ℋ).obj (op y)) :
    primedPushforwardSectionsEquiv B S hS f hf y 𝒢
        (((primedSiteFunctor.{u, w} B S hS f hf).op.ran.map η).app (op y) s) =
      primedPushforwardSectionsEquiv B S hS f hf y ℋ s ≫
        Functor.whiskerLeft (primedProjection B S hS f y).op η :=
  SubsitePushforward.subsitePushforwardSectionsEquiv_naturality 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) y ℋ 𝒢 η s

end LisseEtale

end AlgebraicGeometry.Stack

end
