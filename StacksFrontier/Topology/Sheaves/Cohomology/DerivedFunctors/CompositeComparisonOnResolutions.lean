module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Reading the composite right-derived comparisons through an arbitrary injective resolution

`CategoryTheory.InjectiveResolution.isoRightDerivedObj` computes `(F.rightDerived n).obj X`
from a given injective resolution of `X`, and Mathlib's
`CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` transports that
computation along a descent of a morphism in *one* resolution variable.  The two comparison
isomorphisms for a composite,

* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso : (L ⋙ G).rightDerived n ≅ L ⋙
  G.rightDerived n`,
  for `L` exact and preserving injective objects, and
* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso :
  F.rightDerived n ⋙ G ≅ H.rightDerived n`, for `G` exact and `e : F ⋙ G ≅ H`,

are both built on the resolutions chosen by `CategoryTheory.injectiveResolution`, and a
statement about either of them involves *two* resolution variables at once.  This file supplies
the simultaneous transport in both variables and specializes it to those two isomorphisms, so
that each can be evaluated against an arbitrary triple rather than only against the chosen
resolutions.

For `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` the triple is `(I, J, φ)` with
  `I` an injective
resolution of `X`, `J` an injective resolution of `L.obj X`, and `φ` a cochain map from the
image of `I` under `L` to `J` descending the identity of `L.obj X`.  For
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` the two resolution variables are two
injective resolutions `I` and `I'` of the same object, used for the two functors `F` and `H`,
together with a cochain map `α : I ⟶ I'` descending the identity.

## Main results

* `isoRightDerivedObj_hom_eq` and `isoRightDerivedObj_inv_eq`: the one-variable transport,
  specialized to two injective resolutions of the *same* object and a descent of the identity.
  This is the only form of Mathlib's naturality lemmas used below.
* `compRightDerivedNatIso_hom_app_comp_isoRightDerivedObj`: **the simultaneous two-variable
  transport**, in the shape of Mathlib's `isoRightDerivedObj_hom_naturality`.
* `compRightDerivedNatIso_hom_app_eq`: the same statement solved for the component of the
  comparison, which is the form a consumer quantifying over `(I, J, φ)` wants, and
  `compRightDerivedNatIso_hom_app_eq_of_desc`: that formula does not depend on the triple.
* `isIso_homologyFunctor_map_of_desc` and `compRightDerivedNatIso_app_eq`: a descent of the
  identity induces an isomorphism on the cohomology of the images under `G`, and the component
  of the comparison factors through `(I, J, φ)` as an isomorphism.
* `compRightDerivedNatIso_hom_app_mapInjRes`: the special case `J =
  Stacks.Cohomology.CompositeRightDerived.mapInjRes L I`
  and `φ = 𝟙`, which reads the comparison off an arbitrary injective resolution of `X` alone.
* `rightDerivedCompIso_hom_app_eq` and `rightDerivedCompIso_hom_app_eq_of_desc`: the
  corresponding statements for `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.

## Implementation notes

No homotopy uniqueness of descents is needed, and in particular neither
`CategoryTheory.InjectiveResolution.descHomotopy` nor its weakening
`CategoryTheory.InjectiveResolution.descHomotopy'` appears: every statement here is an equality
of morphisms, obtained by comparing the given data with the chosen resolutions along *some*
descent of the identity, which exists because `CategoryTheory.InjectiveResolution.desc`
produces one.  This is the same economy as in
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution_eq`.

The hypothesis on `φ` is stated with `L.map (I.ι.f 0)` rather than with
`(Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).ι.f 0`, and the type of `φ` with
`(L.mapHomologicalComplex _).obj I.cocomplex` rather than
`(Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).cocomplex`: the latter spellings are
  definitionally equal to the
former but are distinct `simp` keys, and the unfolded spellings are the ones a consumer can
produce without unfolding `Stacks.Cohomology.CompositeRightDerived.mapInjRes`.
  `mapInjRes_ι_f_zero` records the
comparison of augmentations, which is *not* definitional.

`CategoryTheory.InjectiveResolution.isoRightDerivedObj` has
`(HomologicalComplex.homologyFunctor _ _ n).obj ((F.mapHomologicalComplex _).obj K)` as an
endpoint, whereas a composite such as `L ⋙ G` presents the same object through
`(L ⋙ G).mapHomologicalComplex _`.  The two agree only after unfolding
`CategoryTheory.Functor.comp`, so `Category.assoc` does not fire across the junction — its
pattern demands the same object at the inner and the outer position — and neither do
`rw [Category.assoc]` nor `simp only [Category.assoc]`.  All reassociations below are therefore
built as terms (`Category.assoc _ _ _` and `congrArg` elaborated against a goal stated in the
desired spelling), where elaboration sees the two presentations as equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

/-! ### The one-variable transport along a descent of the identity -/

section OneVariable

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C]
  [HasInjectiveResolutions C] [Abelian D]

/-- **Transport of `CategoryTheory.InjectiveResolution.isoRightDerivedObj` between two
injective resolutions of the same object.**  If `α` descends the identity of `X` from `I` to
`I'`, then the computation of `(F.rightDerived n).obj X` through `I'` is the computation
through `I` followed by `α`.

This is `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` at the identity
morphism; it is stated separately because every transport below is of this form. -/
theorem isoRightDerivedObj_hom_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C}
    (I I' : InjectiveResolution X) (α : I.cocomplex ⟶ I'.cocomplex)
    (comm : I.ι.f 0 ≫ α.f 0 = I'.ι.f 0) :
    (I'.isoRightDerivedObj F n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map α := by
  have h := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 X) I I' α
    (comm.trans (Category.id_comp _).symm) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- The inverse form of `isoRightDerivedObj_hom_eq`: if `α` descends the identity of `X` from
`I` to `I'`, the inverse comparison through `I` is `α` followed by the inverse comparison
through `I'`. -/
theorem isoRightDerivedObj_inv_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C}
    (I I' : InjectiveResolution X) (α : I.cocomplex ⟶ I'.cocomplex)
    (comm : I.ι.f 0 ≫ α.f 0 = I'.ι.f 0) :
    (I.isoRightDerivedObj F n).inv =
      (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map α ≫
        (I'.isoRightDerivedObj F n).inv := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 X) I I' α
    (comm.trans (Category.id_comp _).symm) F n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- Every injective resolution of `X` receives a descent of the identity from the chosen
one. -/
theorem exists_desc_from_injectiveResolution {X : C} (I : InjectiveResolution X) :
    ∃ α : (injectiveResolution X).cocomplex ⟶ I.cocomplex,
      (injectiveResolution X).ι.f 0 ≫ α.f 0 = I.ι.f 0 :=
  ⟨InjectiveResolution.desc (𝟙 X) I (injectiveResolution X),
    (InjectiveResolution.desc_commutes_zero (𝟙 X) I (injectiveResolution X)).trans
      (Category.id_comp _)⟩

end OneVariable

/-! ### The two-variable transport for
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` -/

section Comp

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D] [Abelian E]
  (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The augmentation of the image under `L` of an injective resolution, in degree zero: it is
the image under `L` of the augmentation. -/
theorem mapInjRes_ι_f_zero {X : C} (I : InjectiveResolution X) :
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).ι.f 0 = L.map (I.ι.f 0) := by
  dsimp [Stacks.Cohomology.CompositeRightDerived.mapInjRes]
  simp

/-- The component of `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, read through
  the chosen injective
resolution of `X` and its image under `L`. -/
theorem compRightDerivedNatIso_hom_app (n : ℕ) (X : C) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X =
      ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫
        ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution
          X)).isoRightDerivedObj G n).inv :=
  congrArg (fun g => ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫ g)
    (Category.id_comp
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution
        X)).isoRightDerivedObj G n).inv)

/-- **The simultaneous two-variable transport.**  Let `L` be exact and preserve injective
objects and let `G` be additive.  Given an injective resolution `I` of `X`, an injective
resolution `J` of `L.obj X`, and a cochain map `φ` from the image of `I` under `L` to `J`
descending the identity of `L.obj X`, the comparison
`(L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n` is compatible at `X` with the computations of
its two sides through `I` and through `J`.

This is the shape of `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality`,
but transporting in both resolution variables at once; no compatibility between `I`, `J` and
the chosen resolutions is assumed. -/
theorem compRightDerivedNatIso_hom_app_comp_isoRightDerivedObj (n : ℕ) {X : C}
    (I : InjectiveResolution X) (J : InjectiveResolution (L.obj X))
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (comm : L.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X ≫
      (J.isoRightDerivedObj G n).hom =
      (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ := by
  obtain ⟨α, hα⟩ := exists_desc_from_injectiveResolution I
  have h1 : (Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution X)).ι.f 0 ≫
        ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map α ≫ φ).f 0 =
      L.map ((injectiveResolution X).ι.f 0) ≫ L.map (α.f 0) ≫ φ.f 0 :=
    congrArg (fun g => g ≫ L.map (α.f 0) ≫ φ.f 0)
      (mapInjRes_ι_f_zero L (injectiveResolution X))
  have h2 : L.map ((injectiveResolution X).ι.f 0) ≫ L.map (α.f 0) ≫ φ.f 0 = J.ι.f 0 := by
    rw [← Category.assoc, ← L.map_comp, hα, comm]
  have hψ := h1.trans h2
  have ha := isoRightDerivedObj_hom_eq (L ⋙ G) n (injectiveResolution X) I α hα
  have hb := isoRightDerivedObj_hom_eq G n
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution X)) J
    ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map α ≫ φ) hψ
  rw [compRightDerivedNatIso_hom_app, hb]
  calc (((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫
          ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution
            X)).isoRightDerivedObj G n).inv) ≫
        (((Stacks.Cohomology.CompositeRightDerived.mapInjRes L (injectiveResolution
          X)).isoRightDerivedObj G n).hom ≫
          (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
              ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map α ≫ φ))
      = ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫
          (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
              ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map α ≫ φ) :=
        (Category.assoc _ _ _).trans
          (congrArg
            (fun g => ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫ g)
            (Iso.inv_hom_id_assoc _ _))
    _ = ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫
          ((L ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map α ≫
            (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ :=
        congrArg (fun g => ((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫ g)
          (CategoryTheory.Functor.map_comp _ _ _)
    _ = (((injectiveResolution X).isoRightDerivedObj (L ⋙ G) n).hom ≫
            ((L ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map α) ≫
          (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ :=
        (Category.assoc _ _ _).symm
    _ = (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
          (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ :=
        congrArg
          (fun g => g ≫ (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ) ha.symm

/-- **`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` evaluated against an
  arbitrary triple.**  The
component at `X` of the comparison `(L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n` is the
computation of the source through `I`, the map induced by `φ`, and the inverse of the
computation of the target through `J`. -/
theorem compRightDerivedNatIso_hom_app_eq (n : ℕ) {X : C}
    (I : InjectiveResolution X) (J : InjectiveResolution (L.obj X))
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (comm : L.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X =
      (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ ≫
          (J.isoRightDerivedObj G n).inv :=
  calc (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X
      = (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X ≫
          (J.isoRightDerivedObj G n).hom ≫ (J.isoRightDerivedObj G n).inv := by
        rw [Iso.hom_inv_id, Category.comp_id]
    _ = ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X ≫
          (J.isoRightDerivedObj G n).hom) ≫ (J.isoRightDerivedObj G n).inv :=
        (Category.assoc _ _ _).symm
    _ = ((I.isoRightDerivedObj (L ⋙ G) n).hom ≫
          (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ) ≫
          (J.isoRightDerivedObj G n).inv :=
        congrArg (fun g => g ≫ (J.isoRightDerivedObj G n).inv)
          (compRightDerivedNatIso_hom_app_comp_isoRightDerivedObj L G n I J φ comm)
    _ = _ := Category.assoc _ _ _

/-- A cochain map from the image under `L` of an injective resolution of `X` to an injective
resolution of `L.obj X` descending the identity induces an isomorphism on the degree-`n`
cohomology of the images under `G`.

No homotopy uniqueness is needed: by
`compRightDerivedNatIso_hom_app_comp_isoRightDerivedObj` the induced map is a composite of
isomorphisms. -/
theorem isIso_homologyFunctor_map_of_desc (n : ℕ) {X : C}
    (I : InjectiveResolution X) (J : InjectiveResolution (L.obj X))
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (comm : L.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    IsIso ((G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ) := by
  have h : (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ =
      (I.isoRightDerivedObj (L ⋙ G) n).inv ≫
        ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X ≫
          (J.isoRightDerivedObj G n).hom) :=
    ((Iso.inv_hom_id_assoc _ _).symm).trans
      (congrArg (fun g => (I.isoRightDerivedObj (L ⋙ G) n).inv ≫ g)
        (compRightDerivedNatIso_hom_app_comp_isoRightDerivedObj L G n I J φ comm).symm)
  rw [h]
  infer_instance

/-- **`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` as an isomorphism through an
  arbitrary triple.**
The component at `X` of the comparison is the computation of the source through `I`, the
isomorphism induced by `φ`, and the inverse of the computation of the target through `J`.

The `IsIso` hypothesis is never a real one: it is supplied by
`isIso_homologyFunctor_map_of_desc`, which needs only `comm`. -/
theorem compRightDerivedNatIso_app_eq (n : ℕ) {X : C}
    (I : InjectiveResolution X) (J : InjectiveResolution (L.obj X))
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    [IsIso ((G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ)]
    (comm : L.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).app X =
      I.isoRightDerivedObj (L ⋙ G) n ≪≫
        asIso ((G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ) ≪≫
        (J.isoRightDerivedObj G n).symm :=
  Iso.ext (compRightDerivedNatIso_hom_app_eq L G n I J φ comm)

/-- **`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` on an arbitrary injective
  resolution of `X`.**  If
the resolution of `L.obj X` is taken to be the image of `I` under `L`, the comparison at `X` is
read off from `I` alone: this is `compRightDerivedNatIso_hom_app` with the chosen resolution
replaced by any resolution. -/
theorem compRightDerivedNatIso_hom_app_mapInjRes (n : ℕ) {X : C}
    (I : InjectiveResolution X) :
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n).hom.app X =
      (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L I).isoRightDerivedObj G n).inv := by
  refine Eq.trans (compRightDerivedNatIso_hom_app_eq L G n I
    (Stacks.Cohomology.CompositeRightDerived.mapInjRes L I)
    (𝟙 ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))
    ((Category.comp_id _).trans (mapInjRes_ι_f_zero L I).symm)) ?_
  exact congrArg (fun g => (I.isoRightDerivedObj (L ⋙ G) n).hom ≫ g)
    (((congrArg (fun g => g ≫ ((Stacks.Cohomology.CompositeRightDerived.mapInjRes L
      I).isoRightDerivedObj G n).inv)
      (CategoryTheory.Functor.map_id (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)
        ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)))).trans
      (Category.id_comp _))

/-- **The formula through `(I, J, φ)` does not depend on the triple.**  Any two triples
consisting of an injective resolution of `X`, an injective resolution of `L.obj X` and a
descent of the identity between them compute the same comparison. -/
theorem compRightDerivedNatIso_hom_app_eq_of_desc (n : ℕ) {X : C}
    (I I' : InjectiveResolution X) (J J' : InjectiveResolution (L.obj X))
    (φ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (comm : L.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (φ' : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex ⟶ J'.cocomplex)
    (comm' : L.map (I'.ι.f 0) ≫ φ'.f 0 = J'.ι.f 0) :
    (I.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ ≫
          (J.isoRightDerivedObj G n).inv =
      (I'.isoRightDerivedObj (L ⋙ G) n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map φ' ≫
          (J'.isoRightDerivedObj G n).inv :=
  (compRightDerivedNatIso_hom_app_eq L G n I J φ comm).symm.trans
    (compRightDerivedNatIso_hom_app_eq L G n I' J' φ' comm')

end Comp

/-! ### The transport for `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` -/

section CompIso

variable {A : Type*} {B : Type*} {D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] (e : F ⋙ G ≅ H)

/-- The component of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, read through the
chosen injective resolution. -/
theorem rightDerivedCompIso_hom_app (n : ℕ) (M : A) :
    (ModuleComparison.rightDerivedCompIso F G H e n).hom.app M =
      G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
        (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app
            (injectiveResolution M).cocomplex ≫
          ((injectiveResolution M).isoRightDerivedObj H n).inv :=
  rfl

/-- **`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` evaluated against an arbitrary
injective resolution.**  The component at `M` of the comparison
`F.rightDerived n ⋙ G ≅ H.rightDerived n` may be computed through any injective resolution `I`
of `M`, not only the chosen one. -/
theorem rightDerivedCompIso_hom_app_eq (n : ℕ) {M : A} (I : InjectiveResolution M) :
    (ModuleComparison.rightDerivedCompIso F G H e n).hom.app M =
      G.map (I.isoRightDerivedObj F n).hom ≫
        (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app I.cocomplex ≫
          (I.isoRightDerivedObj H n).inv := by
  obtain ⟨β, hβ⟩ := exists_desc_from_injectiveResolution I
  have ha := isoRightDerivedObj_hom_eq F n (injectiveResolution M) I β hβ
  have hc := isoRightDerivedObj_inv_eq H n (injectiveResolution M) I β hβ
  have hnat := (ModuleComparison.mapComplexHomologyIso F G H e n).hom.naturality β
  rw [rightDerivedCompIso_hom_app, hc, ha,
    CategoryTheory.Functor.map_comp]
  calc G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
        (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app
            (injectiveResolution M).cocomplex ≫
          (H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map β ≫
            (I.isoRightDerivedObj H n).inv
      = G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
          ((ModuleComparison.mapComplexHomologyIso F G H e n).hom.app
              (injectiveResolution M).cocomplex ≫
            (H.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map β) ≫
            (I.isoRightDerivedObj H n).inv :=
        congrArg (fun g => G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫ g)
          (Category.assoc _ _ _).symm
    _ = G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
          (G.map ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map β) ≫
            (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app I.cocomplex) ≫
            (I.isoRightDerivedObj H n).inv :=
        congrArg
          (fun g => G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
            g ≫ (I.isoRightDerivedObj H n).inv) hnat.symm
    _ = (G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫
            G.map ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
              HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map β)) ≫
          (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app I.cocomplex ≫
            (I.isoRightDerivedObj H n).inv :=
        (congrArg (fun g => G.map ((injectiveResolution M).isoRightDerivedObj F n).hom ≫ g)
          (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm

/-- **The two-variable form for `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.**
The comparison at `M` may be read through an injective resolution `I` used for
`F.rightDerived n` and a *different* injective resolution `I'` used for `H.rightDerived n`,
transported along any cochain map `α : I ⟶ I'` descending the identity of `M`. -/
theorem rightDerivedCompIso_hom_app_eq_of_desc (n : ℕ) {M : A}
    (I I' : InjectiveResolution M) (α : I.cocomplex ⟶ I'.cocomplex)
    (comm : I.ι.f 0 ≫ α.f 0 = I'.ι.f 0) :
    (ModuleComparison.rightDerivedCompIso F G H e n).hom.app M =
      G.map (I.isoRightDerivedObj F n).hom ≫
        G.map ((F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map α) ≫
          (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app I'.cocomplex ≫
            (I'.isoRightDerivedObj H n).inv := by
  have hc := isoRightDerivedObj_inv_eq H n I I' α comm
  have hnat := (ModuleComparison.mapComplexHomologyIso F G H e n).hom.naturality α
  rw [rightDerivedCompIso_hom_app_eq F G H e n I, hc]
  exact congrArg (fun g => G.map (I.isoRightDerivedObj F n).hom ≫ g)
    (((Category.assoc _ _ _).symm.trans
        (congrArg (fun g => g ≫ (I'.isoRightDerivedObj H n).inv) hnat.symm)).trans
      (Category.assoc _ _ _))

end CompIso

end Stacks.Cohomology.DerivedCompTransport

end
