module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ProjectiveObjectwise
public import StacksFrontier.Cotangent.SurjectionSiteLocalClaim
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The derived change of coefficients of a presheaf of modules, read on sections

Let `C` be a small category with the chaotic topology, let `a : 𝒪 ⟶ 𝒪'` be a morphism of
presheaves of rings on `C` and let `f : ℳ ⟶ 𝒩` be a morphism of presheaves of `𝒪`-modules.  The
global half of the proof of [Stacks, Tag 08RF] needs to know when the map induced by `f` on the
complexes

`(𝒬_• ⊗_𝒪 𝒪')` ,   `𝒬_•` a projective resolution in `PresheafOfModules 𝒪`,

vanishes on homology; and what the source proves is the corresponding statement **over each
object of the site**, where everything is a statement about honest rings and modules.  This file
is that reduction: the homology of a complex of abelian presheaves is computed objectwise, and
over an object `U` the derived change of coefficients of `𝒪`-modules is the derived change of
coefficients `(-) ⊗_{𝒪(U)} 𝒪'(U)` of `𝒪(U)`-modules, because evaluation at `U` carries a
projective resolution of `ℳ` to a projective resolution of `ℳ(U)`
(`PresheafOfModules.projective_obj`).

## Main results

* `Stacks.ChaoticSite.homologyMap_eq_zero_of_evaluation`: a morphism of complexes of diagrams is
  zero on homology as soon as its evaluations at enough objects are — "enough" being a predicate
  `P` on objects together with a hypothesis that a component-wise vanishing over the objects
  satisfying `P` is a component-wise vanishing.  On the polynomial site, for a surjective
  `A → B`, the objects whose point is `0` are enough
  (`CommAlgCat.app_eq_zero_of_forall_smallSitePoint_eq_zero`).
* `Stacks.ChaoticSite.extendScalarsEvaluationIso`: **extension of scalars commutes with
  evaluation**, `(ℳ ⊗_𝒪 𝒪')(U) = ℳ(U) ⊗_{𝒪(U)} 𝒪'(U)`.  The left adjoint of restriction of
  scalars is identified with the objectwise one of
  `Stacks.NoncommChangeOfRings.Presheaf.extendScalars` by uniqueness of left adjoints.
* `Stacks.ChaoticSite.homologyMap_map_lift_eq_zero_of_objectwise` and its reindexed form
  `Stacks.ChaoticSite.homologyMap_map_hom'_eq_zero_of_objectwise`: **the reduction.** If over
  enough objects `U` the map `L_j((-) ⊗_{𝒪(U)} 𝒪'(U))` of `f(U)` vanishes, then applying
  `(-) ⊗_𝒪 𝒪'` degreewise to a lift of `f` to chosen projective resolutions gives a morphism of
  complexes of abelian presheaves which is zero on `H_j`, respectively on `H^{-j}` of the
  extensions by zero along `ComplexShape.embeddingDownNat`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open StacksDraft.PolynomialLocalComplex (eq_zero_of_comp_iso eq_zero_of_iso_comp_comp_iso
  homologyMap_map_eq_zero mapHomologicalComplexHomologyFunctorIso)

universe u

namespace Stacks.NoncommChangeOfRings

universe v u₁ u₂

/-- **Objectwise extension of scalars is additive**, being a left adjoint
(`Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj`).  The instance is recorded here because
the derived functors of extension of scalars are what the global half of [Stacks, Tag 08RF]
computes with. -/
instance extendScalars_additive {A : Type u₁} {B : Type u₂} [Ring A] [Ring B] (f : A →+* B) :
    (extendScalars.{v} f).Additive :=
  (extendRestrictScalarsAdj.{v} f).left_adjoint_additive

end Stacks.NoncommChangeOfRings

namespace Stacks.ChaoticSite

/-- A morphism is sent to zero by a functor if and only if it is by an isomorphic functor. -/
private theorem map_eq_zero_iff_of_iso {D E : Type*} [Category D] [Category E]
    [HasZeroMorphisms E] {F G : D ⥤ E} (e : F ≅ G) {X Y : D} (φ : X ⟶ Y) :
    F.map φ = 0 ↔ G.map φ = 0 := by
  have h := e.hom.naturality φ
  constructor
  · intro hF
    rw [hF, zero_comp] at h
    exact zero_of_epi_comp (e.hom.app X) h.symm
  · intro hG
    rw [hG, comp_zero] at h
    exact zero_of_comp_mono (e.hom.app Y) h

/-! ### Homology of a complex of diagrams is computed objectwise -/

section Evaluation

variable {J : Type*} [Category* J] {D : Type*} [Category* D] [Abelian D]
  {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex (J ⥤ D) c}

/-- **A morphism of complexes of diagrams which is zero on homology after evaluation at enough
objects is zero on homology.** Evaluation at an object of `J` preserves homology, so its value on
the homology map is the homology map of the evaluated complexes; a morphism of diagrams is zero
as soon as all its components are; and `hdet` says that the objects satisfying `P` are enough to
detect a component-wise vanishing — on the polynomial site, for a surjective `A → B`, the objects
whose point is `0` are (`CommAlgCat.app_eq_zero_of_forall_smallSitePoint_eq_zero`).  Taking
`P := fun _ => True` gives the statement for all objects. -/
theorem homologyMap_eq_zero_of_evaluation (P : J → Prop)
    (hdet : ∀ {F₁ F₂ : J ⥤ D} (α : F₁ ⟶ F₂), (∀ X, P X → α.app X = 0) → ∀ X, α.app X = 0)
    (φ : K ⟶ L) (j : ι)
    (h : ∀ X : J, P X → HomologicalComplex.homologyMap
      ((((evaluation J D).obj X).mapHomologicalComplex c).map φ) j = 0) :
    HomologicalComplex.homologyMap φ j = 0 := by
  have happ : ∀ X : J, P X → (HomologicalComplex.homologyMap φ j).app X = 0 := fun X hX =>
    (map_eq_zero_iff_of_iso (mapHomologicalComplexHomologyFunctorIso
      ((evaluation J D).obj X) c j) φ).1 (h X hX)
  exact NatTrans.ext (funext fun X => by simpa using hdet _ happ X)

end Evaluation

/-! ### Extension of scalars on sections -/

section Sections

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- **Evaluation at an object preserves projective presheaves of modules**: this is
`PresheafOfModules.projective_obj` read as the hypothesis
`CategoryTheory.Functor.PreservesProjectiveObjects` of
`CategoryTheory.Functor.mapProjectiveResolution`. -/
instance evaluation_preservesProjectiveObjects (U : Cᵒᵖ) :
    (PresheafOfModules.evaluation.{u} O U).PreservesProjectiveObjects where
  projective_obj {P} hP := by
    have : CategoryTheory.Projective P := hP
    have : Module.Projective (O.obj U) (P.obj U) := PresheafOfModules.projective_obj P U
    exact inferInstanceAs (CategoryTheory.Projective (P.obj U))

/-- **Extension of scalars commutes with evaluation.** The abstract left adjoint of restriction
of scalars is the objectwise extension of scalars of
`Stacks.NoncommChangeOfRings.Presheaf.extendScalars` — both are left adjoint to restriction of
scalars — and the sections of the latter over `U` are `𝒪'(U) ⊗_{𝒪(U)} ℳ(U)` by construction. -/
def extendScalarsEvaluationIso (U : Cᵒᵖ) :
    extendScalars a ⋙ PresheafOfModules.evaluation.{u} O' U ≅
      PresheafOfModules.evaluation.{u} O U ⋙
        Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom :=
  Functor.isoWhiskerRight
    (Adjunction.leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (PresheafOfModules.restrictScalars.{u} a))
      (Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u} a))
    (PresheafOfModules.evaluation.{u} O' U)

end Sections

/-! ### The reduction of the change of coefficients to the sections -/

section Reduction

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')
  {M N : PresheafOfModules.{u} O} (f : M ⟶ N)

/-- A lift of `f` to the chosen projective resolutions of its source and target, packaged as a
`CategoryTheory.ProjectiveResolution.Hom` so that the comparison with the cochain complexes
indexed by `ℤ` is available. -/
def homOfLift : ProjectiveResolution.Hom (ProjectiveResolution.of M)
    (ProjectiveResolution.of N) f where
  hom := ProjectiveResolution.lift f _ _
  hom_f_zero_comp_π_f_zero := HomologicalComplex.congr_hom
    (ProjectiveResolution.lift_commutes f (ProjectiveResolution.of M)
      (ProjectiveResolution.of N)) 0

/-- The commuting square which exhibits the evaluation of
`Stacks.ChaoticSite.homOfLift` as a lift of `f(U)` to the evaluated projective resolutions. -/
private lemma evaluation_lift_commutes (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (ProjectiveResolution.of M)
            (ProjectiveResolution.of N)) ≫
        ((PresheafOfModules.evaluation.{u} O U).mapProjectiveResolution
          (ProjectiveResolution.of N)).π =
      ((PresheafOfModules.evaluation.{u} O U).mapProjectiveResolution
          (ProjectiveResolution.of M)).π ≫
        (ChainComplex.single₀ (ModuleCat.{u} (O.obj U))).map
          ((PresheafOfModules.evaluation.{u} O U).map f) := by
  show ((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (ProjectiveResolution.of M) (ProjectiveResolution.of N)) ≫
        (((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (ProjectiveResolution.of N).π ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (PresheafOfModules.evaluation.{u} O U) (ComplexShape.down ℕ) 0).hom.app N) =
      (((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (ProjectiveResolution.of M).π ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (PresheafOfModules.evaluation.{u} O U) (ComplexShape.down ℕ) 0).hom.app M) ≫
        (ChainComplex.single₀ (ModuleCat.{u} (O.obj U))).map
          ((PresheafOfModules.evaluation.{u} O U).map f)
  rw [← Category.assoc, ← Functor.map_comp,
    ProjectiveResolution.lift_commutes f (ProjectiveResolution.of M) (ProjectiveResolution.of N),
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (ProjectiveResolution.of M).π ≫ ·)
    ((HomologicalComplex.singleMapHomologicalComplex (PresheafOfModules.evaluation.{u} O U)
      (ComplexShape.down ℕ) 0).hom.naturality f)

/-- **The reduction of the change of coefficients to the sections.** If over every object `U` of
the site the map `L_j((-) ⊗_{𝒪(U)} 𝒪'(U))` induced by `f(U)` vanishes, then the chain map
obtained by applying `(-) ⊗_𝒪 𝒪'` degreewise to a lift of `f` to the chosen projective
resolutions is zero on `H_j`.

Over `U` the two functors agree by `Stacks.ChaoticSite.extendScalarsEvaluationIso`, and
evaluation carries the chosen projective resolution of `ℳ` to a projective resolution of `ℳ(U)`
(`CategoryTheory.Functor.mapProjectiveResolution`, whose hypothesis is
`PresheafOfModules.projective_obj`), so `CategoryTheory.Functor.leftDerived_map_eq` computes
`L_j` of `f(U)` from precisely that chain map. -/
theorem homologyMap_map_lift_eq_zero_of_objectwise (j : ℕ) (P : Cᵒᵖ → Prop)
    (hdet : ∀ {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F₁ ⟶ F₂),
      (∀ U, P U → α.app U = 0) → ∀ U, α.app U = 0)
    (h : ∀ U : Cᵒᵖ, P U →
      ((Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom).leftDerived j).map
        ((PresheafOfModules.evaluation.{u} O U).map f) = 0) :
    HomologicalComplex.homologyMap
      (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (ProjectiveResolution.of M)
          (ProjectiveResolution.of N))) j = 0 := by
  refine homologyMap_eq_zero_of_evaluation P hdet _ j fun U hU => ?_
  -- the vanishing over `U`, on the evaluated resolutions
  have hd := (Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom).leftDerived_map_eq j
    ((PresheafOfModules.evaluation.{u} O U).map f)
    (P := (PresheafOfModules.evaluation.{u} O U).mapProjectiveResolution
      (ProjectiveResolution.of M))
    (Q := (PresheafOfModules.evaluation.{u} O U).mapProjectiveResolution
      (ProjectiveResolution.of N))
    (((PresheafOfModules.evaluation.{u} O U).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (ProjectiveResolution.lift f (ProjectiveResolution.of M) (ProjectiveResolution.of N)))
    (evaluation_lift_commutes f U)
  have key : HomologicalComplex.homologyMap
      ((((PresheafOfModules.evaluation.{u} O U ⋙
          Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom) ⋙
            forget₂ (ModuleCat.{u} (O'.obj U)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (ProjectiveResolution.of M)
          (ProjectiveResolution.of N))) j = 0 :=
    homologyMap_map_eq_zero (forget₂ (ModuleCat.{u} (O'.obj U)) AddCommGrpCat.{u})
      (ComplexShape.down ℕ) j _
      (eq_zero_of_iso_comp_comp_iso _ _ (hd.symm.trans (h U hU)))
  -- transport along the identification of the two functors over `U`
  have E := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (extendScalarsEvaluationIso a U)
        (forget₂ (ModuleCat.{u} (O'.obj U)) AddCommGrpCat.{u})) (ComplexShape.down ℕ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) j)
  exact (map_eq_zero_iff_of_iso E (ProjectiveResolution.lift f (ProjectiveResolution.of M)
    (ProjectiveResolution.of N))).2 key

/-- **The reduction of the change of coefficients to the sections, on the cochain complexes
indexed by `ℤ`.** The same statement as
`Stacks.ChaoticSite.homologyMap_map_lift_eq_zero_of_objectwise` for the extension by zero of the
chosen projective resolutions along `ComplexShape.embeddingDownNat`, which is the shape
`CategoryTheory.ProjectiveResolution.cochainComplex` is in and therefore the shape the global
argument consumes. -/
theorem homologyMap_map_hom'_eq_zero_of_objectwise (j : ℕ) (P : Cᵒᵖ → Prop)
    (hdet : ∀ {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F₁ ⟶ F₂),
      (∀ U, P U → α.app U = 0) → ∀ U, α.app U = 0)
    (h : ∀ U : Cᵒᵖ, P U →
      ((Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom).leftDerived j).map
        ((PresheafOfModules.evaluation.{u} O U).map f) = 0) :
    HomologicalComplex.homologyMap
      (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homOfLift f).hom') (-(j : ℤ)) = 0 := by
  show HomologicalComplex.homologyMap
    (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
      (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap
        (ProjectiveResolution.lift f (ProjectiveResolution.of M) (ProjectiveResolution.of N))
        ComplexShape.embeddingDownNat)) (-(j : ℤ)) = 0
  have hj' : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := by simp
  have h1 := homologyMap_map_lift_eq_zero_of_objectwise a f j P hdet h
  have h2 : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
          (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (ProjectiveResolution.of M)
            (ProjectiveResolution.of N))) ComplexShape.embeddingDownNat) (-(j : ℤ)) = 0 := by
    have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := ((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (ProjectiveResolution.of M) (ProjectiveResolution.of N)))
      (e := ComplexShape.embeddingDownNat) (hj' := hj')
    rw [h1, comp_zero] at hnat
    exact eq_zero_of_comp_iso _ hnat
  have E := Functor.isoWhiskerRight
    (Stacks.DerivedIndexing.mapExtendNatIsoSymm
      (extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O') ComplexShape.embeddingDownNat)
    (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) (-(j : ℤ)))
  exact (map_eq_zero_iff_of_iso E (ProjectiveResolution.lift f (ProjectiveResolution.of M)
    (ProjectiveResolution.of N))).2 h2

end Reduction

end Stacks.ChaoticSite

end
