module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionSystemEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparisonPlain
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeLeftOrthogonal

/-!
# The round trip of two pullbacks along functors of chaotic sites

Let `F₁ : C' ⥤ C` and `F₂ : C ⥤ C'` be functors of categories with the chaotic topology, and let
`φ₁ : g₁^*A → A'` and `φ₂ : g₂^*A' → A` be maps of sheaves of differential graded algebras along
the morphisms of chaotic sites they induce. Over an object `U` of `C` the composite of the two
homomorphisms of section algebras is a homomorphism `A(F₁ F₂ U) ⟶ A'(F₂ U) ⟶ A(U)`. Suppose given
a natural transformation `η : F₂.op ⋙ F₁.op ⟶ 𝟭`, that is morphisms `U ⟶ F₁ F₂ U`, such that this
composite is the restriction homomorphism along `η_U`. For an inverse system of differential
graded algebras indexed by a preorder, this is the situation of two representatives of morphisms
of pro-objects whose composite is a transition map.

The round trip `g₂^* g₁^* M` of a right differential graded `A`-module then has sections
`(M(F₁ F₂ U) ⊗_{A(F₁ F₂ U)} A'(F₂ U)) ⊗_{A'(F₂ U)} A(U)` over `U`, and the maps
`(x ⊗ b) ⊗ c ↦ x|_U · φ₂(b) · c` assemble into a homomorphism `g₂^* g₁^* M ⟶ M`, natural in `M`:
`SheafOfModules.DifferentialGradedModule.roundTripCounit`. Over `U` it is, up to the
identification `(X ⊗ A'(F₂ U)) ⊗ A(U) ≅ X ⊗ A(U)` of iterated extension of scalars with extension
along the composite, the comparison map `M(F₁ F₂ U) ⊗_{A(F₁ F₂ U)} A(U) ⟶ M(U)` of
quasi-coherence along `η_U`. Hence it is a quasi-isomorphism at every module with K-projective
sections satisfying the quasi-coherence condition.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.roundTripInner`: the homomorphism
  `M(F₁ F₂ U) ⊗ A'(F₂ U) ⟶ M(U)`, `x ⊗ b ↦ x|_U · φ₂(b)`.
* `SheafOfModules.DifferentialGradedModule.roundTripSystemHom`: the morphism of presheaves of
  section modules from the round trip to `Σ M`.
* `SheafOfModules.DifferentialGradedModule.roundTripCounit`: **the canonical map
  `g₂^* g₁^* M ⟶ M`**, natural in `M`.

## Main results

* `SheafOfModules.DifferentialGradedModule.sectionMap_roundTripCounit`: over `U` the canonical
  map is the comparison map of quasi-coherence along `η_U`, read through the identifications of
  its source.
* `SheafOfModules.DifferentialGradedModule.quasiIso_roundTripCounit_app`: the canonical map is a
  quasi-isomorphism at a module with K-projective sections satisfying the quasi-coherence
  condition.

## References

* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u v' u'

namespace DifferentialGraded.Bimodule

open _root_.DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **The plain transpose on an arbitrary pure tensor**: `g^♯ (x ⊗ b) = g(x) · b`. -/
theorem plainTranspose_pure_apply (ψ : A.Hom B) {X : DifferentialGradedModule.{u, u, u} A}
    {Y : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor ψ).obj Y)
    (x : X.M) (b : B.A) :
    (plainTranspose ψ g).toFun ((tensorPure (regular ψ) X).toLinearMap x b) =
      @HSMul.hSMul B.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op b) (g.toFun x) := by
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero =>
    have h0 : (tensorPure (regular ψ) X).toLinearMap 0 b = 0 := by
      rw [map_zero]
      rfl
    exact (congrArg (plainTranspose ψ g).toFun h0).trans
      ((map_zero _).trans ((smul_zero _).symm.trans (congrArg _ (map_zero g.toFun).symm)))
  | add x y hx hy =>
    have h1 : (tensorPure (regular ψ) X).toLinearMap (x + y) b =
        (tensorPure (regular ψ) X).toLinearMap x b +
          (tensorPure (regular ψ) X).toLinearMap y b := by
      rw [map_add]
      rfl
    exact (congrArg (plainTranspose ψ g).toFun h1).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
        ((smul_add _ _ _).symm.trans (congrArg _ (map_add g.toFun x y).symm))))
  | @homogeneous p x => exact plainTranspose_pure ψ g p x b

variable {C : DifferentialGradedAlgebra.{u, u} R} (ψ₁ : A.Hom B) (ψ₂ : B.Hom C) (κ : A.Hom C)
  (h : ∀ a, ψ₂.toAlgebraHom (ψ₁.toAlgebraHom a) = κ.toAlgebraHom a)
  {X : DifferentialGradedModule.{u, u, u} A} {Y : DifferentialGradedModule.{u, u, u} C}

/-- **Transposing twice is transposing along the composite**: for `g : X ⟶ Y_A`, read over `A`
through `κ = ψ₂ ∘ ψ₁`, the transpose along `ψ₂` of the transpose along `ψ₁` of `g` is, after the
identification `X ⊗_A C ≅ (X ⊗_A B) ⊗_B C`, the transpose of `g` along `κ`. -/
theorem compIso_hom_plainTranspose_plainTranspose (g : X ⟶ (restrictScalarsFunctor κ).obj Y) :
    (compIso ψ₁ ψ₂ κ h X).hom ≫ plainTranspose ψ₂ (plainTranspose ψ₁
      (g ≫ restrictScalarsCongr (ψ' := ψ₂.comp ψ₁) (fun a => (h a).symm) Y)) =
      plainTranspose κ g := by
  refine tensorObj_hom_ext' (regular κ) X _ _ fun x c => ?_
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero => rw [LinearMap.map_zero₂, map_zero, map_zero]
  | add x y hx hy => rw [LinearMap.map_add₂, map_add, map_add, hx, hy]
  | @homogeneous p x =>
    show (plainTranspose ψ₂ _).toFun ((compForward ψ₁ ψ₂ κ h X).toFun _) = _
    rw [compForward_pure ψ₁ ψ₂ κ h X p x c]
    refine (plainTranspose_pure_apply ψ₂ _ _ c).trans ?_
    refine Eq.trans ?_ (plainTranspose_pure_apply κ g _ c).symm
    rw [plainTranspose_pure_apply, MulOpposite.op_one]
    exact congrArg (fun w => @HSMul.hSMul C.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op (show C.A from c)) w)
      (one_smul B.Aᵐᵒᵖ (show ((restrictScalarsFunctor ψ₂).obj Y).M from g.toFun x))

end DifferentialGraded.Bimodule

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {C' : Type u'} [Category.{v'} C']
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{t}}
  {F₁ : C' ⥤ C} {F₂ : C ⥤ C'}
  {σ₁ : F₁.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {σ₂ : F₂.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj}
  {A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ₁ : DifferentialGradedAlgebra.InverseImageHom F₁ σ₁ A A')
  (φ₂ : DifferentialGradedAlgebra.InverseImageHom F₂ σ₂ A' A)
  (η : F₂.op ⋙ F₁.op ⟶ 𝟭 Cᵒᵖ)
  (hη : ∀ (U : Cᵒᵖ) (b : (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U))).A),
    (φ₂.sectionHom U).toAlgebraHom ((φ₁.sectionHom (F₂.op.obj U)).toAlgebraHom b) =
      (A.sectionRestriction (η.app U)).toAlgebraHom b)

/-- Two composites of additive maps out of a relative tensor product agree at every element if
they agree on pure tensors. -/
private theorem tensorObj_comp_apply_eq {B B' : _root_.DifferentialGradedAlgebra (ULift.{m} ℤ)}
    (N : DifferentialGraded.Bimodule B B') (X : _root_.DifferentialGradedModule.{m, m, m} B)
    {P₁ P₂ Q : Type*} [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup Q] (s : P₁ →+ Q)
    (a : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M →+ P₁) (c : P₂ →+ Q)
    (b : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M →+ P₂)
    (w : ((DifferentialGraded.Bimodule.tensorDGFunctor N).functor.obj X).M)
    (h : ∀ (x : X.M) (y : N.rightModule.M),
      s (a (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y)) =
        c (b (((DifferentialGraded.Bimodule.tensorDGFunctor N).pure X).toLinearMap x y))) :
    s (a w) = c (b w) :=
  DFunLike.congr_fun (tensorObj_addHom_ext N X (s.comp a) (c.comp b) h) w

/-! ### The inner map `M(F₁ F₂ U) ⊗ A'(F₂ U) ⟶ M(U)` -/

/-- The homomorphism `M(F₁ F₂ U) ⊗_{A(F₁ F₂ U)} A'(F₂ U) ⟶ M(U)`, `x ⊗ b ↦ x|_U · φ₂(b)`, of
differential graded `A'(F₂ U)`-modules, `M(U)` being read through `φ₂`. It is the transpose of
restriction of sections along `η_U`, which is linear over `A(F₁ F₂ U)` because the composite of
the two homomorphisms of section algebras is the restriction homomorphism. -/
def roundTripInner (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    pullbackSections φ₁ M (F₂.op.obj U) ⟶
      _root_.DifferentialGradedModule.restrictScalars (φ₂.sectionHom U) (M.sectionModule U) :=
  DifferentialGraded.Bimodule.plainTranspose (φ₁.sectionHom (F₂.op.obj U))
    (M.sectionModuleRestriction (η.app U) ≫
      DifferentialGraded.Bimodule.restrictScalarsCongr
        (ψ' := (φ₂.sectionHom U).comp (φ₁.sectionHom (F₂.op.obj U))) (fun b => (hη U b).symm) _)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The inner map sends `x ⊗ b` to `x|_U · φ₂(b)`. -/
theorem roundTripInner_pure (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ)
    (x : (M.sectionModule (F₁.op.obj (F₂.op.obj U))).M)
    (b : (pullbackBimodule φ₁ (F₂.op.obj U)).rightModule.M) :
    (roundTripInner φ₁ φ₂ η hη M U).toFun (pullbackPure φ₁ M (F₂.op.obj U) x b) =
      MulOpposite.op ((φ₂.sectionHom U).toAlgebraHom (algElt φ₁ (F₂.op.obj U) b)) •
        (show (M.sectionModule U).M from (M.sectionModuleRestriction (η.app U)).toFun x) :=
  DifferentialGraded.Bimodule.plainTranspose_pure_apply _ _ x b

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The inner maps commute with restriction of sections. -/
theorem roundTripInner_naturality (M : DifferentialGradedModule.{t, m, m} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) (w : (pullbackSections φ₁ M (F₂.op.obj V)).M) :
    M.sectionRestrictAdd a ((roundTripInner φ₁ φ₂ η hη M V).toFun w) =
      (roundTripInner φ₁ φ₂ η hη M U).toFun ((pullbackRestr φ₁ M (F₂.op.map a)).toFun w) := by
  refine tensorObj_comp_apply_eq _ _ (M.sectionRestrictAdd a)
    (roundTripInner φ₁ φ₂ η hη M V).toFun.toAddMonoidHom
    (roundTripInner φ₁ φ₂ η hη M U).toFun.toAddMonoidHom
    (pullbackRestr φ₁ M (F₂.op.map a)).toFun.toAddMonoidHom w fun x y => ?_
  show M.sectionRestrictAdd a ((roundTripInner φ₁ φ₂ η hη M V).toFun
      (pullbackPure φ₁ M (F₂.op.obj V) x y)) =
    (roundTripInner φ₁ φ₂ η hη M U).toFun ((pullbackRestr φ₁ M (F₂.op.map a)).toFun
      (pullbackPure φ₁ M (F₂.op.obj V) x y))
  rw [pullbackRestr_pure φ₁ M (F₂.op.map a) x y, roundTripInner_pure φ₁ φ₂ η hη M V x y,
    roundTripInner_pure φ₁ φ₂ η hη M U]
  have h1 := (M.sectionModuleRestriction a).map_smul
    ((M.sectionModuleRestriction (η.app V)).toFun x)
    ((φ₂.sectionHom V).toAlgebraHom (algElt φ₁ (F₂.op.obj V) y))
  refine h1.trans (congrArg₂ (fun (b : (A.sectionAlgebra U).A) (z : (M.sectionModule U).M) =>
    MulOpposite.op b • z) ?_ ?_)
  · exact (φ₂.sectionHom_sectionRestriction a _).symm
  · exact (sectionRestrictAdd_comp M a (η.app V) x).symm.trans
      ((congrArg (fun f => M.sectionRestrictAdd f x) (η.naturality a).symm).trans
        (sectionRestrictAdd_comp M (η.app U) (F₁.op.map (F₂.op.map a)) x))

/-! ### The canonical map of the round trip -/

/-- The homomorphism `(g₁^*M)(F₂ U) ⟶ M(U)` read over `A'(F₂ U)`: the inner map, after the
identification of the sections of the pullback. -/
def roundTripOuter (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    ((pullbackFunctor φ₁).obj M).sectionModule (F₂.op.obj U) ⟶
      _root_.DifferentialGradedModule.restrictScalars (φ₂.sectionHom U) (M.sectionModule U) :=
  (pullbackSectionsIso φ₁ M (F₂.op.obj U)).hom ≫ roundTripInner φ₁ φ₂ η hη M U

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The maps `roundTripOuter` commute with restriction of sections. -/
theorem roundTripOuter_naturality (M : DifferentialGradedModule.{t, m, m} A) {U V : Cᵒᵖ}
    (a : V ⟶ U) (z : (((pullbackFunctor φ₁).obj M).sectionModule (F₂.op.obj V)).M) :
    M.sectionRestrictAdd a ((roundTripOuter φ₁ φ₂ η hη M V).toFun z) =
      (roundTripOuter φ₁ φ₂ η hη M U).toFun
        (((pullbackFunctor φ₁).obj M).sectionRestrictAdd (F₂.op.map a) z) := by
  have hs := congrArg (fun g => g.toFun z)
    ((pullbackSystem φ₁ M).sectionModuleRestriction_sectionsIso (F₂.op.map a))
  refine (roundTripInner_naturality φ₁ φ₂ η hη M a _).trans ?_
  exact congrArg (roundTripInner φ₁ φ₂ η hη M U).toFun hs.symm

/-- The homomorphism `(g₁^*M)(F₂ U) ⊗_{A'(F₂ U)} A(U) ⟶ M(U)` of differential graded
`A(U)`-modules, `z ⊗ c ↦ r(z) · c`: the sections over `U` of the canonical map of the round
trip. -/
def roundTripSections (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    pullbackSections φ₂ ((pullbackFunctor φ₁).obj M) U ⟶ M.sectionModule U :=
  DifferentialGraded.Bimodule.plainTranspose (φ₂.sectionHom U) (roundTripOuter φ₁ φ₂ η hη M U)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The map `roundTripSections` sends `z ⊗ c` to `r(z) · c`, where `r` is `roundTripOuter`. -/
theorem roundTripSections_pure (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ)
    (z : (((pullbackFunctor φ₁).obj M).sectionModule (F₂.op.obj U)).M)
    (c : (pullbackBimodule φ₂ U).rightModule.M) :
    (roundTripSections φ₁ φ₂ η hη M U).toFun (pullbackPure φ₂ ((pullbackFunctor φ₁).obj M) U z c) =
      MulOpposite.op (algElt φ₂ U c) •
        (show (M.sectionModule U).M from (roundTripOuter φ₁ φ₂ η hη M U).toFun z) :=
  DifferentialGraded.Bimodule.plainTranspose_pure_apply _ _ z c

/-- **The canonical map of the round trip, on presheaves of section modules.** -/
def roundTripSystemHom (M : DifferentialGradedModule.{t, m, m} A) :
    pullbackSystem φ₂ ((pullbackFunctor φ₁).obj M) ⟶ (sectionSystemFunctor A).obj M where
  app U := roundTripSections φ₁ φ₂ η hη M U
  naturality {U V} a w := by
    have key : (M.sectionRestrictAdd a).comp
        (roundTripSections φ₁ φ₂ η hη M V).toFun.toAddMonoidHom =
        (roundTripSections φ₁ φ₂ η hη M U).toFun.toAddMonoidHom.comp
          (pullbackRestr φ₂ ((pullbackFunctor φ₁).obj M) a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext _ _ _ _ fun z c => ?_
      change M.sectionRestrictAdd a ((roundTripSections φ₁ φ₂ η hη M V).toFun
          (pullbackPure φ₂ ((pullbackFunctor φ₁).obj M) V z c)) =
        (roundTripSections φ₁ φ₂ η hη M U).toFun
          ((pullbackRestr φ₂ ((pullbackFunctor φ₁).obj M) a).toFun
            (pullbackPure φ₂ ((pullbackFunctor φ₁).obj M) V z c))
      rw [pullbackRestr_pure φ₂ ((pullbackFunctor φ₁).obj M) a z c,
        roundTripSections_pure φ₁ φ₂ η hη M V z c, roundTripSections_pure φ₁ φ₂ η hη M U]
      have h1 := (M.sectionModuleRestriction a).map_smul
        ((roundTripOuter φ₁ φ₂ η hη M V).toFun z) (algElt φ₂ V c)
      exact h1.trans (congrArg (fun w : (M.sectionModule U).M => MulOpposite.op
        ((A.sectionRestriction a).toAlgebraHom (algElt φ₂ V c)) • w)
        (roundTripOuter_naturality φ₁ φ₂ η hη M a z))
    exact DFunLike.congr_fun key w

/-! ### Naturality in the module -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The inner maps are natural in the module `M`. -/
theorem roundTripInner_natural {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N)
    (U : Cᵒᵖ) (w : (pullbackSections φ₁ M (F₂.op.obj U)).M) :
    sectionMapAdd f U ((roundTripInner φ₁ φ₂ η hη M U).toFun w) =
      (roundTripInner φ₁ φ₂ η hη N U).toFun ((pullbackSectionsMap φ₁ f (F₂.op.obj U)).toFun w) := by
  refine tensorObj_comp_apply_eq _ _ (sectionMapAdd f U)
    (roundTripInner φ₁ φ₂ η hη M U).toFun.toAddMonoidHom
    (roundTripInner φ₁ φ₂ η hη N U).toFun.toAddMonoidHom
    (pullbackSectionsMap φ₁ f (F₂.op.obj U)).toFun.toAddMonoidHom w fun x y => ?_
  show sectionMapAdd f U ((roundTripInner φ₁ φ₂ η hη M U).toFun
      (pullbackPure φ₁ M (F₂.op.obj U) x y)) =
    (roundTripInner φ₁ φ₂ η hη N U).toFun ((pullbackSectionsMap φ₁ f (F₂.op.obj U)).toFun
      (pullbackPure φ₁ M (F₂.op.obj U) x y))
  rw [pullbackSectionsMap_pure φ₁ f (F₂.op.obj U) x y, roundTripInner_pure φ₁ φ₂ η hη M U x y,
    roundTripInner_pure φ₁ φ₂ η hη N U]
  exact ((sectionMap f U).map_smul _ _).trans (congrArg (fun z : (N.sectionModule U).M =>
    MulOpposite.op ((φ₂.sectionHom U).toAlgebraHom (algElt φ₁ (F₂.op.obj U) y)) • z)
    (sectionRestrictAdd_sectionMapAdd f (η.app U) x).symm)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The maps `roundTripOuter` are natural in the module `M`. -/
theorem roundTripOuter_natural {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N)
    (U : Cᵒᵖ) (z : (((pullbackFunctor φ₁).obj M).sectionModule (F₂.op.obj U)).M) :
    sectionMapAdd f U ((roundTripOuter φ₁ φ₂ η hη M U).toFun z) =
      (roundTripOuter φ₁ φ₂ η hη N U).toFun
        (sectionMapAdd ((pullbackFunctor φ₁).map f) (F₂.op.obj U) z) := by
  have hs := congrArg (fun g => g.toFun z)
    (SectionSystem.sectionsIso_naturality (pullbackSystemMap φ₁ f) (F₂.op.obj U))
  refine (roundTripInner_natural φ₁ φ₂ η hη f U _).trans ?_
  exact congrArg (roundTripInner φ₁ φ₂ η hη N U).toFun hs.symm

/-- The canonical maps of the round trip on presheaves of section modules are natural. -/
theorem roundTripSystemHom_naturality {M N : DifferentialGradedModule.{t, m, m} A} (f : M ⟶ N) :
    roundTripSystemHom φ₁ φ₂ η hη M ≫ (sectionSystemFunctor A).map f =
      pullbackSystemMap φ₂ ((pullbackFunctor φ₁).map f) ≫ roundTripSystemHom φ₁ φ₂ η hη N := by
  refine SectionSystem.hom_ext fun U => ?_
  refine DifferentialGraded.Bimodule.tensorObj_hom_ext' _ _ _ _ fun z c => ?_
  show sectionMapAdd f U ((roundTripSections φ₁ φ₂ η hη M U).toFun
      (pullbackPure φ₂ ((pullbackFunctor φ₁).obj M) U z c)) =
    (roundTripSections φ₁ φ₂ η hη N U).toFun
      ((pullbackSectionsMap φ₂ ((pullbackFunctor φ₁).map f) U).toFun
        (pullbackPure φ₂ ((pullbackFunctor φ₁).obj M) U z c))
  rw [pullbackSectionsMap_pure φ₂ ((pullbackFunctor φ₁).map f) U z c,
    roundTripSections_pure φ₁ φ₂ η hη M U z c, roundTripSections_pure φ₁ φ₂ η hη N U]
  exact ((sectionMap f U).map_smul _ _).trans (congrArg (fun w : (N.sectionModule U).M =>
    MulOpposite.op (algElt φ₂ U c) • w) (roundTripOuter_natural φ₁ φ₂ η hη f U z))

/-- **The canonical map `g₂^* g₁^* M ⟶ M` of the round trip**, natural in `M`: the morphism out of
the realization determined by the maps `(x ⊗ b) ⊗ c ↦ x|_U · φ₂(b) · c` on sections. -/
def roundTripCounit :
    pullbackFunctor φ₁ ⋙ pullbackFunctor φ₂ ⟶ 𝟭 (DifferentialGradedModule.{t, m, m} A) where
  app M := ((SectionSystem.realizeAdjunction A).homEquiv _ _).symm (roundTripSystemHom φ₁ φ₂ η hη M)
  naturality M N f := by
    change (SectionSystem.realizeFunctor A).map
          (pullbackSystemMap φ₂ ((pullbackFunctor φ₁).map f)) ≫
        ((SectionSystem.realizeAdjunction A).homEquiv _ _).symm (roundTripSystemHom φ₁ φ₂ η hη N) =
      ((SectionSystem.realizeAdjunction A).homEquiv _ _).symm (roundTripSystemHom φ₁ φ₂ η hη M) ≫ f
    exact ((SectionSystem.realizeAdjunction A).homEquiv_naturality_left_symm _ _).symm.trans
      ((congrArg (fun g => ((SectionSystem.realizeAdjunction A).homEquiv _ _).symm g)
        (roundTripSystemHom_naturality φ₁ φ₂ η hη f).symm).trans
        ((SectionSystem.realizeAdjunction A).homEquiv_naturality_right_symm _ _))

/-- **Over `U` the canonical map of the round trip is the map `z ⊗ c ↦ r(z) · c`**, after the
identification of the sections of the realization. -/
theorem sectionMap_roundTripCounit (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    sectionMap ((roundTripCounit φ₁ φ₂ η hη).app M) U =
      ((pullbackSystem φ₂ ((pullbackFunctor φ₁).obj M)).sectionsIso U).hom ≫
        (roundTripSystemHom φ₁ φ₂ η hη M).app U := by
  have h := SectionSystem.realizeAdjunction_homEquiv_apply
    (((SectionSystem.realizeAdjunction A).homEquiv _ _).symm (roundTripSystemHom φ₁ φ₂ η hη M))
  rw [Equiv.apply_symm_apply (e := (SectionSystem.realizeAdjunction A).homEquiv _ _)] at h
  have hU : (roundTripSystemHom φ₁ φ₂ η hη M).app U =
      ((pullbackSystem φ₂ ((pullbackFunctor φ₁).obj M)).sectionsIso U).inv ≫
        sectionMap ((roundTripCounit φ₁ φ₂ η hη).app M) U :=
    congrArg (fun g => SectionSystem.Hom.app g U) h
  exact (Iso.inv_comp_eq _).1 hU.symm

/-! ### The canonical map is a quasi-isomorphism on quasi-coherent modules -/

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- **Over `U` the canonical map of the round trip is the comparison map of quasi-coherence along
`η_U`**, up to the identification `M(F₁ F₂ U) ⊗ A(U) ≅ (M(F₁ F₂ U) ⊗ A'(F₂ U)) ⊗ A(U)` and the
identification of the sections of the pullback. -/
theorem roundTripSections_comparison (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ) :
    (DifferentialGraded.Bimodule.compIso (φ₁.sectionHom (F₂.op.obj U)) (φ₂.sectionHom U)
        (A.sectionRestriction (η.app U)) (hη U) (M.sectionModule (F₁.op.obj (F₂.op.obj U)))).hom ≫
      (DifferentialGraded.Bimodule.tensorCompFunctor
          (DifferentialGraded.Bimodule.regular (φ₂.sectionHom U))).map
        (pullbackSectionsIso φ₁ M (F₂.op.obj U)).inv ≫
      roundTripSections φ₁ φ₂ η hη M U =
    Chaotic.plainSectionComparison M (η.app U) := by
  have h1 : (DifferentialGraded.Bimodule.tensorCompFunctor
          (DifferentialGraded.Bimodule.regular (φ₂.sectionHom U))).map
        (pullbackSectionsIso φ₁ M (F₂.op.obj U)).inv ≫ roundTripSections φ₁ φ₂ η hη M U =
      DifferentialGraded.Bimodule.plainTranspose (φ₂.sectionHom U)
        (roundTripInner φ₁ φ₂ η hη M U) := by
    refine ((DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars
      (φ₂.sectionHom U)).homEquiv_naturality_left_symm _ _).symm.trans ?_
    exact congrArg (fun g => ((DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars
      (φ₂.sectionHom U)).homEquiv _ _).symm g) (Iso.inv_hom_id_assoc _ _)
  refine (congrArg (fun g => (DifferentialGraded.Bimodule.compIso (φ₁.sectionHom (F₂.op.obj U))
    (φ₂.sectionHom U) (A.sectionRestriction (η.app U)) (hη U)
      (M.sectionModule (F₁.op.obj (F₂.op.obj U)))).hom ≫ g) h1).trans ?_
  exact DifferentialGraded.Bimodule.compIso_hom_plainTranspose_plainTranspose _ _ _ (hη U) _

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- **The canonical map of the round trip is a quasi-isomorphism on sections over `U`** at a
module satisfying the quasi-coherence condition whose sections over `F₁ F₂ U` are K-projective. -/
theorem quasiIso_roundTripSections (M : DifferentialGradedModule.{t, m, m} A) (U : Cᵒᵖ)
    (hM : (_root_.DifferentialGradedModule.acyclic'
      (A.sectionAlgebra (F₁.op.obj (F₂.op.obj U)))).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
          (M.sectionModule (F₁.op.obj (F₂.op.obj U)))))
    (hQC : Chaotic.IsQCModule M) :
    QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex (A.sectionAlgebra U)).map
      (roundTripSections φ₁ φ₂ η hη M U)) := by
  have hq := (Chaotic.isIso_sectionComparison_iff_quasiIso M (η.app U) hM).1 (hQC (η.app U))
  let e := DifferentialGraded.Bimodule.compIso (φ₁.sectionHom (F₂.op.obj U)) (φ₂.sectionHom U)
      (A.sectionRestriction (η.app U)) (hη U) (M.sectionModule (F₁.op.obj (F₂.op.obj U))) ≪≫
    (DifferentialGraded.Bimodule.tensorCompFunctor
        (DifferentialGraded.Bimodule.regular (φ₂.sectionHom U))).mapIso
      (pullbackSectionsIso φ₁ M (F₂.op.obj U)).symm
  have w : Arrow.mk (Chaotic.plainSectionComparison M (η.app U)) ≅
      Arrow.mk (roundTripSections φ₁ φ₂ η hη M U) :=
    Arrow.isoMk e (Iso.refl _) (by
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
      exact (Category.assoc _ _ _).trans (roundTripSections_comparison φ₁ φ₂ η hη M U))
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((_root_.DifferentialGradedModule.forgetToCochainComplex (A.sectionAlgebra U)).mapArrow.mapIso
      w)).1 hq

end SheafOfModules.DifferentialGradedModule
