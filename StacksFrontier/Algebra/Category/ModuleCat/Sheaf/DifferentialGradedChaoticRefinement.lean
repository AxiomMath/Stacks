module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRoundTripDerived

/-!
# Refining the reindexing of a derived pullback along a chaotic site

Let `F, F' : C' ⥤ C` be functors of categories with the chaotic topology together with a natural
transformation `τ : F'.op ⟶ F.op`, that is morphisms `F U' ⟶ F' U'` of `C`, and let
`φ : g^*A → A'` and `φ' : g'^*A → A'` be maps of sheaves of differential graded algebras along
the induced morphisms of chaotic sites such that `φ'` is `φ` precomposed with restriction along
`τ`: over `U'` the homomorphism `A(F' U') ⟶ A'(U')` is `A(F' U') ⟶ A(F U') ⟶ A'(U')`. For inverse
systems indexed by a preorder this is the passage from a representative `(m, a)` of a morphism of
pro-objects to the representative `(m', a')` with `m' ≥ m` and `a'_i : X_{m'(i)} → X_{m(i)} → Y_i`,
which defines the same morphism of pro-objects (Categories, Example 4.22.6).

The maps `x ⊗ b ↦ x|_{F U'} ⊗ b` from `M(F' U') ⊗_{A(F' U')} A'(U')` to
`M(F U') ⊗_{A(F U')} A'(U')` assemble into a natural homomorphism `g'^*M ⟶ g^*M`. Over `U'` it is,
up to the identification `M(F' U') ⊗ A'(U') ≅ (M(F' U') ⊗ A(F U')) ⊗ A'(U')`, the comparison map of
quasi-coherence along `τ_{U'}` tensored with `A'(U')`, so it is a quasi-isomorphism at a module
with K-projective sections satisfying the quasi-coherence condition. The induced transformation
`Lg'^* ⟶ Lg^*` of derived pullbacks is therefore invertible on `QC(A, d)`, and the two functors
`QC(A, d) ⥤ QC(A', d)` induced by the two representatives are isomorphic.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.refineSections`: the map
  `M(F' U') ⊗ A'(U') ⟶ M(F U') ⊗ A'(U')`, `x ⊗ b ↦ x|_{F U'} ⊗ b`.
* `SheafOfModules.DifferentialGradedModule.refineCounit`: the natural homomorphism
  `g'^*M ⟶ g^*M`.
* `SheafOfModules.DifferentialGradedModule.refineDerived`: the induced transformation
  `Lg'^* ⟶ Lg^*` of derived pullbacks.
* `SheafOfModules.DifferentialGradedModule.chaoticQCPullbackRefineIso`: **the two functors
  `QC(A, d) ⥤ QC(A', d)` are isomorphic.**

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_refineSections`: the map is a
  quasi-isomorphism on sections at a module with K-projective sections satisfying the
  quasi-coherence condition.
* `SheafOfModules.DifferentialGradedModule.isIso_refineDerived_app`: the transformation of
  derived pullbacks is invertible on `QC(A, d)`.

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Example 4.22.6 (Tag 05PY)](https://stacks.math.columbia.edu/tag/05PY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe m u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra
  Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C']
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {Osharp' : Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{u}}
  {F F' : C' ⥤ C}
  {σ : F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {σ' : F'.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp').obj}
  {A : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
  {A' : DifferentialGradedAlgebra.{u, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp')}
  (φ : DifferentialGradedAlgebra.InverseImageHom F σ A A')
  (φ' : DifferentialGradedAlgebra.InverseImageHom F' σ' A A')
  (τ : F'.op ⟶ F.op)
  (hτ : ∀ (U' : C'ᵒᵖ) (b : (A.sectionAlgebra (F'.op.obj U')).A),
    (φ.sectionHom U').toAlgebraHom ((A.sectionRestriction (τ.app U')).toAlgebraHom b) =
      (φ'.sectionHom U').toAlgebraHom b)

/-- The homomorphism `M(F' U') ⟶ M(F U') ⊗_{A(F U')} A'(U')`, `x ↦ x|_{F U'} ⊗ 1`, linear over
`A(F' U')` acting through `φ'`. -/
def refineUnit (M : DifferentialGradedModule.{u, m, m} A) (U' : C'ᵒᵖ) :
    M.sectionModule (F'.op.obj U') ⟶
      _root_.DifferentialGradedModule.restrictScalars (φ'.sectionHom U')
        (pullbackSections φ M U') :=
  M.sectionModuleRestriction (τ.app U') ≫
    (_root_.DifferentialGradedModule.restrictScalarsFunctor (A.sectionRestriction (τ.app U'))).map
      (DifferentialGraded.Bimodule.unitHom (φ.sectionHom U') (M.sectionModule (F.op.obj U'))) ≫
    DifferentialGraded.Bimodule.restrictScalarsCongr
      (ψ := (φ.sectionHom U').comp (A.sectionRestriction (τ.app U'))) (hτ U') _

/-- **The refinement map** `M(F' U') ⊗_{A(F' U')} A'(U') ⟶ M(F U') ⊗_{A(F U')} A'(U')`,
`x ⊗ b ↦ x|_{F U'} ⊗ b`. -/
def refineSections (M : DifferentialGradedModule.{u, m, m} A) (U' : C'ᵒᵖ) :
    pullbackSections φ' M U' ⟶ pullbackSections φ M U' :=
  DifferentialGraded.Bimodule.plainTranspose (φ'.sectionHom U') (refineUnit φ φ' τ hτ M U')

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The refinement map sends a pure tensor `x ⊗ b` to `x|_{F U'} ⊗ b`. -/
theorem refineSections_pure (M : DifferentialGradedModule.{u, m, m} A) (U' : C'ᵒᵖ)
    (x : (M.sectionModule (F'.op.obj U')).M) (b : (pullbackBimodule φ' U').rightModule.M) :
    (refineSections φ φ' τ hτ M U').toFun (pullbackPure φ' M U' x b) =
      pullbackPure φ M U' ((M.sectionModuleRestriction (τ.app U')).toFun x)
        (regElt φ U' (algElt φ' U' b)) := by
  refine (DifferentialGraded.Bimodule.plainTranspose_pure_apply _ _ x b).trans ?_
  have hu := DifferentialGraded.Bimodule.unitHom_apply (φ.sectionHom U')
    (M.sectionModule (F.op.obj U')) ((M.sectionModuleRestriction (τ.app U')).toFun x)
  refine (congrArg (fun z => @HSMul.hSMul (A'.sectionAlgebra U').Aᵐᵒᵖ
    (pullbackSections φ M U').M (pullbackSections φ M U').M _
      (MulOpposite.op (show (A'.sectionAlgebra U').A from b)) z) hu).trans ?_
  exact (((DifferentialGraded.Bimodule.tensorDGFunctor (pullbackBimodule φ U')).pure
    (M.sectionModule (F.op.obj U'))).map_right _ _ _).symm.trans
      (congrArg _ (one_mul (show (A'.sectionAlgebra U').A from b)))

/-- **The refinement maps, as a morphism of presheaves of section modules** `Σ g'^*M ⟶ Σ g^*M`. -/
def refineSystemHom (M : DifferentialGradedModule.{u, m, m} A) :
    pullbackSystem φ' M ⟶ pullbackSystem φ M where
  app U' := refineSections φ φ' τ hτ M U'
  naturality {U' V'} a w := by
    have key : (pullbackRestr φ M a).toFun.toAddMonoidHom.comp
        (refineSections φ φ' τ hτ M V').toFun.toAddMonoidHom =
        (refineSections φ φ' τ hτ M U').toFun.toAddMonoidHom.comp
          (pullbackRestr φ' M a).toFun.toAddMonoidHom := by
      refine tensorObj_addHom_ext _ _ _ _ fun x y => ?_
      change (pullbackRestr φ M a).toFun ((refineSections φ φ' τ hτ M V').toFun
          (pullbackPure φ' M V' x y)) =
        (refineSections φ φ' τ hτ M U').toFun ((pullbackRestr φ' M a).toFun
          (pullbackPure φ' M V' x y))
      rw [refineSections_pure φ φ' τ hτ M V' x y, pullbackRestr_pure φ M a,
        pullbackRestr_pure φ' M a x y, refineSections_pure φ φ' τ hτ M U']
      refine congrArg (fun z => pullbackPure φ M U' z _) ?_
      exact (sectionRestrictAdd_comp M (F.op.map a) (τ.app V') x).symm.trans
        ((congrArg (fun f => M.sectionRestrictAdd f x) (τ.naturality a).symm).trans
          (sectionRestrictAdd_comp M (τ.app U') (F'.op.map a) x))
    exact DFunLike.congr_fun key w

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The refinement maps commute with the maps of pullback section systems induced by a morphism
`f : M ⟶ N`. -/
theorem refineSystemHom_naturality {M N : DifferentialGradedModule.{u, m, m} A} (f : M ⟶ N) :
    refineSystemHom φ φ' τ hτ M ≫ pullbackSystemMap φ f =
      pullbackSystemMap φ' f ≫ refineSystemHom φ φ' τ hτ N := by
  refine SectionSystem.hom_ext fun U' => ?_
  refine DifferentialGraded.Bimodule.tensorObj_hom_ext' _ _ _ _ fun x y => ?_
  change (pullbackSectionsMap φ f U').toFun ((refineSections φ φ' τ hτ M U').toFun
      (pullbackPure φ' M U' x y)) =
    (refineSections φ φ' τ hτ N U').toFun ((pullbackSectionsMap φ' f U').toFun
      (pullbackPure φ' M U' x y))
  rw [refineSections_pure φ φ' τ hτ M U' x y, pullbackSectionsMap_pure,
    pullbackSectionsMap_pure φ' f U' x y, refineSections_pure φ φ' τ hτ N U']
  exact congrArg (fun z => pullbackPure φ N U' z _)
    (sectionRestrictAdd_sectionMapAdd f (τ.app U') x).symm

/-- The refinement maps as a natural transformation of the pullbacks to presheaves of section
modules. -/
def refineSystemNatTrans : pullbackSystemFunctor φ' ⟶ pullbackSystemFunctor φ where
  app M := refineSystemHom φ φ' τ hτ M
  naturality _ _ f := (refineSystemHom_naturality φ φ' τ hτ f).symm

/-- **The natural homomorphism `g'^*M ⟶ g^*M`** of pullbacks along the two representatives. -/
def refineCounit :
    (pullbackFunctor φ' : DifferentialGradedModule.{u, m, m} A ⥤ _) ⟶ pullbackFunctor φ :=
  Functor.whiskerRight (refineSystemNatTrans φ φ' τ hτ) (SectionSystem.realizeFunctor A')

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Over `U'` the refinement homomorphism is the refinement map, after the identification of the
sections of the realizations. -/
theorem sectionMap_refineCounit (M : DifferentialGradedModule.{u, m, m} A) (U' : C'ᵒᵖ) :
    sectionMap ((refineCounit φ φ' τ hτ).app M) U' ≫ ((pullbackSystem φ M).sectionsIso U').hom =
      ((pullbackSystem φ' M).sectionsIso U').hom ≫ (refineSystemHom φ φ' τ hτ M).app U' :=
  SectionSystem.sectionsIso_naturality (refineSystemHom φ φ' τ hτ M) U'

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The refinement map factors as the composition isomorphism followed by the comparison map
tensored with `A'(U')`. -/
private theorem refineSections_eq_compIso_hom_comp (M : DifferentialGradedModule.{u, m, m} A)
    (U' : C'ᵒᵖ) :
    refineSections φ φ' τ hτ M U' =
      (DifferentialGraded.Bimodule.compIso (A.sectionRestriction (τ.app U')) (φ.sectionHom U')
        (φ'.sectionHom U') (hτ U') (M.sectionModule (F'.op.obj U'))).hom ≫
        (DifferentialGraded.Bimodule.tensorCompFunctor
          (DifferentialGraded.Bimodule.regular (φ.sectionHom U'))).map
          (DifferentialGraded.Bimodule.plainTranspose (A.sectionRestriction (τ.app U'))
            (M.sectionModuleRestriction (τ.app U'))) := by
  let ψ := A.sectionRestriction (τ.app U')
  let χ := φ.sectionHom U'
  let Y := M.sectionModule (F.op.obj U')
  let r := M.sectionModuleRestriction (τ.app U')
  let p := DifferentialGraded.Bimodule.plainTranspose ψ r
  have hp : DifferentialGraded.Bimodule.plainTranspose ψ
      (r ≫ (_root_.DifferentialGradedModule.restrictScalarsFunctor ψ).map
        (DifferentialGraded.Bimodule.unitHom χ Y)) =
      p ≫ DifferentialGraded.Bimodule.unitHom χ Y :=
    (DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars ψ).homEquiv_naturality_right_symm
      r (DifferentialGraded.Bimodule.unitHom χ Y)
  have hq : DifferentialGraded.Bimodule.plainTranspose χ
      (p ≫ DifferentialGraded.Bimodule.unitHom χ Y) =
      (DifferentialGraded.Bimodule.tensorCompFunctor
        (DifferentialGraded.Bimodule.regular χ)).map p := by
    refine ((DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars χ).homEquiv _ _
      ).symm_apply_eq.2 ?_
    rw [Adjunction.homEquiv_unit]
    exact (DifferentialGraded.Bimodule.tensorRegularAdjRestrictScalars χ).unit.naturality p
  refine (DifferentialGraded.Bimodule.compIso_hom_plainTranspose_plainTranspose ψ χ
    (φ'.sectionHom U') (hτ U') (refineUnit φ φ' τ hτ M U')).symm.trans
      (congrArg (fun g => _ ≫ g) ?_)
  exact (congrArg (DifferentialGraded.Bimodule.plainTranspose χ) hp).trans hq

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The refinement map is a quasi-isomorphism** at a module whose sections over `F U'` and
`F' U'` are K-projective and whose comparison map along `τ_{U'}` is invertible: it is the
comparison map tensored with `A'(U')`, a homotopy equivalence between K-projective modules
tensored. -/
theorem quasiIso_refineSections (M : DifferentialGradedModule.{u, m, m} A) (U' : C'ᵒᵖ)
    (hM : (_root_.DifferentialGradedModule.acyclic'
      (A.sectionAlgebra (F'.op.obj U'))).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
          (M.sectionModule (F'.op.obj U'))))
    (hM' : (_root_.DifferentialGradedModule.acyclic'
      (A.sectionAlgebra (F.op.obj U'))).leftOrthogonal
        ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
          (M.sectionModule (F.op.obj U'))))
    (hQC : IsIso (Chaotic.sectionComparison M (τ.app U'))) :
    QuasiIso ((_root_.DifferentialGradedModule.forgetToCochainComplex (A'.sectionAlgebra U')).map
      (refineSections φ φ' τ hτ M U')) := by
  let ψ := A.sectionRestriction (τ.app U')
  let χ := φ.sectionHom U'
  let X := M.sectionModule (F'.op.obj U')
  let p := DifferentialGraded.Bimodule.plainTranspose ψ (M.sectionModuleRestriction (τ.app U'))
  have hm := (Chaotic.isIso_sectionComparison_iff_quasiIso M (τ.app U') hM).1 hQC
  have hX := DifferentialGraded.Bimodule.leftOrthogonal_tensorCompFunctor_obj ψ hM
  have h3 :=
    DifferentialGraded.Bimodule.isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal
      (DifferentialGraded.Bimodule.regular χ)
      ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra (F.op.obj U'))).map p)
      ((_root_.DifferentialGradedModule.quasiIsomorphisms_map_iff' _ _).2 hm) hX hM'
  have h4 : IsIso (((DifferentialGraded.Bimodule.tensorCompFunctor
      (DifferentialGraded.Bimodule.regular χ) ⋙
        _root_.DifferentialGradedModule.toHomotopyCategory (A'.sectionAlgebra U')) ⋙
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q).map p) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (DifferentialGraded.Bimodule.tensorCompFunctor_quotient
        (DifferentialGraded.Bimodule.regular χ))
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A'.sectionAlgebra U')).Q) _).2 h3
  have h5 := (_root_.DifferentialGradedModule.quasiIsomorphisms_map_iff' _ _).1
    (_root_.DifferentialGradedModule.quasiIsomorphisms'_of_isIso_Q_map _ _ h4)
  have h6 : QuasiIso
      ((_root_.DifferentialGradedModule.forgetToCochainComplex (A'.sectionAlgebra U')).map
      (DifferentialGraded.Bimodule.compIso ψ χ (φ'.sectionHom U') (hτ U') X).hom ≫
      (_root_.DifferentialGradedModule.forgetToCochainComplex (A'.sectionAlgebra U')).map
        ((DifferentialGraded.Bimodule.tensorCompFunctor
          (DifferentialGraded.Bimodule.regular χ)).map p)) := inferInstance
  rwa [← Functor.map_comp, ← refineSections_eq_compIso_hom_comp] at h6

/-! ### The derived refinement -/

/-- The refinement homomorphism on the homotopy categories. -/
def refineHomotopy : pullbackHomotopyFunctor φ' ⟶ pullbackHomotopyFunctor φ :=
  CategoryTheory.Quotient.natTransLift _
    { app := fun M => (HomotopyCategory.quotient A').map ((refineCounit φ φ' τ hτ).app M)
      naturality := fun M N f => by
        change (HomotopyCategory.quotient A').map ((pullbackFunctor φ').map f) ≫
            (HomotopyCategory.quotient A').map ((refineCounit φ φ' τ hτ).app N) =
          (HomotopyCategory.quotient A').map ((refineCounit φ φ' τ hτ).app M) ≫
            (HomotopyCategory.quotient A').map ((pullbackFunctor φ).map f)
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (HomotopyCategory.quotient A').map ((refineCounit φ φ' τ hτ).naturality f) }

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- At the image of a module `M`, the refinement homomorphism on homotopy categories is the image
of the refinement homomorphism `g'^*M ⟶ g^*M`. -/
theorem refineHomotopy_app (M : DifferentialGradedModule.{u, m, m} A) :
    (refineHomotopy φ φ' τ hτ).app ((HomotopyCategory.quotient A).obj M) =
      (HomotopyCategory.quotient A').map ((refineCounit φ φ' τ hτ).app M) :=
  rfl

variable [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type m)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [HasSheafify (⊥ : GrothendieckTopology C') AddCommGrpCat.{m}]

/-- **The transformation `Lg'^* ⟶ Lg^*` of derived pullbacks** induced by the refinement
homomorphisms. -/
def refineDerived : chaoticDerivedPullback φ' ⟶ chaoticDerivedPullback φ :=
  haveI := hasLeftDerivedFunctor_pullbackToDerived φ
  Functor.leftDerivedNatTrans (chaoticDerivedPullback φ') (chaoticDerivedPullback φ)
    (chaoticDerivedPullbackCounit φ') (chaoticDerivedPullbackCounit φ)
    (quasiIsomorphisms.{u, m, m} A)
    (Functor.whiskerRight (refineHomotopy φ φ' τ hτ) (toDerivedCategory.{u, m, m} A'))

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The transformation `Lg'^* ⟶ Lg^*` is compatible with the counits of the derived pullbacks
and the refinement homomorphism on homotopy categories. -/
theorem refineDerived_app (X : HomotopyCategory.{u, m, m} A) :
    (refineDerived φ φ' τ hτ).app ((toDerivedCategory.{u, m, m} A).obj X) ≫
        (chaoticDerivedPullbackCounit φ).app X =
      (chaoticDerivedPullbackCounit φ').app X ≫
        (toDerivedCategory.{u, m, m} A').map ((refineHomotopy φ φ' τ hτ).app X) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ X

omit [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The transformation `Lg'^* ⟶ Lg^*` is invertible on `QC(A, d)`.** -/
theorem isIso_refineDerived_app (K : derivedCategory.{u, m, m} A) (hK : Chaotic.QC A K) :
    IsIso ((refineDerived φ φ' τ hτ).app K) := by
  obtain ⟨M, rfl⟩ := exists_toDerivedCategory_obj_eq A K
  obtain ⟨P, f, hf, -, -, hs⟩ := exists_flat_quasiIso_sectionwise (A := A) M
  have : IsIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map f)) :=
    (quasiIsomorphisms.{u, m, m} A).Q_inverts _ ((quasiIsomorphisms_quotient_map_iff f).2 hf)
  let e := asIso ((toDerivedCategory.{u, m, m} A).map ((HomotopyCategory.quotient A).map f))
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have hP : IsQC (sectionDatum A)
      ((toDerivedCategory.{u, m, m} A).obj ((HomotopyCategory.quotient A).obj P)) :=
    isQC_of_iso _ e.symm ((qc_iff_isQC_sectionDatum A _).1 hK)
  have hQC := (isQC_sectionDatum_iff P).1 hP
  have hr : QuasiIso ((refineCounit φ φ' τ hτ).app P).toHomologicalComplex := by
    refine quasiIso_of_forall_quasiIso_sectionMap _ fun U' => ?_
    have w : Arrow.mk (sectionMap ((refineCounit φ φ' τ hτ).app P) U') ≅
        Arrow.mk (refineSections φ φ' τ hτ P U') :=
      Arrow.isoMk ((pullbackSystem φ' P).sectionsIso U') ((pullbackSystem φ P).sectionsIso U')
        (sectionMap_refineCounit φ φ' τ hτ P U').symm
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      ((_root_.DifferentialGradedModule.forgetToCochainComplex
        (A'.sectionAlgebra U')).mapArrow.mapIso w)).2
      (quasiIso_refineSections φ φ' τ hτ P U' (hs _) (hs _) (hQC (τ.app U')))
  have : IsIso ((toDerivedCategory.{u, m, m} A').map
      ((refineHomotopy φ φ' τ hτ).app ((HomotopyCategory.quotient A).obj P))) :=
    (quasiIsomorphisms.{u, m, m} A').Q_inverts _ ((quasiIsomorphisms_quotient_map_iff _).2 hr)
  have := isIso_chaoticDerivedPullbackCounit_app φ hs
  have := isIso_chaoticDerivedPullbackCounit_app φ' hs
  have h' : IsIso ((refineDerived φ φ' τ hτ).app ((toDerivedCategory.{u, m, m} A).obj
      ((HomotopyCategory.quotient A).obj P)) ≫
        (chaoticDerivedPullbackCounit φ).app ((HomotopyCategory.quotient A).obj P)) := by
    rw [refineDerived_app φ φ' τ hτ]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((chaoticDerivedPullbackCounit φ).app ((HomotopyCategory.quotient A).obj P))

/-- **The functors `QC(A, d) ⥤ QC(A', d)` induced by the two representatives are isomorphic.** -/
def chaoticQCPullbackRefineIso : chaoticQCPullback φ' ≅ chaoticQCPullback φ :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      (@asIso _ _ _ _ _ (isIso_refineDerived_app φ φ' τ hτ K.obj K.property)))
    (fun f => ObjectProperty.hom_ext _ ((refineDerived φ φ' τ hτ).naturality f.hom))

end SheafOfModules.DifferentialGradedModule
