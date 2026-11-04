module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticExtensionModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparisonPlain

/-!
# Quasi-coherence and the extension from a subcategory of a chaotic site

Let `F : C' ⥤ C` be a functor of chaotic sites such that every `U/F` is cofiltered, `(A, d)` a
sheaf of differential graded algebras on `C` and `(A', d)` its restriction to `C'`. This file shows
that restriction along `F` and the extension `E` preserve the quasi-coherence condition of
Definition 0GZ9 on good modules, which is the content of the second paragraph of the proof of
Tag 0GZE.

The comparison map `M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)` of a module `M` can be read on any module `X`
orthogonal on the left to the acyclic modules together with a quasi-isomorphism `X ⟶ M(V)`: it
is invertible exactly when the plain transpose `X ⊗_{A(V)} A(U) ⟶ M(U)` is a quasi-isomorphism.
For the extension `E(M')` one takes `X = M'(V') ⊗_{A'(V')} A(V)` for an arrow `V → F V'`, the
coprojection into the filtered colimit being a quasi-isomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.isIso_sectionComparison_iff_of_quasiIso`: the
  comparison map read through a quasi-isomorphism from a module orthogonal to the acyclics.
* `SheafOfModules.DifferentialGradedModule.ChaoticExtension.isQCModule_restriction` and
  `isQCModule_extension`: restriction and extension preserve the quasi-coherence condition on
  good modules.

## References

* [Stacks Project, Lemma 24.34.1 (Tag 0GZE)](https://stacks.math.columbia.edu/tag/0GZE)
* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf
open DifferentialGradedModule (forgetToCochainComplex acyclic' toHomotopyCategory
  quasiIsomorphisms')
open DifferentialGraded.Bimodule (tensorCompFunctor regular plainTranspose)

universe u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

namespace DifferentialGradedModule

namespace Chaotic

variable {C : Type u} [Category.{u} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}}
  {B : DifferentialGradedAlgebra.{u, u} R}

/-- **The comparison map of quasi-coherence, read through a resolution of the source.** For a
module `X` over `A(V)` orthogonal on the left to the acyclic modules and a quasi-isomorphism
`q : X ⟶ M(V)`, the comparison map `M(V) ⊗^𝐋_{A(V)} A(U) ⟶ M(U)` is invertible exactly when the
plain transpose `X ⊗_{A(V)} A(U) ⟶ M(U)` of `x ↦ q(x)|_U` is a quasi-isomorphism. -/
theorem isIso_sectionComparison_iff_of_quasiIso (M : DifferentialGradedModule.{u, u, u} B)
    {U V : Cᵒᵖ} (a : V ⟶ U) {X : _root_.DifferentialGradedModule.{u, u, u} (B.sectionAlgebra V)}
    (hX : (acyclic' (B.sectionAlgebra V)).leftOrthogonal
      ((toHomotopyCategory (B.sectionAlgebra V)).obj X))
    (q : X ⟶ M.sectionModule V) (hq : QuasiIso ((forgetToCochainComplex _).map q)) :
    IsIso (sectionComparison M a) ↔
      QuasiIso ((forgetToCochainComplex (B.sectionAlgebra U)).map
        (plainTranspose (B.sectionRestriction a) (q ≫ M.sectionModuleRestriction a))) := by
  let ψ := B.sectionRestriction a
  let Q := (quasiIsomorphisms' (B.sectionAlgebra V)).Q
  have hQq : IsIso (Q.map ((toHomotopyCategory (B.sectionAlgebra V)).map q)) :=
    (_root_.DifferentialGradedModule.isIso_q_map_toHomotopyCategory_map_iff _ q).2 hq
  have key : (sectionBaseChange B a).map (Q.map ((toHomotopyCategory _).map q)) ≫
      sectionComparison M a =
      (DifferentialGraded.Bimodule.derivedTensorFunctorCounit (regular ψ)).app
          ((toHomotopyCategory (B.sectionAlgebra V)).obj X) ≫
        (quasiIsomorphisms' (B.sectionAlgebra U)).Q.map
          ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient (regular ψ)).inv.app X) ≫
        (quasiIsomorphisms' (B.sectionAlgebra U)).Q.map ((toHomotopyCategory _).map
          (plainTranspose ψ (q ≫ M.sectionModuleRestriction a))) := by
    refine ((sectionBaseChangeAdj B a).homEquiv_naturality_left_symm _ _).symm.trans ?_
    refine Eq.trans ?_ (DifferentialGraded.Bimodule.derivedTranspose_eq ψ
      (q ≫ M.sectionModuleRestriction a))
    congr 1
    show Q.map ((toHomotopyCategory _).map q) ≫ (Q.map ((toHomotopyCategory _).map
        (M.sectionModuleRestriction a)) ≫ _ ≫ _) = _
    refine Eq.trans ?_ (congrArg (· ≫ _) ((congrArg Q.map ((toHomotopyCategory _).map_comp q
      (M.sectionModuleRestriction a))).trans (Q.map_comp _ _))).symm
    exact (Category.assoc _ _ _).symm
  have h₁ := DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal
    (regular ψ) _ hX
  rw [← isIso_comp_left_iff ((sectionBaseChange B a).map (Q.map ((toHomotopyCategory _).map q))),
    key, isIso_comp_left_iff, isIso_comp_left_iff,
    _root_.DifferentialGradedModule.isIso_q_map_toHomotopyCategory_map_iff]

end Chaotic

/-! ### Quasi-coherence of a realization -/

section Realize

variable {C : Type u} [Category.{u} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}

/-- Under the identifications `X(V) ≅ (realize X)(V)` and `X(U) ≅ (realize X)(U)`, the restriction
of sections of the realization along `a : V ⟶ U` agrees with the restriction map `X.restrFun a`. -/
theorem SectionSystem.sectionsIso_inv_sectionModuleRestriction_apply (X : SectionSystem B)
    {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    X.realize.sectionRestrictAdd a ((X.sectionsIso V).inv.toFun x) =
      (X.sectionsIso U).inv.toFun (X.restrFun a x) := by
  have hU : ∀ z, (X.sectionsIso U).hom.toFun ((X.sectionsIso U).inv.toFun z) = z := fun z =>
    congrArg (fun g => g.toFun z) (X.sectionsIso U).inv_hom_id
  have hV : ∀ z, (X.sectionsIso V).hom.toFun ((X.sectionsIso V).inv.toFun z) = z := fun z =>
    congrArg (fun g => g.toFun z) (X.sectionsIso V).inv_hom_id
  apply (X.sectionsAddEquiv U).injective
  refine (X.sectionsAddEquiv_sectionRestrictAdd a _).trans ?_
  refine (congrArg (X.restrFun a) (hV x)).trans ?_
  exact (hU _).symm

/-- **The comparison map of a realization is computed by the plain transposes of its restriction
homomorphisms**, at an object whose module is orthogonal on the left to the acyclic modules. -/
theorem SectionSystem.isIso_sectionComparison_realize_iff (X : SectionSystem B) {U V : Cᵒᵖ}
    (a : V ⟶ U) (hX : (acyclic' (B.sectionAlgebra V)).leftOrthogonal
      ((toHomotopyCategory (B.sectionAlgebra V)).obj (X.obj V))) :
    IsIso (Chaotic.sectionComparison X.realize a) ↔
      QuasiIso ((forgetToCochainComplex (B.sectionAlgebra U)).map
        (plainTranspose (B.sectionRestriction a) (X.restr a))) := by
  have : QuasiIso ((forgetToCochainComplex (B.sectionAlgebra V)).map (X.sectionsIso V).inv) :=
    quasiIso_of_isIso _
  refine (Chaotic.isIso_sectionComparison_iff_of_quasiIso X.realize a hX (X.sectionsIso V).inv
    inferInstance).trans ?_
  have e : plainTranspose (B.sectionRestriction a)
      ((X.sectionsIso V).inv ≫ X.realize.sectionModuleRestriction a) =
      plainTranspose (B.sectionRestriction a) (X.restr a) ≫ (X.sectionsIso U).inv := by
    refine Eq.trans ?_ (DifferentialGraded.Bimodule.plainTranspose_naturality_right _ _ _)
    congr 1
    exact _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun x =>
      X.sectionsIso_inv_sectionModuleRestriction_apply a x)
  rw [e, Functor.map_comp]
  have : QuasiIso ((forgetToCochainComplex (B.sectionAlgebra U)).map (X.sectionsIso U).inv) :=
    quasiIso_of_isIso _
  exact quasiIso_iff_comp_right _ _

end Realize

/-! ### Restriction and extension preserve quasi-coherence -/

namespace ChaoticExtension

variable {C : Type u} [Category.{u} C] {C' : Type u} [Category.{u} C'] (F : C' ⥤ C)
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
  [∀ U : C, IsCofiltered (StructuredArrow U F)]

attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- **Restriction preserves quasi-coherence of good modules.** The comparison maps of `P|_{C'}`
are those of `P` along the image of `F`, read through the identification `A'(U') = A(F U')`. -/
theorem isQCModule_restriction {P : DifferentialGradedModule.{u, u, u} A}
    (hP : ∀ U : Cᵒᵖ, (acyclic' (A.sectionAlgebra U)).leftOrthogonal
      ((toHomotopyCategory (A.sectionAlgebra U)).obj (P.sectionModule U)))
    (hqc : Chaotic.IsQCModule P) : Chaotic.IsQCModule ((restriction F A).obj P) := by
  intro U' V' a
  refine (SectionSystem.isIso_sectionComparison_realize_iff
    ((ofAlong F A).obj ((restrictFunctor F A).obj ((sectionSystemFunctor A).obj P))) a
    (DifferentialGraded.Bimodule.leftOrthogonal_restrictScalars_of_inverse
      (A.restrictSectionInv F V') (A.restrictSectionHom F V') (A.restrictSectionHom_inv F V')
      (A.restrictSectionInv_hom F V') _ (hP (F.op.obj V')))).2 ?_
  refine (DifferentialGraded.Bimodule.quasiIso_plainTranspose_iff_of_square
    (A.restrictSectionHom F V') ((A.restrict F).sectionRestriction a)
    (A.sectionRestriction (F.op.map a)) (A.restrictSectionHom F U')
    (fun b => DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A a b)
    (𝟙 _) (𝟙 _) (((ofAlong F A).obj ((restrictFunctor F A).obj
      ((sectionSystemFunctor A).obj P))).restr a) (P.sectionModuleRestriction (F.op.map a))
    (A.restrictSectionInv F V') (A.restrictSectionInv F U')
    (fun b => DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A a b)
    (DifferentialGraded.Bimodule.restrictScalarsInverseHom (A.restrictSectionInv F V')
      (A.restrictSectionHom F V') (A.restrictSectionHom_inv F V') _)
    (fun _ => rfl) (fun _ => rfl) (A.restrictSectionInv_hom F U') (A.restrictSectionHom_inv F U')
    Function.bijective_id (fun _ => rfl)).2 ?_
  exact (Chaotic.isIso_sectionComparison_iff_quasiIso P (F.op.map a) (hP _)).1 (hqc _)

/-- A module over the restriction `A'`, as a presheaf of section modules along `F`. -/
abbrev alongOf (M : DifferentialGradedModule.{u, u, u} (A.restrict F)) : AlongSystem F A :=
  (toAlong F A).obj ((sectionSystemFunctor (A.restrict F)).obj M)

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- If every section module of `M` is orthogonal on the left to the acyclic modules, then so is
every module of `alongOf F A M`. -/
theorem alongOf_isGood {M : DifferentialGradedModule.{u, u, u} (A.restrict F)}
    (hM : ∀ U' : C'ᵒᵖ, (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj (M.sectionModule U'))) :
    (alongOf F A M).IsGood := fun U' =>
  DifferentialGraded.Bimodule.leftOrthogonal_restrictScalars_of_inverse
    (A.restrictSectionHom F U') (A.restrictSectionInv F U') (A.restrictSectionInv_hom F U')
    (A.restrictSectionHom_inv F U') _ (hM U')

omit [∀ U : C, IsCofiltered (StructuredArrow U F)] in
attribute [local irreducible] DifferentialGradedAlgebra.sectionAlgebra in
/-- If every section module of `M` is orthogonal on the left to the acyclic modules and `M`
satisfies `Chaotic.IsQCModule`, then `Z = alongOf F A M` is quasi-coherent: its plain comparison
maps `Z(V') ⊗_{A(F V')} A(F U') ⟶ Z(U')` are quasi-isomorphisms. -/
theorem alongOf_isQC {M : DifferentialGradedModule.{u, u, u} (A.restrict F)}
    (hM : ∀ U' : C'ᵒᵖ, (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj (M.sectionModule U')))
    (hqc : Chaotic.IsQCModule M) : (alongOf F A M).IsQC := by
  intro U' V' a
  refine (DifferentialGraded.Bimodule.quasiIso_plainTranspose_iff_of_square
    (A.restrictSectionInv F V') (A.sectionRestriction (F.op.map a))
    ((A.restrict F).sectionRestriction a) (A.restrictSectionInv F U')
    (fun b => DifferentialGradedAlgebra.restrictSectionInv_sectionRestriction F A a b)
    (𝟙 _) (𝟙 _) ((alongOf F A M).restr a) (M.sectionModuleRestriction a)
    (A.restrictSectionHom F V') (A.restrictSectionHom F U')
    (fun b => DifferentialGradedAlgebra.restrictSectionHom_sectionRestriction F A a b)
    (DifferentialGraded.Bimodule.restrictScalarsInverseHom (A.restrictSectionHom F V')
      (A.restrictSectionInv F V') (A.restrictSectionInv_hom F V') _)
    (fun _ => rfl) (fun _ => rfl) (A.restrictSectionHom_inv F U') (A.restrictSectionInv_hom F U')
    Function.bijective_id (fun _ => rfl)).2 ?_
  exact (Chaotic.isIso_sectionComparison_iff_quasiIso M a (hM _)).1 (hqc _)

/-- The transpose of a restriction leg is the inverse of the identification
`(X ⊗_{A(F V')} A(V)) ⊗_{A(V)} A(U) ≅ X ⊗_{A(F V')} A(U)`. -/
theorem plainTranspose_restrLeg (Z : AlongSystem F A) {U V : Cᵒᵖ} (a : V ⟶ U)
    (b : StructuredArrow V.unop F) :
    plainTranspose (A.sectionRestriction a) (restrLeg Z a b) =
      DifferentialGraded.Bimodule.compBackward (arrowHom F A b) (A.sectionRestriction a)
        (arrowHom F A (pre F a b)) (fun y => arrowHom_pre F A a b y)
        (Z.obj (Opposite.op b.right)) :=
  congrArg (plainTranspose (A.sectionRestriction a)) (tensor_hom_ext _ fun p x c =>
    (restrLeg_pure Z a b p x c).trans
      (DifferentialGraded.Bimodule.compBackwardInner_pure (arrowHom F A b)
        (A.sectionRestriction a) (arrowHom F A (pre F a b)) (fun y => arrowHom_pre F A a b y)
        (Z.obj (Opposite.op b.right)) p x c).symm)

/-- **The extension preserves quasi-coherence of good modules.** Over `V` the extension is
computed by any single term `M'(V') ⊗_{A'(V')} A(V)`, a module orthogonal on the left to the
acyclic modules, and its comparison map along `V → U` is, up to isomorphisms, the coprojection
of the colimit over `U` at the composite arrow, a quasi-isomorphism. -/
theorem isQCModule_extension {M : DifferentialGradedModule.{u, u, u} (A.restrict F)}
    (hM : ∀ U' : C'ᵒᵖ, (acyclic' ((A.restrict F).sectionAlgebra U')).leftOrthogonal
      ((toHomotopyCategory ((A.restrict F).sectionAlgebra U')).obj (M.sectionModule U')))
    (hqc : Chaotic.IsQCModule M) : Chaotic.IsQCModule ((extension F A).obj M) := by
  intro U V a
  have hZg := alongOf_isGood F A hM
  have hZq := alongOf_isQC F A hM hqc
  obtain ⟨b⟩ : Nonempty (StructuredArrow V.unop F) := IsCofiltered.nonempty
  let Z := alongOf F A M
  have hι {W : Cᵒᵖ} (c : StructuredArrow W.unop F) :
      QuasiIso ((forgetToCochainComplex (A.sectionAlgebra W)).map
        (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram Z W) (Opposite.op c) ≫
          ((extSystem Z).sectionsIso W).inv)) := by
    have hinv : QuasiIso ((forgetToCochainComplex (A.sectionAlgebra W)).map
        ((extSystem Z).sectionsIso W).inv) := quasiIso_of_isIso _
    show QuasiIso ((forgetToCochainComplex (A.sectionAlgebra W)).map _ ≫
      (forgetToCochainComplex (A.sectionAlgebra W)).map ((extSystem Z).sectionsIso W).inv)
    exact @quasiIso_comp _ _ _ _ _ _ _ _ _ _ _ _ _ (quasiIso_ι hZg hZq c) hinv
  have hq := hι b
  have := hι (pre F a b)
  show IsIso (Chaotic.sectionComparison (extSystem Z).realize a)
  refine (Chaotic.isIso_sectionComparison_iff_of_quasiIso (extSystem Z).realize a
    (DifferentialGraded.Bimodule.leftOrthogonal_tensorCompFunctor_obj
      (A.sectionRestriction b.hom.op) (hZg (Opposite.op b.right))) _ hq).2 ?_
  have e : plainTranspose (A.sectionRestriction a)
      ((_root_.DifferentialGradedModule.FilteredColimit.ι (diagram Z V) (Opposite.op b) ≫
        ((extSystem Z).sectionsIso V).inv) ≫ (extSystem Z).realize.sectionModuleRestriction a) =
      plainTranspose (A.sectionRestriction a) (restrLeg Z a b) ≫
        (_root_.DifferentialGradedModule.FilteredColimit.ι (diagram Z U)
          (Opposite.op (pre F a b)) ≫ ((extSystem Z).sectionsIso U).inv) := by
    refine Eq.trans ?_ (DifferentialGraded.Bimodule.plainTranspose_naturality_right _ _ _)
    congr 1
    refine _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun z => ?_)
    exact (SectionSystem.sectionsIso_inv_sectionModuleRestriction_apply (extSystem Z) a
      (germ Z b z)).trans
        (congrArg ((extSystem Z).sectionsIso U).inv.toFun (extSystem_restrFun_germ Z a b z))
  rw [e, Functor.map_comp, plainTranspose_restrLeg]
  have : IsIso (DifferentialGraded.Bimodule.compBackward (arrowHom F A b) (A.sectionRestriction a)
      (arrowHom F A (pre F a b)) (fun y => arrowHom_pre F A a b y) (Z.obj (Opposite.op b.right))) :=
    (DifferentialGraded.Bimodule.compIso (arrowHom F A b) (A.sectionRestriction a)
      (arrowHom F A (pre F a b)) (fun y => arrowHom_pre F A a b y)
        (Z.obj (Opposite.op b.right))).isIso_inv
  have : QuasiIso ((forgetToCochainComplex (A.sectionAlgebra U)).map
      (DifferentialGraded.Bimodule.compBackward (arrowHom F A b) (A.sectionRestriction a)
        (arrowHom F A (pre F a b)) (fun y => arrowHom_pre F A a b y)
          (Z.obj (Opposite.op b.right)))) := quasiIso_of_isIso _
  infer_instance

end ChaoticExtension

end DifferentialGradedModule

end SheafOfModules

end
