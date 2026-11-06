module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Limits.HasLimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRightDerivedLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimDerived
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleKFlatComparison
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# Functorial derived limits of derived tensor products

An inverse system `E` in `D(A)` lifts to an object of `D(ℕ, A)`. Tensoring this lift with
constant systems and applying the derived inverse-limit functor gives an exact functor of `K`.
Its value is a derived limit of the pointwise tensor products, with their induced transitions.

Here `D(ℕ, A)` is the derived category of compatible module systems over the constant ring
system, as in Stacks 091D, 091H and 091I. Stacks 0CQD supplies the canonical derived-limit
triangle.

## Main results

* `ModuleSystemRlimTensor.exists_exactFunctor_isDerivedLimit_tensor` (Stacks 091J): the composite
  of the constant-system functor, the derived tensor product with a lift of `E`, and the derived
  inverse limit is exact, and computes a derived limit of `K ⊗ᴸ[A] Eₙ`.
* `ModuleSystemRlimTensor.derivedLimit_tensor_mapTriangle_distinguished` (Stacks 091K): that
  composite carries distinguished triangles to distinguished triangles.

## References

* [The Stacks Project, Tag 091J](https://stacks.math.columbia.edu/tag/091J)
* [The Stacks Project, Tag 091K](https://stacks.math.columbia.edu/tag/091K)
-/

namespace ModuleSystemRlimTensor

section Construction

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

attribute [local instance 2000] HasDerivedCategory.standard

universe u v



/-- The constant inverse system of modules over the constant ring system on `A`. -/
public abbrev constantSystem (A : Type u) [Ring A] :
    ModuleCat.{u} A ⥤ PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) :=
  PresheafOfModules.constFunctor (constCocone ℕᵒᵖ (RingCat.of A))

/-- Evaluating a constant system of `A`-modules at any stage recovers the module. -/
public def constantSystemEvaluation (A : Type u) [Ring A] (n : ℕᵒᵖ) :
    constantSystem A ⋙ PresheafOfModules.evaluation _ n ≅ 𝟭 (ModuleCat.{u} A) :=
  ModuleCat.restrictScalarsId A

/-- The constant-system functor is additive. -/
public theorem constantSystem_additive (A : Type u) [Ring A] :
    (constantSystem A).Additive where
  map_add := by intros; ext; rfl

/-- The constant-system functor preserves finite limits, since each evaluation of it does. -/
public theorem constantSystem_preservesFiniteLimits (A : Type u) [Ring A] :
    PreservesFiniteLimits (constantSystem A) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro n
  have : PreservesLimitsOfShape J
      (constantSystem A ⋙ PresheafOfModules.evaluation _ n) :=
    preservesLimitsOfShape_of_natIso (constantSystemEvaluation A n).symm
  exact isLimitOfPreserves (constantSystem A ⋙ PresheafOfModules.evaluation _ n)
    (limit.isLimit K)

/-- The constant-system functor preserves finite colimits, since each evaluation of it does. -/
public theorem constantSystem_preservesFiniteColimits (A : Type u) [Ring A] :
    PreservesFiniteColimits (constantSystem A) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro n
  have : PreservesColimitsOfShape J
      (constantSystem A ⋙ PresheafOfModules.evaluation _ n) :=
    preservesColimitsOfShape_of_natIso (constantSystemEvaluation A n).symm
  exact isColimitOfPreserves (constantSystem A ⋙ PresheafOfModules.evaluation _ n)
    (colimit.isColimit K)
attribute [local instance] constantSystem_additive constantSystem_preservesFiniteLimits
  constantSystem_preservesFiniteColimits

/-- On derived categories, the constant-system functor followed by evaluation at any stage is
isomorphic to the identity. -/
public def constantDerivedEvaluation (A : Type u) [Ring A] (n : ℕᵒᵖ) :
    (constantSystem A).mapDerivedCategory ⋙
      (PresheafOfModules.evaluation _ n).mapDerivedCategory ≅
        𝟭 (DerivedCategory (ModuleCat.{u} A)) := by
  let F := constantSystem A
  let G := PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) n
  let e : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (constantSystemEvaluation A n) (ComplexShape.up ℤ)) _ ≪≫
    isoWhiskerRight (Functor.mapHomologicalComplexIdIso _ _) _ ≪≫
    Functor.leftUnitor _
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    _ _ _ _ e


attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive

/-- A complex of module systems over `R`, viewed as an inverse system of complexes of modules over
the inverse-limit ring `limit R`. -/
public abbrev complexDiagramFunctor (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    CochainComplex (PresheafOfModules.{v} R) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} (limit R : RingCat.{u})) ℤ) :=
  (ModuleInverseLimit.moduleDiagramFunctor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The inverse system in `D(limit R)` attached to a complex of module systems over `R`. -/
public abbrev complexDerivedDiagram (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    CochainComplex (PresheafOfModules.{v} R) ℤ ⥤
      (ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} (limit R : RingCat.{u}))) :=
  complexDiagramFunctor.{u, v} R ⋙
    (whiskeringRight ℕᵒᵖ _ _).obj DerivedCategory.Q

/-- `complexDerivedDiagram R` sends quasi-isomorphisms to isomorphisms. -/
public theorem complexDerivedDiagram_inverts (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    (HomologicalComplex.quasiIso (PresheafOfModules.{v} R) (ComplexShape.up ℤ)).IsInvertedBy
      (complexDerivedDiagram R) := by
  intro K L f hf
  have : QuasiIso f := hf
  have (n : ℕᵒᵖ) : IsIso ((complexDerivedDiagram R).map f |>.app n) := by
    have := ModuleRightDerivedLimit.restrictScalars_preservesHomology.{v} (limit.π R n).hom
    show IsIso (DerivedCategory.Q.map
      (((ModuleCat.restrictScalars.{v} (limit.π R n).hom).mapHomologicalComplex _).map
        (((PresheafOfModules.evaluation R n).mapHomologicalComplex _).map f)))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The functor from `D(ℕ, R)` to inverse systems in `D(limit R)` induced by
`complexDerivedDiagram R`. -/
public def derivedDiagramFunctor (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    DerivedCategory (PresheafOfModules.{v} R) ⥤
      (ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} (limit R : RingCat.{u}))) :=
  Localization.lift (complexDerivedDiagram R) (complexDerivedDiagram_inverts R)
    DerivedCategory.Q

/-- `derivedDiagramFunctor R` composed with the localization functor is
`complexDerivedDiagram R`. -/
public def derivedDiagramFunctorFactors (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    DerivedCategory.Q ⋙ derivedDiagramFunctor.{u, v} R ≅ complexDerivedDiagram R :=
  Localization.fac _ (complexDerivedDiagram_inverts R) _

/-- `derivedDiagramFunctor R` agrees with `ModuleRightDerivedLimit.derivedModuleDiagram R` on
objects. -/
public def derivedDiagramFunctorIso (R : ℕᵒᵖ ⥤ RingCat.{u})
    (K : DerivedCategory (PresheafOfModules.{v} R)) :
    (derivedDiagramFunctor R).obj K ≅ ModuleRightDerivedLimit.derivedModuleDiagram R K :=
  (derivedDiagramFunctor R).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (derivedDiagramFunctorFactors R).app (DerivedCategory.Q.objPreimage K)

set_option backward.isDefEq.respectTransparency false in
/-- A triangulated functor that preserves countable products carries a derived limit of `F` to a
derived limit of any system `G` isomorphic to the image of `F`. -/
public theorem isDerivedLimit_map_of_iso
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (U : C ⥤ D) [U.CommShift ℤ] [U.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) U]
    (F : ℕᵒᵖ ⥤ C) (G : ℕᵒᵖ ⥤ D) (e : F ⋙ U ≅ G)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (X : C) (hX : IsDerivedLimit F X) :
    ∃ _ : HasProduct fun n : ℕ => G.obj ⟨n⟩, IsDerivedLimit G (U.obj X) := by
  obtain ⟨f, δ, hT⟩ := hX
  let P := ∏ᶜ fun n : ℕ => F.obj ⟨n⟩
  let p (n : ℕ) := U.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)
  let q (n : ℕ) := p n ≫ (e.app ⟨n⟩).hom
  let ei : Discrete.functor (fun n : ℕ => U.obj (F.obj ⟨n⟩)) ≅
      Discrete.functor (fun n : ℕ => G.obj ⟨n⟩) :=
    Discrete.natIso (fun n : Discrete ℕ => e.app ⟨n.as⟩)
  have hp : IsLimit (Fan.mk (U.obj P) p) :=
    Fan.isLimitMapConeEquiv U _ _ (isLimitOfPreserves U (productIsProduct _))
  have hq : IsLimit (Fan.mk (U.obj P) q) :=
    IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv ei (Fan.mk (U.obj P) p)).symm hp)
      (Cone.ext (Iso.refl _) fun _ => by simp [q, ei])
  apply ModuleRightDerivedLimit.isDerivedLimit_of_fan G (Iso.refl _) q hq (U.map f)
    (U.map (Pi.lift fun n : ℕ => Pi.π _ n -
      Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op))
    (U.map δ ≫ (U.commShiftIso (1 : ℤ)).hom.app X)
    (U.map_distinguished _ hT)
  intro n
  have hd : U.map (Pi.lift fun n : ℕ => Pi.π _ n -
      Pi.π _ (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) ≫ p n =
      p n - p (n + 1) ≫ U.map (F.map (homOfLE (Nat.le_succ n)).op) := by
    dsimp only [p]
    rw [← U.map_comp, Pi.lift_comp_π, U.map_sub, U.map_comp]
  show U.map _ ≫ (p n ≫ e.hom.app ⟨n⟩) = _
  rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc]
  have hn := e.hom.naturality (homOfLE (Nat.le_succ n)).op
  dsimp only [Functor.comp_map] at hn
  rw [hn, ← Category.assoc]
  rfl

/-- The limit of the constant ring system on `A` is `A`. -/
public abbrev constantLimitIso (A : Type u) [Ring A] :
    limit ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ≅ RingCat.of A :=
  limit.isoLimitCone
    ⟨constCone ℕᵒᵖ (RingCat.of A), isLimitConstCone ℕᵒᵖ (RingCat.of A)⟩

/-- Restriction of scalars along the identification of `A` with the limit of its constant ring
system. -/
public abbrev constantLimitScalars (A : Type u) [Ring A] :=
  ModuleCat.restrictScalars.{u} (constantLimitIso A).inv.hom

/-- Restriction of scalars along `constantLimitIso A` is an equivalence. -/
public theorem constantLimitScalars_isEquivalence (A : Type u) [Ring A] :
    (constantLimitScalars A).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (constantLimitIso A).symm.ringCatIsoToRingEquiv
attribute [local instance] constantLimitScalars_isEquivalence

/-- The `n`-th stage of the diagram of a constant system of complexes is, after restricting scalars
along `constantLimitIso A`, the original complex. -/
public def constantComplexIso (A : Type u) [Ring A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕᵒᵖ) :
    ((constantLimitScalars A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((complexDiagramFunctor ((Functor.const ℕᵒᵖ).obj (RingCat.of A))).obj
        (((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).obj n) ≅ K := by
  let R := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
  have h : (RingHom.id A) = (limit.π R n).hom.comp (constantLimitIso A).inv.hom :=
    (congrArg RingCat.Hom.hom (limit.isoLimitCone_inv_π
      ⟨constCone ℕᵒᵖ (RingCat.of A), isLimitConstCone ℕᵒᵖ (RingCat.of A)⟩ n)).symm
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    ((ModuleCat.restrictScalarsComp' (constantLimitIso A).inv.hom
      (limit.π R n).hom (RingHom.id A) h).symm.app _) ≪≫
      (ModuleCat.restrictScalarsId A).app _ ≪≫
      (constantSystemEvaluation A n).app (K.X i)) ?_
  intro i j hij
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The derived diagram of a constant system of complexes is, after restricting scalars, the
constant inverse system on the original complex. -/
public def constantComplexDerivedDiagramIso (A : Type u) [Ring A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((complexDerivedDiagram ((Functor.const ℕᵒᵖ).obj (RingCat.of A))).obj
      (((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ⋙
      (constantLimitScalars A).mapDerivedCategory ≅
        (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) := by
  refine NatIso.ofComponents (fun n =>
    (constantLimitScalars A).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso (constantComplexIso A K n)) ?_
  intro n m f
  let Z := (complexDiagramFunctor ((Functor.const ℕᵒᵖ).obj (RingCat.of A))).obj
    (((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h : ((constantLimitScalars A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Z.map f) ≫ (constantComplexIso A K m).hom = (constantComplexIso A K n).hom := by
    apply HomologicalComplex.Hom.ext
    funext i
    ext x
    rfl
  have h' := congrArg DerivedCategory.Q.map h
  rw [DerivedCategory.Q.map_comp] at h'
  change (constantLimitScalars A).mapDerivedCategory.map (DerivedCategory.Q.map (Z.map f)) ≫
    ((constantLimitScalars A).mapDerivedCategoryFactors.hom.app (Z.obj m) ≫
      DerivedCategory.Q.map (constantComplexIso A K m).hom) =
    ((constantLimitScalars A).mapDerivedCategoryFactors.hom.app (Z.obj n) ≫
      DerivedCategory.Q.map (constantComplexIso A K n).hom) ≫ 𝟙 _
  calc
    _ = (constantLimitScalars A).mapDerivedCategoryFactors.hom.app (Z.obj n) ≫
        (DerivedCategory.Q.map
          (((constantLimitScalars A).mapHomologicalComplex _).map (Z.map f)) ≫
            DerivedCategory.Q.map (constantComplexIso A K m).hom) :=
      (constantLimitScalars A).mapDerivedCategoryFactors_hom_naturality_assoc _ _
    _ = (constantLimitScalars A).mapDerivedCategoryFactors.hom.app (Z.obj n) ≫
        DerivedCategory.Q.map (constantComplexIso A K n).hom := congrArg _ h'
    _ = _ := (Category.comp_id _).symm

/-- The derived module diagram of the constant system on `K` is, after restricting scalars, the
constant inverse system on `K`. -/
public def constantDerivedDiagramIso (A : Type u) [Ring A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    ModuleRightDerivedLimit.derivedModuleDiagram ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
      ((constantSystem A).mapDerivedCategory.obj K) ⋙
        (constantLimitScalars A).mapDerivedCategory ≅ (Functor.const ℕᵒᵖ).obj K := by
  let R := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
  let P := DerivedCategory.Q.objPreimage K
  let e : (constantSystem A).mapDerivedCategory.obj K ≅
      DerivedCategory.Q.obj (((constantSystem A).mapHomologicalComplex _).obj P) :=
    (constantSystem A).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (constantSystem A).mapDerivedCategoryFactors.app P
  exact isoWhiskerRight
    ((derivedDiagramFunctorIso R _).symm ≪≫
      (derivedDiagramFunctor R).mapIso e ≪≫ (derivedDiagramFunctorFactors R).app _)
      (constantLimitScalars A).mapDerivedCategory ≪≫
    constantComplexDerivedDiagramIso A P ≪≫
    (Functor.const ℕᵒᵖ).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- An inverse system of `A`-modules, viewed as a module system over the constant ring system. -/
public def systemOfModuleDiagram (A : Type u) [Ring A]
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) where
  obj := M.obj
  map f := M.map f ≫ (ModuleCat.restrictScalarsId A).inv.app _
  map_id n := by
    ext x
    change M.map (𝟙 n) x = x
    exact ConcreteCategory.congr_hom (M.map_id n) x
  map_comp f g := by
    ext x
    change M.map (f ≫ g) x = M.map g (M.map f x)
    exact ConcreteCategory.congr_hom (M.map_comp f g) x

/-- An inverse system of complexes of `A`-modules, viewed as a complex of module systems over the
constant ring system. -/
public def complexSystemOfDiagram (A : Type u) [Ring A]
    (M : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ where
  X i := systemOfModuleDiagram A (M ⋙ HomologicalComplex.eval _ _ i)
  d i j :=
    { app n := (M.obj n).d i j
      naturality f := by
        ext x
        exact ConcreteCategory.congr_hom ((M.map f).comm i j) x }
  shape i j hij := PresheafOfModules.hom_ext fun n => (M.obj n).shape i j hij
  d_comp_d' i j k _ _ := PresheafOfModules.hom_ext fun n => (M.obj n).d_comp_d i j k

private def complexSystemOfDiagramIso (A : Type u) [Ring A]
    (M : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    ((complexDiagramFunctor ((Functor.const ℕᵒᵖ).obj (RingCat.of A))).obj
      (complexSystemOfDiagram A M)) ⋙
      (constantLimitScalars A).mapHomologicalComplex (ComplexShape.up ℤ) ≅ M := by
  let R := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
  have h (n : ℕᵒᵖ) : RingHom.id A =
      (limit.π R n).hom.comp (constantLimitIso A).inv.hom :=
    (congrArg RingCat.Hom.hom (limit.isoLimitCone_inv_π
      ⟨constCone ℕᵒᵖ (RingCat.of A), isLimitConstCone ℕᵒᵖ (RingCat.of A)⟩ n)).symm
  let e (n : ℕᵒᵖ) :
      (((complexDiagramFunctor R).obj (complexSystemOfDiagram A M)) ⋙
        (constantLimitScalars A).mapHomologicalComplex (ComplexShape.up ℤ)).obj n ≅
          M.obj n := HomologicalComplex.Hom.isoOfComponents
    (fun i => ((ModuleCat.restrictScalarsComp' (constantLimitIso A).inv.hom
      (limit.π R n).hom (RingHom.id A) (h n)).symm.app _) ≪≫
      (ModuleCat.restrictScalarsId A).app _) (by intros; ext x; rfl)
  exact NatIso.ofComponents e (by intros; ext i x; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_complexDiagram
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (E : ℕᵒᵖ ⥤ DerivedCategory B) :
    ∃ M : ℕᵒᵖ ⥤ CochainComplex B ℤ, Nonempty (M ⋙ DerivedCategory.Q ≅ E) := by
  classical
  let D (n : ℕ) := Σ M : CochainComplex B ℤ, DerivedCategory.Q.obj M ≅ E.obj ⟨n⟩
  have step (n : ℕ) (d : D n) :
      ∃ (d' : D (n + 1)) (t : d'.1 ⟶ d.1),
        DerivedCategory.Q.map t ≫ d.2.hom =
          d'.2.hom ≫ E.map (homOfLE (Nat.le_succ n)).op := by
    let P := DerivedCategory.Q.objPreimage (E.obj ⟨n + 1⟩)
    let e := DerivedCategory.Q.objObjPreimageIso (E.obj ⟨n + 1⟩)
    obtain ⟨M, s, hs, t, ht⟩ := DerivedCategory.right_fac
      (e.hom ≫ E.map (homOfLE (Nat.le_succ n)).op ≫ d.2.inv)
    have := hs
    refine ⟨⟨M, asIso (DerivedCategory.Q.map s) ≪≫ e⟩, t, ?_⟩
    dsimp
    have ht' := congrArg (fun f => DerivedCategory.Q.map s ≫ f ≫ d.2.hom) ht
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using ht'.symm
  let next (n : ℕ) (d : D n) : D (n + 1) := (step n d).choose
  let d : ∀ n, D n := fun n => Nat.rec
    ⟨DerivedCategory.Q.objPreimage (E.obj ⟨0⟩),
      DerivedCategory.Q.objObjPreimageIso (E.obj ⟨0⟩)⟩ next n
  let t (n : ℕ) : (d (n + 1)).1 ⟶ (d n).1 := (step n (d n)).choose_spec.choose
  let M := Functor.ofOpSequence (X := fun n => (d n).1) t
  let e : M ⋙ DerivedCategory.Q ⟶ E := NatTrans.ofOpSequence
    (fun n => (d n).2.hom) (fun n => by
      simpa only [Functor.comp_map, M, Functor.ofOpSequence_map_homOfLE_succ] using
        (step n (d n)).choose_spec.choose_spec)
  have : ∀ n, IsIso (e.app n) := fun n => inferInstanceAs (IsIso (d n.unop).2.hom)
  have : IsIso e := NatIso.isIso_of_isIso_app e
  exact ⟨M, ⟨asIso e⟩⟩

private theorem exists_lift_derivedModuleDiagram (A : Type u) [Ring A]
    (E : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A)) :
    ∃ X : DerivedCategory (PresheafOfModules.{u}
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A))),
      Nonempty (ModuleRightDerivedLimit.derivedModuleDiagram
        ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) X ⋙
        (constantLimitScalars A).mapDerivedCategory ≅ E) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_complexDiagram E
  let R := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
  let K := complexSystemOfDiagram A M
  exact ⟨DerivedCategory.Q.obj K, ⟨isoWhiskerRight
    ((derivedDiagramFunctorIso R _).symm ≪≫ (derivedDiagramFunctorFactors R).app K)
      (constantLimitScalars A).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft ((complexDiagramFunctor R).obj K)
      (constantLimitScalars A).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (complexSystemOfDiagramIso A M) DerivedCategory.Q ≪≫ e⟩⟩

set_option backward.isDefEq.respectTransparency false in
private def systemIndexEquivalence (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{u} R ≌
      PresheafOfModules.{u} ((AsSmall.down : AsSmall.{u} ℕ ⥤ ℕ).op ⋙ R) where
  functor := PresheafOfModules.pushforward₀ AsSmall.down R
  inverse := PresheafOfModules.pushforward₀ AsSmall.up _
  unitIso := NatIso.ofComponents (fun _ => PresheafOfModules.isoMk
    (fun _ => Iso.refl _) (by intros; ext x; rfl)) (by intros; ext n x; rfl)
  counitIso := NatIso.ofComponents (fun _ => PresheafOfModules.isoMk
    (fun _ => Iso.refl _) (by intros; ext x; rfl)) (by intros; ext n x; rfl)

private theorem system_enoughInjectives (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    EnoughInjectives (PresheafOfModules.{u} R) :=
  EnoughInjectives.of_equivalence (systemIndexEquivalence R).functor

private theorem system_hasExactProducts (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{u} R) :=
  HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf R)

/-- A complex satisfying `P` resolving a chosen representative of `X`, supplied by `hP`. -/
public def resolutionComplex {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (X : DerivedCategory B) : CochainComplex B ℤ :=
  (hP (DerivedCategory.Q.objPreimage X)).choose

/-- The complex `resolutionComplex P hP X` satisfies `P`. -/
public theorem resolutionComplex_prop {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (X : DerivedCategory B) : P (resolutionComplex P hP X) :=
  (hP (DerivedCategory.Q.objPreimage X)).choose_spec.choose_spec.1

/-- The resolution of `X` by a complex satisfying `P` becomes an isomorphism in `D(B)`. -/
public def resolutionIso {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (X : DerivedCategory B) : DerivedCategory.Q.obj (resolutionComplex P hP X) ≅ X :=
  letI s : resolutionComplex P hP X ⟶ DerivedCategory.Q.objPreimage X :=
    (hP (DerivedCategory.Q.objPreimage X)).choose_spec.choose
  haveI : QuasiIso s := (hP (DerivedCategory.Q.objPreimage X)).choose_spec.choose_spec.2
  asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso X

/-- A family of maps on the complexes satisfying `P`, natural in chain maps between them, is
natural in all of the morphisms of `D(B)` between their images: a morphism of `D(B)` between
two such images is a fraction, and `P` resolves the complex in its denominator. -/
public theorem map_comp_eq_of_resolutions {B D : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ⟶ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ e L hL = e K hK ≫ G.map (DerivedCategory.Q.map f))
    (K L : CochainComplex B ℤ) (hK : P K) (hL : P L)
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    F.map f ≫ e L hL = e K hK ≫ G.map f := by
  obtain ⟨M, s, hs, t, ht⟩ := DerivedCategory.right_fac f
  obtain ⟨N, w, hN, hw⟩ := hP M
  have := hs
  have := hw
  let a := w ≫ s
  let b := w ≫ t
  have ha : IsIso (DerivedCategory.Q.map a) := by
    dsimp [a]
    rw [Functor.map_comp]
    infer_instance
  have hab : DerivedCategory.Q.map a ≫ f = DerivedCategory.Q.map b := by
    simp [a, b, ht, Functor.map_comp]
  apply (cancel_epi (F.map (DerivedCategory.Q.map a))).mp
  calc
    _ = F.map (DerivedCategory.Q.map b) ≫ e L hL := by
      rw [← F.map_comp_assoc, hab]
    _ = e N hN ≫ G.map (DerivedCategory.Q.map b) := he N L hN hL b
    _ = F.map (DerivedCategory.Q.map a) ≫ e K hK ≫ G.map f := by
      rw [← Category.assoc, he N K hN hK a, Category.assoc, ← G.map_comp, hab]

/-- A family of morphisms on a resolving class of complexes descends to a natural transformation
on all of `D(B)`.

If every cochain complex admits a quasi-isomorphism from one satisfying `P`, then a family of
morphisms `F (Q K) ⟶ G (Q K)` for `P K`, natural in chain maps between complexes satisfying `P`,
determines a natural transformation `F ⟶ G` of functors on all of `D(B)`: the component at `X` is
conjugated from the component at a resolution of `X` by the resolution isomorphism, and
well-definedness is naturality along the fractions of the localization. No invertibility of the
given family is assumed; see `natIsoOfResolutions` for the version producing an isomorphism. -/
public def natTransOfResolutions
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ⟶ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ e L hL =
        e K hK ≫ G.map (DerivedCategory.Q.map f)) : F ⟶ G where
  app X := F.map (resolutionIso P hP X).inv ≫ e _ (resolutionComplex_prop P hP X) ≫
    G.map (resolutionIso P hP X).hom
  naturality X Y f := by
    have h := map_comp_eq_of_resolutions P hP F G e he _ _ (resolutionComplex_prop P hP X)
      (resolutionComplex_prop P hP Y)
      ((resolutionIso P hP X).hom ≫ f ≫ (resolutionIso P hP Y).inv)
    apply (cancel_epi (F.map (resolutionIso P hP X).hom)).mp
    apply (cancel_mono (G.map (resolutionIso P hP Y).inv)).mp
    simpa [Functor.map_comp, Category.assoc] using h

/-- The components of `natTransOfResolutions` are conjugates of the given family by the resolution
isomorphisms. -/
public theorem natTransOfResolutions_app
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ⟶ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ e L hL =
        e K hK ≫ G.map (DerivedCategory.Q.map f)) (X : DerivedCategory B) :
    (natTransOfResolutions P hP F G e he).app X =
      F.map (resolutionIso P hP X).inv ≫ e _ (resolutionComplex_prop P hP X) ≫
        G.map (resolutionIso P hP X).hom := rfl

/-- A family of isomorphisms on a resolving class of complexes descends to an isomorphism of
functors on all of `D(B)`: the underlying natural transformation is
`natTransOfResolutions`, whose components are isomorphisms because the given family is. -/
public def natIsoOfResolutions
    {B D : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [Category* D]
    (P : CochainComplex B ℤ → Prop)
    (hP : ∀ K, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K), P L ∧ QuasiIso s)
    (F G : DerivedCategory B ⥤ D)
    (e : ∀ K, P K → (F.obj (DerivedCategory.Q.obj K) ≅ G.obj (DerivedCategory.Q.obj K)))
    (he : ∀ K L (hK : P K) (hL : P L) (f : K ⟶ L),
      F.map (DerivedCategory.Q.map f) ≫ (e L hL).hom =
        (e K hK).hom ≫ G.map (DerivedCategory.Q.map f)) : F ≅ G :=
  haveI h (X : DerivedCategory B) :
      IsIso ((natTransOfResolutions P hP F G (fun K hK => (e K hK).hom) he).app X) := by
    rw [natTransOfResolutions_app]
    infer_instance
  haveI := NatIso.isIso_of_isIso_app
    (natTransOfResolutions P hP F G (fun K hK => (e K hK).hom) he)
  asIso (natTransOfResolutions P hP F G (fun K hK => (e K hK).hom) he)

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring with a K-flat complex sends quasi-isomorphisms to isomorphisms in the derived
category. -/
public theorem tensorComplex_inverts (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).IsInvertedBy
      (TleftCochain P ⋙ DerivedCategory.Q) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  intro X Y f hf
  have h := (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso P hP)
    ((HomotopyCategory.quotient _ _).map f)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
  change HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright P).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  have : QuasiIso ((TrightCochain P).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h
  have hc : DerivedCategory.Q.map ((TleftCochain P).map f) ≫
      DerivedCategory.Q.map (β_ P Y).hom =
    DerivedCategory.Q.map (β_ P X).hom ≫
      DerivedCategory.Q.map ((TrightCochain P).map f) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (BraidedCategory.braiding_naturality_right P f)
  exact IsIso.of_isIso_fac_right hc

/-- Tensoring with a K-flat complex `P`, as an endofunctor of `D(A)`. -/
public def tensorComplexDerived (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (TleftCochain P ⋙ DerivedCategory.Q)
    (tensorComplex_inverts A P hP) DerivedCategory.Q

/-- `tensorComplexDerived A P hP` composed with the localization functor is tensoring with `P`
followed by localization. -/
public def tensorComplexDerivedFactors (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    DerivedCategory.Q ⋙ tensorComplexDerived A P hP ≅ TleftCochain P ⋙ DerivedCategory.Q :=
  Localization.fac _ (tensorComplex_inverts A P hP) _

set_option backward.isDefEq.respectTransparency false in
/-- For K-flat `P`, the derived tensor product with `P` agrees with
`tensorComplexDerived A P hP`. -/
public def derivedTensorComplexIso (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    T.tensor.obj (DerivedCategory.Q.obj P) ≅ tensorComplexDerived A P hP := by
  apply natIsoOfResolutions (B := ModuleCat.{u} A) (fun K => K.KFlat)
    (fun K => by
      obtain ⟨L, f, hL, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
      exact ⟨L, f, hL, hf⟩)
    _ _
    (fun K hK => T.comparison P K hP hK ≪≫ (tensorComplexDerivedFactors A P hP).symm.app K)
  intro K L hK hL f
  have ht := T.comparison_naturality (𝟙 P) f hP hP hK hL
  have ht' : (T.tensor.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map f) ≫
      (T.comparison P L hP hL).hom =
    (T.comparison P K hP hK).hom ≫ DerivedCategory.Q.map ((TleftCochain P).map f) := by
    simp only [map_id, NatTrans.id_app, Category.id_comp] at ht
    convert! ht using 1
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ht', Category.assoc, Category.assoc]
  exact congrArg ((T.comparison P K hP hK).hom ≫ ·)
    ((tensorComplexDerivedFactors A P hP).inv.naturality f)

/-- For K-flat `P`, the derived tensor product with `P` on complexes is tensoring with `P` followed
by localization. -/
public def derivedTensorComplexComparison (A : Type u) [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj P) ≅
      TleftCochain P ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q (derivedTensorComplexIso A T P hP) ≪≫
    tensorComplexDerivedFactors A P hP

/-- A module system over the constant ring system on `A`, viewed as an inverse system of
`A`-modules. -/
public def moduleDiagramOfSystem (A : Type u) [Ring A] :
    PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ⥤
      (ℕᵒᵖ ⥤ ModuleCat.{u} A) where
  obj M :=
    { obj := M.obj
      map f := M.map f ≫ (ModuleCat.restrictScalarsId A).hom.app _
      map_id n := by
        ext x
        change M.map (𝟙 n) x = x
        simp
        rfl
      map_comp f g := by ext x; exact M.map_comp_apply f g x }
  map f :=
    { app := f.app
      naturality _ _ g := by ext x; exact PresheafOfModules.naturality_apply f g x }
  map_id _ := by ext n; rfl
  map_comp _ _ := by ext n; rfl

/-- The functor `moduleDiagramOfSystem A` is additive. -/
public theorem moduleDiagramOfSystem_additive (A : Type u) [Ring A] :
    (moduleDiagramOfSystem A).Additive where
  map_add := by intros; ext; rfl
attribute [local instance] moduleDiagramOfSystem_additive

/-- A complex of module systems over the constant ring system on `A`, viewed as an inverse system
of complexes of `A`-modules. -/
public abbrev complexEvaluationDiagram (A : Type u) [Ring A] :=
  (moduleDiagramOfSystem A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

set_option backward.isDefEq.respectTransparency false in
/-- The diagram of a complex of constant-ring module systems is, after restricting scalars along
`constantLimitIso A`, its evaluation diagram. -/
public def complexDiagramScalarsIso (A : Type u) [Ring A]
    (K : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ) :
    (complexDiagramFunctor ((Functor.const ℕᵒᵖ).obj (RingCat.of A))).obj K ⋙
      (constantLimitScalars A).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (complexEvaluationDiagram A).obj K := by
  let R := (Functor.const ℕᵒᵖ).obj (RingCat.of A)
  have h (n : ℕᵒᵖ) : RingHom.id A =
      (limit.π R n).hom.comp (constantLimitIso A).inv.hom :=
    (congrArg RingCat.Hom.hom (limit.isoLimitCone_inv_π
      ⟨constCone ℕᵒᵖ (RingCat.of A), isLimitConstCone ℕᵒᵖ (RingCat.of A)⟩ n)).symm
  refine NatIso.ofComponents (fun n => HomologicalComplex.Hom.isoOfComponents
    (fun i => ((ModuleCat.restrictScalarsComp' (constantLimitIso A).inv.hom
      (limit.π R n).hom (RingHom.id A) (h n)).symm.app _) ≪≫
      (ModuleCat.restrictScalarsId A).app _) (by intros; ext x; rfl)) ?_
  intros
  ext i x
  rfl

/-- The derived module diagram of a complex of constant-ring module systems is, after restricting
scalars, the localization of its evaluation diagram. -/
public def derivedModuleDiagramComplexIso (A : Type u) [Ring A]
    (K : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ) :
    ModuleRightDerivedLimit.derivedModuleDiagram ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
      (DerivedCategory.Q.obj K) ⋙ (constantLimitScalars A).mapDerivedCategory ≅
        (complexEvaluationDiagram A).obj K ⋙ DerivedCategory.Q :=
  isoWhiskerRight ((derivedDiagramFunctorIso _ _).symm ≪≫
    (derivedDiagramFunctorFactors _).app K) (constantLimitScalars A).mapDerivedCategory ≪≫
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _
    (constantLimitScalars A).mapDerivedCategoryFactors ≪≫
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (complexDiagramScalarsIso A K) DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private def tensorEvaluationIso (A : Type u) [CommRing A]
    (M : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ)
    (n : ℕ) (hM : CochainComplex.KFlat ((complexEvaluationDiagram A).obj M |>.obj ⟨n⟩)) :
    ((ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
      (CommRingCat.of A))).tensor.flip.obj
      (DerivedCategory.Q.obj M)) ⋙
        (PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
          ⟨n⟩).mapDerivedCategory ≅
      (PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ⟨n⟩).mapDerivedCategory
        ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.flip.obj
          (DerivedCategory.Q.obj (((complexEvaluationDiagram A).obj M).obj ⟨n⟩)) := by
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let V := PresheafOfModules.evaluation ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) ⟨n⟩
  let P : CochainComplex (ModuleCat.{u} A) ℤ := ((complexEvaluationDiagram A).obj M).obj ⟨n⟩
  let F := S.tensor.obj (DerivedCategory.Q.obj M) ⋙ V.mapDerivedCategory
  let G := V.mapDerivedCategory ⋙ T.tensor.obj (DerivedCategory.Q.obj P)
  let s : DerivedCategory.Q ⋙ F ≅
      V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TleftCochain (C := ModuleCat.{u} A) P ⋙
        DerivedCategory.Q :=
    NatIso.ofComponents (fun N => S.evaluationIso M N n hM)
      (fun f => (S.evaluationIso_naturality_right M _ _ n hM f).symm)
  let t : DerivedCategory.Q ⋙ G ≅
      V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TleftCochain (C := ModuleCat.{u} A) P ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight V.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (derivedTensorComplexComparison A T P hM)
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (DerivedCategory.Q ⋙ F) F :=
    ⟨Iso.refl _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (DerivedCategory.Q ⋙ G) G :=
    ⟨Iso.refl _⟩
  exact isoWhiskerRight (S.symmetry.app (DerivedCategory.Q.obj M)).symm _ ≪≫
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ F G (s ≪≫ t.symm) ≪≫
    isoWhiskerLeft V.mapDerivedCategory
      ((CochainComplex.DerivedTensor.derivedTensorProductKoszulBraiding A).iso.app
        (DerivedCategory.Q.obj P))

set_option backward.isDefEq.respectTransparency false in
/-- The stagewise identifications of the total tensor system with the tensor products of the
stages are compatible with the transition maps. -/
public theorem totalTensorEvaluation_naturality (A : Type u) [CommRing A]
    (M N : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ)
    {n m : ℕᵒᵖ} (f : n ⟶ m) :
    let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
      (CommRingCat.of A))
    let DM := (complexEvaluationDiagram A).obj M
    let DN := (complexEvaluationDiagram A).obj N
    let X := ((ModuleSystemKFlatComparison.totalTensorSystem.{u, u} ((Functor.const ℕᵒᵖ).obj
      (CommRingCat.of A))).obj M).obj N
    ((complexEvaluationDiagram A).obj X).map f ≫
        (S.totalTensorEvaluationIso M N m.unop).hom =
      (S.totalTensorEvaluationIso M N n.unop).hom ≫
        HomologicalComplex.mapBifunctorMap (DM.map f) (DN.map f)
          (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) := by
  dsimp only
  let AR := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} AR
  let DM := (complexEvaluationDiagram A).obj M
  let DN := (complexEvaluationDiagram A).obj N
  let X := ((ModuleSystemKFlatComparison.totalTensorSystem.{u, u} AR).obj M).obj N
  let V (i : ℕᵒᵖ) := PresheafOfModules.evaluation (AR ⋙ forget₂ CommRingCat RingCat) i
  let : (ModuleSystemKFlatComparison.systemTensor.{u, u} AR).PreservesZeroMorphisms :=
    { map_zero := by
        intro source target
        apply NatTrans.ext
        funext other
        apply PresheafOfModules.hom_ext
        intro stage
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext left right
        simp [ModuleSystemKFlatComparison.systemTensor,
          ModuleSystemKFlatComparison.tensorSystemMap] }
  let : ∀ other, ((ModuleSystemKFlatComparison.systemTensor.{u, u} AR).obj
    other).PreservesZeroMorphisms := by
    refine fun other => { map_zero := fun source target => ?_ }
    apply PresheafOfModules.hom_ext
    intro stage
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext left right
    simp [ModuleSystemKFlatComparison.systemTensor, ModuleSystemKFlatComparison.tensorSystemMap]
  apply HomologicalComplex.Hom.ext
  funext k
  let e (j : ℕᵒᵖ) := (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k).mapIso
    (S.totalTensorEvaluationIso M N j.unop)
  apply (cancel_epi (e n).inv).mp
  show (e n).inv ≫ (((complexEvaluationDiagram A).obj X).map f |>.f k) ≫ (e m).hom =
    (e n).inv ≫ (e n).hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := DM.obj n) (K₂ := DN.obj n)
    (F := curriedTensor (ModuleCat.{u} A))
  intro p q hpq
  let ι := HomologicalComplex.ιMapBifunctor M N (ModuleSystemKFlatComparison.systemTensor.{u, u} AR)
    (ComplexShape.up ℤ) p q k hpq
  have hι (j : ℕᵒᵖ) : (V j).map ι ≫ (e j).hom =
      HomologicalComplex.ιMapBifunctor (DM.obj j) (DN.obj j)
        (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) p q k hpq := by
    convert S.totalTensorEvaluationIso_ι M N j.unop p q k hpq using 1 <;> rfl
  have hi : (V n).map ι ≫ (((complexEvaluationDiagram A).obj X).map f |>.f k) =
      ((curriedTensor (ModuleCat.{u} A)).map ((DM.map f).f p)).app ((DN.obj n).X q) ≫
        ((curriedTensor (ModuleCat.{u} A)).obj ((DM.obj m).X p)).map ((DN.map f).f q) ≫
          (V m).map ι := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact (PresheafOfModules.naturality_apply ι f (x ⊗ₜ[A] y)).symm
  calc
    _ = (V n).map ι ≫ (((complexEvaluationDiagram A).obj X).map f |>.f k) ≫ (e m).hom := by
      rw [← hι n]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [← Category.assoc, hi]
      simp only [Category.assoc, hι m, HomologicalComplex.ι_mapBifunctorMap]
      rfl

/-- An isomorphism in `D(ℕ, R)` induces an isomorphism of derived module diagrams. -/
public def derivedModuleDiagramIso (R : ℕᵒᵖ ⥤ RingCat.{u})
    {X Y : DerivedCategory (PresheafOfModules.{u} R)} (e : X ≅ Y) :
    ModuleRightDerivedLimit.derivedModuleDiagram R X ≅ ModuleRightDerivedLimit.derivedModuleDiagram
      R Y :=
  (derivedDiagramFunctorIso R X).symm ≪≫
    (derivedDiagramFunctor R).mapIso e ≪≫ derivedDiagramFunctorIso R Y

/-- The evaluation diagram of a constant system of complexes is the constant inverse system on
the complex. -/
public def constantComplexEvaluationIso (A : Type u) [Ring A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexEvaluationDiagram A).obj
      (((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (Functor.const ℕᵒᵖ).obj P :=
  NatIso.ofComponents (fun n => HomologicalComplex.Hom.isoOfComponents
    (fun i => (constantSystemEvaluation A n).app (P.X i)) (by intros; ext x; rfl))
    (by intros; ext i x; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- Elaborating the tensor products of complexes of module systems here is expensive.
/-- The evaluation diagram of the total tensor product of a constant system on `P` with `M` is the
evaluation diagram of `M` tensored with `P`. -/
public def constantTensorComplexDiagramIso (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ) :
    (complexEvaluationDiagram A).obj
      (((ModuleSystemKFlatComparison.totalTensorSystem.{u, u} ((Functor.const ℕᵒᵖ).obj
        (CommRingCat.of A))).obj
        (((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).obj M) ≅
      (complexEvaluationDiagram A).obj M ⋙ TleftCochain P := by
  let Z := ((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let D := (complexEvaluationDiagram A).obj M
  let c := constantComplexEvaluationIso A P
  refine NatIso.ofComponents (fun n => S.totalTensorEvaluationIso Z M n.unop ≪≫
    tensorIso (c.app n) (Iso.refl (D.obj n))) ?_
  intro n m f
  change _ ≫ ((S.totalTensorEvaluationIso Z M m.unop).hom ≫
      ((c.app m).hom ⊗ₘ 𝟙 (D.obj m))) =
    ((S.totalTensorEvaluationIso Z M n.unop).hom ≫
      ((c.app n).hom ⊗ₘ 𝟙 (D.obj n))) ≫ (𝟙 P ⊗ₘ D.map f)
  rw [← Category.assoc, totalTensorEvaluation_naturality, Category.assoc, Category.assoc]
  congr 1
  change (((complexEvaluationDiagram A).obj Z).map f ⊗ₘ D.map f) ≫
      ((c.app m).hom ⊗ₘ 𝟙 (D.obj m)) =
    ((c.app n).hom ⊗ₘ 𝟙 (D.obj n)) ≫ (𝟙 P ⊗ₘ D.map f)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have hc := c.hom.naturality f
  dsimp only [Functor.const_obj_map] at hc
  simp only [Category.comp_id, Category.id_comp] at hc ⊢
  change (((complexEvaluationDiagram A).obj Z).map f ≫ c.hom.app m) ⊗ₘ D.map f =
    (c.hom.app n ≫ 𝟙 P) ⊗ₘ D.map f
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- The derived module diagram of the derived tensor product of `M` with a constant system on `K`
is, after restricting scalars, the diagram of `M` tensored with `K`. -/
public def tensorDerivedDiagramIso (A : Type u) [CommRing A]
    (M : CochainComplex (PresheafOfModules.{u}
      ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    ModuleRightDerivedLimit.derivedModuleDiagram ((Functor.const ℕᵒᵖ).obj (RingCat.of A))
      (((ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
        (CommRingCat.of A))).tensor.flip.obj
        (DerivedCategory.Q.obj M)).obj ((constantSystem A).mapDerivedCategory.obj K)) ⋙
        (constantLimitScalars A).mapDerivedCategory ≅
      ((complexEvaluationDiagram A).obj M ⋙ DerivedCategory.Q) ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K := by
  apply Classical.choice
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution
    (DerivedCategory.Q.objPreimage K)
  have := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let Z := ((constantSystem A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hZ (n : ℕ) : CochainComplex.KFlat (((complexEvaluationDiagram A).obj Z).obj ⟨n⟩) :=
    CochainComplex.KFlat.of_iso ((constantComplexEvaluationIso A P).app ⟨n⟩).symm hP
  let eZ := (constantSystem A).mapDerivedCategory.mapIso e.symm ≪≫
    (constantSystem A).mapDerivedCategoryFactors.app P
  let eS := (S.tensor.flip.obj (DerivedCategory.Q.obj M)).mapIso eZ ≪≫
    S.comparison Z M hZ
  exact ⟨isoWhiskerRight (derivedModuleDiagramIso _ eS) _ ≪≫
    derivedModuleDiagramComplexIso A _ ≪≫
    isoWhiskerRight (constantTensorComplexDiagramIso A P M) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (derivedTensorComplexComparison A T P hP).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (T.tensor.mapIso e)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 091J.** The construction is the composite of the constant-system functor,
derived tensor product with a lift of `E` in the derived category of compatible systems,
and derived inverse limit. Its value at `K` is a derived limit of `K ⊗ᴸ[A] Eₙ`. -/
@[stacks 091J]
public theorem exists_exactFunctor_isDerivedLimit_tensor
    (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ CochainComplex.DerivedTensor.DObj A) :
    let AR : ℕᵒᵖ ⥤ CommRingCat.{u} := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
    let R : ℕᵒᵖ ⥤ RingCat.{u} := AR ⋙ forget₂ CommRingCat RingCat
    let C := PresheafOfModules.{u} R
    let DA := CochainComplex.DerivedTensor.DObj A
    let DN := DerivedCategory C
    let DB := DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u}))
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
    let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} AR
    let L : C ⥤ ModuleCat.{u} (limit R : RingCat.{u}) := ModuleInverseLimit.inverseLimit R
    ∃ (ρ : (limit R : RingCat.{u}) ≅ RingCat.of A),
      letI : (ModuleCat.restrictScalars.{u} ρ.inv.hom).IsEquivalence :=
        ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
          ρ.symm.ringCatIsoToRingEquiv
      let U : DB ⥤ DA := (ModuleCat.restrictScalars.{u} ρ.inv.hom).mapDerivedCategory
      ∃ (hL : L.Additive),
      letI := hL
      ∃ (Δ : DA ⥤ DN)
        (_ : ∀ n : ℕᵒᵖ,
          Δ ⋙ (PresheafOfModules.evaluation R n).mapDerivedCategory ≅ 𝟭 DA)
        (_ : ∀ K : DA,
          ModuleRightDerivedLimit.derivedModuleDiagram R (Δ.obj K) ⋙ U ≅
            (Functor.const ℕᵒᵖ).obj K)
        (Etilde : DN)
        (_ : ModuleRightDerivedLimit.derivedModuleDiagram R Etilde ⋙ U ≅ E)
        (RF : DN ⥤ DB)
        (α : L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        (hRFShift : RF.CommShift ℤ),
        letI := hRFShift
        RF.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
        RF.IsTriangulated ∧
        (∀ X : DN, ∃ _ : HasProduct fun n : ℕ ↦
            (ModuleRightDerivedLimit.derivedModuleDiagram R X).obj ⟨n⟩,
          IsDerivedLimit (ModuleRightDerivedLimit.derivedModuleDiagram R X) (RF.obj X)) ∧
        let tensorE := S.tensor.flip.obj Etilde
        ∃ (_ : ∀ n : ℕᵒᵖ,
          tensorE ⋙ (PresheafOfModules.evaluation R n).mapDerivedCategory ≅
            (PresheafOfModules.evaluation R n).mapDerivedCategory ⋙
              T.tensor.flip.obj (E.obj n))
          (_ : ∀ K : DA,
            ModuleRightDerivedLimit.derivedModuleDiagram R (tensorE.obj (Δ.obj K)) ⋙ U ≅
              E ⋙ T.tensor.obj K),
        let F := (Δ ⋙ tensorE) ⋙ RF ⋙ U
        ∃ (hF : F.CommShift ℤ),
          letI := hF
          F.IsTriangulated ∧
            ∀ K, ∃ (_ : HasProduct fun n : ℕ ↦
              (E ⋙ T.tensor.obj K).obj ⟨n⟩),
              IsDerivedLimit (E ⋙ T.tensor.obj K) (F.obj K) := by
  classical
  refine ⟨limit.isoLimitCone
    ⟨constCone ℕᵒᵖ (RingCat.of A), isLimitConstCone ℕᵒᵖ (RingCat.of A)⟩, ?_⟩
  obtain ⟨hL, RF, α, hRF, -⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A) ⋙ forget₂ CommRingCat RingCat)
  refine ⟨hL, ?_⟩
  have := hL
  have := hRF
  let hRFShift := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso
      (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A) ⋙
        forget₂ CommRingCat RingCat))
      (ComplexShape.up ℤ)) ℤ
  have hlim := ModuleRightDerivedLimit.rightDerivedInverseLimit_isDerivedLimit
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A) ⋙ forget₂ CommRingCat RingCat)
    hL RF α hRF
  refine ⟨(constantSystem A).mapDerivedCategory, constantDerivedEvaluation A,
    constantDerivedDiagramIso A, ?_⟩
  obtain ⟨X, ⟨eX⟩⟩ := exists_lift_derivedModuleDiagram A E
  obtain ⟨M, eM, hM⟩ := ModuleSystemKFlat.exists_representative_with_kFlat_components.{u, u + 1}
    (A := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)) X
  change CochainComplex (PresheafOfModules.{u} ((Functor.const ℕᵒᵖ).obj (RingCat.of A))) ℤ at M
  let Etilde := DerivedCategory.Q.obj M
  let eE := (derivedModuleDiagramComplexIso A M).symm ≪≫
    isoWhiskerRight (derivedModuleDiagramIso _ eM) (constantLimitScalars A).mapDerivedCategory ≪≫ eX
  have hRFExact : let := hRFShift; RF.IsTriangulated := by
    apply Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    intro K
    have := system_enoughInjectives
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A) ⋙ forget₂ CommRingCat RingCat)
    have := system_hasExactProducts
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A) ⋙ forget₂ CommRingCat RingCat)
    obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
    exact ⟨I, f, hI, hf⟩
  refine ⟨Etilde, derivedModuleDiagramComplexIso A M ≪≫ eE,
    RF, α, hRFShift, hRF, hRFExact, hlim, ?_⟩
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} ((Functor.const ℕᵒᵖ).obj
    (CommRingCat.of A))
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let tensorE := S.tensor.flip.obj Etilde
  let eTensor (K : DerivedCategory (ModuleCat.{u} A)) := tensorDerivedDiagramIso A M K ≪≫
    isoWhiskerRight eE (T.tensor.obj K)
  refine ⟨(fun n => tensorEvaluationIso A M n.unop (hM n.unop) ≪≫
    isoWhiskerLeft _ (T.tensor.flip.mapIso (eE.app n))), eTensor, ?_⟩
  let := S.commShift_left Etilde
  have := S.exact_left Etilde
  let := hRFShift
  have := hRFExact
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence (constantLimitScalars A)
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro K
  obtain ⟨hprod, hlimK⟩ := hlim (tensorE.obj ((constantSystem A).mapDerivedCategory.obj K))
  let := hprod
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u}
      (limit ((Functor.const ℕᵒᵖ).obj (RingCat.of A)) : RingCat.{u}))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact isDerivedLimit_map_of_iso (constantLimitScalars A).mapDerivedCategory _ _
    (eTensor K) _ hlimK

end
end Construction

section Exactness

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

/-- **Stacks 091K.** The canonical composite `Rlim ∘ (ΔK ⊗ᴸ[A] -)` from `D(ℕ, A)` to
`D(A)` is exact. Equivalently, its canonical image of every distinguished triangle is
distinguished. -/
@[stacks 091K]
public theorem derivedLimit_tensor_mapTriangle_distinguished
    (A : Type u) [CommRing A]
    (K : CochainComplex.DerivedTensor.DObj A) :
    let AR : ℕᵒᵖ ⥤ CommRingCat.{u} := (Functor.const ℕᵒᵖ).obj (CommRingCat.of A)
    let R : ℕᵒᵖ ⥤ RingCat.{u} := AR ⋙ forget₂ CommRingCat RingCat
    let C := PresheafOfModules.{u} R
    let DA := CochainComplex.DerivedTensor.DObj A
    let DN := DerivedCategory C
    let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u} AR
    let L : C ⥤ ModuleCat.{u} (limit R : RingCat.{u}) := ModuleInverseLimit.inverseLimit R
    ∃ (ρ : (limit R : RingCat.{u}) ≅ RingCat.of A),
      letI : (ModuleCat.restrictScalars.{u} ρ.inv.hom).IsEquivalence :=
        ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
          ρ.symm.ringCatIsoToRingEquiv
      let U : DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})) ⥤ DA :=
        (ModuleCat.restrictScalars.{u} ρ.inv.hom).mapDerivedCategory
      ∃ (hL : L.Additive),
        letI := hL
        ∃ (Δ : DA ⥤ DN)
          (_ : ∀ n : ℕᵒᵖ,
            Δ ⋙ (PresheafOfModules.evaluation R n).mapDerivedCategory ≅ 𝟭 DA)
          (_ : ModuleRightDerivedLimit.derivedModuleDiagram R (Δ.obj K) ⋙ U ≅
            (Functor.const ℕᵒᵖ).obj K)
          (RF : DN ⥤ DerivedCategory (ModuleCat.{u} (limit R : RingCat.{u})))
          (α : L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ RF)
          (hRFShift : RF.CommShift ℤ),
          letI := hRFShift
          RF.IsRightDerivedFunctor α
              (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
            RF.IsTriangulated ∧
            let tensorK := S.tensor.obj (Δ.obj K)
            let hTensorShift : tensorK.CommShift ℤ := S.commShift_right (Δ.obj K)
            letI := hTensorShift
            let G := tensorK ⋙ RF ⋙ U
            let hGShift : G.CommShift ℤ := inferInstance
            letI := hGShift
            G.IsTriangulated := by
  let E : ℕᵒᵖ ⥤ CochainComplex.DerivedTensor.DObj A := (Functor.const ℕᵒᵖ).obj K
  obtain ⟨ρ, hL, Δ, hΔeval, hΔdiagram, Etilde, hEtilde, RF, α, hRFShift,
      hRFderived, hRFexact, hlimits, htensorEval, htensorDiagram, hFShift, hFexact, hFcompute⟩ :=
    ModuleSystemRlimTensor.exists_exactFunctor_isDerivedLimit_tensor A E
  refine ⟨ρ, hL, Δ, hΔeval, hΔdiagram K, RF, α, hRFShift, hRFderived, hRFexact, ?_⟩
  dsimp
  let S := ModuleSystemKFlatComparison.derivedTensorProduct.{u, u}
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A))
  let : (S.tensor.obj (Δ.obj K)).CommShift ℤ := S.commShift_right (Δ.obj K)
  let : (S.tensor.obj (Δ.obj K)).IsTriangulated := S.exact_right (Δ.obj K)
  let : RF.CommShift ℤ := hRFShift
  let : RF.IsTriangulated := hRFexact
  infer_instance
end

end Exactness

end ModuleSystemRlimTensor
