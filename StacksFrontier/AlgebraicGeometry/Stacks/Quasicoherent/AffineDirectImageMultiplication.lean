module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackDirectImageUnit

/-!
# The multiplication of the direct image of the structure sheaf

Let `g : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks. The direct image `g_*𝒪_𝒰` is the right Kan
extension along `g`: its sections over `y` are the compatible families of functions on the legs
`j = (x, g x ⟶ y)`. Multiplying such families leg by leg is the multiplication
`g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` of `𝒪_𝒳`-modules, the sheafification of the objectwise map
`s ⊗ s' ↦ (s_j · s'_j)_j`. For `g` affine it is a map of quasi-coherent modules, and at an object
`y` with a terminal arrow `(x₀, g x₀ ⟶ y)`, through `Γ(y, g_*𝒪_𝒰) ≅ Γ(x₀, 𝒪_𝒰)`, it is the
multiplication of the ring `Γ(x₀, 𝒪_𝒰)`.

This is the `𝒪_𝒳`-algebra structure on `g_*𝒪_𝒰` which makes the pullback of `g_*𝒪_𝒰` to a point
`Spec B ⟶ 𝒳` the ring of functions of the fibre product `Spec B ×_𝒳 𝒰`, used in the proof of
Stacks 0GRP: an isomorphism of tensor functors induces ring isomorphisms between these rings.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageMulPresheafMap`: the objectwise
  multiplication of the right Kan extension of `𝒪_𝒰`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.directImageMulRan`: its sheafification.
* `AlgebraicGeometry.Stack.AlgebraicStacks.affineDirectImageMul`: the multiplication
  `g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` in `QCoh(𝒪_𝒳)`, for `g` affine.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointSectionsAddEquiv`: `y^*(g_*𝒪_𝒰) ≃ Γ(x₀, 𝒪_𝒰)` at
  a terminal arrow `(x₀, g x₀ ⟶ y)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ranπ_directImageMulApp`: on the legs the
  multiplication is the multiplication of functions.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointSectionsAddEquiv_affineDirectImageMul`: at a
  point, the multiplication is the multiplication of `Γ(x₀, 𝒪_𝒰)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pointSectionsAddEquiv_map`: naturality in
  endomorphisms of `𝒪_𝒰`.

## Implementation notes

The structure sheaf of `𝒰` is spelled `quasicoherentUnit 𝒰`, whose module is
`(SheafOfModules.unit _ : Stack.fppfModules B S hS 𝒰)`, everywhere it meets the direct image or
its sections: two spellings of the same structure sheaf unify only by unfolding the structure
sheaves, which exceeds the heartbeat budget inside the sections formulas.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)

/-- The structure map of the canonical direct image along `g`. -/
local notation "𝔣" => moduleDirectImageStructureMap B S hS 𝒰.val.val.p
  𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
  (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  B.topology le_rfl

/-- The structure sheaf of `𝒰`, as a quasi-coherent module. -/
abbrev quasicoherentUnit (𝒰 : AlgebraicStacks.{u, w} B S hS) : quasicoherentModules B S hS 𝒰 :=
  ⟨(SheafOfModules.unit _ : Stack.fppfModules B S hS 𝒰), SheafOfModules.isQuasicoherentOnSite_unit
      _⟩

section Legs

variable {y : 𝒳.val.val.obj}

/-- The objectwise tensor square `(g_*𝒪_𝒰)(y) ⊗_{𝒪(y)} (g_*𝒪_𝒰)(y)`, for the canonical direct
image. -/
abbrev directImageMulSections (y : 𝒳.val.val.obj) :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
    ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val
    ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val).obj (op y)

/-- The leg at `j = (x, g x ⟶ y)` of the limit computing `(g_*𝒪_𝒰)(y)`, with values in the ring
`𝒪_𝒰(x)`. -/
abbrev directImageUnitLeg
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.obj (op y) →+
      FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop :=
  (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
    (quasicoherentUnit 𝒰).obj.val.presheaf (op y) j).hom

variable {g} in
/-- The legs of `g_*𝒪_𝒰` are semilinear along the ring maps `𝒪_𝒳(y) ⟶ 𝒪_𝒰(x)`. -/
theorem directImageUnitLeg_smul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op y))
    (s : ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.obj (op y)) :
    directImageUnitLeg g j (r • s) =
      (show FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop from
        (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
          (op y) j).hom r) *
        directImageUnitLeg g j s :=
  ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranSMul_π
    (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom (quasicoherentUnit 𝒰).obj.val (op y) r j) s

variable {g} in
/-- The legs of `g_*𝒪_𝒰` form a cone of rings. -/
theorem directImageUnitLeg_naturality
    {j₁ j₂ : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (s : ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.obj (op y)) :
    ((FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
        .fppf).obj.map φ.right).hom (directImageUnitLeg g j₁ s) = directImageUnitLeg g j₂ s :=
  ConcreteCategory.congr_hom
    (Stacks.SheafOfModules.ranπ_naturality (CatFiberedInGroupoids.homFunctor g.hom).op
      (quasicoherentUnit 𝒰).obj.val.presheaf φ) s

/-- The leg at `j = (x, g x ⟶ y)` of the multiplication: `s ⊗ s' ↦ s_j · s'_j`. -/
def directImageMulLeg
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    directImageMulSections g y →+ FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop :=
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.comp (directImageUnitLeg g j)).compl₂ (directImageUnitLeg g j))
    (fun r s s' =>
      (congrArg (· * directImageUnitLeg g j s') (directImageUnitLeg_smul j r s)).trans
        ((mul_assoc _ _ _).trans ((mul_left_comm _ _ _).trans
          (congrArg (directImageUnitLeg g j s * ·) (directImageUnitLeg_smul j r s').symm))))

/-- **The multiplication on a leg**: `s ⊗ s' ↦ s_j · s'_j`. -/
theorem directImageMulLeg_tmul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (s s' : ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.obj (op y)) :
    directImageMulLeg g j (s ⊗ₜ s') = directImageUnitLeg g j s * directImageUnitLeg g j s' :=
  rfl

variable {g} in
/-- The legs of the multiplication form a cone. -/
theorem directImageMulLeg_naturality
    {j₁ j₂ : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (z : directImageMulSections g y) :
    ((FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
        .fppf).obj.map φ.right).hom (directImageMulLeg g j₁ z) = directImageMulLeg g j₂ z := by
  induction z using TensorProduct.inductionOn with
  | tmul s s' =>
    exact ((RingCat.Hom.hom _).map_mul _ _).trans (congrArg₂ (· * ·)
      (directImageUnitLeg_naturality φ s) (directImageUnitLeg_naturality φ s'))
  | add z z' hz hz' =>
    exact (congrArg _ ((directImageMulLeg g j₁).map_add z z')).trans
      (((RingCat.Hom.hom _).map_add _ _).trans ((congrArg₂ (· + ·) hz hz').trans
        ((directImageMulLeg g j₂).map_add z z').symm))

variable (y) in
/-- The cone of multiplication legs over the diagram computing the sections of `g_*𝒪_𝒰` over
`y`. -/
def directImageMulCone : Cone (StructuredArrow.proj (op y)
    (CatFiberedInGroupoids.homFunctor g.hom).op ⋙
      (quasicoherentUnit 𝒰).obj.val.presheaf) where
  pt := AddCommGrpCat.of (directImageMulSections g y)
  π :=
    { app := fun j => AddCommGrpCat.ofHom (directImageMulLeg g j)
      naturality := fun j₁ j₂ φ => by
        ext z
        exact (directImageMulLeg_naturality φ z).symm }

variable (y) in
/-- **The multiplication `g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` on sections over `y`**, objectwise:
`s ⊗ s' ↦ (s_j · s'_j)_j`, defined by its legs. -/
def directImageMulApp :
    AddCommGrpCat.of (directImageMulSections g y) ⟶
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.presheaf.obj (op y) :=
  (Stacks.SheafOfModules.ranIsLimit (CatFiberedInGroupoids.homFunctor g.hom).op
    (quasicoherentUnit 𝒰).obj.val.presheaf (op y)).lift (directImageMulCone g y)

/-- **The legs of the multiplication** at `y` are the products of the legs. -/
theorem ranπ_directImageMulApp
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (z : directImageMulSections g y) :
    directImageUnitLeg g j ((directImageMulApp g y).hom z) = directImageMulLeg g j z :=
  ConcreteCategory.congr_hom ((Stacks.SheafOfModules.ranIsLimit
    (CatFiberedInGroupoids.homFunctor g.hom).op
    (quasicoherentUnit 𝒰).obj.val.presheaf (op y)).fac (directImageMulCone g y) j) z

/-- The multiplication legs are compatible with restriction along `y' ⟶ y`. -/
theorem directImageMulLeg_map {y' : 𝒳.val.val.obj} (k : op y ⟶ op y')
    (j : StructuredArrow (op y') (CatFiberedInGroupoids.homFunctor g.hom).op)
    (z : directImageMulSections g y) :
    directImageMulLeg g j ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val).map k z) =
        directImageMulLeg g ((StructuredArrow.map k).obj j) z := by
  have h1 : ∀ s, directImageUnitLeg g j
      (((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val.map k s) =
        directImageUnitLeg g ((StructuredArrow.map k).obj j) s := fun s =>
    ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranπ_map
      (CatFiberedInGroupoids.homFunctor g.hom).op (quasicoherentUnit 𝒰).obj.val.presheaf k j) s
  induction z using TensorProduct.inductionOn with
  | tmul s s' =>
    exact (directImageMulLeg_tmul g j _ _).trans ((congrArg₂ (· * ·) (h1 s) (h1 s')).trans
      (directImageMulLeg_tmul g _ s s').symm)
  | add z z' hz hz' =>
    exact (congrArg (directImageMulLeg g j)
      (map_add ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val).map k).hom z z')).trans
        (((directImageMulLeg g j).map_add _ _).trans
          ((congrArg₂ (· + ·) hz hz').trans ((directImageMulLeg g _).map_add z z').symm))

variable {g} in
/-- The multiplication legs are semilinear along the ring maps `𝒪_𝒳(y) ⟶ 𝒪_𝒰(x)`. -/
theorem directImageMulLeg_smul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj ⋙
        forget₂ CommRingCat RingCat).obj (op y))) (z : directImageMulSections g y) :
    directImageMulLeg g j (r • z) =
      (show FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop from
        (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
          (op y) j).hom r) *
        directImageMulLeg g j z := by
  induction z using TensorProduct.inductionOn with
  | tmul s s' =>
    exact (congrArg (· * directImageUnitLeg g j s') (directImageUnitLeg_smul j r s)).trans
      (mul_assoc _ _ _)
  | add z z' hz hz' =>
    exact (congrArg (directImageMulLeg g j)
      (@smul_add _ _ _ (directImageMulSections g y).isModule.toDistribMulAction.toDistribSMul
        r z z')).trans
      (((directImageMulLeg g j).map_add _ _).trans ((congrArg₂ (· + ·) hz hz').trans
        ((mul_add _ _ _).symm.trans (congrArg (_ * ·)
          ((directImageMulLeg g j).map_add z z').symm))))

end Legs

section PresheafMap

/-- **The multiplication `g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` of presheaves of modules**, from the
objectwise tensor product: on sections over `y`, `s ⊗ s' ↦ (s_j · s'_j)_j`. -/
def directImageMulPresheafMap :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val
      ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val ⟶
    ((ranDirectImage g).obj (quasicoherentUnit 𝒰).obj).val :=
  PresheafOfModules.homMk
    { app := fun X => directImageMulApp g X.unop
      naturality := fun X X' k => by
        refine Stacks.SheafOfModules.ran_hom_ext _
          (quasicoherentUnit 𝒰).obj.val.presheaf (fun j => ?_)
        ext z
        exact (ranπ_directImageMulApp g j _).trans ((directImageMulLeg_map g k j z).trans
          ((ranπ_directImageMulApp g _ z).symm.trans (ConcreteCategory.congr_hom
            (Stacks.SheafOfModules.ranπ_map (CatFiberedInGroupoids.homFunctor g.hom).op
              (quasicoherentUnit 𝒰).obj.val.presheaf k j) _).symm)) }
    (fun X r z => by
      let σ : AddCommGrpCat.of (directImageMulSections g X.unop) ⟶
          AddCommGrpCat.of (directImageMulSections g X.unop) :=
        AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun m => r • m) (smul_add r))
      have h : σ ≫ directImageMulApp g X.unop = directImageMulApp g X.unop ≫
          Stacks.SheafOfModules.ranSMul (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
            (quasicoherentUnit 𝒰).obj.val X r := by
        refine Stacks.SheafOfModules.ran_hom_ext _
          (quasicoherentUnit 𝒰).obj.val.presheaf (fun j => ?_)
        ext z
        exact (ranπ_directImageMulApp g j _).trans ((directImageMulLeg_smul j r z).trans
          ((congrArg (fun n : FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop =>
            (show FibredSite.objRing B S hS 𝒰.val.val.p j.right.unop from
              (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
                X j).hom r) * n) (ranπ_directImageMulApp g j z).symm).trans
            (ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranSMul_π
              (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
              (quasicoherentUnit 𝒰).obj.val X r j) _).symm))
      exact ConcreteCategory.congr_hom h z)

/-- The multiplication of presheaves of modules is `directImageMulApp` on sections. -/
theorem directImageMulPresheafMap_app_apply (y : 𝒳.val.val.obj) (z : directImageMulSections g y) :
    ((directImageMulPresheafMap g).app (op y)).hom z = (directImageMulApp g y).hom z :=
  rfl

end PresheafMap

section SheafMap

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-- The sheafification adjunction of presheaves of modules on the fppf site of `𝒳`. -/
local notation "𝔰" => Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
  (fppfStructurePresheaf B S hS 𝒳) (fppfStructurePresheaf_isSheaf B S hS 𝒳)

/-- The identification of the fppf direct image along `g` with the right Kan extension. -/
local notation "𝔦" => fppfModulesPushforwardIsoModuleDirectImage B S hS g

/-- **The multiplication `g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` in `Mod(𝒪_𝒳)`**, for the direct image as the
right Kan extension along `g`: the sheafification of `directImageMulPresheafMap`. -/
def directImageMulRan :
    (ranDirectImage g).obj (quasicoherentUnit 𝒰).obj ⊗ (ranDirectImage g).obj (quasicoherentUnit
        𝒰).obj ⟶
      (ranDirectImage g).obj (quasicoherentUnit 𝒰).obj :=
  ((𝔰).homEquiv _ _).symm (directImageMulPresheafMap g)

/-- On the sheafification of a section of the objectwise tensor product, `directImageMulRan` is
the objectwise multiplication. -/
theorem directImageMulRan_val_app_toSheafify (y : 𝒳.val.val.obj)
    (z : directImageMulSections g y) :
    (directImageMulRan g).val.app (op y)
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify (fppfStructurePresheaf B S hS 𝒳)
          (fppfStructurePresheaf_isSheaf B S hS 𝒳) _).app (op y) z) =
      (directImageMulApp g y).hom z := by
  have h2 : (𝔰).unit.app _ ≫ (SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars _).map (directImageMulRan g) =
        directImageMulPresheafMap g :=
    ((𝔰).homEquiv_unit (f := directImageMulRan g)).symm.trans (Equiv.apply_symm_apply _ _)
  exact congrArg (fun φ => (φ.app (op y)).hom z) h2

end SheafMap

section Quasicoherent

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {g} (hg : IsAffineHom B S hS g)

/-- The direct image `g_*𝒪_𝒰` as the right Kan extension along `g`, as a quasi-coherent module for
`g` affine. -/
abbrev ranQuasicoherentUnit : quasicoherentModules B S hS 𝒳 :=
  ⟨(ranDirectImage g).obj (quasicoherentUnit 𝒰).obj,
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((fppfModulesPushforwardIsoModuleDirectImage B S hS g).app (quasicoherentUnit 𝒰).obj)
      (isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom B S hS g hg
        (quasicoherentUnit 𝒰))⟩

/-- The identification of `g_{QCoh,*}𝒪_𝒰` with the right Kan extension of `𝒪_𝒰` along `g`. -/
def affineDirectImageUnitIsoRan :
    (affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰) ≅
      ranQuasicoherentUnit hg :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((fppfModulesPushforwardIsoModuleDirectImage B S hS g).app (quasicoherentUnit 𝒰).obj)

/-- **The multiplication `g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰 ⟶ g_*𝒪_𝒰` in `QCoh(𝒪_𝒳)`**, for `g` affine: on
sections over `y` it is `s ⊗ s' ↦ (s_j · s'_j)_j` on the legs `j = (x, g x ⟶ y)` of the right Kan
extension computing `g_*`. -/
def affineDirectImageMul :
    (affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰) ⊗
        (affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰) ⟶
      (affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰) :=
  ((affineDirectImageUnitIsoRan hg).hom ⊗ₘ (affineDirectImageUnitIsoRan hg).hom) ≫
    ObjectProperty.homMk (X := ranQuasicoherentUnit hg ⊗ ranQuasicoherentUnit hg)
      (Y := ranQuasicoherentUnit hg) (directImageMulRan g) ≫
    (affineDirectImageUnitIsoRan hg).inv

/-- **The multiplication at a terminal arrow is the multiplication of functions.** For a terminal
arrow `(x₀, g x₀ ⟶ y)`, through `Γ(y, g_*𝒪_𝒰) ≅ Γ(x₀, 𝒪_𝒰)`, the multiplication sends the image
of `s ⊗ s'` in the sections of the tensor product to the product of the functions corresponding
to `s` and `s'`. -/
theorem fppfModulesPushforwardSectionsIsoOfIsTerminal_affineDirectImageMul {y : 𝒳.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) y} (ht : IsTerminal t)
    (s s' : (modulesPresheaf B S hS 𝒳
      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))).obj (op y)) :
    (show FibredSite.objRing B S hS 𝒰.val.val.p t.left from
      ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).hom.app
        (quasicoherentUnit 𝒰).obj).hom ((affineDirectImageMul hg).hom.val.app (op y)
          ((pointTensorMap B S hS 𝒳 y _ _).hom (s ⊗ₜ s')))) =
      (show FibredSite.objRing B S hS 𝒰.val.val.p t.left from
        ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).hom.app
          (quasicoherentUnit 𝒰).obj).hom s) *
      (show FibredSite.objRing B S hS 𝒰.val.val.p t.left from
        ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).hom.app
          (quasicoherentUnit 𝒰).obj).hom s') := by
  let i := affineDirectImageUnitIsoRan hg
  have h1 := tensorHom_pointTensorMap B S hS 𝒳 y i.hom i.hom s s'
  have h3 : ∀ w, i.hom.hom.val.app (op y) (i.inv.hom.val.app (op y) w) = w := fun w =>
    congrArg (fun φ => φ.hom.val.app (op y) w) i.inv_hom_id
  change directImageUnitLeg g (StructuredArrow.mk (Y := op t.left) t.hom.op)
      (i.hom.hom.val.app (op y) (i.inv.hom.val.app (op y) ((directImageMulRan g).val.app (op y)
        ((i.hom ⊗ₘ i.hom).hom.val.app (op y) ((pointTensorMap B S hS 𝒳 y _ _).hom (s ⊗ₜ s')))))) =
    directImageUnitLeg g (StructuredArrow.mk (Y := op t.left) t.hom.op) (i.hom.hom.val.app (op y)
        s) *
      directImageUnitLeg g (StructuredArrow.mk (Y := op t.left) t.hom.op)
        (i.hom.hom.val.app (op y) s')
  rw [h3, h1]
  exact (congrArg (directImageUnitLeg g (StructuredArrow.mk (Y := op t.left) t.hom.op))
    (directImageMulRan_val_app_toSheafify g y _)).trans (ranπ_directImageMulApp g _ _)

section Point

variable {R : Type u} [CommRing R] {y : 𝒳.val.val.obj}
  (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of R))
  {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor g.hom) y} (ht : IsTerminal t)

/-- The identification `y^*(g_*𝒪_𝒰) ≃ Γ(x₀, 𝒪_𝒰)` at a terminal arrow `(x₀, g x₀ ⟶ y)`, with
values in the ring of functions of `x₀`. -/
def pointSectionsAddEquiv :
    (pointPullback B S hS 𝒳 y e).obj
        ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰)) ≃+
      FibredSite.objRing B S hS 𝒰.val.val.p t.left :=
  ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).app
    (quasicoherentUnit 𝒰).obj).addCommGroupIsoToAddEquiv

/-- `pointSectionsAddEquiv` is given by the sections of the isomorphism
`fppfModulesPushforwardSectionsIsoOfIsTerminal` at `𝒪_𝒰`. -/
theorem pointSectionsAddEquiv_apply (z : (pointPullback B S hS 𝒳 y e).obj
      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))) :
    pointSectionsAddEquiv hg e ht z =
      ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).hom.app
        (quasicoherentUnit 𝒰).obj).hom z :=
  rfl

/-- `pointSectionsAddEquiv` is natural in endomorphisms of `𝒪_𝒰`. -/
theorem pointSectionsAddEquiv_map
    (ψ : (quasicoherentUnit 𝒰).obj ⟶ (quasicoherentUnit 𝒰).obj)
    (z : (pointPullback B S hS 𝒳 y e).obj
      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))) :
    pointSectionsAddEquiv hg e ht (((pointPullback B S hS 𝒳 y e).map
      (ObjectProperty.homMk (X := (affineQuasicoherentDirectImage B S hS g hg).obj
        (quasicoherentUnit 𝒰)) (Y := (affineQuasicoherentDirectImage B S hS g hg).obj
          (quasicoherentUnit 𝒰)) ((fppfModulesPushforward B S hS g).map ψ))).hom z) =
      (ψ.val.app (op t.left)).hom (pointSectionsAddEquiv hg e ht z) := by
  refine (congrArg (pointSectionsAddEquiv hg e ht) (pointPullback_map_apply B S hS 𝒳 y e _ z)).trans
    ?_
  have h2 := ConcreteCategory.congr_hom
    ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS g ht).hom.naturality ψ) z
  exact h2

/-- **The pullback of the multiplication to a point is the multiplication of functions.** For a
point `y` over `Spec R` and a terminal arrow `(x₀, g x₀ ⟶ y)`, through
`y^*(g_*𝒪_𝒰) ≅ Γ(x₀, 𝒪_𝒰)`, the composite
`y^*(g_*𝒪_𝒰) ⊗_R y^*(g_*𝒪_𝒰) ⟶ y^*(g_*𝒪_𝒰 ⊗ g_*𝒪_𝒰) ⟶ y^*(g_*𝒪_𝒰)` is the multiplication of
`Γ(x₀, 𝒪_𝒰)`. -/
theorem pointSectionsAddEquiv_affineDirectImageMul
    (s s' : (pointPullback B S hS 𝒳 y e).obj
      ((affineQuasicoherentDirectImage B S hS g hg).obj (quasicoherentUnit 𝒰))) :
    pointSectionsAddEquiv hg e ht (((pointPullback B S hS 𝒳 y e).map
      (affineDirectImageMul hg)).hom
      ((Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 y e) _ _).hom (s ⊗ₜ s'))) =
      pointSectionsAddEquiv hg e ht s * pointSectionsAddEquiv hg e ht s' := by
  rw [μ_pointPullback, pointPullbackμ_tmul]
  exact (congrArg (pointSectionsAddEquiv hg e ht) (pointPullback_map_apply B S hS 𝒳 y e
    (affineDirectImageMul hg) _)).trans
    (fppfModulesPushforwardSectionsIsoOfIsTerminal_affineDirectImageMul hg ht s s')

/-- `pointSectionsAddEquiv_affineDirectImageMul`, read backwards: the section of `y^*(g_*𝒪_𝒰)`
corresponding to a product of functions on `x₀` is the image of the tensor product of the
corresponding sections under the multiplication. -/
theorem pointSectionsAddEquiv_symm_mul (c c' : FibredSite.objRing B S hS 𝒰.val.val.p t.left) :
    (pointSectionsAddEquiv hg e ht).symm (c * c') =
      ((pointPullback B S hS 𝒳 y e).map (affineDirectImageMul hg)).hom
        ((Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 y e) _ _).hom
          ((pointSectionsAddEquiv hg e ht).symm c ⊗ₜ (pointSectionsAddEquiv hg e ht).symm c')) := by
  have h := pointSectionsAddEquiv_affineDirectImageMul hg e ht
    ((pointSectionsAddEquiv hg e ht).symm c) ((pointSectionsAddEquiv hg e ht).symm c')
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
  rw [AddEquiv.symm_apply_eq, h]

end Point

end Quasicoherent

end AlgebraicGeometry.Stack.AlgebraicStacks
