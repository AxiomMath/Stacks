module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineQuasicoherentDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousCartesian

/-!
# The projection formula for an affine 1-morphism of algebraic stacks

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks (Stacks 0CHQ) and `M` a
quasi-coherent `𝒪_𝒳`-module. The **projection formula**

`M ⊗_{𝒪_𝒳} g_{QCoh,*}𝒪_𝒰 ≅ g_{QCoh,*}g^*M`

holds, naturally in `M`. It is step 5 of the proof of Stacks 0GRQ, where it identifies
`F(M) ⊗_B C = F(M ⊗ g_*𝒪_𝒰)` with `F(g_*g^*M)` for `C = F(g_*𝒪_𝒰)`.

## The map

The inverse image `g^*` is restriction along the underlying functor of `g`, and the direct image
`g_*` is the right Kan extension along it: the sections of `g_* N` over `y` are compatible
families of sections of `N` over the legs `j = (x, g x ⟶ y)`. The projection map is, on sections
over `y` of the objectwise tensor product,

`m ⊗ s ↦ (s_j · m|_{g x})_j`,

for `s_j ∈ 𝒪_𝒰(x) = 𝒪_𝒳(g x)` the leg of `s` (`projectionLeg`). It is semilinear and compatible
with restriction, so it is a morphism of presheaves of modules (`projectionPresheafMap`), natural
in `M`, and it sheafifies to a morphism out of the tensor product sheaf (`projectionMap`).

## The isomorphism

A morphism of `𝒪_𝒳`-modules which is bijective on the sections over every object lying over an
affine scheme is an isomorphism, the affine objects forming a dense subsite
(`isIso_of_bijective_app_of_isAffine`). Over such a `y`, `g` affine gives a terminal arrow
`(x₀, g x₀ ⟶ y)` with `x₀` over an affine scheme; the sheafification unit is bijective at `y`
because `M` and `g_*𝒪_𝒰` are quasi-coherent, and on the leg at the terminal arrow the projection
map is `M(y) ⊗_{𝒪(y)} 𝒪_𝒰(x₀) ⟶ M(g x₀)`, `m ⊗ s ↦ s · m|_{g x₀}`, the base change of the sections
of `M` along an arrow between objects over affine schemes, bijective by quasi-coherence
(`bijective_projectionMapApp`).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.projectionMap`: the projection map
  `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` in `Mod(𝒪_𝒳)`, for every 1-morphism `g`, and
  `AlgebraicGeometry.Stack.AlgebraicStacks.projectionNatTrans`, the natural transformation.
* `AlgebraicGeometry.Stack.AlgebraicStacks.affineProjectionIso`: for `g` affine, the natural
  isomorphism `(-) ⊗ g_*𝒪_𝒰 ≅ g_* ∘ g^*` of endofunctors of `QCoh(𝒪_𝒳)`, `g_*` the direct image
  of modules (`affineQuasicoherentDirectImage`).
* `AlgebraicGeometry.Stack.AlgebraicStacks.projectionFormulaIso`: the same with
  `g_{QCoh,*} = quasicoherentDirectImage g` of Stacks 077A.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_projectionMap`: for `g` affine and `M`
  quasi-coherent, the projection map is an isomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_of_bijective_app_of_isAffine`: isomorphisms of
  `𝒪_𝒳`-modules are detected on the sections over objects lying over affine schemes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.projectionLeg_tmul` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.ranπ_projectionMapApp`: the sections formula of the
  projection map on the legs, which is what compatibilities with the tensor structure reduce to.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

/-- Additive maps out of a tensor product agreeing on pure tensors are equal. -/
private theorem addMonoidHom_ext_tmul {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] {f g : TensorProduct R M N →+ P}
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- **A map out of a tensor product which is, on pure tensors, a bijection out of the swapped
tensor product after two linear equivalences, is bijective.** -/
theorem Function.Bijective.of_tmul_eq_swap {R : Type*} [CommRing R] {M N M' N' T : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N'] [AddCommGroup T] (τ : M ≃ₗ[R] M') (σ : N ≃ₗ[R] N')
    (Θ : TensorProduct R M N →+ T) (Φ : TensorProduct R N' M' →+ T) (hΦ : Function.Bijective Φ)
    (h : ∀ m n, Θ (m ⊗ₜ n) = Φ (σ n ⊗ₜ τ m)) : Function.Bijective Θ := by
  have : Θ = Φ.comp ((TensorProduct.comm R M' N').toLinearMap.toAddMonoidHom.comp
      (TensorProduct.congr τ σ).toLinearMap.toAddMonoidHom) := by
    exact addMonoidHom_ext_tmul fun m n => by simp [h]
  rw [this]
  exact hΦ.comp ((TensorProduct.comm R M' N').bijective.comp (TensorProduct.congr τ σ).bijective)

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)

/-- The structure map of the canonical direct image along `g`. -/
local notation "𝔣" => moduleDirectImageStructureMap B S hS 𝒰.val.val.p
  𝒳.val.val.p 𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
  (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  B.topology le_rfl

/-- The identification of the structure presheaf of `𝒰` with the restriction of the one of `𝒳`
along `g`. -/
local notation "𝔢" => ringStructureSheafCore_obj_eq B S hS 𝒰.val.val.p 𝒳.val.val.p
  𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
  (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  B.topology le_rfl

/-- The direct image of modules along `g`, as the right Kan extension along its underlying
functor with the structure map `𝔣`. -/
abbrev ranDirectImage : Stack.fppfModules B S hS 𝒰 ⥤ Stack.fppfModules B S hS 𝒳 :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u} (CatFiberedInGroupoids.homFunctor g.hom) 𝔣

section Legs

variable (M : Stack.fppfModules B S hS 𝒳) {y : 𝒳.val.val.obj}

/-- The objectwise tensor product `M(y) ⊗_{𝒪(y)} (g_*𝒪_𝒰)(y)`, for the canonical direct image. -/
abbrev projectionSections (y : 𝒳.val.val.obj) :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
    M.val ((ranDirectImage g).obj (SheafOfModules.unit _)).val).obj (op y)

variable {g}

/-- The ring map `𝒪_𝒳(y) ⟶ 𝒪_𝒰(x)` at a leg `j = (x, g x ⟶ y)`. -/
abbrev projectionScalar
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op y) →+*
      (FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
        .fppf).obj.obj j.right :=
  (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom (op y) j).hom

/-- The ring map `𝒪_𝒳(y) ⟶ 𝒪_𝒰(x)` cut out by the structure map at a leg `(x, g x ⟶ y)`, read
in `𝒪_𝒳(g x)`, is restriction along the leg. -/
theorem eqToHom_app_scalarπ_moduleDirectImageStructureMap
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
      le_rfl).obj.obj (op y)) :
    ((eqToHom 𝔢).app j.right).hom
        ((Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
          (op y) j).hom r) =
      ((ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
        le_rfl).obj.map j.hom).hom r := by
  rw [scalarπ_moduleDirectImageStructureMap, ← RingCat.comp_apply, Category.assoc,
    ← NatTrans.comp_app, eqToHom_trans, eqToHom_refl, NatTrans.id_app]
  rfl

/-- `eqToHom_app_scalarπ_moduleDirectImageStructureMap` for `projectionScalar`. -/
theorem eqToHom_app_projectionScalar
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.obj (op y)) :
    ((eqToHom 𝔢).app j.right).hom (projectionScalar j r) =
      ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.map j.hom).hom r :=
  eqToHom_app_scalarπ_moduleDirectImageStructureMap j r

variable (g) in
/-- The leg at `j = (x, g x ⟶ y)` of the limit computing `(g_*𝒪_𝒰)(y)`, read in
`𝒪_𝒰(x) = 𝒪_𝒳(g x)`. -/
abbrev projectionUnitLeg
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    ((ranDirectImage g).obj (SheafOfModules.unit _)).val.obj (op y) →+
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj
        ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) :=
  ((eqToHom 𝔢).app j.right).hom.toAddMonoidHom.comp
    (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
      (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p
        𝒰.val.isFiberedInGroupoids .fppf)).val.presheaf (op y) j).hom

/-- Restriction of sections of `M` along a leg `j = (x, g x ⟶ y)`. -/
abbrev projectionRestrict
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    M.val.obj (op y) →+ M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) :=
  (M.val.map j.hom).hom.toAddMonoidHom

/-- The legs of `g_*𝒪_𝒰` are semilinear along restriction of functions along the leg. -/
theorem projectionUnitLeg_smul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op y))
    (s : ((ranDirectImage g).obj (SheafOfModules.unit _)).val.obj (op y)) :
    projectionUnitLeg g j (r • s) =
      ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.map j.hom).hom r * projectionUnitLeg g j s :=
  (congrArg ((eqToHom 𝔢).app j.right).hom (ConcreteCategory.congr_hom
    (Stacks.SheafOfModules.ranSMul_π (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
      (SheafOfModules.unit _).val (op y) r j) s)).trans
    ((map_mul _ _ _).trans (congrArg (· * _) (eqToHom_app_projectionScalar j r)))

/-- The leg at `j = (x, g x ⟶ y)` of the projection map: `m ⊗ s ↦ s_j · m|_{g x}`. -/
def projectionLeg (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op) :
    projectionSections g M y →+
      M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) :=
  TensorProduct.liftAddHom
    (((smulAddHom ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj
        ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right))
        (M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right))).flip.comp
      (projectionRestrict M j)).compl₂ (projectionUnitLeg g j))
    (fun r m s => by
      have e1 : projectionRestrict M j (r • m) =
          ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            .fppf).obj.map j.hom).hom r • projectionRestrict M j m :=
        (M.val.map j.hom).hom.map_smul r m
      have e2 := projectionUnitLeg_smul j r s
      exact (congrArg (projectionUnitLeg g j s • ·) e1).trans ((smul_smul _ _ _).trans
        ((congrArg (fun c : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids .fppf).obj.obj
            ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) =>
              c • projectionRestrict M j m)
          (@mul_comm (FibredSite.objRing B S hS 𝒳.val.val.p
            ((CatFiberedInGroupoids.homFunctor g.hom).obj j.right.unop)) _
            (projectionUnitLeg g j s) _)).trans
          (congrArg (fun c : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
              𝒳.val.isFiberedInGroupoids .fppf).obj.obj
            ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) =>
              c • projectionRestrict M j m) e2.symm))))

/-- **The sections formula of the projection map on a leg**: `m ⊗ s ↦ s_j · m|_{g x}`. -/
theorem projectionLeg_tmul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (m : M.val.obj (op y)) (s : ((ranDirectImage g).obj (SheafOfModules.unit _)).val.obj (op y)) :
    projectionLeg M j (m ⊗ₜ s) = projectionUnitLeg g j s • projectionRestrict M j m :=
  rfl

/-- The legs of `g_*𝒪_𝒰` form a cone. -/
theorem projectionUnitLeg_naturality
    {j₁ j₂ : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (s : ((ranDirectImage g).obj (SheafOfModules.unit _)).val.obj (op y)) :
    ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.map ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)).hom
      (projectionUnitLeg g j₁ s) = projectionUnitLeg g j₂ s :=
  (ConcreteCategory.congr_hom ((eqToHom 𝔢).naturality φ.right)
    ((Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
      (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p
        𝒰.val.isFiberedInGroupoids .fppf)).val.presheaf (op y) j₁).hom s)).symm.trans
    (congrArg ((eqToHom 𝔢).app j₂.right).hom (ConcreteCategory.congr_hom
      (Stacks.SheafOfModules.ranπ_naturality (CatFiberedInGroupoids.homFunctor g.hom).op
        (SheafOfModules.unit _).val.presheaf φ) s))

/-- Restriction along the legs is compatible with morphisms of legs. -/
theorem projectionRestrict_naturality
    {j₁ j₂ : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (m : M.val.obj (op y)) :
    M.val.map ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)
        (projectionRestrict M j₁ m) = projectionRestrict M j₂ m := by
  change M.val.map ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)
        (M.val.map j₁.hom m) = M.val.map j₂.hom m
  rw [← PresheafOfModules.map_comp_apply, StructuredArrow.w φ]

/-- The legs of the projection map form a cone. -/
theorem projectionLeg_naturality
    {j₁ j₂ : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op} (φ : j₁ ⟶ j₂)
    (z : projectionSections g M y) :
    M.val.map ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right) (projectionLeg M j₁ z) =
      projectionLeg M j₂ z := by
  refine DFunLike.congr_fun (addMonoidHom_ext_tmul (f := (M.val.map
    ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)).hom.toAddMonoidHom.comp
      (projectionLeg M j₁)) (g := projectionLeg M j₂) fun m s => ?_) z
  refine (congrArg (M.val.map _) (projectionLeg_tmul M j₁ m s)).trans
    (Eq.trans ?_ (projectionLeg_tmul M j₂ m s).symm)
  refine ((M.val.map _).hom.map_smul _ _).trans ?_
  change @HSMul.hSMul ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj.obj
      ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j₂.right))
    (M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j₂.right)) _ instHSMul
    (((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.map
      ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)).hom (projectionUnitLeg g j₁ s))
    (M.val.map ((CatFiberedInGroupoids.homFunctor g.hom).op.map φ.right)
      (projectionRestrict M j₁ m)) = _
  rw [projectionUnitLeg_naturality, projectionRestrict_naturality]

variable (y) in
/-- The cone of projection legs over the diagram computing the sections of `g_*g^*M` over `y`. -/
def projectionCone : Cone (StructuredArrow.proj (op y)
    (CatFiberedInGroupoids.homFunctor g.hom).op ⋙
      (CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) where
  pt := AddCommGrpCat.of (projectionSections g M y)
  π :=
    { app := fun j => AddCommGrpCat.ofHom (projectionLeg M j)
      naturality := fun j₁ j₂ φ => by
        ext z
        exact (projectionLeg_naturality M φ z).symm }

variable (g y) in
/-- **The projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` on sections over `y`**, objectwise:
`m ⊗ s ↦ (s_j · m|_{g x})_j`, defined by its legs. -/
def projectionMapApp :
    AddCommGrpCat.of (projectionSections g M y) ⟶
      ((ranDirectImage g).obj ((fppfModulesPullback B S hS g).obj M)).val.presheaf.obj (op y) :=
  (Stacks.SheafOfModules.ranIsLimit (CatFiberedInGroupoids.homFunctor g.hom).op
    ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) (op y)).lift
      (projectionCone M y)

/-- The legs of the projection map at `y` are the projection legs. -/
theorem ranπ_projectionMapApp
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (z : projectionSections g M y) :
    (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
      ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) (op y) j).hom
        ((projectionMapApp g M y).hom z) = projectionLeg M j z :=
  ConcreteCategory.congr_hom ((Stacks.SheafOfModules.ranIsLimit
    (CatFiberedInGroupoids.homFunctor g.hom).op
    ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) (op y)).fac
      (projectionCone M y) j) z

/-- The projection legs are compatible with restriction along `y' ⟶ y`. -/
theorem projectionLeg_map {y' : 𝒳.val.val.obj} (k : op y ⟶ op y')
    (j : StructuredArrow (op y') (CatFiberedInGroupoids.homFunctor g.hom).op)
    (z : projectionSections g M y) :
    projectionLeg M j ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      M.val ((ranDirectImage g).obj (SheafOfModules.unit _)).val).map k z) =
        projectionLeg M ((StructuredArrow.map k).obj j) z := by
  refine DFunLike.congr_fun (addMonoidHom_ext_tmul (f := (projectionLeg M j).comp
    ((PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      M.val ((ranDirectImage g).obj (SheafOfModules.unit _)).val).map k).hom.toAddMonoidHom)
    (g := projectionLeg M ((StructuredArrow.map k).obj j)) fun m s => ?_) z
  have h1 : projectionUnitLeg g j
      (((ranDirectImage g).obj (SheafOfModules.unit _)).val.map k s) =
        projectionUnitLeg g ((StructuredArrow.map k).obj j) s :=
    congrArg ((eqToHom 𝔢).app j.right).hom (ConcreteCategory.congr_hom
      (Stacks.SheafOfModules.ranπ_map (CatFiberedInGroupoids.homFunctor g.hom).op
        (SheafOfModules.unit _).val.presheaf k j) s)
  have h2 : projectionRestrict M j (M.val.map k m) =
      projectionRestrict M ((StructuredArrow.map k).obj j) m := by
    change M.val.map j.hom (M.val.map k m) = M.val.map (k ≫ j.hom) m
    rw [PresheafOfModules.map_comp_apply]
  exact (projectionLeg_tmul M j _ _).trans ((congrArg₂ (· • ·) h1 h2).trans
    (projectionLeg_tmul M _ m s).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The projection legs are semilinear along restriction of functions along the leg. -/
theorem projectionLeg_smul
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj ⋙
        forget₂ CommRingCat RingCat).obj (op y))) (z : projectionSections g M y) :
    projectionLeg M j (r • z) = ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf).obj.map j.hom).hom r • projectionLeg M j z := by
  refine DFunLike.congr_fun (addMonoidHom_ext_tmul
    (f := (projectionLeg M j).comp (DistribSMul.toAddMonoidHom _
      (show ((FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op y) : Type _) from r)))
    (g := (DistribSMul.toAddMonoidHom _ (((FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj.map j.hom).hom r)).comp
        (projectionLeg M j)) fun m s => ?_) z
  have e1 : projectionRestrict M j
      (@HSMul.hSMul ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op y)) (M.val.obj (op y)) _ instHSMul r m) =
        ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf).obj.map j.hom).hom r • projectionRestrict M j m :=
    (M.val.map j.hom).hom.map_smul r m
  change projectionUnitLeg g j s • projectionRestrict M j
      (@HSMul.hSMul ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op y)) (M.val.obj (op y)) _ instHSMul r m) =
    ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.map j.hom).hom r • (projectionUnitLeg g j s • projectionRestrict M j m)
  rw [e1, smul_smul, smul_smul]
  exact congrArg (fun c : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj.obj
        ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) =>
          c • projectionRestrict M j m)
      (@mul_comm (FibredSite.objRing B S hS 𝒳.val.val.p
        ((CatFiberedInGroupoids.homFunctor g.hom).obj j.right.unop)) _
        (projectionUnitLeg g j s) _)

/-- Scalar multiplication on the inverse image, by the image of a function along a leg, is
scalar multiplication by its restriction along the leg. -/
theorem smulPresheaf_fppfModulesPullback_projectionScalar
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf).obj.obj (op y))
    (n : M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right)) :
    (Stacks.SheafOfModules.smulPresheaf ((fppfModulesPullback B S hS g).obj M).val j.right
      (projectionScalar j r)).hom n = ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf).obj.map j.hom).hom r • n := by
  change @HSMul.hSMul ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf).obj.obj
      ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right))
    (M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right)) _ instHSMul
    (((eqToHom 𝔢).app j.right).hom (projectionScalar j r)) n = _
  rw [eqToHom_app_projectionScalar]

end Legs

section PresheafMap

variable (M : Stack.fppfModules B S hS 𝒳)

/-- **The projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` of presheaves of modules**, from the objectwise
tensor product: on sections over `y`, `m ⊗ s ↦ (s_j · m|_{g x})_j`. -/
def projectionPresheafMap :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      M.val ((ranDirectImage g).obj (SheafOfModules.unit _)).val ⟶
    ((ranDirectImage g).obj ((fppfModulesPullback B S hS g).obj M)).val :=
  PresheafOfModules.homMk
    { app := fun X => projectionMapApp g M X.unop
      naturality := fun X X' k => by
        refine Stacks.SheafOfModules.ran_hom_ext _
          ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) (fun j => ?_)
        ext z
        exact (ranπ_projectionMapApp M j _).trans ((projectionLeg_map M k j z).trans
          ((ranπ_projectionMapApp M _ z).symm.trans (ConcreteCategory.congr_hom
            (Stacks.SheafOfModules.ranπ_map (CatFiberedInGroupoids.homFunctor g.hom).op
              ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) k j) _).symm)) }
    (fun X r z => by
      let σ : AddCommGrpCat.of (projectionSections g M X.unop) ⟶
          AddCommGrpCat.of (projectionSections g M X.unop) :=
        AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun m => r • m) (smul_add r))
      have h : σ ≫ projectionMapApp g M X.unop = projectionMapApp g M X.unop ≫
          Stacks.SheafOfModules.ranSMul (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
            ((fppfModulesPullback B S hS g).obj M).val X r := by
        refine Stacks.SheafOfModules.ran_hom_ext _
          ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.val.presheaf) (fun j => ?_)
        ext z
        exact (ranπ_projectionMapApp M j _).trans ((projectionLeg_smul M j r z).trans
          ((congrArg (fun n : M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right) =>
            ((FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
              .fppf).obj.map j.hom).hom r • n) (ranπ_projectionMapApp M j z).symm).trans
            ((smulPresheaf_fppfModulesPullback_projectionScalar M j r _).symm.trans
              (ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranSMul_π
                (CatFiberedInGroupoids.homFunctor g.hom) (𝔣).hom
                ((fppfModulesPullback B S hS g).obj M).val X r j) _).symm)))
      exact ConcreteCategory.congr_hom h z)

variable {M} in
/-- The legs of the direct image of a morphism are its components at the legs. -/
theorem ranπ_ranDirectImage_map {N N' : Stack.fppfModules B S hS 𝒰} (ψ : N ⟶ N')
    {y : 𝒳.val.val.obj}
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (w : ((ranDirectImage g).obj N).val.obj (op y)) :
    (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op N'.val.presheaf
      (op y) j).hom (((ranDirectImage g).map ψ).val.app (op y) w) =
      ψ.val.app j.right ((Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
        N.val.presheaf (op y) j).hom w) :=
  ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranπ_map_functor
    (CatFiberedInGroupoids.homFunctor g.hom).op (Stacks.SheafOfModules.presheafMap ψ.val)
      (op y) j) w

variable {M} in
/-- The inverse image of a morphism is its restriction along `g`. -/
theorem fppfModulesPullback_map_val_app {M' : Stack.fppfModules B S hS 𝒳} (φ : M ⟶ M')
    (X : 𝒰.val.val.objᵒᵖ) (n : M.val.obj ((CatFiberedInGroupoids.homFunctor g.hom).op.obj X)) :
    ((fppfModulesPullback B S hS g).map φ).val.app X n =
      φ.val.app ((CatFiberedInGroupoids.homFunctor g.hom).op.obj X) n :=
  rfl

/-- The legs of the projection map at `y`, read on the inverse image. -/
theorem ranπ_pullback_projectionMapApp {y : 𝒳.val.val.obj}
    (j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op)
    (z : projectionSections g M y) :
    (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
      ((fppfModulesPullback B S hS g).obj M).val.presheaf (op y) j).hom
        ((projectionMapApp g M y).hom z) = projectionLeg M j z :=
  ranπ_projectionMapApp M j z

/-- The projection map of presheaves of modules is natural in `M`. -/
theorem projectionPresheafMap_naturality {M M' : Stack.fppfModules B S hS 𝒳} (φ : M ⟶ M') :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom
        (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
        φ.val (𝟙 ((ranDirectImage g).obj (SheafOfModules.unit _)).val) ≫
      projectionPresheafMap g M' =
    projectionPresheafMap g M ≫
      ((ranDirectImage g).map ((fppfModulesPullback B S hS g).map φ)).val := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  refine NatTrans.ext (funext fun X => ?_)
  refine Stacks.SheafOfModules.ran_hom_ext _
    ((fppfModulesPullback B S hS g).obj M').val.presheaf (fun j => ?_)
  refine AddCommGrpCat.hom_ext (addMonoidHom_ext_tmul fun m s => ?_)
  have h4 : φ.val.app ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right)
      (projectionLeg M j (m ⊗ₜ s)) = projectionLeg M' j (φ.val.app X m ⊗ₜ s) :=
    ((φ.val.app _).hom.map_smul _ _).trans (congrArg (projectionUnitLeg g j s • ·)
      (PresheafOfModules.naturality_apply φ.val j.hom m))
  exact (ranπ_pullback_projectionMapApp g M' j _).trans (h4.symm.trans
    ((congrArg (φ.val.app ((CatFiberedInGroupoids.homFunctor g.hom).op.obj j.right))
      (ranπ_pullback_projectionMapApp g M j (m ⊗ₜ s))).symm.trans
        ((fppfModulesPullback_map_val_app g φ j.right _).symm.trans
          (ranπ_ranDirectImage_map g ((fppfModulesPullback B S hS g).map φ) j _).symm)))

end PresheafMap

section Bijective

variable {g}

/-- **The projection map is bijective on the sections over an object lying over an affine
scheme**, objectwise, for `g` affine and `M` quasi-coherent. Let `(x₀, g x₀ ⟶ y)` be the terminal
arrow of `g` at `y`; on the leg there the map is `M(y) ⊗_{𝒪(y)} 𝒪_𝒰(x₀) ⟶ M(g x₀)`,
`m ⊗ s ↦ s · m|_{g x₀}`, the base change of the sections of `M` along the arrow `g x₀ ⟶ y`
between objects lying over affine schemes, which is bijective since `M` is quasi-coherent. -/
theorem bijective_projectionMapApp (hg : IsAffineHom B S hS g)
    (M : quasicoherentModules B S hS 𝒳) {y : 𝒳.val.val.obj}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y))) :
    Function.Bijective (projectionMapApp g M.obj y) := by
  obtain ⟨t, ⟨ht⟩, hta⟩ := exists_isTerminal_costructuredArrow_of_isAffineHom B S hS g hg y hy
  let j : StructuredArrow (op y) (CatFiberedInGroupoids.homFunctor g.hom).op :=
    StructuredArrow.mk (Y := op t.left) t.hom.op
  have hπ : Function.Bijective (Stacks.SheafOfModules.ranπ
      (CatFiberedInGroupoids.homFunctor g.hom).op
      ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.obj.val.presheaf) (op y) j).hom := by
    have := Stacks.SheafOfModules.isIso_ranπ_of_isTerminal
      (CatFiberedInGroupoids.homFunctor g.hom)
      ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.obj.val.presheaf) ht
    exact ConcreteCategory.bijective_of_isIso _
  refine (Function.Bijective.of_comp_iff' hπ _).1 ?_
  rw [show ⇑(Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor g.hom).op
      ((CatFiberedInGroupoids.homFunctor g.hom).op ⋙ M.obj.val.presheaf) (op y) j).hom ∘
      ⇑(projectionMapApp g M.obj y).hom = ⇑(projectionLeg M.obj j) from
    funext (ranπ_projectionMapApp M.obj j)]
  let x := (CatFiberedInGroupoids.homFunctor g.hom).obj t.left
  have hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) := by
    rw [show 𝒳.val.val.p.obj x = 𝒰.val.val.p.obj t.left from
      Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p g.hom) t.left]
    exact hta
  let := FibredSite.objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj y
  let := FibredSite.objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.obj x
  let := FibredSite.objModule B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    ((ranDirectImage g).obj (SheafOfModules.unit _)) y
  let := FibredSite.objAlgebra B S hS 𝒳.val.val.p t.hom
  let : Module (FibredSite.objRing B S hS 𝒳.val.val.p y) (M.obj.val.obj (op x)) :=
    Module.compHom _ (algebraMap (FibredSite.objRing B S hS 𝒳.val.val.p y)
      (FibredSite.objRing B S hS 𝒳.val.val.p x))
  have : IsScalarTower (FibredSite.objRing B S hS 𝒳.val.val.p y)
      (FibredSite.objRing B S hS 𝒳.val.val.p x) (M.obj.val.obj (op x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let L := (FibredSite.restrictionLinear M.obj t.hom).liftBaseChange
    (FibredSite.objRing B S hS 𝒳.val.val.p x)
  have hL : Function.Bijective L :=
    FibredSite.bijective_liftBaseChange_of_eq_restriction M.obj M.property t.hom hy hx _
      (fun _ => rfl)
  let τ : ((ranDirectImage g).obj (SheafOfModules.unit _)).val.obj (op y) →ₗ[
      FibredSite.objRing B S hS 𝒳.val.val.p y] FibredSite.objRing B S hS 𝒳.val.val.p x :=
    { toFun := fun s => projectionUnitLeg g j s
      map_add' := map_add _
      map_smul' := fun r s => projectionUnitLeg_smul j r s }
  have hτ : Function.Bijective τ := by
    have h1 := Stacks.SheafOfModules.isIso_ranπ_of_isTerminal
      (CatFiberedInGroupoids.homFunctor g.hom) (SheafOfModules.unit
        (FibredSite.ringStructureSheafCore B S hS 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids
          .fppf)).val.presheaf ht
    exact (ConcreteCategory.bijective_of_isIso ((eqToHom 𝔢).app j.right)).comp
      (ConcreteCategory.bijective_of_isIso _)
  exact Function.Bijective.of_tmul_eq_swap (LinearEquiv.refl _ _) (LinearEquiv.ofBijective τ hτ)
    (projectionLeg M.obj j) L.toAddMonoidHom hL (fun m s => rfl)

end Bijective

section Detection

variable (𝒳) in
/-- **A morphism of `𝒪_𝒳`-modules which is bijective on the sections over every object lying over
an affine scheme is an isomorphism.** The affine objects form a dense subsite (Stacks 0H0B), so a
morphism of sheaves which restricts to an isomorphism on it is an isomorphism. -/
theorem isIso_of_bijective_app_of_isAffine {T P : Stack.fppfModules B S hS 𝒳} (ψ : T ⟶ P)
    (h : ∀ y : 𝒳.val.val.obj, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) →
      Function.Bijective (ψ.val.app (op y))) : IsIso ψ := by
  have hD := AffineCategory.isDenseSubsite_inclusion_siteKind B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf
  have := hD.isCoverDense'
  have := hD.isLocallyFull'
  let α := (SheafOfModules.toSheaf _).map ψ
  have hα : IsIso α := by
    refine Functor.IsCoverDense.iso_of_restrict_iso
      (G := AffineCategory.inclusion B S hS 𝒳.val.val.p) α ?_
    rw [NatTrans.isIso_iff_isIso_app]
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h x.unop.obj x.unop.property
  have hα' : IsIso α.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map α))
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map ψ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun y => inferInstanceAs (IsIso (α.hom.app y))
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

end Detection

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

variable (M : Stack.fppfModules B S hS 𝒳)

/-- **The projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` in `Mod(𝒪_𝒳)`**, for the direct image as the
right Kan extension along `g`: the sheafification of `projectionPresheafMap`. -/
def projectionMapRan :
    M ⊗ (ranDirectImage g).obj (SheafOfModules.unit _) ⟶
      (ranDirectImage g).obj ((fppfModulesPullback B S hS g).obj M) :=
  ((𝔰).homEquiv _ _).symm (projectionPresheafMap g M)

variable {M} in
/-- `projectionMapRan` is natural in `M`. -/
@[reassoc]
theorem projectionMapRan_naturality {M' : Stack.fppfModules B S hS 𝒳} (φ : M ⟶ M') :
    φ ▷ (ranDirectImage g).obj (SheafOfModules.unit _) ≫ projectionMapRan g M' =
      projectionMapRan g M ≫ (ranDirectImage g).map ((fppfModulesPullback B S hS g).map φ) := by
  refine (congrArg (· ≫ projectionMapRan g M')
    (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map (fppfStructurePresheaf B S hS 𝒳)
      (fppfStructurePresheaf_isSheaf B S hS 𝒳) φ
        ((ranDirectImage g).obj (SheafOfModules.unit _)))).trans ?_
  refine ((𝔰).homEquiv_naturality_left_symm _ _).symm.trans
    (Eq.trans ?_ ((𝔰).homEquiv_naturality_right_symm _ _))
  exact congrArg ((𝔰).homEquiv _ _).symm (projectionPresheafMap_naturality g φ)

/-- The identification of the fppf direct image along `g` with the right Kan extension. -/
local notation "𝔦" => fppfModulesPushforwardIsoModuleDirectImage B S hS g

/-- **The projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` in `Mod(𝒪_𝒳)`**, for the fppf direct image
`g_* = fppfModulesPushforward g`: on sections over `y` it is `m ⊗ s ↦ (s_j · m|_{g x})_j` on the
legs `j = (x, g x ⟶ y)` of the right Kan extension computing `g_*`. -/
def projectionMap :
    M ⊗ (fppfModulesPushforward B S hS g).obj (SheafOfModules.unit _) ⟶
      (fppfModulesPushforward B S hS g).obj ((fppfModulesPullback B S hS g).obj M) :=
  M ◁ (𝔦).hom.app (SheafOfModules.unit _) ≫ projectionMapRan g M ≫
    (𝔦).inv.app ((fppfModulesPullback B S hS g).obj M)

variable {M} in
/-- The projection map is natural in `M`. -/
theorem projectionMap_naturality {M' : Stack.fppfModules B S hS 𝒳} (φ : M ⟶ M') :
    φ ▷ (fppfModulesPushforward B S hS g).obj (SheafOfModules.unit _) ≫ projectionMap g M' =
      projectionMap g M ≫
        (fppfModulesPushforward B S hS g).map ((fppfModulesPullback B S hS g).map φ) := by
  simp only [projectionMap, Category.assoc]
  rw [← whisker_exchange_assoc]
  refine congrArg (M ◁ (𝔦).hom.app (SheafOfModules.unit _) ≫ ·) ?_
  exact (projectionMapRan_naturality_assoc g φ _).trans ((congrArg (projectionMapRan g M ≫ ·)
    ((𝔦).inv.naturality ((fppfModulesPullback B S hS g).map φ))).trans
      (Category.assoc _ _ _).symm)

/-- **The projection map, as a natural transformation** `(-) ⊗ g_*𝒪_𝒰 ⟶ g_* ∘ g^*` of functors
`Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`. -/
def projectionNatTrans :
    tensorRight ((fppfModulesPushforward B S hS g).obj (SheafOfModules.unit _)) ⟶
      fppfModulesPullback B S hS g ⋙ fppfModulesPushforward B S hS g where
  app M := projectionMap g M
  naturality _ _ φ := projectionMap_naturality g φ

variable {g} in
/-- For `g` affine and `M` quasi-coherent, `projectionMapRan` is an isomorphism: it is bijective
on the sections over every object lying over an affine scheme, where the sheafification unit of
the objectwise tensor product of the quasi-coherent modules `M` and `g_*𝒪_𝒰` is bijective. -/
theorem isIso_projectionMapRan (hg : IsAffineHom B S hS g) (M : quasicoherentModules B S hS 𝒳) :
    IsIso (projectionMapRan g M.obj) := by
  refine isIso_of_bijective_app_of_isAffine 𝒳 _ (fun y hy => ?_)
  have h2 : (𝔰).unit.app _ ≫ (SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars _).map (projectionMapRan g M.obj) =
        projectionPresheafMap g M.obj :=
    ((𝔰).homEquiv_unit (f := projectionMapRan g M.obj)).symm.trans (Equiv.apply_symm_apply _ _)
  have hO : ((ranDirectImage g).obj (SheafOfModules.unit _)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso ((𝔦).app (SheafOfModules.unit _))
      (isQuasicoherentOnSite_fppfModulesPushforward_of_isAffineHom B S hS g hg
        ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩)
  have hu := FibredSite.bijective_sheafTensor_unit_app_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids M.obj ((ranDirectImage g).obj (SheafOfModules.unit _))
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite M.obj
      M.property φ hz hx)
    (fun φ hz hx _ => FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite _ hO φ hz hx)
    hy
  have hb : Function.Bijective ((projectionPresheafMap g M.obj).app (op y)) :=
    bijective_projectionMapApp hg M hy
  rw [← h2] at hb
  exact (Function.Bijective.of_comp_iff _ hu).1 hb

variable {g} in
/-- For `g` affine and `M` quasi-coherent, the projection map `M ⊗ g_*𝒪_𝒰 ⟶ g_*g^*M` is an
isomorphism. -/
theorem isIso_projectionMap (hg : IsAffineHom B S hS g) (M : quasicoherentModules B S hS 𝒳) :
    IsIso (projectionMap g M.obj) := by
  have := isIso_projectionMapRan hg M
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom (whiskerLeftIso M.obj
    ((𝔦).app (SheafOfModules.unit _)))) (@IsIso.comp_isIso _ _ _ _ _ _ _ this
      (Iso.isIso_inv ((𝔦).app ((fppfModulesPullback B S hS g).obj M.obj))))

end SheafMap

section Quasicoherent

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {g} (hg : IsAffineHom B S hS g)

/-- **The projection formula for an affine 1-morphism, with `g_*` the direct image of modules**:
for `g : 𝒰 ⟶ 𝒳` affine, `M ⊗ g_*𝒪_𝒰 ≅ g_*g^*M` naturally in `M ∈ QCoh(𝒪_𝒳)`. The component at
`M` is the projection map `projectionMap g M`, `m ⊗ s ↦ (s_j · m|_{g x})_j`. -/
def affineProjectionIso :
    tensorRight ((affineQuasicoherentDirectImage B S hS g hg).obj (𝟙_ _)) ≅
      quasicoherentPullback B S hS g ⋙ affineQuasicoherentDirectImage B S hS g hg :=
  NatIso.ofComponents (fun (M : quasicoherentModules B S hS 𝒳) =>
      (ObjectProperty.fullyFaithfulι _).preimageIso
        (@asIso _ _ _ _ (projectionMap g M.obj) (isIso_projectionMap hg M)))
    (fun φ => (ObjectProperty.fullyFaithfulι _).map_injective
      (projectionMap_naturality g φ.hom))

/-- The component of `affineProjectionIso` at `M` is the projection map. -/
theorem affineProjectionIso_hom_app_hom (M : quasicoherentModules B S hS 𝒳) :
    ((affineProjectionIso hg).hom.app M).hom = projectionMap g M.obj :=
  rfl

/-- **The projection formula for an affine 1-morphism** `g : 𝒰 ⟶ 𝒳` of algebraic stacks:
`M ⊗ g_{QCoh,*}𝒪_𝒰 ≅ g_{QCoh,*}g^*M`, naturally in `M ∈ QCoh(𝒪_𝒳)`. It is `affineProjectionIso`
read through `affineQuasicoherentDirectImageIso`, the coherator doing nothing to the
direct image of a quasi-coherent module along an affine 1-morphism. -/
def projectionFormulaIso :
    tensorRight ((quasicoherentDirectImage B S hS g).obj (𝟙_ _)) ≅
      quasicoherentPullback B S hS g ⋙ quasicoherentDirectImage B S hS g :=
  (tensoringRight _).mapIso ((affineQuasicoherentDirectImageIso B S hS g hg).app (𝟙_ _)) ≪≫
    affineProjectionIso hg ≪≫
      Functor.isoWhiskerLeft (quasicoherentPullback B S hS g)
        (affineQuasicoherentDirectImageIso B S hS g hg).symm

end Quasicoherent

end AlgebraicGeometry.Stack.AlgebraicStacks
