module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherenceSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The multiplication of an algebra sheaf as a morphism of modules

Let `X` be a scheme and `A` a sheaf of commutative `𝒪_X`-algebras, i.e. an object of
`Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf`. Its underlying `𝒪_X`-module
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule A` is the sheaf of rings `A` with scalars
restricted along the structure morphism, so the multiplication of `A` is `Γ(X, U)`-bilinear on
sections and therefore induces a morphism of `𝒪_X`-modules `A ⊗_{𝒪_X} A ⟶ A`. This file builds
that morphism, builds the converse construction turning a multiplicative unital morphism of
underlying modules into a morphism of algebra sheaves, and uses the two to detect
multiplicativity of a morphism of underlying modules on the tensor square.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.mulSection`, `oneSection` and `structSection` name the
  product, the unit and the image of a section of the structure sheaf, each typed as a section
  of the underlying module; see the implementation notes.
* `Stacks.RelativeSpec.AlgebraSheaf.multiplicationPresheaf` is the multiplication as a morphism
  out of the pointwise tensor product of presheaves of modules, and
  `Stacks.RelativeSpec.AlgebraSheaf.multiplication` is **the multiplication of an algebra sheaf
  as a morphism of `𝒪_X`-modules** `A ⊗_{𝒪_X} A ⟶ A`, obtained from it through the
  sheafification adjunction.
* `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap` is the structure morphism of an algebra
  sheaf read as a morphism of `𝒪_X`-modules `𝒪_X ⟶ A`.
* `Stacks.RelativeSpec.AlgebraSheaf.homOfMultiplicative` is **the constructor**: a morphism of
  the underlying modules of two algebra sheaves which is multiplicative and unital on sections
  is a morphism of algebra sheaves.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.multiplication_tmul`: the multiplication sends the pure
  tensor of two local sections to their product. This is the characterisation that identifies
  `multiplication`.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection`: two morphisms out
  of a tensor product of sheaves of modules agreeing on pure tensors of local sections are
  equal.
* `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_homOfMultiplicative`: the morphism of
  underlying modules of `homOfMultiplicative` is the given morphism.
* `Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective`: **the multiplicativity
  criterion.** A morphism `φ` of the underlying modules of `B` and `C`, with that of `B`
  coherent and finite locally free, which becomes a morphism of algebra sheaves after
  composition with each member of a family `r n : C ⟶ D n` that is jointly injective on the
  morphisms out of coherent finite locally free modules, is itself a morphism of algebra
  sheaves — provided the structure sheaf of the base is coherent.
* `Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective_of_isLocallyNoetherian`: the
  same over a locally Noetherian scheme, where the coherence of the structure sheaf is
  automatic.

## Implementation notes

**Why the sections are named.** The carrier of a section of `underlyingModule A` over `U` is
the carrier of `A.right.obj.obj U`, but the two are spelled differently: the first is a
`ModuleCat.restrictScalars` object and the second is a `CommRingCat`. Instance resolution does
not connect the spellings, so `x * y` and `1` are not found at the first spelling at all.
`mulSection`, `oneSection` and `structSection` take their arguments at the ring spelling and
return the module spelling; every ring law is then a lemma about them, accepted at the module
goals by a definitional check. This is the same device as the `resSection`/`resRing`/`dualApp`
abbreviations of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom`.

**Which tensor product.** The tensor product used is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of the underlying ringed space,
because that is the spelling carrying the pure-tensor API (`toTensorSheafSection`,
`tensorSheafMap`, `tensorSheafMap_app_toTensorSheafSection`). It is definitionally the
`Stacks.SheafOfModules.Tensor.sheafTensor` and
`Stacks.SheafOfModules.Tensor.sheafTensor` spellings in which the two stability results consumed
below — `Stacks.SheafOfModules.isFiniteLocallyFree_tensor` and
`Stacks.TensorCoherence.isCoherent_tensorSheafBifunctor` — are stated, so nothing is
transported.

**Coherence of the structure sheaf is a genuine hypothesis of
`exists_hom_of_jointlyInjective`, not an artefact.** Multiplicativity of `φ` comes from joint
injectivity at the tensor square, which is coherent and finite locally free as soon as the
underlying module of `B` is; but *unitality* of `φ` comes from joint injectivity at `𝒪_Z`
itself, and `𝒪_Z` is admitted by the joint-injectivity hypothesis only when it is coherent.
Without it the conclusion is false. Take for `Z` the one-point scheme
`Spec k[y₁, y₂, …]/(yᵢyⱼ)`, whose structure sheaf is coherent on no nonempty open because the
annihilator of `y₁` is not finitely generated; its only opens are `∅` and `⊤`, so a finite
locally free module is globally free of finite rank, and a free module of positive rank cannot
be coherent there without making `𝒪_Z` coherent (Tag 01BY (1), a finite type subsheaf of a
coherent sheaf is coherent). Hence every coherent finite locally free `𝒪_Z`-module is zero.
Now let `B` and `D n` be the zero sheaf of rings, which is an algebra sheaf because the zero
ring is terminal and whose underlying module is zero, hence coherent and finite locally free of
rank zero, and let `C = 𝒪_Z`. All four hypotheses hold — the lift is the identity of the zero
algebra, and joint injectivity is vacuous because the only admissible `P` is zero — while a
morphism of algebra sheaves from the zero algebra to `𝒪_Z` would force `1 = 0` in
`Γ(Z, 𝒪_Z)`. The hypothesis is harmless for the intended consumer, where the base is
Noetherian; see `exists_hom_of_jointlyInjective_of_isLocallyNoetherian`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

/-- **Two morphisms out of a tensor product of sheaves of modules that agree on pure tensors of
local sections are equal.** The tensor product is the sheafification of the pointwise one, so
this is injectivity of the sheafification adjunction's bijection together with the fact that
the pure tensors generate the pointwise tensor product. -/
theorem hom_ext_toTensorSheafSection (X : AlgebraicGeometry.RingedSpace.{u, u})
    {F G N : SheafOfModules.{u} (structureSheafRing X)}
    (a b : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(X).presheaf, (X).IsSheaf⟩).obj F).obj G ⟶ N)
    (h : ∀ (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      (a.val.app U).hom (toTensorSheafSection X F G U (x ⊗ₜ[X.presheaf.obj U] y))
        = (b.val.app U).hom (toTensorSheafSection X F G U (x ⊗ₜ[X.presheaf.obj U] y))) :
    a = b := by
  refine ((PresheafOfModules.sheafificationAdjunction (R := structureSheafRing X)
    (𝟙 (structureSheafRing X).obj)).homEquiv
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) N).injective ?_
  exact PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (TensorProduct.ext' fun x y => h U x y)

end Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-! ### Sections of an algebra sheaf, typed as sections of its underlying module -/

/-- The underlying presheaf of modules of the underlying `𝒪_X`-module of an algebra sheaf,
spelled over the structure presheaf of the underlying ringed space. The spelling matters: it is
the one in which instance resolution finds the `Γ(X, U)`-module structure on sections that the
pointwise tensor product is formed over. -/
abbrev underlyingPresheaf (A : AlgebraSheaf X) : PresheafOfModules.{u} (O X.toRingedSpace) :=
  (underlyingModule A).val

/-- The product of two sections of an algebra sheaf over an open, as a section of the
underlying module. -/
def mulSection (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    (underlyingPresheaf A).obj U :=
  x * y

/-- The unit section of an algebra sheaf over an open, as a section of the underlying
module. -/
def oneSection (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) : (underlyingPresheaf A).obj U :=
  (1 : (ringSheaf A).obj.obj U)

/-- The image of a section of the structure sheaf under the structure morphism of an algebra
sheaf, as a section of the underlying module. -/
def structSection (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (r : X.presheaf.obj U) :
    (underlyingPresheaf A).obj U :=
  ((structureMap A).hom.app U).hom r

/-- The product of sections is additive in its first argument. -/
theorem mulSection_add_left (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x y z : A.right.obj.obj U) :
    mulSection A U (x + y) z = mulSection A U x z + mulSection A U y z :=
  add_mul x y z

/-- The product of sections is additive in its second argument. -/
theorem mulSection_add_right (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x y z : A.right.obj.obj U) :
    mulSection A U x (y + z) = mulSection A U x y + mulSection A U x z :=
  mul_add x y z

/-- Associativity of the product of sections, in the form that gives linearity of the
multiplication in its first argument. -/
theorem mulSection_mul_left (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (s x y : A.right.obj.obj U) :
    mulSection A U (s * x) y = mulSection A U s (x * y) :=
  mul_assoc s x y

/-- Commutativity and associativity of the product of sections, in the form that gives
linearity of the multiplication in its second argument. -/
theorem mulSection_mul_right (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (s x y : A.right.obj.obj U) :
    mulSection A U x (s * y) = mulSection A U s (x * y) :=
  mul_left_comm x s y

/-- The restriction maps of an algebra sheaf are multiplicative. -/
theorem mulSection_naturality (A : AlgebraSheaf X) {U V : (X.Opens)ᵒᵖ} (f : U ⟶ V)
    (x y : A.right.obj.obj U) :
    ((underlyingPresheaf A).map f).hom (mulSection A U x y)
      = mulSection A V ((A.right.obj.map f).hom x) ((A.right.obj.map f).hom y) :=
  map_mul (A.right.obj.map f).hom x y

/-- The structure morphism sends `1` to the unit section. -/
theorem structSection_one (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) :
    structSection A U 1 = oneSection A U :=
  map_one ((structureMap A).hom.app U).hom

/-- The structure morphism is multiplicative. -/
theorem structSection_mul (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (r s : X.presheaf.obj U) :
    structSection A U (r * s) = mulSection A U (structSection A U r) (structSection A U s) :=
  map_mul ((structureMap A).hom.app U).hom r s

/-- The structure morphism commutes with the restriction maps. -/
theorem structSection_naturality (A : AlgebraSheaf X) {U V : (X.Opens)ᵒᵖ} (f : U ⟶ V)
    (r : X.presheaf.obj U) :
    ((underlyingPresheaf A).map f).hom (structSection A U r)
      = structSection A V ((X.presheaf.map f).hom r) :=
  congrArg (fun φ : X.ringCatSheaf.obj.obj U ⟶ (ringSheaf A).obj.obj V => φ.hom r)
    ((structureMap A).hom.naturality f).symm

/-- A morphism of algebra sheaves is multiplicative on sections. -/
theorem underlyingModuleMap_mulSection {A B : AlgebraSheaf X} (f : A ⟶ B) (U : (X.Opens)ᵒᵖ)
    (x y : A.right.obj.obj U) :
    ((underlyingModuleMap f).val.app U).hom (mulSection A U x y)
      = mulSection B U (((underlyingModuleMap f).val.app U).hom x)
          (((underlyingModuleMap f).val.app U).hom y) :=
  map_mul ((ringSheafMap f).hom.app U).hom x y

/-- A morphism of algebra sheaves is unital on sections. -/
theorem underlyingModuleMap_oneSection {A B : AlgebraSheaf X} (f : A ⟶ B) (U : (X.Opens)ᵒᵖ) :
    ((underlyingModuleMap f).val.app U).hom (oneSection A U) = oneSection B U :=
  map_one ((ringSheafMap f).hom.app U).hom

/-- A morphism of algebra sheaves is a morphism over the structure sheaf, on sections. -/
theorem underlyingModuleMap_structSection {A B : AlgebraSheaf X} (f : A ⟶ B) (U : (X.Opens)ᵒᵖ)
    (r : X.presheaf.obj U) :
    ((underlyingModuleMap f).val.app U).hom (structSection A U r) = structSection B U r :=
  ringSheafMap_app_structureMap_app f U r

/-! ### The multiplication as a morphism of modules -/

/-- Multiplication by a fixed section of an algebra sheaf, as a `Γ(X, U)`-linear endomorphism
of the sections of the underlying module. -/
def mulLinear (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x : A.right.obj.obj U) :
    (underlyingPresheaf A).obj U →ₗ[X.presheaf.obj U] (underlyingPresheaf A).obj U where
  toFun y := mulSection A U x y
  map_add' y z := mulSection_add_right A U x y z
  map_smul' r y := mulSection_mul_right A U (((structureMap A).hom.app U).hom r) x y

/-- The multiplication of an algebra sheaf over an open, as a `Γ(X, U)`-bilinear map on the
sections of the underlying module. -/
def mulBilinear (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) :
    (underlyingPresheaf A).obj U →ₗ[X.presheaf.obj U]
      ((underlyingPresheaf A).obj U →ₗ[X.presheaf.obj U] (underlyingPresheaf A).obj U) where
  toFun x := mulLinear A U x
  map_add' x y := LinearMap.ext fun z => mulSection_add_left A U x y z
  map_smul' r x := LinearMap.ext fun z =>
    mulSection_mul_left A U (((structureMap A).hom.app U).hom r) x z

/-- The multiplication of an algebra sheaf over an open, as a linear map out of the tensor
product of the sections of the underlying module with itself. -/
def mulTensorLift (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) :
    TensorProduct (X.presheaf.obj U) ((underlyingPresheaf A).obj U)
        ((underlyingPresheaf A).obj U) →ₗ[X.presheaf.obj U]
      (underlyingPresheaf A).obj U :=
  TensorProduct.lift (mulBilinear A U)

/-- The multiplication on sections sends a pure tensor to the product. -/
theorem mulTensorLift_tmul (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    mulTensorLift A U (x ⊗ₜ[X.presheaf.obj U] y) = mulSection A U x y :=
  rfl

/-- The multiplication of an algebra sheaf as a morphism of the underlying presheaves of
abelian groups of the pointwise tensor square. -/
def mulNat (A : AlgebraSheaf X) :
    (PresheafOfModules.tensorObj (O := X.presheaf)
      (underlyingPresheaf A) (underlyingPresheaf A)).presheaf ⟶
      (underlyingPresheaf A).presheaf where
  app U := AddCommGrpCat.ofHom (mulTensorLift A U).toAddMonoidHom
  naturality U V f := by
    apply AddCommGrpCat.hom_ext
    refine AddMonoidHom.ext fun t => ?_
    change mulTensorLift A V
        ((PresheafOfModules.tensorObj (O := X.presheaf)
          (underlyingPresheaf A) (underlyingPresheaf A)).restrictₛₗ f t)
      = ((underlyingPresheaf A).map f).hom (mulTensorLift A U t)
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
        rw [PresheafOfModules.tensorObj_restrictₛₗ_tmul]
        exact (mulSection_naturality A f x y).symm
    | add a b ha hb =>
        simp only [map_add]
        exact (congrArg (mulTensorLift A V)
          (((PresheafOfModules.tensorObj (O := X.presheaf)
            (underlyingPresheaf A) (underlyingPresheaf A)).restrictₛₗ f).map_add a b)).trans
          (((mulTensorLift A V).map_add _ _).trans (congrArg₂ (· + ·) ha hb))

/-- **The multiplication of an algebra sheaf, on the pointwise tensor square**: the morphism of
presheaves of `𝒪_X`-modules `A ⊗^{pre}_{𝒪_X} A ⟶ A` given on sections by the multiplication. -/
def multiplicationPresheaf (A : AlgebraSheaf X) :
    PresheafOfModules.tensorObj (O := X.presheaf) (underlyingPresheaf A) (underlyingPresheaf A) ⟶
      underlyingPresheaf A :=
  PresheafOfModules.homMk (mulNat A) fun U r t => (mulTensorLift A U).map_smul r t

/-- The multiplication on the pointwise tensor square sends a pure tensor to the product. -/
theorem multiplicationPresheaf_app_tmul (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ)
    (x y : A.right.obj.obj U) :
    PresheafOfModules.Hom.app (multiplicationPresheaf A) U (x ⊗ₜ[X.presheaf.obj U] y)
      = mulSection A U x y :=
  rfl

/-- **The multiplication of an algebra sheaf as a morphism of `𝒪_X`-modules**
`A ⊗_{𝒪_X} A ⟶ A`. The tensor product of sheaves of modules is the sheafification of the
pointwise one, so this is the morphism that `multiplicationPresheaf` induces through the
sheafification adjunction; `multiplication_tmul` is its characterisation on pure tensors. -/
def multiplication (A : AlgebraSheaf X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
      (underlyingModule A)).obj (underlyingModule A) ⟶ underlyingModule A :=
  ((PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing X.toRingedSpace)
      (𝟙 (structureSheafRing X.toRingedSpace).obj)).homEquiv
    (PresheafOfModules.tensorObj (O := X.presheaf) (underlyingModule A).val
      (underlyingModule A).val)
    (underlyingModule A)).symm (multiplicationPresheaf A)

/-- The multiplication of an algebra sheaf agrees with the pointwise multiplication on the
image of the sheafification unit. -/
theorem multiplication_toTensorSheafSection (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ)
    (t : TensorProduct (X.presheaf.obj U) ((underlyingPresheaf A).obj U)
      ((underlyingPresheaf A).obj U)) :
    ((multiplication A).val.app U).hom
        (toTensorSheafSection X.toRingedSpace (underlyingModule A) (underlyingModule A) U t)
      = PresheafOfModules.Hom.app (multiplicationPresheaf A) U t :=
  congrArg (fun q => PresheafOfModules.Hom.app q U t)
    (((PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing X.toRingedSpace)
      (𝟙 (structureSheafRing X.toRingedSpace).obj)).homEquiv
      (PresheafOfModules.tensorObj (O := X.presheaf) (underlyingModule A).val
        (underlyingModule A).val)
      (underlyingModule A)).apply_symm_apply (multiplicationPresheaf A))

/-- **The multiplication of an algebra sheaf, on pure tensors**: it sends the pure tensor of
two sections of `A` over `U` to their product. -/
theorem multiplication_tmul (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    ((multiplication A).val.app U).hom
        (toTensorSheafSection X.toRingedSpace (underlyingModule A) (underlyingModule A) U
          (x ⊗ₜ[X.presheaf.obj U] y))
      = mulSection A U x y :=
  multiplication_toTensorSheafSection A U _

/-! ### The structure morphism as a morphism of modules -/

/-- The structure morphism of an algebra sheaf, as a morphism of presheaves of
`𝒪_X`-modules `𝒪_X ⟶ A`. -/
def unitPresheafMap (A : AlgebraSheaf X) :
    (SheafOfModules.unit X.ringCatSheaf).val ⟶ (underlyingModule A).val where
  app U := ConcreteCategory.ofHom (C := ModuleCat (X.ringCatSheaf.obj.obj U))
    { toFun := fun r => structSection A U r
      map_add' := fun r s => map_add ((structureMap A).hom.app U).hom r s
      map_smul' := fun r s => structSection_mul A U r s }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun r => ?_
    exact (structSection_naturality A f r).symm

/-- **The structure morphism of an algebra sheaf as a morphism of `𝒪_X`-modules**
`𝒪_X ⟶ A`, i.e. `r ↦ r · 1`. -/
def unitModuleMap (A : AlgebraSheaf X) :
    SheafOfModules.unit X.ringCatSheaf ⟶ underlyingModule A :=
  show SheafOfModules.Hom _ _ from { val := unitPresheafMap A }

/-- The structure morphism as a morphism of modules, read on sections. -/
theorem unitModuleMap_apply (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) (r : X.presheaf.obj U) :
    ((unitModuleMap A).val.app U).hom r = structSection A U r :=
  rfl

/-- The structure morphisms of two algebra sheaves are compatible with any morphism between
them. -/
theorem unitModuleMap_comp {A B : AlgebraSheaf X} (f : A ⟶ B) :
    unitModuleMap A ≫ underlyingModuleMap f = unitModuleMap B := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  exact underlyingModuleMap_structSection f U r

/-- The image of a section of the structure sheaf is that section acting on the unit
section. -/
theorem structSection_eq_smul_oneSection (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ)
    (r : X.presheaf.obj U) : structSection A U r = r • oneSection A U :=
  (mul_one (((structureMap A).hom.app U).hom r)).symm

/-- A unital morphism of the underlying modules of two algebra sheaves is compatible with their
structure morphisms: `𝒪_X`-linearity turns the image of a section `r` of the structure sheaf
into `r · φ(1)`, and `φ(1) = 1`. -/
theorem structSection_of_oneSection {A B : AlgebraSheaf X}
    (φ : underlyingModule A ⟶ underlyingModule B)
    (hone : ∀ U : (X.Opens)ᵒᵖ, (φ.val.app U).hom (oneSection A U) = oneSection B U)
    (U : (X.Opens)ᵒᵖ) (r : X.presheaf.obj U) :
    (φ.val.app U).hom (structSection A U r) = structSection B U r :=
  (congrArg (φ.val.app U).hom (structSection_eq_smul_oneSection A U r)).trans
    (((φ.val.app U).hom.map_smul r (oneSection A U)).trans
      ((congrArg (fun z : (underlyingPresheaf B).obj U => r • z) (hone U)).trans
        (structSection_eq_smul_oneSection B U r).symm))

/-! ### Composites out of the tensor square, on pure tensors -/

/-- The multiplication followed by any morphism, on a pure tensor of local sections. -/
theorem multiplication_comp_tmul {A : AlgebraSheaf X} {N : X.Modules}
    (g : underlyingModule A ⟶ N) (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    ((multiplication A ≫ g).val.app U).hom
        (toTensorSheafSection X.toRingedSpace (underlyingModule A) (underlyingModule A) U
          (x ⊗ₜ[X.presheaf.obj U] y))
      = (g.val.app U).hom (mulSection A U x y) :=
  congrArg (g.val.app U).hom (multiplication_tmul A U x y)

/-- The tensor square of a morphism followed by any morphism, on a pure tensor of local
sections. -/
theorem tensorSheafMap_comp_tmul {A B : AlgebraSheaf X}
    (φ : underlyingModule A ⟶ underlyingModule B) {N : X.Modules}
    (g : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
      (underlyingModule B)).obj (underlyingModule B) ⟶ N)
    (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).map φ).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X).presheaf, (X).IsSheaf⟩).obj _).map φ) ≫ g).val.app U).hom
        (toTensorSheafSection X.toRingedSpace (underlyingModule A) (underlyingModule A) U
          (x ⊗ₜ[X.presheaf.obj U] y))
      = (g.val.app U).hom
          (toTensorSheafSection X.toRingedSpace (underlyingModule B) (underlyingModule B) U
            ((φ.val.app U).hom x ⊗ₜ[X.presheaf.obj U] (φ.val.app U).hom y)) :=
  congrArg (g.val.app U).hom
    (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace (underlyingModule A)
      (underlyingModule A) (underlyingModule B) (underlyingModule B) φ φ U.unop x y)

/-- The structure morphism of an algebra sheaf followed by any morphism, read at the unit
section of the structure sheaf. -/
theorem unitModuleMap_comp_one {A : AlgebraSheaf X} {N : X.Modules}
    (g : underlyingModule A ⟶ N) (U : (X.Opens)ᵒᵖ) :
    ((unitModuleMap A ≫ g).val.app U).hom (1 : X.presheaf.obj U)
      = (g.val.app U).hom (oneSection A U) :=
  congrArg (g.val.app U).hom (structSection_one A U)

/-- The structure morphism of an algebra sheaf, read at the unit section of the structure
sheaf. -/
theorem unitModuleMap_one (A : AlgebraSheaf X) (U : (X.Opens)ᵒᵖ) :
    ((unitModuleMap A).val.app U).hom (1 : X.presheaf.obj U) = oneSection A U :=
  structSection_one A U

/-! ### From a multiplicative morphism of modules to a morphism of algebra sheaves -/

section Constructor

variable {A B : AlgebraSheaf X} (φ : underlyingModule A ⟶ underlyingModule B)
  (hone : ∀ U : (X.Opens)ᵒᵖ, (φ.val.app U).hom (oneSection A U) = oneSection B U)
  (hmul : ∀ (U : (X.Opens)ᵒᵖ) (x y : A.right.obj.obj U),
    (φ.val.app U).hom (mulSection A U x y)
      = mulSection B U ((φ.val.app U).hom x) ((φ.val.app U).hom y))

include hone hmul

/-- The sections of a multiplicative unital morphism of underlying modules, as a morphism of
commutative rings. -/
def ringHomOfMultiplicative (U : (X.Opens)ᵒᵖ) : A.right.obj.obj U ⟶ B.right.obj.obj U :=
  CommRingCat.ofHom
    { toFun := fun x => (φ.val.app U).hom x
      map_one' := hone U
      map_mul' := fun x y => hmul U x y
      map_zero' := map_zero (φ.val.app U).hom
      map_add' := fun x y => map_add (φ.val.app U).hom x y }

/-- The sections of `ringHomOfMultiplicative` are the sections of the given morphism of
modules. -/
theorem ringHomOfMultiplicative_apply (U : (X.Opens)ᵒᵖ) (x : A.right.obj.obj U) :
    (ringHomOfMultiplicative φ hone hmul U).hom x = (φ.val.app U).hom x :=
  rfl

/-- The morphism of sheaves of commutative rings underlying a multiplicative unital morphism of
underlying modules. -/
def sheafHomOfMultiplicative : A.right ⟶ B.right :=
  ⟨{ app := ringHomOfMultiplicative φ hone hmul
     naturality := fun U V f => by
       apply CommRingCat.hom_ext
       refine RingHom.ext fun x => ?_
       exact PresheafOfModules.naturality_apply φ.val f x }⟩

/-- **A multiplicative unital morphism of underlying modules is a morphism of algebra
sheaves.** The compatibility with the two structure morphisms is forced: `𝒪_X`-linearity turns
the image of a section `r` of the structure sheaf into `r · φ(1)`, and `φ(1) = 1`. -/
def homOfMultiplicative : A ⟶ B :=
  Under.homMk (sheafHomOfMultiplicative φ hone hmul) (by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    exact structSection_of_oneSection φ hone U r)

/-- The morphism of underlying modules of `homOfMultiplicative` is the given morphism. -/
theorem underlyingModuleMap_homOfMultiplicative :
    underlyingModuleMap (homOfMultiplicative φ hone hmul) = φ := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rfl

end Constructor

/-! ### The multiplicativity criterion -/

/-- Equal morphisms of `𝒪_X`-modules agree on every section. -/
private theorem app_hom_congr {M N : X.Modules} {f g : M ⟶ N} (h : f = g) (U : (X.Opens)ᵒᵖ)
    (z : M.val.obj U) : (f.val.app U).hom z = (g.val.app U).hom z :=
  congrArg (fun t : M ⟶ N => (t.val.app U).hom z) h

/-- The structure sheaf of a scheme is finite locally free: it is free of rank one on itself. -/
theorem isFiniteLocallyFree_unitModule (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
    (Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u}
      (Stacks.SheafOfModules.Site.freePUnitIso (R := X.ringCatSheaf))).1

/-- The tensor square of a finite locally free sheaf of modules is finite locally free. -/
theorem isFiniteLocallyFree_tensorSquare {X : Scheme.{u}} (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj M).obj M) :=
  Stacks.SheafOfModules.isFiniteLocallyFree_tensor X.sheaf hM hM

/-- The tensor square of a coherent sheaf of modules on a scheme with coherent structure sheaf
is coherent: coherence of the structure sheaf turns coherence of `M` into finite presentation,
and the tensor product of a finitely presented module with a coherent one is coherent. -/
theorem isCoherent_tensorSquare {X : Scheme.{u}} (M : X.Modules)
    (hunit : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hM : _root_.SheafOfModules.IsCoherent M) :
    _root_.SheafOfModules.IsCoherent
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj M).obj M) := by
  have hu : Stacks.SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    ⟨hunit.isFiniteType, hunit.kernel_isFiniteType⟩
  have hM' : Stacks.SheafOfModules.IsCoherent M := ⟨hM.isFiniteType, hM.kernel_isFiniteType⟩
  have _ : M.IsFinitePresentation :=
    (Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation X.ringCatSheaf M).mp hM'
  have h := Stacks.SheafOfModules.Site.isCoherent_iff_isCoherent_opens.mp
    (Stacks.TensorCoherence.isCoherent_tensorSheafBifunctor (O := X.sheaf) M M
      (Stacks.SheafOfModules.Site.isCoherent_iff_isCoherent_opens.mpr hM'))
  exact ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- **The multiplicativity criterion for a morphism of the underlying modules of two algebra
sheaves.** Let `B`, `C` be sheaves of commutative `𝒪_Z`-algebras, let `r n : C ⟶ D n` be a
family of morphisms of algebra sheaves which is jointly injective on the morphisms out of
coherent finite locally free modules, and let `φ` be a morphism of the underlying modules of
`B` and `C` with that of `B` coherent and finite locally free. If `φ` becomes a morphism of
algebra sheaves after composition with each `r n`, then `φ` is itself a morphism of algebra
sheaves.

Multiplicativity is the square built from `φ ⊗ φ` and the two multiplication maps, tested by
joint injectivity at the tensor square `B ⊗_{𝒪_Z} B`, which is coherent and finite locally free
by `isCoherent_tensorSquare` and `isFiniteLocallyFree_tensorSquare`. Unitality is the same test
at `𝒪_Z`, which is why coherence of the structure sheaf is assumed; see the implementation notes
of this file for what fails without it. -/
theorem exists_hom_of_jointlyInjective {Z : Scheme.{u}} (B C : AlgebraSheaf Z)
    (D : ℕ → AlgebraSheaf Z) (r : ∀ n : ℕ, C ⟶ D n)
    (φ : underlyingModule B ⟶ underlyingModule C)
    (hunit : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (underlyingModule B))
    (hcoh : _root_.SheafOfModules.IsCoherent (underlyingModule B))
    (hlift : ∀ n : ℕ, ∃ ψ : B ⟶ D n,
      underlyingModuleMap ψ = φ ≫ underlyingModuleMap (r n))
    (hjoint : ∀ P : Z.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
      _root_.SheafOfModules.IsCoherent P →
      ∀ a b : P ⟶ underlyingModule C,
        (∀ n : ℕ, a ≫ underlyingModuleMap (r n) = b ≫ underlyingModuleMap (r n)) → a = b) :
    ∃ ψ : B ⟶ C, underlyingModuleMap ψ = φ := by
  choose ψ hψ using hlift
  have hcomp : ∀ (n : ℕ) (U : (Z.Opens)ᵒᵖ) (z : (underlyingModule B).val.obj U),
      ((underlyingModuleMap (r n)).val.app U).hom ((φ.val.app U).hom z)
        = ((underlyingModuleMap (ψ n)).val.app U).hom z := fun n U z =>
    (app_hom_congr (hψ n) U z).symm
  have hone : ∀ U : (Z.Opens)ᵒᵖ, (φ.val.app U).hom (oneSection B U) = oneSection C U := by
    have key : unitModuleMap B ≫ φ = unitModuleMap C :=
      hjoint _ (isFiniteLocallyFree_unitModule Z) hunit _ _ fun n => by
        erw [Category.assoc, ← hψ n, unitModuleMap_comp, unitModuleMap_comp]
    intro U
    exact (unitModuleMap_comp_one φ U).symm.trans
      ((app_hom_congr key U (1 : Z.presheaf.obj U)).trans (unitModuleMap_one C U))
  have hmul : ∀ (U : (Z.Opens)ᵒᵖ) (x y : B.right.obj.obj U),
      (φ.val.app U).hom (mulSection B U x y)
        = mulSection C U ((φ.val.app U).hom x) ((φ.val.app U).hom y) := by
    have key : multiplication B ≫ φ
        = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Z).presheaf, (Z).IsSheaf⟩).map φ).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Z).presheaf, (Z).IsSheaf⟩).obj _).map φ) ≫ multiplication C := by
      refine hjoint _ (isFiniteLocallyFree_tensorSquare _ hflf)
        (isCoherent_tensorSquare _ hunit hcoh) _ _ fun n => ?_
      erw [Category.assoc, ← hψ n, Category.assoc]
      refine hom_ext_toTensorSheafSection Z.toRingedSpace _ _ fun U x y => ?_
      refine (multiplication_comp_tmul (underlyingModuleMap (ψ n)) U x y).trans ?_
      refine Eq.trans ?_ (tensorSheafMap_comp_tmul φ
        (multiplication C ≫ underlyingModuleMap (r n)) U x y).symm
      refine Eq.trans ?_ (multiplication_comp_tmul (underlyingModuleMap (r n)) U
        ((φ.val.app U).hom x) ((φ.val.app U).hom y)).symm
      refine (underlyingModuleMap_mulSection (ψ n) U x y).trans ?_
      refine Eq.trans ?_ (underlyingModuleMap_mulSection (r n) U
        ((φ.val.app U).hom x) ((φ.val.app U).hom y)).symm
      rw [hcomp n U x, hcomp n U y]
    intro U x y
    exact (multiplication_comp_tmul φ U x y).symm.trans
      ((app_hom_congr key U _).trans ((tensorSheafMap_comp_tmul φ (multiplication C) U x y).trans
        (multiplication_tmul C U ((φ.val.app U).hom x) ((φ.val.app U).hom y))))
  exact ⟨homOfMultiplicative φ hone hmul, underlyingModuleMap_homOfMultiplicative φ hone hmul⟩

/-- **The multiplicativity criterion over a locally Noetherian scheme.** The structure sheaf of
a locally Noetherian scheme is coherent, so the coherence hypothesis of
`Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective` is automatic. -/
theorem exists_hom_of_jointlyInjective_of_isLocallyNoetherian {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (B C : AlgebraSheaf Z) (D : ℕ → AlgebraSheaf Z)
    (r : ∀ n : ℕ, C ⟶ D n) (φ : underlyingModule B ⟶ underlyingModule C)
    (hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (underlyingModule B))
    (hcoh : _root_.SheafOfModules.IsCoherent (underlyingModule B))
    (hlift : ∀ n : ℕ, ∃ ψ : B ⟶ D n,
      underlyingModuleMap ψ = φ ≫ underlyingModuleMap (r n))
    (hjoint : ∀ P : Z.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} P →
      _root_.SheafOfModules.IsCoherent P →
      ∀ a b : P ⟶ underlyingModule C,
        (∀ n : ℕ, a ≫ underlyingModuleMap (r n) = b ≫ underlyingModuleMap (r n)) → a = b) :
    ∃ ψ : B ⟶ C, underlyingModuleMap ψ = φ :=
  have hu := Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  exists_hom_of_jointlyInjective B C D r φ
    ⟨hu.isFiniteType, hu.kernel_isFiniteType⟩ hflf hcoh hlift hjoint

end Stacks.RelativeSpec.AlgebraSheaf

end
