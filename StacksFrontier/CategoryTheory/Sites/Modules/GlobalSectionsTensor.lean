module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The module `M ⊗_A 𝒪` attached to a module over the global functions of a site

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it and write
`A = Γ(C, O)` for the ring of compatible families of sections of `O`.  For an `A`-module `M`
the assignment `U ↦ O(U) ⊗_A M` is a presheaf of `O`-modules, and its sheafification is the
`O`-module written `M ⊗_A 𝒪`.  This file constructs that presheaf, the functor it defines, the
sheafified functor, and the canonical `A`-linear map from `M` to the global sections of
`M ⊗_A 𝒪`.

## Main definitions

* `Stacks.Cohomology.SiteModules.ringSheafOfSite`: a sheaf of commutative rings read as a sheaf
  of rings, and `GlobalFunctionRing` the ring `A` of its global sections.
* `Stacks.Cohomology.SiteModules.globalSectionEvalHom`: evaluation `A →+* O(U)` of a global
  function at an object of the site, and the `A`-algebra structure it puts on `O(U)`.
* `Stacks.Cohomology.SiteModules.sectionTensorPresheaf`: the presheaf of `O`-modules
  `U ↦ O(U) ⊗_A M`, with `sectionTensorPresheafFunctor` its functoriality in `M`.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`: the functor `M ↦ M ⊗_A 𝒪` from
  `A`-modules to `O`-modules, the sheafification of `sectionTensorPresheafFunctor`.
* `Stacks.Cohomology.SiteModules.sectionsOfTensorPresheafHom`: the `A`-linear map
  `M ⟶ Γ(C, F)` carried by a morphism of presheaves of modules `(U ↦ O(U) ⊗_A M) ⟶ F`,
  namely `m ↦ 1 ⊗ m`.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafUnit`: the canonical `A`-linear map
  `M ⟶ Γ(C, M ⊗_A 𝒪)`, the above at the unit of sheafification.
* `Stacks.Cohomology.SiteModules.sectionTensorPresheafHomOfSections`: the morphism of presheaves
  of `O`-modules `(U ↦ O(U) ⊗_A M) ⟶ F` carried by an `A`-linear map `θ : M ⟶ Γ(C, F)`, namely
  `a ⊗ m ↦ a · θ(m)|_U`; it is the inverse of `sectionsOfTensorPresheafHom`.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction`: the adjunction exhibiting
  `M ↦ M ⊗_A 𝒪` as the left adjoint of global sections.

## Main results

* `Stacks.Cohomology.SiteModules.sectionTensorPresheaf_map_tmul` and
  `sectionTensorPresheafFunctorMap_app_tmul`: the restriction maps of `U ↦ O(U) ⊗_A M`, and its
  functoriality in `M`, computed on a tensor.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafUnit_eval`: the canonical map evaluated at an
  object of the site is the sheafification map applied to `1 ⊗ m`.
* `Stacks.Cohomology.SiteModules.sectionTensorPresheafHomEquiv`: morphisms of presheaves of
  `O`-modules from `U ↦ O(U) ⊗_A M` into a sheaf of `O`-modules `F` are the `A`-linear maps
  `M ⟶ Γ(C, F)`.
* `Stacks.Cohomology.SiteModules.sectionTensorHomEquiv`: the same for morphisms of sheaves of
  `O`-modules `M ⊗_A 𝒪 ⟶ F`, which is the universal property of `M ⊗_A 𝒪`.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor_isLeftAdjoint`: `M ↦ M ⊗_A 𝒪` is a
  left adjoint, hence preserves all colimits and in particular is right exact.
* `Stacks.Cohomology.SiteModules.sectionTensorSheafAdjunction_unit_app`: the unit of the
  adjunction is the canonical map `sectionTensorSheafUnit`.

## Implementation notes

The ring `A` of global functions lies in the universe `max u r`, where `u` is the universe of
the objects of the site and `r` that of the rings of sections of `O`.  On the small étale site
of an algebraic space these differ — the objects lie one universe above the rings — so `A` is
strictly larger than the rings of `O`, and the extension-of-scalars functor for presheaves of
modules over a presheaf of rings at a *fixed* universe, which is what
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` provides, does not apply: there is no
presheaf of rings with constant value `A` at the universe of `O`.  The presheaf
`U ↦ O(U) ⊗_A M` is therefore assembled directly from `TensorProduct`, whose base ring and
modules may lie in unrelated universes.  The module universe is `max u r w` for an `A`-module
universe `w`: extension of scalars raises it to that of the rings, and global sections raise it
to that of the objects of the site.

`A` is spelled `Stacks.Cohomology.SiteModules.GlobalSectionRing` of the ring sheaf rather than
as the section ring of the bare presheaf, although the two are the same by definition.  This is
what lets instance search find `Stacks.Cohomology.SiteModules.sectionsModule`, the `A`-module
structure on the global sections of a sheaf of modules: that instance is indexed by a sheaf of
rings, and unification does not recover a sheaf from its underlying presheaf.  For the same
reason no module structure is declared on the sections of a general presheaf of modules, which
would shadow it.

Restriction along `f` is `A`-linear because a compatible family of sections of `O` restricts to
itself, which is `globalSectionEvalHom_naturality`; that is the only input beyond the ring
structure, and it is what makes `U ↦ O(U) ⊗_A M` a presheaf of modules at all.

The map `O(U) ⊗_A M → F(U)` attached to `θ : M ⟶ Γ(C, F)` is built with
`TensorProduct.liftAddHom`, so it is only additive to begin with and its `O(U)`-linearity is a
separate lemma.  An `A`-linear construction would need an `A`-module structure on the sections of
`F`, which is not declared: the scalars of a sheaf of `O`-modules are the sections of `O` over an
object, and restricting them along evaluation at that object would shadow the structure the
sheaves-of-modules API uses.  What makes the additive map well defined is instead commutativity
of `O(U)`.  Scalars acting on sections of `F` must be presented in the `RingCat` spelling of the
sections of `O`, which is `ringSheafSection`; the `CommRingCat` spelling carries a `Ring`
projection that instance search does not identify with the one the module structure uses.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

section Setup

variable (O : Sheaf J CommRingCat.{r})

/-- A sheaf of commutative rings on a site, read as a sheaf of rings: the rings over which its
sheaves of modules are indexed. -/
abbrev ringSheafOfSite : Sheaf J RingCat.{r} :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj O

/-- The ring `A = Γ(C, O)` of compatible families of sections of a sheaf of commutative
rings. -/
abbrev GlobalFunctionRing := GlobalSectionRing (ringSheafOfSite O)

/-- The global functions of a sheaf of commutative rings form a commutative ring, the
operations being pointwise. -/
instance globalFunctionRingCommRing : CommRing (GlobalFunctionRing O) :=
  { (inferInstance : Ring (GlobalFunctionRing O)) with
    mul_comm := fun a b => Subtype.ext (funext fun X =>
      mul_comm (G := O.obj.obj X) (a.val X) (b.val X)) }

/-- Evaluation of a compatible family of sections of `O` at an object of the site. -/
def globalSectionEvalHom (X : Cᵒᵖ) : GlobalFunctionRing O →+* O.obj.obj X where
  toFun a := a.val X
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation at an object makes the sections of `O` there an algebra over the global
functions. -/
instance algebraGlobalSectionEval (X : Cᵒᵖ) : Algebra (GlobalFunctionRing O) (O.obj.obj X) :=
  (globalSectionEvalHom O X).toAlgebra

/-- The structure map of that algebra is evaluation of a global function. -/
@[simp] theorem algebraMap_globalSectionEval (X : Cᵒᵖ) (a : GlobalFunctionRing O) :
    algebraMap (GlobalFunctionRing O) (O.obj.obj X) a = a.val X := rfl

/-- A global function acts on sections over an object by multiplication by its value
there. -/
theorem smul_eq_globalSectionEval_mul {X : Cᵒᵖ} (a : GlobalFunctionRing O) (x : O.obj.obj X) :
    a • x = globalSectionEvalHom O X a * x := rfl

variable {O}

/-- A global function restricts to a global function: the defining compatibility of a
compatible family of sections of `O`. -/
theorem globalSectionEvalHom_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : GlobalFunctionRing O) :
    (O.obj.map f).hom (globalSectionEvalHom O X a) = globalSectionEvalHom O Y a := a.2 f

/-- The restriction map of `O` along `f`, as a map of modules over the global functions. -/
def restrictionLinearMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (O.obj.obj X) →ₗ[GlobalFunctionRing O] (O.obj.obj Y) where
  toFun x := (O.obj.map f).hom x
  map_add' x y := map_add (O.obj.map f).hom x y
  map_smul' a x := by
    change (O.obj.map f).hom (globalSectionEvalHom O X a * x) =
      globalSectionEvalHom O Y a * (O.obj.map f).hom x
    rw [map_mul, globalSectionEvalHom_naturality]

end Setup

section Presheaf

variable {O : Sheaf J CommRingCat.{r}}

/-- The restriction map of the presheaf `U ↦ O(U) ⊗_A M`, as a map of `A`-modules. -/
def tensorRestriction (M : ModuleCat.{w} (GlobalFunctionRing O)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M →ₗ[GlobalFunctionRing O]
      TensorProduct (GlobalFunctionRing O) (O.obj.obj Y) M :=
  TensorProduct.map (restrictionLinearMap f) LinearMap.id

/-- Restriction in `O(U) ⊗_A M` restricts the first factor and leaves the second. -/
@[simp] theorem tensorRestriction_tmul (M : ModuleCat.{w} (GlobalFunctionRing O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : O.obj.obj X) (m : M) :
    tensorRestriction M f (a ⊗ₜ[GlobalFunctionRing O] m) =
      ((O.obj.map f).hom a) ⊗ₜ[GlobalFunctionRing O] m := rfl

/-- A map out of `O(U) ⊗_A M` that is additive and satisfies a scalar identity on tensors satisfies
it everywhere. -/
private theorem tensor_map_smul_of_tmul {M : ModuleCat.{w} (GlobalFunctionRing O)} {X : Cᵒᵖ}
    {N S G : Type*} [AddCommMonoid N] [DistribSMul S N]
    [FunLike G (TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) N]
    [AddMonoidHomClass G (TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) N]
    (g : G) (b : O.obj.obj X) (b' : S)
    (h : ∀ (a : O.obj.obj X) (m : M),
      g (b • (a ⊗ₜ[GlobalFunctionRing O] m)) = b' • g (a ⊗ₜ[GlobalFunctionRing O] m))
    (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) : g (b • t) = b' • g t := by
  induction t using TensorProduct.inductionOn with
  | tmul a m => exact h a m
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Restriction in `O(U) ⊗_A M` is semilinear along the restriction map of `O`. -/
theorem tensorRestriction_smul (M : ModuleCat.{w} (GlobalFunctionRing O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : O.obj.obj X)
    (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) :
    tensorRestriction M f (b • t) = (O.obj.map f).hom b • tensorRestriction M f t := by
  refine tensor_map_smul_of_tmul (tensorRestriction M f) b ((O.obj.map f).hom b)
    (fun a m => ?_) t
  change tensorRestriction M f ((b * a) ⊗ₜ[GlobalFunctionRing O] m) = _
  rw [tensorRestriction_tmul, map_mul]
  rfl

/-- Restriction along an identity is the identity. -/
theorem tensorRestriction_id (M : ModuleCat.{w} (GlobalFunctionRing O)) (X : Cᵒᵖ) :
    tensorRestriction M (𝟙 X) = LinearMap.id := by
  apply TensorProduct.ext'
  intro a m
  change ((O.obj.map (𝟙 X)).hom a) ⊗ₜ[GlobalFunctionRing O] m = a ⊗ₜ[GlobalFunctionRing O] m
  rw [O.obj.map_id]; rfl

/-- Restriction along a composite is the composite of the restrictions. -/
theorem tensorRestriction_comp (M : ModuleCat.{w} (GlobalFunctionRing O))
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorRestriction M (f ≫ g) = (tensorRestriction M g).comp (tensorRestriction M f) := by
  apply TensorProduct.ext'
  intro a m
  change ((O.obj.map (f ≫ g)).hom a) ⊗ₜ[GlobalFunctionRing O] m =
    ((O.obj.map g).hom ((O.obj.map f).hom a)) ⊗ₜ[GlobalFunctionRing O] m
  rw [O.obj.map_comp]; rfl

/-- `O(U) ⊗_A M` is a module over the sections of `O` at `U` read in `RingCat`, which is the
spelling the sheaves-of-modules API uses.  The ring is the same as the one coming from
`CommRingCat`, but instance search does not unfold the forgetful functor. -/
instance moduleTensorRingSheafObj (M : ModuleCat.{w} (GlobalFunctionRing O)) (X : Cᵒᵖ) :
    Module ((ringSheafOfSite O).obj.obj X) (TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) :=
  inferInstanceAs (Module (O.obj.obj X) (TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M))

/-- The module `O(U) ⊗_A M` of sections of `M ⊗_A 𝒪` over an object, before
sheafification. -/
def sectionTensorPresheafObj (M : ModuleCat.{w} (GlobalFunctionRing O)) (X : Cᵒᵖ) :
    ModuleCat.{max r w} ((ringSheafOfSite O).obj.obj X) :=
  ModuleCat.of _ (TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M)

/-- The restriction map of the presheaf `U ↦ O(U) ⊗_A M`, as a semilinear map of modules. -/
def sectionTensorPresheafMap (M : ModuleCat.{w} (GlobalFunctionRing O)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    sectionTensorPresheafObj M X ⟶ (ModuleCat.restrictScalars
      ((ringSheafOfSite O).obj.map f).hom).obj (sectionTensorPresheafObj M Y) :=
  ModuleCat.ofHom (X := sectionTensorPresheafObj M X)
    (Y := (ModuleCat.restrictScalars ((ringSheafOfSite O).obj.map f).hom).obj
      (sectionTensorPresheafObj M Y))
    { toFun := tensorRestriction M f
      map_add' := map_add (tensorRestriction M f)
      map_smul' := tensorRestriction_smul M f }

/-- The presheaf of `O`-modules `U ↦ O(U) ⊗_A M` attached to a module `M` over the ring `A` of
global functions of `O`. -/
def sectionTensorPresheaf (M : ModuleCat.{w} (GlobalFunctionRing O)) :
    PresheafOfModules.{max r w} (ringSheafOfSite O).obj where
  obj X := sectionTensorPresheafObj M X
  map f := sectionTensorPresheafMap M f
  map_id X := by
    ext t
    simp only [ModuleCat.restrictScalarsId', NatIso.ofComponents_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply]
    exact LinearMap.congr_fun (tensorRestriction_id M X) t
  map_comp {X Y Z} f g := by
    ext t
    simp only [ModuleCat.restrictScalarsComp', NatIso.ofComponents_inv_app,
      ModuleCat.comp_apply]
    exact LinearMap.congr_fun (tensorRestriction_comp M f g) t

/-- The restriction map of the presheaf `U ↦ O(U) ⊗_A M`, computed on a tensor. -/
@[simp] theorem sectionTensorPresheaf_map_tmul (M : ModuleCat.{w} (GlobalFunctionRing O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : O.obj.obj X) (m : M) :
    (sectionTensorPresheaf M).map f (a ⊗ₜ[GlobalFunctionRing O] m) =
      ((O.obj.map f).hom a) ⊗ₜ[GlobalFunctionRing O] m := rfl

/-- Scalars from `A` may be moved across the tensor: `1 ⊗ a m` is `a` times `1 ⊗ m`, the
scalar acting through its value at the object. -/
theorem sectionTensorPresheaf_one_tmul_smul (M : ModuleCat.{w} (GlobalFunctionRing O))
    (X : Cᵒᵖ) (a : GlobalFunctionRing O) (m : M) :
    (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] (a • m)) : (sectionTensorPresheaf M).obj X)
      = a.val X •
        (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m) : (sectionTensorPresheaf M).obj X) := by
  rw [← TensorProduct.smul_tmul]
  rfl

/-- Tensors add in the second variable: `1 ⊗ (m₁ + m₂)` splits. -/
theorem sectionTensorPresheaf_one_tmul_add (M : ModuleCat.{w} (GlobalFunctionRing O))
    (X : Cᵒᵖ) (m₁ m₂ : M) :
    (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] (m₁ + m₂)) : (sectionTensorPresheaf M).obj X)
      = (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m₁) : (sectionTensorPresheaf M).obj X)
        + (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m₂) : (sectionTensorPresheaf M).obj X) :=
  TensorProduct.tmul_add _ _ _

/-- The map `O(U) ⊗_A M → O(U) ⊗_A N` induced by an `A`-linear map `M → N`. -/
def tensorCoefficient {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N) (X : Cᵒᵖ) :
    TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M →ₗ[GlobalFunctionRing O]
      TensorProduct (GlobalFunctionRing O) (O.obj.obj X) N :=
  TensorProduct.map LinearMap.id φ.hom

/-- A map of coefficients acts on the second factor of a tensor. -/
@[simp] theorem tensorCoefficient_tmul {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (a : O.obj.obj X) (m : M) :
    tensorCoefficient φ X (a ⊗ₜ[GlobalFunctionRing O] m) =
      a ⊗ₜ[GlobalFunctionRing O] (φ.hom m) := rfl

/-- A map of coefficients is linear over the sections of `O`. -/
theorem tensorCoefficient_smul {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (b : O.obj.obj X) (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) :
    tensorCoefficient φ X (b • t) = b • tensorCoefficient φ X t := by
  exact tensor_map_smul_of_tmul (tensorCoefficient φ X) b b (fun _ _ => rfl) t

/-- A map of coefficients commutes with restriction. -/
theorem tensorCoefficient_comp_tensorRestriction
    {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (tensorCoefficient φ Y).comp (tensorRestriction M f) =
      (tensorRestriction N f).comp (tensorCoefficient φ X) := by
  apply TensorProduct.ext'
  intro a m
  rfl

/-- The morphism of presheaves of `O`-modules induced by an `A`-linear map of coefficients. -/
def sectionTensorPresheafFunctorMap {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N) :
    sectionTensorPresheaf M ⟶ sectionTensorPresheaf N where
  app X := ModuleCat.ofHom (X := sectionTensorPresheafObj M X) (Y := sectionTensorPresheafObj N X)
    { toFun := tensorCoefficient φ X
      map_add' := map_add (tensorCoefficient φ X)
      map_smul' := tensorCoefficient_smul φ X }
  naturality {X Y} f := by
    ext t
    simp only [ModuleCat.comp_apply]
    exact LinearMap.congr_fun (tensorCoefficient_comp_tensorRestriction φ f) t

/-- The morphism of presheaves induced by a map of coefficients, on a tensor. -/
@[simp] theorem sectionTensorPresheafFunctorMap_app_tmul
    {M N : ModuleCat.{w} (GlobalFunctionRing O)} (φ : M ⟶ N) (X : Cᵒᵖ) (a : O.obj.obj X) (m : M) :
    ((sectionTensorPresheafFunctorMap φ).app X).hom (a ⊗ₜ[GlobalFunctionRing O] m) =
      a ⊗ₜ[GlobalFunctionRing O] (φ.hom m) := rfl

variable (O)

/-- The functor `M ↦ (U ↦ O(U) ⊗_A M)` from modules over the global functions of `O` to
presheaves of `O`-modules. -/
def sectionTensorPresheafFunctor :
    ModuleCat.{w} (GlobalFunctionRing O) ⥤ PresheafOfModules.{max r w} (ringSheafOfSite O).obj where
  obj M := sectionTensorPresheaf M
  map φ := sectionTensorPresheafFunctorMap φ
  map_id M := by
    ext X t
    have h : tensorCoefficient (𝟙 M) X = LinearMap.id :=
      TensorProduct.ext' fun _ _ => rfl
    exact LinearMap.congr_fun h t
  map_comp φ ψ := by
    ext X t
    have h : tensorCoefficient (φ ≫ ψ) X =
        (tensorCoefficient ψ X).comp (tensorCoefficient φ X) :=
      TensorProduct.ext' fun _ _ => rfl
    exact LinearMap.congr_fun h t

end Presheaf

section Sheaf

variable {O : Sheaf J CommRingCat.{r}}

/-- The presheaf of `O`-modules underlying a sheaf of `O`-modules, in the shape produced by
Mathlib's sheafification adjunction. -/
abbrev underlyingPresheaf (F : SheafOfModules.{max u r w} (ringSheafOfSite O)) :
    PresheafOfModules.{max u r w} (ringSheafOfSite O).obj :=
  (SheafOfModules.forget (ringSheafOfSite O) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringSheafOfSite O).obj)).obj F

/-- The `A`-linear map `M ⟶ Γ(C, F)` carried by a morphism of presheaves of `O`-modules from
`U ↦ O(U) ⊗_A M` to `F`: it sends `m` to the compatible family of sections `1 ⊗ m`. -/
def sectionsOfTensorPresheafHom {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (ψ : sectionTensorPresheaf M ⟶ underlyingPresheaf F) :
    M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F :=
  ModuleCat.ofHom (X := M) (Y := (globalSectionsFunctor (ringSheafOfSite O)).obj F)
    { toFun := fun m => F.val.sectionsMk
        (fun X => (ψ.app X).hom ((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m))
        (fun X Y f => by
          have h := PresheafOfModules.naturality_apply ψ f
            ((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m)
          have e : (sectionTensorPresheaf M).map f ((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m)
              = (1 : O.obj.obj Y) ⊗ₜ[GlobalFunctionRing O] m := by
            rw [sectionTensorPresheaf_map_tmul, map_one]
          exact h.symm.trans (congrArg (ψ.app Y).hom e))
      map_add' := fun m₁ m₂ => Subtype.ext <| funext fun X =>
        (congrArg (ψ.app X).hom (sectionTensorPresheaf_one_tmul_add M X m₁ m₂)).trans
          (map_add _ _ _)
      map_smul' := fun a m => Subtype.ext <| funext fun X =>
        (congrArg (ψ.app X).hom (sectionTensorPresheaf_one_tmul_smul M X a m)).trans
          (map_smul _ _ _) }

/-- The global section associated with a morphism out of `U ↦ O(U) ⊗_A M`, evaluated at an
object of the site. -/
@[simp] theorem sectionsOfTensorPresheafHom_eval {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (ψ : sectionTensorPresheaf M ⟶ underlyingPresheaf F) (m : M) (X : Cᵒᵖ) :
    ((sectionsOfTensorPresheafHom ψ).hom m).eval X =
      (ψ.app X).hom ((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m) := rfl

variable (O) [HasWeakSheafify J AddCommGrpCat.{max u r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]

/-- The functor `M ↦ M ⊗_A 𝒪` from modules over the global functions of `O` to sheaves of
`O`-modules: the sheafification of `U ↦ O(U) ⊗_A M`. -/
def sectionTensorSheafFunctor : ModuleCat.{max u r w} (GlobalFunctionRing O) ⥤
    SheafOfModules.{max u r w} (ringSheafOfSite O) :=
  sectionTensorPresheafFunctor.{u, v, r, max u r w} O ⋙
    PresheafOfModules.sheafification (𝟙 (ringSheafOfSite O).obj)

variable {O}

/-- The canonical `A`-linear map from `M` to the global sections of `M ⊗_A 𝒪`: it sends `m` to
the compatible family of sections obtained from `1 ⊗ m` by sheafification. -/
def sectionTensorSheafUnit (M : ModuleCat.{max u r w} (GlobalFunctionRing O)) :
    M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj ((sectionTensorSheafFunctor O).obj M) :=
  sectionsOfTensorPresheafHom
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheafOfSite O).obj)).unit.app (sectionTensorPresheaf M))

/-- The canonical map to the global sections of `M ⊗_A 𝒪`, evaluated at an object of the
site. -/
@[simp] theorem sectionTensorSheafUnit_eval
    (M : ModuleCat.{max u r w} (GlobalFunctionRing O)) (m : M) (X : Cᵒᵖ) :
    ((sectionTensorSheafUnit M).hom m).eval X =
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheafOfSite O).obj)).unit.app (sectionTensorPresheaf M)).app X).hom
        ((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m) := rfl

end Sheaf

section Adjunction

variable {O : Sheaf J CommRingCat.{r}}

/-- A section of `O` over an object of the site, read as a section of the underlying sheaf of
rings.  This is the spelling in which the sheaves-of-modules API expects scalars. -/
def ringSheafSection {X : Cᵒᵖ} (a : O.obj.obj X) : (ringSheafOfSite O).obj.obj X := a

/-- Reading a product of sections of `O` in `RingCat` multiplies the readings. -/
theorem ringSheafSection_mul {X : Cᵒᵖ} (a b : O.obj.obj X) :
    ringSheafSection (O := O) (a * b) = ringSheafSection a * ringSheafSection b := rfl

/-- Two additive maps out of `O(U) ⊗_A M` agree as soon as they agree on tensors. -/
theorem sectionTensorAddHom_ext {M : ModuleCat.{w} (GlobalFunctionRing O)} {X : Cᵒᵖ}
    {N : Type*} [AddCommMonoid N]
    {g h : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M →+ N}
    (hgh : ∀ (a : O.obj.obj X) (m : M),
      g (a ⊗ₜ[GlobalFunctionRing O] m) = h (a ⊗ₜ[GlobalFunctionRing O] m))
    (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) : g t = h t := by
  induction t using TensorProduct.inductionOn with
  | tmul a m => exact hgh a m
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The additive map `O(U) ⊗_A M → F(U)` attached to an `A`-linear map `θ : M ⟶ Γ(C, F)`: it
sends `a ⊗ m` to `a` times the value over `U` of the global section `θ m`.

It is built as an additive map rather than an `A`-linear one because no `A`-module structure is
declared on the sections of `F`; the scalars from `A` cross the tensor because the sections of
`O` over an object commute. -/
def sectionTensorLift {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) (X : Cᵒᵖ) :
    TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M →+ F.val.obj X :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun m => ringSheafSection a • (θ.hom m).eval X
          map_zero' := by rw [map_zero]; exact smul_zero (ringSheafSection a)
          map_add' := fun m₁ m₂ => by rw [map_add]; exact smul_add (ringSheafSection a) _ _ }
      map_zero' := by ext m; exact zero_smul _ _
      map_add' := fun a b => by ext m; exact add_smul (ringSheafSection a) (ringSheafSection b) _ }
    (fun c a m => by
      change ringSheafSection (c • a) • (θ.hom m).eval X =
        ringSheafSection a • (θ.hom (c • m)).eval X
      have hs : (θ.hom (c • m)).eval X = ringSheafSection (c.val X) • (θ.hom m).eval X := by
        rw [map_smul]; rfl
      have he : ringSheafSection (O := O) (c • a) =
          ringSheafSection a * ringSheafSection (c.val X) :=
        mul_comm (G := O.obj.obj X) (c.val X) a
      rw [hs, smul_smul, he])

/-- The map attached to `θ : M ⟶ Γ(C, F)` sends `a ⊗ m` to `a` times the value of `θ m`. -/
@[simp] theorem sectionTensorLift_tmul {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) (X : Cᵒᵖ) (a : O.obj.obj X)
    (m : M) :
    sectionTensorLift θ X (a ⊗ₜ[GlobalFunctionRing O] m) =
      ringSheafSection a • (θ.hom m).eval X := rfl

/-- The map attached to `θ : M ⟶ Γ(C, F)` is linear over the sections of `O`. -/
theorem sectionTensorLift_smul {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) (X : Cᵒᵖ) (b : O.obj.obj X)
    (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) :
    sectionTensorLift θ X (b • t) = ringSheafSection b • sectionTensorLift θ X t := by
  refine tensor_map_smul_of_tmul (sectionTensorLift θ X) b (ringSheafSection b)
    (fun a m => ?_) t
  change sectionTensorLift θ X ((b * a) ⊗ₜ[GlobalFunctionRing O] m) = _
  rw [sectionTensorLift_tmul, sectionTensorLift_tmul, smul_smul, ringSheafSection_mul]

/-- The map attached to `θ : M ⟶ Γ(C, F)` commutes with restriction, because the values of a
global section of `F` restrict to one another. -/
theorem sectionTensorLift_restriction {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (t : TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M) :
    sectionTensorLift θ Y (tensorRestriction M f t) =
      F.val.map f (sectionTensorLift θ X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
      rw [tensorRestriction_tmul, sectionTensorLift_tmul, sectionTensorLift_tmul,
        PresheafOfModules.map_smul F.val f (ringSheafSection a) ((θ.hom m).eval X),
        PresheafOfModules.sections_property (θ.hom m) f]
      rfl
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      exact (map_add _ _ _).symm

/-- The morphism of presheaves of `O`-modules `(U ↦ O(U) ⊗_A M) ⟶ F` attached to an `A`-linear
map `θ : M ⟶ Γ(C, F)`: over `U` it sends `a ⊗ m` to `a` times the value of `θ m` over `U`. -/
def sectionTensorPresheafHomOfSections {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) :
    sectionTensorPresheaf M ⟶ underlyingPresheaf F where
  app X := ModuleCat.ofHom (X := sectionTensorPresheafObj M X)
    (Y := (underlyingPresheaf F).obj X)
    { toFun := sectionTensorLift θ X
      map_add' := map_add (sectionTensorLift θ X)
      map_smul' := sectionTensorLift_smul θ X }
  naturality {X Y} f := by
    ext t
    simp only [ModuleCat.comp_apply]
    exact sectionTensorLift_restriction θ f t

/-- The morphism of presheaves attached to `θ : M ⟶ Γ(C, F)`, evaluated on a tensor. -/
@[simp] theorem sectionTensorPresheafHomOfSections_app_tmul
    {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (θ : M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) (X : Cᵒᵖ) (a : O.obj.obj X)
    (m : M) :
    ((sectionTensorPresheafHomOfSections θ).app X).hom (a ⊗ₜ[GlobalFunctionRing O] m) =
      ringSheafSection a • (θ.hom m).eval X := rfl

/-- A morphism of presheaves of `O`-modules out of `U ↦ O(U) ⊗_A M`, over a fixed object of the
site, as an additive map out of the bare tensor product. -/
def sectionTensorAppAddHom {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (ψ : sectionTensorPresheaf M ⟶ underlyingPresheaf F) (X : Cᵒᵖ) :
    TensorProduct (GlobalFunctionRing O) (O.obj.obj X) M →+ F.val.obj X where
  toFun t := (ψ.app X).hom t
  map_zero' := map_zero (ψ.app X).hom
  map_add' x y := map_add (ψ.app X).hom x y

/-- **Morphisms of presheaves of `O`-modules from `U ↦ O(U) ⊗_A M` to a sheaf of `O`-modules `F`
are the `A`-linear maps `M ⟶ Γ(C, F)`.**

Such a morphism is determined by the images of the sections `1 ⊗ m`, which form a compatible
family and hence a global section of `F`, and every `A`-linear map `M ⟶ Γ(C, F)` arises this
way. -/
def sectionTensorPresheafHomEquiv (M : ModuleCat.{max u r w} (GlobalFunctionRing O))
    (F : SheafOfModules.{max u r w} (ringSheafOfSite O)) :
    (sectionTensorPresheaf M ⟶ underlyingPresheaf F) ≃
      (M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) where
  toFun := sectionsOfTensorPresheafHom
  invFun := sectionTensorPresheafHomOfSections
  left_inv ψ := by
    refine PresheafOfModules.hom_ext (fun X => ModuleCat.hom_ext (LinearMap.ext (fun t => ?_)))
    refine sectionTensorAddHom_ext (g := sectionTensorLift (sectionsOfTensorPresheafHom ψ) X)
      (h := sectionTensorAppAddHom ψ X) (fun a m => ?_) t
    have he : ringSheafSection (O := O) a •
        (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m) : sectionTensorPresheafObj M X)
        = a ⊗ₜ[GlobalFunctionRing O] m := by
      change ((a * 1) ⊗ₜ[GlobalFunctionRing O] m : sectionTensorPresheafObj M X) = _
      rw [mul_one]
    refine Eq.trans ?_ (congrArg (fun s => (ψ.app X).hom s) he)
    exact ((ψ.app X).hom.map_smul (ringSheafSection a)
      (((1 : O.obj.obj X) ⊗ₜ[GlobalFunctionRing O] m) : sectionTensorPresheafObj M X)).symm
  right_inv θ := ModuleCat.hom_ext <| LinearMap.ext fun m => Subtype.ext <| funext fun X =>
    one_smul ((ringSheafOfSite O).obj.obj X) ((θ.hom m).eval X)

/-- Precomposition with a map of coefficients, on the presheaf-level correspondence. -/
theorem sectionTensorPresheafHomOfSections_comp_left
    {M N : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F : SheafOfModules.{max u r w} (ringSheafOfSite O)} (φ : M ⟶ N)
    (θ : N ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) :
    sectionTensorPresheafHomOfSections (φ ≫ θ) =
      sectionTensorPresheafFunctorMap φ ≫ sectionTensorPresheafHomOfSections θ := by
  refine PresheafOfModules.hom_ext (fun X => ModuleCat.hom_ext (LinearMap.ext (fun t => ?_)))
  exact sectionTensorAddHom_ext (g := sectionTensorLift (φ ≫ θ) X)
    (h := (sectionTensorLift θ X).comp (tensorCoefficient φ X).toAddMonoidHom)
    (fun a m => rfl) t

/-- Postcomposition with a morphism of sheaves of modules, on the presheaf-level
correspondence. -/
theorem sectionsOfTensorPresheafHom_comp_right
    {M : ModuleCat.{max u r w} (GlobalFunctionRing O)}
    {F G : SheafOfModules.{max u r w} (ringSheafOfSite O)}
    (ψ : sectionTensorPresheaf M ⟶ underlyingPresheaf F) (h : F ⟶ G) :
    sectionsOfTensorPresheafHom (ψ ≫ (SheafOfModules.forget (ringSheafOfSite O) ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringSheafOfSite O).obj)).map h) =
      sectionsOfTensorPresheafHom ψ ≫ (globalSectionsFunctor (ringSheafOfSite O)).map h :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ => Subtype.ext <| funext fun _ => rfl

variable (O) [HasWeakSheafify J AddCommGrpCat.{max u r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]

/-- **Morphisms of sheaves of `O`-modules `M ⊗_A 𝒪 ⟶ F` are the `A`-linear maps
`M ⟶ Γ(C, F)`.**

This is the universal property of `M ⊗_A 𝒪`: the presheaf-level correspondence
`Stacks.Cohomology.SiteModules.sectionTensorPresheafHomEquiv` composed with the sheafification
adjunction. -/
def sectionTensorHomEquiv (M : ModuleCat.{max u r w} (GlobalFunctionRing O))
    (F : SheafOfModules.{max u r w} (ringSheafOfSite O)) :
    ((sectionTensorSheafFunctor O).obj M ⟶ F) ≃
      (M ⟶ (globalSectionsFunctor (ringSheafOfSite O)).obj F) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheafOfSite O).obj)).homEquiv (sectionTensorPresheaf M) F).trans
    (sectionTensorPresheafHomEquiv M F)

/-- **The functor `M ↦ M ⊗_A 𝒪` is left adjoint to global sections.**

Consequently it preserves all colimits; in particular it is right exact, which is what a
presentation of `M` by free `A`-modules is used for. -/
@[stacks 07UZ "the module M ⊗_A 𝒪_X of the statement, as the left adjoint of global sections"]
def sectionTensorSheafAdjunction :
    sectionTensorSheafFunctor O ⊣ globalSectionsFunctor (ringSheafOfSite O) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sectionTensorHomEquiv O
      homEquiv_naturality_left_symm := fun φ θ => by
        refine Eq.trans ?_ ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheafOfSite O).obj)).homEquiv_naturality_left_symm
            (sectionTensorPresheafFunctorMap φ) (sectionTensorPresheafHomOfSections θ))
        exact congrArg (fun ψ => ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheafOfSite O).obj)).homEquiv _ _).symm ψ)
          (sectionTensorPresheafHomOfSections_comp_left φ θ)
      homEquiv_naturality_right := fun k h => by
        refine Eq.trans (congrArg (fun ψ => sectionsOfTensorPresheafHom ψ)
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheafOfSite O).obj)).homEquiv_naturality_right k h)) ?_
        exact sectionsOfTensorPresheafHom_comp_right _ h }

/-- The functor `M ↦ M ⊗_A 𝒪` is a left adjoint, hence preserves all colimits. -/
instance sectionTensorSheafFunctor_isLeftAdjoint :
    (sectionTensorSheafFunctor O).IsLeftAdjoint :=
  (sectionTensorSheafAdjunction O).isLeftAdjoint

/-- The unit of the adjunction is the canonical map `M ⟶ Γ(C, M ⊗_A 𝒪)`. -/
theorem sectionTensorSheafAdjunction_unit_app
    (M : ModuleCat.{max u r w} (GlobalFunctionRing O)) :
    (sectionTensorSheafAdjunction O).unit.app M = sectionTensorSheafUnit M := by
  change sectionsOfTensorPresheafHom ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheafOfSite O).obj)).homEquiv (sectionTensorPresheaf M) _ (𝟙 _)) = _
  refine congrArg _ ?_
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Adjunction

end Stacks.Cohomology.SiteModules

end
