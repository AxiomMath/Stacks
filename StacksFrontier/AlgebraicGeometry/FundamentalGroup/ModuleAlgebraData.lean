module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion

/-!
# Algebra structures on a sheaf of modules, as data

A commutative unital multiplication `E ⊗ E ⟶ E` with unit `𝒪_X ⟶ E` on a sheaf of
`𝒪_X`-modules makes `E` into a sheaf of `𝒪_X`-algebras. The base module
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion` uses this
packaging internally, as private declarations; the proof of Grothendieck existence for finite
sheaves of algebras ([Stacks, Tag 09ZT], via [Stacks, Tag 088E]) needs it in public. The
section-level part is done here in its natural generality — a presheaf of modules over an
arbitrary presheaf of commutative rings on an arbitrary category, `PresheafAlgebraData` — and only
the passage to a sheaf of `𝒪_X`-algebras is specific to schemes. The base file is left
untouched.

## Main definitions

* `Stacks.FundamentalGroup.PresheafAlgebraData`: unit and multiplication with the algebra laws on
  a presheaf of modules over a presheaf of commutative rings, with the resulting rings of sections
  (`PresheafAlgebraData.commRing`), algebra structures (`PresheafAlgebraData.algebra`), presheaf
  of rings (`PresheafAlgebraData.ringPresheaf`) and structure morphism
  (`PresheafAlgebraData.structureMap`).
* `Stacks.FundamentalGroup.ModuleAlgebraData`: the same data on a sheaf of `𝒪_X`-modules.
* `Stacks.FundamentalGroup.algebraSheafOfModule`: the resulting sheaf of algebras.
* `Stacks.FundamentalGroup.algebraSheafOfModuleIso`: its underlying module is the given one.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ Stacks.Algebraization.monoSubmoduleι
  Stacks.Algebraization.sectionsModuleΓPresheaf Stacks.Algebraization.epi_cokernelπ_submodule

namespace Stacks.FundamentalGroup

open MonoidalCategory
open scoped TensorProduct

/-- The monoidal structure on presheaves of modules over the structure sheaf of `X`. -/
local instance (X : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- The symmetric monoidal structure on presheaves of modules over the structure sheaf of `X`. -/
local instance (X : Scheme.{u}) :
    SymmetricCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

/-- **A commutative unital multiplication on a sheaf of `𝒪_X`-modules** `E`: a unit `𝒪_X ⟶ E`
and a multiplication `E ⊗ E ⟶ E`, commutative, associative and unital on sections. -/
public structure ModuleAlgebraData {X : Scheme.{u}} (E : X.Modules) where
  unit : SheafOfModules.unit X.ringCatSheaf ⟶ E
  mul : E.val ⊗ E.val ⟶ E.val
  mul_comm : ∀ U (x y : E.val.obj U),
      mul.app U (x ⊗ₜ[Γ(X, U.unop)] y) = mul.app U (y ⊗ₜ[Γ(X, U.unop)] x)
  mul_assoc : ∀ U (x y z : E.val.obj U),
      mul.app U (mul.app U (x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ[Γ(X, U.unop)] z) =
        mul.app U (x ⊗ₜ[Γ(X, U.unop)] mul.app U (y ⊗ₜ[Γ(X, U.unop)] z))
  one_mul : ∀ U (x : E.val.obj U), mul.app U
      (unit.val.app U (1 : Γ(X, U.unop)) ⊗ₜ[Γ(X, U.unop)] x) = x

/-! ### Algebra data on a presheaf of modules over a presheaf of commutative rings -/

section General

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **A commutative unital multiplication on a presheaf of modules** over a presheaf of
commutative rings `R`: a unit `R ⟶ M` and a multiplication `M ⊗ M ⟶ M`, commutative,
associative and unital on sections. -/
public structure PresheafAlgebraData (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  unit : PresheafOfModules.unit _ ⟶ M
  mul : M ⊗ M ⟶ M
  mul_comm : ∀ U (x y : M.obj U),
      mul.app U (x ⊗ₜ[R.obj U] y) = mul.app U (y ⊗ₜ[R.obj U] x)
  mul_assoc : ∀ U (x y z : M.obj U),
      mul.app U (mul.app U (x ⊗ₜ[R.obj U] y) ⊗ₜ[R.obj U] z) =
        mul.app U (x ⊗ₜ[R.obj U] mul.app U (y ⊗ₜ[R.obj U] z))
  one_mul : ∀ U (x : M.obj U), mul.app U (unit.app U (1 : R.obj U) ⊗ₜ[R.obj U] x) = x

namespace PresheafAlgebraData

variable {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (d : PresheafAlgebraData M)

/-- The commutative ring structure on the sections of `M` given by the multiplication. -/
@[instance_reducible] public def commRing (U : Cᵒᵖ) : CommRing (M.obj U) where
  __ := (inferInstance : AddCommGroup (M.obj U))
  one := d.unit.app U (1 : R.obj U)
  mul x y := d.mul.app U (x ⊗ₜ[R.obj U] y)
  mul_assoc := d.mul_assoc U
  mul_comm := d.mul_comm U
  one_mul := d.one_mul U
  mul_one x := (d.mul_comm U _ _).trans (d.one_mul U x)
  left_distrib x y z :=
    (congrArg (fun t => d.mul.app U t) (TensorProduct.tmul_add (R := R.obj U) x y z)).trans
      ((d.mul.app U).hom.map_add _ _)
  right_distrib x y z :=
    (congrArg (fun t => d.mul.app U t) (TensorProduct.add_tmul (R := R.obj U) x y z)).trans
      ((d.mul.app U).hom.map_add _ _)
  zero_mul x :=
    (congrArg (fun t => d.mul.app U t) (TensorProduct.zero_tmul _ _)).trans
      ((d.mul.app U).hom.map_zero)
  mul_zero x :=
    (congrArg (fun t => d.mul.app U t) (TensorProduct.tmul_zero _ _)).trans
      ((d.mul.app U).hom.map_zero)
  natCast n := n • d.unit.app U (1 : R.obj U)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • d.unit.app U (1 : R.obj U)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

/-- The sections of `M` form an `R(U)`-algebra. -/
@[instance_reducible] public def algebra (U : Cᵒᵖ) :
    letI := d.commRing U
    Algebra (R.obj U) (M.obj U) :=
  letI := d.commRing U
  Algebra.ofModule
    (fun r x y =>
      (congrArg (fun t => d.mul.app U t) (TensorProduct.smul_tmul' (R := R.obj U) r x y).symm).trans
        ((d.mul.app U).hom.map_smul r _))
    (fun r x y =>
      (congrArg (fun t => d.mul.app U t) (TensorProduct.tmul_smul (R := R.obj U) r x y)).trans
        ((d.mul.app U).hom.map_smul r _))

/-- The structure map of the algebra of sections is the unit. -/
public lemma algebraMap_eq (U : Cᵒᵖ) (r : R.obj U) :
    letI := d.commRing U
    letI := d.algebra U
    algebraMap (R.obj U) (M.obj U) r = d.unit.app U r :=
  ((d.unit.app U).hom.map_smul r (1 : R.obj U)).symm.trans
    (congrArg (fun t => d.unit.app U t) (mul_one r))

/-- The presheaf of commutative rings of sections of `M`. -/
public def ringPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} :=
  letI (U : Cᵒᵖ) := d.commRing U
  { obj U := CommRingCat.of (M.obj U)
    map f := CommRingCat.ofHom
      { __ := (M.map f).hom.toAddMonoidHom
        map_one' := (PresheafOfModules.naturality_apply d.unit f (1 : R.obj _)).symm.trans
          (congrArg (fun t => d.unit.app _ t) ((R.map f).hom.map_one))
        map_mul' x y := (PresheafOfModules.naturality_apply d.mul f (x ⊗ₜ[R.obj _] y)).symm }
    map_id U := by ext x; exact congrArg (fun f => f x) (M.map_id U)
    map_comp f g := by ext x; exact M.map_comp_apply f g x }

/-- The structure morphism `R ⟶ ringPresheaf d`, the algebra maps of the sections. -/
public def structureMap : R ⟶ d.ringPresheaf :=
  letI (U : Cᵒᵖ) := d.commRing U
  letI (U : Cᵒᵖ) := d.algebra U
  { app U := CommRingCat.ofHom (algebraMap (R.obj U) (M.obj U))
    naturality {U V} f := by
      ext r
      change algebraMap (R.obj V) (M.obj V) ((R.map f).hom r) =
        M.map f (algebraMap (R.obj U) (M.obj U) r)
      rw [algebraMap_eq]
      exact (PresheafOfModules.naturality_apply d.unit f r).trans
        (congrArg (fun t => M.map f t) (d.algebraMap_eq U r).symm) }

end PresheafAlgebraData

end General

/-! ### Sheaves of `𝒪_X`-algebras -/

/-- The data of a `ModuleAlgebraData` on the underlying presheaf of modules. -/
public def ModuleAlgebraData.toPresheafAlgebraData {X : Scheme.{u}} {E : X.Modules}
    (d : ModuleAlgebraData E) : PresheafAlgebraData (R := X.presheaf) E.val where
  unit := d.unit.val
  mul := d.mul
  mul_comm := d.mul_comm
  mul_assoc := d.mul_assoc
  one_mul := d.one_mul

/-- **The sheaf of `𝒪_X`-algebras of a `ModuleAlgebraData`**: the presheaf of rings of sections,
which is a sheaf because its underlying presheaf of abelian groups is, under `𝒪_X`. -/
public def algebraSheafOfModule {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) : Stacks.RelativeSpec.AlgebraSheaf X :=
  Under.mk (Y := ⟨d.toPresheafAlgebraData.ringPresheaf,
      (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X)
        d.toPresheafAlgebraData.ringPresheaf
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).mpr E.isSheaf⟩)
    ⟨d.toPresheafAlgebraData.structureMap⟩

/-- **The underlying module of `algebraSheafOfModule E d` is `E`**, by the identity on sections. -/
public def algebraSheafOfModuleIso {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) :
    (algebraSheafOfModule E d).underlyingModule ≅ E :=
  letI (U : X.Opensᵒᵖ) := d.toPresheafAlgebraData.commRing U
  letI (U : X.Opensᵒᵖ) := d.toPresheafAlgebraData.algebra U
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso (PresheafOfModules.isoMk
    (fun U => LinearEquiv.toModuleIso
      { toFun := id
        invFun := id
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' r x := by
          change Mul.mul (α := E.val.obj U) (algebraMap Γ(X, U.unop) (E.val.obj U) r)
            x = @SMul.smul Γ(X, U.unop) (E.val.obj U)
              (E.val.obj U).isModule.toDistribMulAction.toSMul r x
          exact @Algebra.smul_def Γ(X, U.unop) (E.val.obj U) _ _ _ r x |>.symm :
        ((algebraSheafOfModule E d).underlyingModule.val.obj U) ≃ₗ[Γ(X, U.unop)] E.val.obj U })
    (fun {_ _} f => by ext x; rfl))

end Stacks.FundamentalGroup

end
