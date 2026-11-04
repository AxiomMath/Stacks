module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.PresheafAlgebraMonObj
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.MonObjTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness

/-!
# The direct image of the structure sheaf along an affine morphism is a commutative algebra

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks.  The direct image
`g_*𝒪_𝒰 : x ↦ 𝒪_𝒰(r x)` is a sheaf of commutative `𝒪_𝒳`-algebras, hence a commutative monoid
object of the symmetric monoidal category `Mod(𝒪_𝒳)` (tensor product of Stacks 05NA, built by
localizing the objectwise tensor product of presheaves of modules).  This is the commutative
`𝒪_𝒳`-algebra structure of the proof of Stacks 0GRK (Remarks 0GQR and 0GQM of the source).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.modulesMonoidalCategory`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.modulesSymmetricCategory`: the symmetric monoidal
  structure on `Mod(𝒪_𝒴)` for an algebraic stack `𝒴`.
* `AlgebraicGeometry.Stack.affinePushforwardStructureSheaf`: `g_*𝒪_𝒰`.
* `AlgebraicGeometry.Stack.monObjAffinePushforwardStructureSheaf` and
  `AlgebraicGeometry.Stack.isCommMonObjAffinePushforwardStructureSheaf`: its structure of a
  commutative monoid object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

local notation "J[" Y "]" => AlgebraicStacks.fppfSiteTopology _ _ _ Y
local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

section Monoidal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure presheaf of rings of an algebraic stack is a sheaf for its fppf topology. -/
theorem AlgebraicStacks.isSheaf_structureRingPresheaf (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Presheaf.IsSheaf (AlgebraicStacks.fppfSiteTopology B S hS 𝒴)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (𝒪c[𝒴]).obj) :=
  FibredSite.structureRingPresheaf_isSheaf B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf

/-- **The monoidal structure `⊗_{𝒪_𝒴}` on `Mod(𝒪_𝒴)`** for an algebraic stack `𝒴` (Stacks 05NA). -/
@[instance_reducible]
noncomputable def AlgebraicStacks.modulesMonoidalCategory (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    MonoidalCategory (SheafOfModules.{u} 𝒪[𝒴]) :=
  FibredSite.monoidalCategory B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf

/-- **The symmetric monoidal structure on `Mod(𝒪_𝒴)`**: the braiding of `⊗_{𝒪_𝒴}`. -/
@[instance_reducible]
noncomputable def AlgebraicStacks.modulesSymmetricCategory (𝒴 : AlgebraicStacks.{u, w} B S hS) :
    letI := AlgebraicStacks.modulesMonoidalCategory B S hS 𝒴
    SymmetricCategory (SheafOfModules.{u} 𝒪[𝒴]) :=
  Stacks.SheafOfModules.symmetricCategory (𝒪c[𝒴]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒴)

end Monoidal

attribute [local instance] AlgebraicStacks.modulesMonoidalCategory
  AlgebraicStacks.modulesSymmetricCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)
  (hg : AlgebraicStacks.IsAffineHom B S hS g)

/-- **The direct image `g_*𝒪_𝒰` of the structure sheaf along an affine 1-morphism.** -/
noncomputable abbrev affinePushforwardStructureSheaf : SheafOfModules.{u} 𝒪[𝒳] :=
  (affinePushforward.{u, w, u} g hg).obj (SheafOfModules.unit 𝒪[𝒰])

/-- The underlying presheaf of modules of `g_*𝒪_𝒰` is the presheaf of commutative
`𝒪_𝒳`-algebras `x ↦ 𝒪_𝒰(r x)`. -/
theorem affinePushforwardStructureSheaf_val :
    (affinePushforwardStructureSheaf g hg).val =
      PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg) := rfl

/-- **`g_*𝒪_𝒰` is a monoid object of `Mod(𝒪_𝒳)`**: the sheafification of the presheaf of algebras
`x ↦ 𝒪_𝒰(r x)` is a monoid because sheafification is monoidal, and `g_*𝒪_𝒰`, being a sheaf, is its
own sheafification. -/
@[instance_reducible]
noncomputable def monObjAffinePushforwardStructureSheaf :
    MonObj (affinePushforwardStructureSheaf g hg) :=
  letI := Stacks.SheafOfModules.monoidalCategory (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  letI := Stacks.SheafOfModules.sheafifyMonoidal (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let M : MonObj ((Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).obj
        (affinePushforwardStructureSheaf g hg).val) :=
    Functor.monObjObj (F := Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
      (X := PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg))
  @MonObj.ofIso (SheafOfModules.{u} 𝒪[𝒳]) _ (AlgebraicStacks.modulesMonoidalCategory B S hS 𝒳) _ _ M
    (Stacks.SheafOfModules.sheafifyValIso (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
      (affinePushforwardStructureSheaf g hg))

/-- **`g_*𝒪_𝒰` is a commutative monoid object of `Mod(𝒪_𝒳)`**: sheafification is braided. -/
theorem isCommMonObjAffinePushforwardStructureSheaf :
    letI := monObjAffinePushforwardStructureSheaf g hg
    IsCommMonObj (affinePushforwardStructureSheaf g hg) := by
  let := Stacks.SheafOfModules.monoidalCategory (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let := Stacks.SheafOfModules.braidedCategory (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let := Stacks.SheafOfModules.sheafifyMonoidal (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let := Stacks.SheafOfModules.sheafifyBraided (𝒪c[𝒳]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
  let M : MonObj ((Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)).obj
        (affinePushforwardStructureSheaf g hg).val) :=
    Functor.monObjObj (F := Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
      (X := PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg))
  have hM : @IsCommMonObj _ _ _ _ _ M :=
    Functor.isCommMonObj_obj (F := Stacks.SheafOfModules.sheafifyFunctor (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳))
      (M := PresheafOfModules.algebraPresheaf (pushforwardCommRingHom g hg))
  -- commutativity is carried along `MonObj.ofIso` by naturality of the braiding
  have key : ∀ [MonoidalCategory (SheafOfModules.{u} 𝒪[𝒳])]
      [BraidedCategory (SheafOfModules.{u} 𝒪[𝒳])] {P Q : SheafOfModules.{u} 𝒪[𝒳]} [MonObj P]
      [IsCommMonObj P] (e : P ≅ Q), let := MonObj.ofIso e; IsCommMonObj Q := by
    intro _ _ P Q _ _ e
    let := MonObj.ofIso e
    constructor
    show (β_ Q Q).hom ≫ (e.inv ⊗ₘ e.inv) ≫ MonObj.mul ≫ e.hom =
      (e.inv ⊗ₘ e.inv) ≫ MonObj.mul ≫ e.hom
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
  exact @key (AlgebraicStacks.modulesMonoidalCategory B S hS 𝒳)
    (AlgebraicStacks.modulesSymmetricCategory B S hS 𝒳).toBraidedCategory _ _ M hM
    (Stacks.SheafOfModules.sheafifyValIso (𝒪c[𝒳]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS 𝒳)
      (affinePushforwardStructureSheaf g hg))

end AlgebraicGeometry.Stack
