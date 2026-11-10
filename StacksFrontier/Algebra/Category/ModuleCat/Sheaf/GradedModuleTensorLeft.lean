module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Quasicoherent

/-!
# Tensoring a graded module by a fixed sheaf of modules on the left

Let `(C, J)` be a site, let `𝒪` be a presheaf of commutative rings on it whose underlying
presheaf of rings is a sheaf, and let `R` be that sheaf of rings. Let `A` be a sheaf of
`ℤ`-graded `R`-algebras ([Stacks, Tag 0FQW]), let `M` be a right graded `A`-module
([Stacks, Tag 0FQZ]) and let `F` be a fixed, ungraded sheaf of `R`-modules. The family
`n ↦ F ⊗ Mⁿ` of tensor product sheaves ([Stacks, Tag 05NA]) is then again a right graded
`A`-module, a homogeneous local section `a` of `A` acting by `(x ⊗ m) · a = x ⊗ (m · a)`.

This file builds that graded module and its universal property.

## Main definitions

* `SheafOfModules.GradedModule.preTensorLeft` is `F ⊗ M` before sheafifying: its degree-`n`
  piece is the objectwise tensor product of the underlying presheaves of modules, on whose
  sections the action can be written down.
* `SheafOfModules.GradedModule.tensorLeft` is **the right graded `A`-module `F ⊗ M`**, the
  degreewise sheafification of `preTensorLeft`.
* `SheafOfModules.GradedModule.tensorLeftUnit` is the canonical map from the objectwise tensor
  product to the degree-`n` piece of `F ⊗ M`, and
  `SheafOfModules.GradedModule.tensorLeftMk` is that map read on sections over one object.
* `SheafOfModules.GradedModule.tensorLeftDesc` is the homomorphism of graded `A`-modules out of
  `F ⊗ M` attached to a degreewise family of bilinear maps compatible with the two actions, and
  `SheafOfModules.GradedModule.tensorLeftDescApp` is its degree-`n` component.

## Main results

* `SheafOfModules.GradedModule.tensorLeft_piece`: the degree-`n` piece of `F ⊗ M` **is** the
  tensor product sheaf `F ⊗ Mⁿ`, on the nose rather than up to isomorphism.
* `SheafOfModules.GradedModule.tensorLeft_smul_tmul` computes the action on the image of a pure
  tensor: `(x ⊗ m) · a = x ⊗ (m · a)`.
* `SheafOfModules.GradedModule.tensorLeftDesc_app_tmul` computes the descended homomorphism on
  the image of a pure tensor; together with
  `SheafOfModules.GradedModule.tensorLeft_hom_ext`, which says that those images determine a
  morphism out of a homogeneous piece, this is the universal property of `F ⊗ M`.
* `SheafOfModules.GradedModule.isQuasicoherent_tensorLeft_piece`: the pieces of `F ⊗ M` are
  quasi-coherent as soon as `F` and all the pieces of `M` are. This is Stacks 0GQM applied
  degreewise, and it is available precisely because the pieces are the tensor product sheaves
  themselves.

## Implementation notes

**Why a presheaf-level graded module first.** The degree-`n` piece of `F ⊗ M` is a
sheafification, so its sections have no description and the action cannot be defined on them
directly. It is defined instead on the objectwise tensor product, where every section is a sum
of pure tensors, and transported along the degreewise sheafification maps by
`SheafOfModules.PreGradedModule.sheafify`. This is the device the degreewise direct sum and the
degreewise cokernel of graded modules already use.

**Why the pieces agree on the nose.** `SheafOfModules.PreGradedModule.sheafifyPiece` applies
`PresheafOfModules.sheafification (𝟙 R.obj)` to the piece, and
`Stacks.SheafOfModules.Tensor.sheafTensor` applies the very same functor to the
very same presheaf, so `tensorLeft_piece` holds by `rfl`. Consequently every statement about
the tensor product sheaves `F ⊗ Mⁿ` — cohomological, or about quasi-coherence — is literally a
statement about the homogeneous pieces of `F ⊗ M`, and no transport intervenes.

**The sheaf of rings is written as an anonymous constructor.** The base is
`⟨Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪, h𝒪⟩`, which is
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪` with its one definitional step
taken; `SheafOfModules.GradedModule.mk_eq_structureSheaf` records that the two are equal. The
step is load-bearing rather than cosmetic. Written as `structureSheaf 𝒪 h𝒪`, the presheaf of
rings underlying the base is a projection of a constant that does not unfold at reducible
transparency, so the sections of `F` carry a module structure over a ring that instance search
cannot identify with the one the objectwise tensor product is formed over: a pure tensor of
local sections then fails to elaborate at all, and every `rw` reports the goal as not
type-correct. Unfolding the constant makes the projection reduce by `iota`, after which both
spellings of the ring agree reducibly and the whole development is stated in the obvious way.

For the same reason the action is stated through
`SheafOfModules.GradedModule.tensorLeftSection`, `tensorLeftRestr` and `tensorLeftMk`, whose
types mention the tensor product of the modules of sections rather than the sections of the
tensor product presheaf: the two are equal, but only the first form survives the transparency
at which `rw` builds its motive. The conversion to the second form happens once, where
`preTensorLeft` is assembled.

**The dependent laws.** Associativity and unitality of the action are recorded by
`SheafOfModules.PreGradedModule` with the transport `Stacks.degCast`, the degrees `(n + i) + j`
and `n + (i + j)` being only propositionally equal. The three lemmas
`SheafOfModules.GradedModule.degCast_tensorLeft_zero`,
`SheafOfModules.GradedModule.degCast_tensorLeft_add` and
`SheafOfModules.GradedModule.degCast_tensorLeft_tmul` move that transport past the additive
structure of the tensor product and past a pure tensor, which reduces each law to the
corresponding law of `M` on the second factor.

**The algebra as a module over itself** is not constructed here: it already exists, as
`SheafOfModules.GradedModule.regularModule`, so `F ⊗ A` is an instance of `tensorLeft`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
-/

@[expose] public section

open CategoryTheory Stacks.SheafOfModules.TensorSheafification

open scoped TensorProduct

universe w v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  {A : GradedAlgebra.{w, w} (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w})}
  (F : SheafOfModules.{w} (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w}))
  (M : GradedModule.{w, w, w} A)

/-- The sheaf of rings this file works over **is** the structure sheaf of `𝒪`: the anonymous
constructor `⟨structureRingPresheaf 𝒪, h𝒪⟩` is
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`. -/
theorem mk_eq_structureSheaf :
    (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w}) = structureSheaf 𝒪 h𝒪 := rfl

/-- The sections over `U` of the objectwise tensor product of `F` with the degree-`n` piece of
`M`, written as a tensor product of modules rather than as the sections of
`PresheafOfModules.tensorObj`. -/
abbrev tensorLeftSection (n : ℤ) (U : Cᵒᵖ) : Type w :=
  F.val.obj U ⊗[(structureRingPresheaf 𝒪).obj U] (M.piece n).val.obj U

/-- The sections of the objectwise tensor product are the tensor product of the sections. -/
theorem tensorLeftSection_eq (n : ℤ) (U : Cᵒᵖ) :
    tensorLeftSection 𝒪 h𝒪 F M n U =
      (PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val).obj U := rfl

/-- The restriction map of the objectwise tensor product `F ⊗ Mⁿ`, as an additive map between
the types of sections. -/
noncomputable def tensorLeftRestr (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    tensorLeftSection 𝒪 h𝒪 F M n U →+ tensorLeftSection 𝒪 h𝒪 F M n V :=
  AddMonoidHom.mk' (fun t => (PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val).map f t)
    (fun t t' => map_add _ t t')

/-- The restriction of a pure tensor `x ⊗ m` is the pure tensor of the restrictions. -/
@[simp]
theorem tensorLeftRestr_tmul (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) :
    tensorLeftRestr 𝒪 h𝒪 F M n f (x ⊗ₜ m)
      = Stacks.restr F.val f x ⊗ₜ Stacks.restr (M.piece n).val f m :=
  PresheafOfModules.tensorObj_restrictₛₗ_tmul f x m

/-- The right action of `A` on a pure tensor `x ⊗ m` of local sections, as an additive map in
the algebra variable: a homogeneous section `a` goes to `x ⊗ (m · a)`. -/
noncomputable def tensorLeftTmulHom (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) :
    (A.piece i).val.obj U →+ tensorLeftSection 𝒪 h𝒪 F M (n + i) U :=
  AddMonoidHom.mk' (fun y => x ⊗ₜ M.smul n i U m y)
    (fun y y' => by rw [map_add]; exact TensorProduct.tmul_add x _ _)

/-- `SheafOfModules.GradedModule.tensorLeftTmulHom` sends `a` to `x ⊗ (m · a)`. -/
@[simp]
theorem tensorLeftTmulHom_apply (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    tensorLeftTmulHom 𝒪 h𝒪 F M n i U x m y = x ⊗ₜ M.smul n i U m y := rfl

/-- The right action of `A` on the objectwise tensor product `F ⊗ Mⁿ` over one object of the
site, as a morphism of modules into the additive maps out of `Aⁱ`. -/
noncomputable def tensorLeftSmulLin (n i : ℤ) (U : Cᵒᵖ) :
    ModuleCat.of ((structureRingPresheaf 𝒪).obj U) (tensorLeftSection 𝒪 h𝒪 F M n U) ⟶
      ModuleCat.of ((structureRingPresheaf 𝒪).obj U)
        ((A.piece i).val.obj U →+ tensorLeftSection 𝒪 h𝒪 F M (n + i) U) :=
  ModuleCat.tensorLift (fun x m => tensorLeftTmulHom 𝒪 h𝒪 F M n i U x m)
    (fun x x' m => by
      ext y
      simp only [tensorLeftTmulHom_apply, AddMonoidHom.add_apply]
      exact TensorProduct.add_tmul x x' _)
    (fun r x m => by
      ext y
      simp only [tensorLeftTmulHom_apply, AddMonoidHom.smul_apply]
      exact TensorProduct.smul_tmul' r x _)
    (fun x m m' => by
      ext y
      simp only [tensorLeftTmulHom_apply, AddMonoidHom.add_apply]
      rw [map_add, AddMonoidHom.add_apply]
      exact TensorProduct.tmul_add x _ _)
    (fun r x m => by
      ext y
      simp only [tensorLeftTmulHom_apply, AddMonoidHom.smul_apply]
      rw [M.smul_smul_left]
      exact TensorProduct.tmul_smul r x _)

/-- The right action of `A` on the sections of `F ⊗ Mⁿ` over one object of the site, as a
biadditive map. This is `SheafOfModules.GradedModule.tensorLeftSmulLin` with its module
structures forgotten, which is the shape `Stacks.BilinearMap` records. -/
noncomputable def tensorLeftSmulApp (n i : ℤ) (U : Cᵒᵖ) :
    tensorLeftSection 𝒪 h𝒪 F M n U →+
      ((A.piece i).val.obj U →+ tensorLeftSection 𝒪 h𝒪 F M (n + i) U) :=
  (ModuleCat.Hom.hom (tensorLeftSmulLin 𝒪 h𝒪 F M n i U)).toAddMonoidHom

/-- The action of `A` on a pure tensor: `(x ⊗ m) · a = x ⊗ (m · a)`. -/
theorem tensorLeftSmulLin_tmul (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    tensorLeftSmulLin 𝒪 h𝒪 F M n i U (x ⊗ₜ m) y = x ⊗ₜ M.smul n i U m y :=
  DFunLike.congr_fun (ModuleCat.tensorLift_tmul _ _ _ _ _ _ _) y

/-- The action of `A` on a pure tensor, as a biadditive map: `(x ⊗ m) · a = x ⊗ (m · a)`. -/
@[simp]
theorem tensorLeftSmulApp_tmul (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    tensorLeftSmulApp 𝒪 h𝒪 F M n i U (x ⊗ₜ m) y = x ⊗ₜ M.smul n i U m y :=
  tensorLeftSmulLin_tmul 𝒪 h𝒪 F M n i U x m y

/-- The action is linear over the sheaf of rings in the module variable. -/
theorem tensorLeftSmulApp_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : (structureRingPresheaf 𝒪).obj U)
    (x : tensorLeftSection 𝒪 h𝒪 F M n U) (y : (A.piece i).val.obj U) :
    tensorLeftSmulApp 𝒪 h𝒪 F M n i U (r • x) y
      = r • tensorLeftSmulApp 𝒪 h𝒪 F M n i U x y :=
  DFunLike.congr_fun (map_smul (ModuleCat.Hom.hom (tensorLeftSmulLin 𝒪 h𝒪 F M n i U)) r x) y

/-- The action is linear over the sheaf of rings in the algebra variable. -/
theorem tensorLeftSmulApp_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : (structureRingPresheaf 𝒪).obj U)
    (x : tensorLeftSection 𝒪 h𝒪 F M n U) (y : (A.piece i).val.obj U) :
    tensorLeftSmulApp 𝒪 h𝒪 F M n i U x (r • y)
      = r • tensorLeftSmulApp 𝒪 h𝒪 F M n i U x y := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [tensorLeftSmulApp_tmul, tensorLeftSmulApp_tmul, M.smul_smul_right]
    exact TensorProduct.tmul_smul r s _
  | add x x' hx hx' =>
    rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, hx, hx', smul_add]

/-- The action commutes with restriction. -/
theorem tensorLeftSmulApp_naturality (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : tensorLeftSection 𝒪 h𝒪 F M n U) (y : (A.piece i).val.obj U) :
    tensorLeftRestr 𝒪 h𝒪 F M (n + i) f (tensorLeftSmulApp 𝒪 h𝒪 F M n i U x y)
      = tensorLeftSmulApp 𝒪 h𝒪 F M n i V (tensorLeftRestr 𝒪 h𝒪 F M n f x)
          (Stacks.restr (A.piece i).val f y) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    simp only [tensorLeftSmulApp_tmul, tensorLeftRestr_tmul]
    rw [smul_restr M n i f m y]
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The action of `A` on `F ⊗ M` before sheafifying**, as a bilinear map of presheaves of
modules: a homogeneous local section `a` of `A` sends `x ⊗ m` to `x ⊗ (m · a)`. -/
noncomputable def tensorLeftSmulBil (n i : ℤ) :
    Stacks.BilinearMap (PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val) (A.piece i).val
      (PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece (n + i)).val) where
  app U := tensorLeftSmulApp 𝒪 h𝒪 F M n i U
  map_smul_left U r x y := tensorLeftSmulApp_smul_left 𝒪 h𝒪 F M n i U r x y
  map_smul_right U r x y := tensorLeftSmulApp_smul_right 𝒪 h𝒪 F M n i U r x y
  naturality f x y := tensorLeftSmulApp_naturality 𝒪 h𝒪 F M n i f x y

/-- Transport along an equality of degrees preserves zero, for the objectwise tensor products
`F ⊗ Mⁿ`. -/
theorem degCast_tensorLeft_zero (U : Cᵒᵖ) {n n' : ℤ} (h : n = n') :
    Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) h
        (0 : tensorLeftSection 𝒪 h𝒪 F M n U) = 0 := by
  subst h; rfl

/-- Transport along an equality of degrees is additive, for the objectwise tensor products
`F ⊗ Mⁿ`. -/
theorem degCast_tensorLeft_add (U : Cᵒᵖ) {n n' : ℤ} (h : n = n')
    (x x' : tensorLeftSection 𝒪 h𝒪 F M n U) :
    Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) h (x + x')
      = Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) h x
        + Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) h x' := by
  subst h; rfl

/-- Transport along an equality of degrees leaves the first factor of a pure tensor alone and
acts on the second. It is stated with a heterogeneous equality of second factors, which is the
shape in which the laws of a graded module arrive. -/
theorem degCast_tensorLeft_tmul (U : Cᵒᵖ) {n n' : ℤ} (h : n = n') (x : F.val.obj U)
    {m : (M.piece n).val.obj U} {m' : (M.piece n').val.obj U} (hm : HEq m m') :
    Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) h (x ⊗ₜ m) = x ⊗ₜ m' := by
  subst h
  rw [Stacks.degCast_rfl, eq_of_heq hm]

/-- The action on `F ⊗ M` is associative: on a pure tensor it is the associativity of the
action on `M`, carried through the second factor. -/
theorem tensorLeftSmulApp_assoc (n i j : ℤ) (U : Cᵒᵖ)
    (x : tensorLeftSection 𝒪 h𝒪 F M n U) (y : (A.piece i).val.obj U)
    (z : (A.piece j).val.obj U) :
    Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) (add_assoc n i j)
        (tensorLeftSmulApp 𝒪 h𝒪 F M (n + i) j U (tensorLeftSmulApp 𝒪 h𝒪 F M n i U x y) z)
      = tensorLeftSmulApp 𝒪 h𝒪 F M n (i + j) U x ((A.mul i j).app U y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [tensorLeftSmulApp_tmul, tensorLeftSmulApp_tmul, tensorLeftSmulApp_tmul]
    exact degCast_tensorLeft_tmul 𝒪 h𝒪 F M U (add_assoc n i j) s (M.smul_mul n i j U m y z)
  | add x x' hx hx' => simp [degCast_tensorLeft_add, hx, hx']

/-- The degree-zero unit of `A` acts as the identity on `F ⊗ M`: on a pure tensor it is the
unit law of `M`, carried through the second factor. -/
theorem tensorLeftSmulApp_one (n : ℤ) (U : Cᵒᵖ) (x : tensorLeftSection 𝒪 h𝒪 F M n U) :
    Stacks.degCast (F := fun k => tensorLeftSection 𝒪 h𝒪 F M k U) (add_zero n)
        (tensorLeftSmulApp 𝒪 h𝒪 F M n 0 U x (A.one.eval U)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [tensorLeftSmulApp_tmul]
    exact degCast_tensorLeft_tmul 𝒪 h𝒪 F M U (add_zero n) s (M.smul_one n U m)
  | add x x' hx hx' => simp [degCast_tensorLeft_add, hx, hx']

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sheafification map of a presheaf-level graded module is locally surjective. The
instance of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian` is stated for an
arbitrary sheaf of rings and is not found for the sheaf of rings built from `𝒪`; the same
restatement is made in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction`. -/
instance isLocallySurjective_toSheafifyPiece (P : PreGradedModule.{w, w, w} A) (n : ℤ) :
    PresheafOfModules.IsLocallySurjective J (P.toSheafifyPiece n) := by
  have h : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf
      (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w}).obj).map
        (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallySurjective
  exact h

/-- The sheafification map of a presheaf-level graded module is locally injective, restated for
the sheaf of rings built from `𝒪` for the same reason. -/
instance isLocallyInjective_toSheafifyPiece (P : PreGradedModule.{w, w, w} A) (n : ℤ) :
    PresheafOfModules.IsLocallyInjective J (P.toSheafifyPiece n) := by
  have h : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf
      (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w}).obj).map
        (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallyInjective
  exact h

/-- **`F ⊗ M` before sheafifying.** Its degree-`n` piece is the objectwise tensor product of the
underlying presheaf of modules of `F` with that of the degree-`n` piece of `M`, and a
homogeneous local section `a` of `A` sends `x ⊗ m` to `x ⊗ (m · a)`. -/
noncomputable def preTensorLeft : PreGradedModule.{w, w, w} A where
  piece n := PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val
  smulBil n i := tensorLeftSmulBil 𝒪 h𝒪 F M n i
  smulBil_assoc := tensorLeftSmulApp_assoc 𝒪 h𝒪 F M
  smulBil_one := tensorLeftSmulApp_one 𝒪 h𝒪 F M

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The degree-`n` piece of `SheafOfModules.GradedModule.preTensorLeft` is the objectwise
tensor product of `F` with `Mⁿ`. -/
@[simp]
theorem preTensorLeft_piece (n : ℤ) :
    (preTensorLeft 𝒪 h𝒪 F M).piece n =
      PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val := rfl

/-- **The right graded `A`-module `F ⊗ M`**, for a fixed sheaf of modules `F`: the degreewise
sheafification of `SheafOfModules.GradedModule.preTensorLeft`. -/
noncomputable def tensorLeft : GradedModule.{w, w, w} A := (preTensorLeft 𝒪 h𝒪 F M).sheafify

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The degree-`n` piece of `F ⊗ M` is the tensor product sheaf `F ⊗ Mⁿ`**, on the nose: both
are the sheafification of the objectwise tensor product of `F` with `Mⁿ`. -/
@[simp]
theorem tensorLeft_piece (n : ℤ) :
    (tensorLeft 𝒪 h𝒪 F M).piece n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj
          F).obj (M.piece n) := rfl

/-- The canonical map from the objectwise tensor product `F ⊗ Mⁿ` of presheaves of modules to
the degree-`n` piece of `F ⊗ M`, exhibiting the latter as its sheafification. -/
noncomputable def tensorLeftUnit (n : ℤ) :
    PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val ⟶
      ((tensorLeft 𝒪 h𝒪 F M).piece n).val :=
  (preTensorLeft 𝒪 h𝒪 F M).toSheafifyPiece n

/-- The image of a section of the objectwise tensor product in the degree-`n` piece of
`F ⊗ M`: `SheafOfModules.GradedModule.tensorLeftUnit` read on sections over one object. -/
noncomputable def tensorLeftMk (n : ℤ) (U : Cᵒᵖ) :
    tensorLeftSection 𝒪 h𝒪 F M n U →+ ((tensorLeft 𝒪 h𝒪 F M).piece n).val.obj U :=
  AddMonoidHom.mk' (fun t => (tensorLeftUnit 𝒪 h𝒪 F M n).app U t) (fun t t' => map_add _ t t')

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The action of `A` on `F ⊗ M`, on the image of a pure tensor**:
`(x ⊗ m) · a = x ⊗ (m · a)`. This is `SheafOfModules.PreGradedModule.sheafify_smul` with the
action of `preTensorLeft` computed. -/
theorem tensorLeft_smul_tmul (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    (tensorLeft 𝒪 h𝒪 F M).smul n i U (tensorLeftMk 𝒪 h𝒪 F M n U (x ⊗ₜ m)) y
      = tensorLeftMk 𝒪 h𝒪 F M (n + i) U (x ⊗ₜ M.smul n i U m y) :=
  ((preTensorLeft 𝒪 h𝒪 F M).sheafify_smul n i U (x ⊗ₜ m) y).trans
    (congrArg (fun t : tensorLeftSection 𝒪 h𝒪 F M (n + i) U =>
        tensorLeftMk 𝒪 h𝒪 F M (n + i) U t)
      (tensorLeftSmulApp_tmul 𝒪 h𝒪 F M n i U x m y))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two morphisms of sheaves of modules out of the degree-`n` piece of `F ⊗ M` which agree on
the images of pure tensors of local sections are equal. -/
theorem tensorLeft_hom_ext (n : ℤ)
    {T : SheafOfModules.{w} (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w})}
    {φ ψ : (tensorLeft 𝒪 h𝒪 F M).piece n ⟶ T}
    (h : ∀ (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U),
      φ.val.app U (tensorLeftMk 𝒪 h𝒪 F M n U (x ⊗ₜ m))
        = ψ.val.app U (tensorLeftMk 𝒪 h𝒪 F M n U (x ⊗ₜ m))) :
    φ = ψ :=
  (preTensorLeft 𝒪 h𝒪 F M).hom_ext_of_comp (preTensorLeft 𝒪 h𝒪 F M).sheafifyPiece
    (preTensorLeft 𝒪 h𝒪 F M).toSheafifyPiece n T (PresheafOfModules.tensorObj_hom_ext h)

variable (N : GradedModule.{w, w, w} A)
  (θ : ∀ n, Stacks.BilinearMap F.val (M.piece n).val (N.piece n).val)

/-- The degree-`n` component of the homomorphism out of `F ⊗ M` attached to a degreewise family
of bilinear maps: the extension of `θ n` along the sheafification unit. -/
noncomputable def tensorLeftDescApp (n : ℤ) : (tensorLeft 𝒪 h𝒪 F M).piece n ⟶ N.piece n :=
  ((preTensorLeft 𝒪 h𝒪 F M).transferHomEquiv (preTensorLeft 𝒪 h𝒪 F M).sheafifyPiece
      (preTensorLeft 𝒪 h𝒪 F M).toSheafifyPiece n (N.piece n)).symm
    (PresheafOfModules.ofBilinear (θ n))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The degree-`n` component `SheafOfModules.GradedModule.tensorLeftDescApp` sends the image of
the pure tensor `x ⊗ m` to `θ n (x, m)`. -/
@[simp]
theorem tensorLeftDescApp_tmul (n : ℤ) (U : Cᵒᵖ) (x : F.val.obj U)
    (m : (M.piece n).val.obj U) :
    (tensorLeftDescApp 𝒪 h𝒪 F M N θ n).val.app U (tensorLeftMk 𝒪 h𝒪 F M n U (x ⊗ₜ m))
      = (θ n).app U x m :=
  (congrArg (fun φ : PresheafOfModules.tensorObj (O := 𝒪) F.val (M.piece n).val ⟶ (N.piece n).val =>
      PresheafOfModules.Hom.app φ U (x ⊗ₜ m))
    ((preTensorLeft 𝒪 h𝒪 F M).transferHomEquiv_symm_apply
      (preTensorLeft 𝒪 h𝒪 F M).sheafifyPiece (preTensorLeft 𝒪 h𝒪 F M).toSheafifyPiece n
      (N.piece n) (PresheafOfModules.ofBilinear (θ n)))).trans
    (PresheafOfModules.ofBilinear_tmul (θ n) U x m)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The compatibility with the two actions that
`SheafOfModules.PreGradedModule.hom_map_smul` asks for, checked on the objectwise tensor
product: on a pure tensor it is the hypothesis `hθ`. -/
theorem tensorLeftDescApp_map_smul
    (hθ : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U)
      (y : (A.piece i).val.obj U),
      (θ (n + i)).app U x (M.smul n i U m y) = N.smul n i U ((θ n).app U x m) y)
    (n i : ℤ) (U : Cᵒᵖ)
    (t : tensorLeftSection 𝒪 h𝒪 F M n U) (y : (A.piece i).val.obj U) :
    (tensorLeftDescApp 𝒪 h𝒪 F M N θ (n + i)).val.app U
        (tensorLeftMk 𝒪 h𝒪 F M (n + i) U (tensorLeftSmulApp 𝒪 h𝒪 F M n i U t y))
      = N.smul n i U
          ((tensorLeftDescApp 𝒪 h𝒪 F M N θ n).val.app U (tensorLeftMk 𝒪 h𝒪 F M n U t)) y := by
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    rw [tensorLeftSmulApp_tmul, tensorLeftDescApp_tmul, tensorLeftDescApp_tmul]
    exact hθ n i U s m y
  | add t t' ht ht' => simp only [map_add, AddMonoidHom.add_apply, ht, ht']

/-- **The universal property of `F ⊗ M`.** A degreewise family of bilinear maps
`θ n : F × Mⁿ → Nⁿ` into a right graded `A`-module `N`, compatible with the two actions in the
sense that `θ (x, m · a) = θ (x, m) · a`, descends to a homomorphism of graded `A`-modules
`F ⊗ M ⟶ N`. -/
noncomputable def tensorLeftDesc
    (hθ : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U)
      (y : (A.piece i).val.obj U),
      (θ (n + i)).app U x (M.smul n i U m y) = N.smul n i U ((θ n).app U x m) y) :
    tensorLeft 𝒪 h𝒪 F M ⟶ N where
  app n := tensorLeftDescApp 𝒪 h𝒪 F M N θ n
  map_smul n i U x y :=
    (preTensorLeft 𝒪 h𝒪 F M).hom_map_smul (preTensorLeft 𝒪 h𝒪 F M).sheafifyPiece
      (preTensorLeft 𝒪 h𝒪 F M).toSheafifyPiece N (tensorLeftDescApp 𝒪 h𝒪 F M N θ)
      (tensorLeftDescApp_map_smul 𝒪 h𝒪 F M N θ hθ) n i U x y

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The degree-`n` component of `SheafOfModules.GradedModule.tensorLeftDesc` is
`SheafOfModules.GradedModule.tensorLeftDescApp`. -/
@[simp]
theorem tensorLeftDesc_app
    (hθ : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U)
      (y : (A.piece i).val.obj U),
      (θ (n + i)).app U x (M.smul n i U m y) = N.smul n i U ((θ n).app U x m) y) (n : ℤ) :
    (tensorLeftDesc 𝒪 h𝒪 F M N θ hθ).app n = tensorLeftDescApp 𝒪 h𝒪 F M N θ n := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The computation rule for the universal property**: the degree-`n` component of the
descended homomorphism sends the image of the pure tensor `x ⊗ m` to `θ (x, m)`. -/
@[simp]
theorem tensorLeftDesc_app_tmul
    (hθ : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U)
      (y : (A.piece i).val.obj U),
      (θ (n + i)).app U x (M.smul n i U m y) = N.smul n i U ((θ n).app U x m) y)
    (n : ℤ) (U : Cᵒᵖ) (x : F.val.obj U) (m : (M.piece n).val.obj U) :
    ((tensorLeftDesc 𝒪 h𝒪 F M N θ hθ).app n).val.app U
        (tensorLeftMk 𝒪 h𝒪 F M n U (x ⊗ₜ m)) = (θ n).app U x m :=
  tensorLeftDescApp_tmul 𝒪 h𝒪 F M N θ n U x m

/-! ### Quasi-coherence -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The pieces of `F ⊗ M` are quasi-coherent** as soon as `F` and every piece of `M` is: each
piece is the tensor product sheaf `F ⊗ Mⁿ` on the nose, and a tensor product of quasi-coherent
sheaves of modules on a site is quasi-coherent (Stacks 0GQM). -/
theorem isQuasicoherent_tensorLeft_piece [UnivLE.{max v u, w}] [Limits.HasPullbacks C]
    [HasSheafify J AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
    [SheafOfModules.IsQuasicoherent (R := structureSheaf 𝒪 h𝒪) F]
    (hM : ∀ k : ℤ, SheafOfModules.IsQuasicoherent (R := structureSheaf 𝒪 h𝒪) (M.piece k))
    (n : ℤ) :
    SheafOfModules.IsQuasicoherent (R := structureSheaf 𝒪 h𝒪)
      ((tensorLeft 𝒪 h𝒪 F M).piece n) :=
  have := hM n
  Stacks.SheafOfModules.TensorProduct.isQuasicoherent_tensorSheaf' 𝒪 h𝒪 F (M.piece n)

end SheafOfModules.GradedModule

end
