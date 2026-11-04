module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# The quotient of a sheaf of graded algebras by a graded ideal

Let `A` be a sheaf of `ℤ`-graded algebras on a site and `I ⊆ A` a graded two-sided ideal: in every
degree a submodule `I_n ⊆ A_n`, stable under multiplication by homogeneous local sections. The
quotient `A ⧸ I` is the sheafification of the sectionwise quotient `U ↦ A_n(U) ⧸ I_n(U)`, which
is a graded algebra of presheaves of modules; the quotient map `A ⟶ A ⧸ I` is a unital
homomorphism, an epimorphism in each degree, with kernel `I`.

## Main definitions

* `PresheafOfModules.Submodule.quotient`, `PresheafOfModules.Submodule.mkQ`: the sectionwise
  quotient of a presheaf of modules by a submodule, and the quotient map.
* `SheafOfModules.GradedAlgebra.Ideal`: a graded two-sided ideal of a sheaf of graded algebras.
* `SheafOfModules.GradedAlgebra.Ideal.quotientPresheafAlgebra`: the sectionwise quotient as a
  graded algebra of presheaves of modules.
* `SheafOfModules.GradedAlgebra.Ideal.quotient`: the sheaf of graded algebras `A ⧸ I`.
* `SheafOfModules.GradedAlgebra.Ideal.quotientMap`: the unital homomorphism `A ⟶ A ⧸ I`.

## Main results

* `SheafOfModules.GradedAlgebra.Ideal.epi_quotientMapApp`: the quotient map is an epimorphism in
  every degree.
* `SheafOfModules.GradedAlgebra.Ideal.quotientMapApp_eq_zero_iff` and
  `SheafOfModules.GradedAlgebra.Ideal.kerSubmodule_quotientMapApp`: its kernel is `I`.
* `SheafOfModules.GradedAlgebra.Ideal.quotient_mul_comm`: the quotient of a commutative graded
  algebra is commutative.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u v' u'

namespace PresheafOfModules.Submodule

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{v} R}
  (N : M.Submodule)

/-- The presheaf of abelian groups `X ↦ M(X) ⧸ N(X)`. -/
def quotientPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (M.obj X ⧸ N.obj X)
  map {X Y} f := AddCommGrpCat.ofHom
    ((N.obj X).mapQ (N.obj Y) (M.restrictₛₗ f) fun _ hx ↦ N.map_mem f hx).toAddMonoidHom
  map_id X := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (by simp)
  map_comp f g := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (M.map_comp_apply f g m)

/-- The sections `M(X) ⧸ N(X)` of the quotient presheaf are an `R(X)`-module. -/
instance (X : Cᵒᵖ) : Module (R.obj X) (N.quotientPresheaf.obj X) :=
  inferInstanceAs (Module (R.obj X) (M.obj X ⧸ N.obj X))

/-- The quotient `M ⧸ N` of a presheaf of modules by a submodule, computed sectionwise. -/
def quotient : PresheafOfModules.{v} R :=
  ofPresheaf N.quotientPresheaf fun X Y f r x ↦ by
    induction x using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (M.map_smul f r m)

/-- The quotient map `M ⟶ M ⧸ N`. -/
def mkQ : M ⟶ N.quotient where
  app X := ModuleCat.ofHom (N.obj X).mkQ
  naturality _ := rfl

/-- On sections over `X`, the quotient map sends `m` to its class in `M(X) ⧸ N(X)`. -/
@[simp]
theorem mkQ_app_apply (X : Cᵒᵖ) (m : M.obj X) :
    N.mkQ.app X m = Submodule.Quotient.mk (p := N.obj X) m := rfl

/-- The quotient map `M ⟶ M ⧸ N` is surjective on sections over every object. -/
theorem mkQ_app_surjective (X : Cᵒᵖ) : Function.Surjective (N.mkQ.app X) :=
  (N.obj X).mkQ_surjective

/-- The map `M ⧸ N ⟶ M ⧸ N'` of quotients by nested submodules. -/
def quotientMapOfLE {N N' : M.Submodule} (h : N ≤ N') : N.quotient ⟶ N'.quotient where
  app X := ModuleCat.ofHom ((N.obj X).mapQ (N'.obj X) LinearMap.id
    fun _ hx ↦ (PresheafOfModules.Submodule.le_iff.1 h X) hx)
  naturality f := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H m => rfl

/-- The map of quotients for `N ≤ N'` carries the quotient map of `N` to that of `N'`. -/
@[reassoc (attr := simp)]
theorem mkQ_comp_quotientMapOfLE {N N' : M.Submodule} (h : N ≤ N') :
    N.mkQ ≫ quotientMapOfLE h = N'.mkQ := rfl

end PresheafOfModules.Submodule

namespace SheafOfModules.GradedAlgebra

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A graded two-sided ideal of a sheaf of graded algebras: in every degree a submodule of the
homogeneous piece, stable under multiplication by homogeneous local sections on either side. -/
structure Ideal (A : GradedAlgebra.{u, v} R) where
  /-- The degree-`n` piece of the ideal. -/
  piece (n : ℤ) : (A.piece n).Submodule
  /-- The ideal is stable under left multiplication. -/
  mul_mem_left (i j : ℤ) (X : Cᵒᵖ) (a : (A.piece i).val.obj X) {x : (A.piece j).val.obj X} :
    x ∈ (piece j).obj X → (A.mul i j).app X a x ∈ (piece (i + j)).obj X
  /-- The ideal is stable under right multiplication. -/
  mul_mem_right (i j : ℤ) (X : Cᵒᵖ) {x : (A.piece i).val.obj X} (b : (A.piece j).val.obj X) :
    x ∈ (piece i).obj X → (A.mul i j).app X x b ∈ (piece (i + j)).obj X

namespace Ideal

variable {A : GradedAlgebra.{u, v} R} (I : Ideal A)

/-- The homogeneous pieces of the presheaf quotient `A ⧸ I`, computed sectionwise. -/
abbrev presheafPiece (n : ℤ) : PresheafOfModules.{v} R.obj :=
  (I.piece n).toSubmodule.quotient

/-- The quotient map `A_n ⟶ A_n ⧸ I_n` of presheaves of modules. -/
abbrev presheafMkQ (n : ℤ) : (A.piece n).val ⟶ I.presheafPiece n :=
  (I.piece n).toSubmodule.mkQ

/-- Left multiplication by a fixed homogeneous section, on the quotient. -/
def quotientMulLeft (i j : ℤ) (X : Cᵒᵖ) (a : (A.piece i).val.obj X) :
    (I.presheafPiece j).obj X →+ (I.presheafPiece (i + j)).obj X :=
  QuotientAddGroup.lift ((I.piece j).obj X).toAddSubgroup
    (((I.presheafMkQ (i + j)).app X).hom.toAddMonoidHom.comp
      ((A.mul i j).app X a)) fun _ hx ↦
        (Submodule.Quotient.mk_eq_zero ((I.piece (i + j)).toSubmodule.obj X)).2
          (I.mul_mem_left i j X a hx)

/-- Left multiplication by `a` on the quotient sends the class of `x` to the class of `a * x`. -/
theorem quotientMulLeft_mk (i j : ℤ) (X : Cᵒᵖ) (a : (A.piece i).val.obj X)
    (x : (A.piece j).val.obj X) :
    I.quotientMulLeft i j X a ((I.presheafMkQ j).app X x) =
      (I.presheafMkQ (i + j)).app X ((A.mul i j).app X a x) := rfl

/-- Left multiplication on the quotient, as an additive function of the left factor. -/
def quotientMulLeftHom (i j : ℤ) (X : Cᵒᵖ) :
    (A.piece i).val.obj X →+ (I.presheafPiece j).obj X →+ (I.presheafPiece (i + j)).obj X :=
  AddMonoidHom.mk' (I.quotientMulLeft i j X) fun a a' ↦ by
    refine AddMonoidHom.ext fun y ↦ ?_
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      exact (congrArg ((I.presheafMkQ (i + j)).app X)
        ((A.mul i j).map_add_left X a a' y)).trans (map_add _ _ _)

/-- The multiplication of the quotient, on sections over one object. -/
def quotientMulApp (i j : ℤ) (X : Cᵒᵖ) :
    (I.presheafPiece i).obj X →+ (I.presheafPiece j).obj X →+ (I.presheafPiece (i + j)).obj X :=
  (QuotientAddGroup.lift ((I.piece i).obj X).toAddSubgroup (I.quotientMulLeftHom i j X)
    fun a ha ↦ by
      refine AddMonoidHom.ext fun y ↦ ?_
      induction y using QuotientAddGroup.induction_on with
      | H y =>
        exact (Submodule.Quotient.mk_eq_zero ((I.piece (i + j)).toSubmodule.obj X)).2
          (I.mul_mem_right i j X y ha) :
    (A.piece i).val.obj X ⧸ ((I.piece i).obj X).toAddSubgroup →+ _)

/-- The multiplication of the quotient sends the classes of `x` and `y` to the class of
`x * y`. -/
theorem quotientMulApp_mk (i j : ℤ) (X : Cᵒᵖ) (x : (A.piece i).val.obj X)
    (y : (A.piece j).val.obj X) :
    I.quotientMulApp i j X ((I.presheafMkQ i).app X x) ((I.presheafMkQ j).app X y) =
      (I.presheafMkQ (i + j)).app X ((A.mul i j).app X x y) := rfl

/-- The multiplication of the presheaf quotient `A ⧸ I`, induced by that of `A`. -/
def quotientMul (i j : ℤ) :
    Stacks.BilinearMap (I.presheafPiece i) (I.presheafPiece j) (I.presheafPiece (i + j)) where
  app := I.quotientMulApp i j
  map_smul_left X r x y := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact congrArg ((I.presheafMkQ (i + j)).app X) ((A.mul i j).map_smul_left X r x y)
  map_smul_right X r x y := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact congrArg ((I.presheafMkQ (i + j)).app X) ((A.mul i j).map_smul_right X r x y)
  naturality f x y := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact congrArg ((I.presheafMkQ (i + j)).app _) ((A.mul i j).naturality f x y)

/-- **The presheaf quotient `A ⧸ I` as a graded algebra of presheaves of modules**: sectionwise
the quotient of the homogeneous pieces, with the induced multiplication and unit. -/
def quotientPresheafAlgebra : Stacks.GradedAlgebra I.presheafPiece where
  mul := I.quotientMul
  one := PresheafOfModules.sectionsMap (I.presheafMkQ 0) A.one
  mul_assoc i j k X x y z := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          exact Stacks.heq_apply _ _ (fun n s => (I.presheafMkQ n).app X s) (add_assoc i j k)
            (A.mul_assoc i j k X x y z)
  one_mul i X x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      exact Stacks.heq_apply _ _ (fun n s => (I.presheafMkQ n).app X s) (zero_add i)
        (A.one_mul i X x)
  mul_one i X x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      exact Stacks.heq_apply _ _ (fun n s => (I.presheafMkQ n).app X s) (add_zero i)
        (A.mul_one i X x)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- **The quotient `A ⧸ I` of a sheaf of graded algebras by a graded ideal**: the
sheafification of the sectionwise quotient. -/
def quotient : GradedAlgebra.{u, v} R :=
  I.quotientPresheafAlgebra.sheafify (𝟙 R.obj)

/-- The degree-`n` piece of `A ⧸ I` is the sheafification of the sectionwise quotient
`A_n ⧸ I_n`. -/
theorem quotient_piece (n : ℤ) :
    I.quotient.piece n = (PresheafOfModules.sheafification (𝟙 R.obj)).obj (I.presheafPiece n) :=
  rfl

/-- The degree-`n` component of the quotient map `A ⟶ A ⧸ I`: the sectionwise quotient map
followed by the sheafification unit. -/
def quotientMapApp (n : ℤ) : A.piece n ⟶ I.quotient.piece n :=
  ⟨I.presheafMkQ n ≫ PresheafOfModules.sheafifyUnit (𝟙 R.obj) (I.presheafPiece n)⟩

/-- On sections over `X`, the degree-`n` component of the quotient map sends `x` to the image
under the sheafification unit of its class in `A_n(X) ⧸ I_n(X)`. -/
theorem quotientMapApp_val_app (n : ℤ) (X : Cᵒᵖ) (x : (A.piece n).val.obj X) :
    (I.quotientMapApp n).val.app X x =
      (PresheafOfModules.sheafifyUnit (𝟙 R.obj) (I.presheafPiece n)).app X
        ((I.presheafMkQ n).app X x) := rfl

/-- **The quotient map `A ⟶ A ⧸ I`**, a unital homomorphism of sheaves of graded algebras. -/
def quotientMap : UnitalHom A I.quotient where
  app := I.quotientMapApp
  map_mul i j X x y :=
    (I.quotientPresheafAlgebra.sheafify_mul_unit (𝟙 R.obj) i j X
      ((I.presheafMkQ i).app X x) ((I.presheafMkQ j).app X y)).symm
  map_one _ := rfl

/-- The degree-`n` component of the quotient map `A ⟶ A ⧸ I` is `quotientMapApp I n`. -/
theorem quotientMap_app (n : ℤ) : I.quotientMap.app n = I.quotientMapApp n := rfl

/-- The quotient map is an epimorphism in every degree: it is surjective sectionwise followed by
the locally surjective sheafification unit. -/
instance epi_quotientMapApp (n : ℤ) : Epi (I.quotientMapApp n) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ?_
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (I.presheafMkQ n)) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun X ↦
      (I.piece n).toSubmodule.mkQ_app_surjective X
  change Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map
    (I.presheafMkQ n) ≫ (PresheafOfModules.toPresheaf R.obj).map
      (PresheafOfModules.sheafifyUnit (𝟙 R.obj) (I.presheafPiece n)))
  infer_instance

/-- **The kernel of the quotient map is the ideal**: a local section of `A_n` dies in `A_n ⧸ I_n`
exactly when it lies in `I_n`. -/
theorem quotientMapApp_eq_zero_iff (n : ℤ) (X : Cᵒᵖ) (x : (A.piece n).val.obj X) :
    (I.quotientMapApp n).val.app X x = 0 ↔ x ∈ (I.piece n).obj X := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have hmem := Presheaf.equalizerSieve_mem J
      ((PresheafOfModules.toPresheaf R.obj).map
        (PresheafOfModules.sheafifyUnit (𝟙 R.obj) (I.presheafPiece n)))
      ((I.presheafMkQ n).app X x) 0 (hx.trans (map_zero _).symm)
    refine (I.piece n).isSheaf x (J.superset_covering (fun Y f hf ↦ ?_) hmem)
    have h0 : (I.presheafMkQ n).app (op Y) ((A.piece n).val.map f.op x) = 0 :=
      hf.trans (map_zero _)
    exact (Submodule.Quotient.mk_eq_zero ((I.piece n).toSubmodule.obj (op Y))).1 h0
  · rw [quotientMapApp_val_app, show (I.presheafMkQ n).app X x = 0 from
      (Submodule.Quotient.mk_eq_zero ((I.piece n).toSubmodule.obj X)).2 hx, map_zero]
    rfl

/-- The ideal is the kernel of the quotient map, as a subsheaf of the homogeneous piece. -/
theorem kerSubmodule_quotientMapApp (n : ℤ) :
    Stacks.SheafOfModules.kerSubmodule (I.quotientMapApp n) = I.piece n :=
  SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun X ↦ SetLike.ext fun x ↦
    (Stacks.SheafOfModules.mem_kerSubmodule_obj _ X x).trans (I.quotientMapApp_eq_zero_iff n X x))

/-- A homogeneous piece of the quotient vanishes as soon as the corresponding piece of `A`
does, the quotient map being an epimorphism. -/
theorem isZero_quotient_piece {n : ℤ} (h : Limits.IsZero (A.piece n)) :
    Limits.IsZero (I.quotient.piece n) :=
  Limits.IsZero.of_epi (I.quotientMapApp n) h

/-- **The quotient of a commutative graded algebra is commutative.** -/
theorem quotient_mul_comm
    (hA : ∀ (i j : ℤ) (X : Cᵒᵖ) (a : (A.piece i).val.obj X) (b : (A.piece j).val.obj X),
      HEq ((A.mul i j).app X a b) ((A.mul j i).app X b a))
    (i j : ℤ) (X : Cᵒᵖ) (a : (I.quotient.piece i).val.obj X)
    (b : (I.quotient.piece j).val.obj X) :
    HEq ((I.quotient.mul i j).app X a b) ((I.quotient.mul j i).app X b a) := by
  let B := I.quotientPresheafAlgebra
  refine Stacks.heq_of_isSeparated (congrArg (fun n : ℤ => I.quotient.piece n) (add_comm i j))
    (J.intersection_covering (Stacks.liftSieve_mem (𝟙 R.obj) (I.presheafPiece i) a)
      (Stacks.liftSieve_mem (𝟙 R.obj) (I.presheafPiece j) b)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  induction x₀ using Submodule.Quotient.induction_on with
  | H x =>
    induction y₀ using Submodule.Quotient.induction_on with
    | H y =>
      have h1 := B.sheafify_mul_restrict (𝟙 R.obj) i j f.op a b _ _ hx₀ hy₀
      have h2 := B.sheafify_mul_restrict (𝟙 R.obj) j i f.op b a _ _ hy₀ hx₀
      exact (heq_of_eq h1).trans ((Stacks.heq_apply _ _
        (fun n s => (PresheafOfModules.sheafifyUnit (𝟙 R.obj) (I.presheafPiece n)).app (op Y)
          ((I.presheafMkQ n).app (op Y) s)) (add_comm i j) (hA i j (op Y) x y)).trans
        (heq_of_eq h2.symm))

/-- **The map `A ⧸ J ⟶ A ⧸ I` for nested graded ideals `J ⊆ I`**, a unital homomorphism of
sheaves of graded algebras. -/
def quotientMapOfLE {J : Ideal A} (h : ∀ n, J.piece n ≤ I.piece n) :
    UnitalHom J.quotient I.quotient where
  app n := (PresheafOfModules.sheafification (𝟙 R.obj)).map
    (PresheafOfModules.Submodule.quotientMapOfLE (h n))
  map_mul i j X x y :=
    (J.quotientPresheafAlgebra.sheafifyGradedHom (𝟙 R.obj) I.quotientPresheafAlgebra
      (fun n => PresheafOfModules.Submodule.quotientMapOfLE (h n)) (fun i j X x y => by
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          induction y using Submodule.Quotient.induction_on with
          | H y => rfl)).map_mul i j X x y
  map_one X :=
    PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj)
      (PresheafOfModules.Submodule.quotientMapOfLE (h 0)) X _

/-- The map of quotients for `J ⊆ I` carries the quotient map of `J` to that of `I`. -/
theorem quotientMap_comp_quotientMapOfLE {J : Ideal A} (h : ∀ n, J.piece n ≤ I.piece n) :
    J.quotientMap.comp (I.quotientMapOfLE h) = I.quotientMap := by
  refine UnitalHom.ext fun n => ?_
  ext X x
  exact PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj)
    (PresheafOfModules.Submodule.quotientMapOfLE (h n)) X _

end Ideal

end SheafOfModules.GradedAlgebra
