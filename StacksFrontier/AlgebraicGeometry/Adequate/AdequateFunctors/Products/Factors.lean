module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Restriction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksCore.Tactic.StacksAttribute

/-!
# Adequate functors over finite products of rings: algebras and modules over the factors

For a finite family of commutative rings `A i`, this file sets up the algebra and module
infrastructure over the product `∀ i, A i` and its factors: the coordinatewise map `piAlgHom`
between products of algebras, the base change of an algebra over the product to each factor, the
restriction of a module-valued functor along the projections onto the factors, and the
equivalence between modules over the product and families of modules over the factors.

This is the first part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products`.
-/

@[expose] public section

open CategoryTheory
universe w v u u₁ v₁

namespace AdequateFunctor

/-- The componentwise algebra map associated to a family of algebra maps. -/
public def piAlgHom (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (B C : ∀ i, CommAlgCat.{max u v} (A i)) (f : ∀ i, B i ⟶ C i) :
    (∀ i, (B i : Type (max u v))) →ₐ[∀ i, A i] (∀ i, (C i : Type (max u v))) :=
  { RingHom.pi (fun i =>
      (f i).hom.toRingHom.comp (Pi.evalRingHom (fun i => (B i : Type (max u v))) i)) with
    commutes' := by
      intro a
      ext i
      exact (f i).hom.commutes (a i) }

open CategoryTheory.Limits

/-- Evaluating the kernel of a morphism of presheaves of modules gives the kernel of the
evaluated morphism. -/
lemma kernelApp_exact {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {F G : PresheafOfModules.{w} R} (f : F ⟶ G) (X : Cᵒᵖ) :
    Function.Exact ((kernel.ι f).app X).hom (f.app X).hom := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS := (ShortComplex.exact_kernel f).map (PresheafOfModules.evaluation R X)
  intro x
  constructor
  · exact ((S.map (PresheafOfModules.evaluation R X)).moduleCat_exact_iff.mp hS) x
  · rintro ⟨y, rfl⟩
    exact congrArg (fun g => g.app X y) (kernel.condition f)

/-- Adequacy descends from the universe lift of a module-valued functor. -/
private lemma isAdequate_of_ulift {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{w, v} A)
    (h : IsAdequate (𝟭 _)
      ((presheafOfModulesUliftFunctor.{u}
        (algebraRingDiagram.{v} A)).obj F)) :
    IsAdequate (𝟭 _) F := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := h
  refine ⟨M, N, f, ⟨?_ ≪≫ e⟩⟩
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · exact (ULift.moduleEquiv.trans
      (ULift.moduleEquiv.trans ULift.moduleEquiv).symm).toModuleIso
  · intros
    ext x
    rfl

/-- Adequacy is preserved by restriction of the base ring. -/
private lemma isAdequate_restrict {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (F : ModuleValuedFunctor.{w, v} A)
    (hF : IsAdequate (𝟭 _) F) :
    IsAdequate (𝟭 _) ((restrictFunctor.{w, v} f).obj F) :=
  isAdequate_of_ulift _ (IsAdequate.restrict f F hF)

/-- Each factor is an algebra over the product ring, via the evaluation homomorphism. -/
instance piEvalAlgebra (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (i : Fin n) : Algebra (∀ i, A i) (A i) := (Pi.evalRingHom A i).toAlgebra

/-- The product of a family of algebras over the factors, as an algebra over the product
ring. -/
abbrev piAlgFamily (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (G : ∀ i, CommAlgCat.{max u v} (A i)) : CommAlgCat.{max u v} (∀ i, A i) := by
  letI (i : Fin n) : Algebra (∀ j, A j) (G i) :=
    Algebra.compHom (A := (G i : Type (max u v))) (Pi.evalRingHom A i)
  exact CommAlgCat.of (∀ i, A i) (∀ i, (G i : Type (max u v)))

/-- The product of a family of algebra maps. -/
def piAlgFamilyMap (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (G H : ∀ i, CommAlgCat.{max u v} (A i)) (f : ∀ i, G i ⟶ H i) :
    piAlgFamily n A G ⟶ piAlgFamily n A H :=
  CommAlgCat.ofHom (piAlgHom n A G H f)

/-- Taking the product of a family of factor algebras, as a functor. -/
private def piAlgFamilyFunctor (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)] :
  (∀ i, CommAlgCat.{max u v} (A i)) ⥤ CommAlgCat.{max u v} (∀ i, A i) where
  obj := piAlgFamily n A
  map := fun {G H} f => piAlgFamilyMap n A G H f
  map_id G := by
    apply CommAlgCat.hom_ext
    ext i x
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    ext i x
    rfl

/-- The base change to the `i`-th factor of an algebra over the product ring. -/
abbrev factorAlg (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) : CommAlgCat.{max u v} (A i) := by
  letI : Algebra (∀ i, A i) (A i) := (Pi.evalRingHom A i).toAlgebra
  letI : Algebra (A i) (TensorProduct (∀ i, A i) (B : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.rightAlgebra (R := ∀ i, A i) (A := (B : Type (max u v))) (B := A i)
  exact CommAlgCat.of (A i) (TensorProduct (∀ i, A i) (B : Type (max u v)) (A i))

/-- The algebra structure on the base change to the `i`-th factor. -/
instance factorBaseChangeAlgebra (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) :
    Algebra B (TensorProduct (∀ i, A i) (B : Type (max u v)) (A i)) :=
  Algebra.TensorProduct.leftAlgebra (R := ∀ i, A i) (S := B)
    (A := (B : Type (max u v))) (B := A i)

/-- The canonical factor algebras of a product-base algebra multiply back to that algebra. -/
noncomputable def piAlgFactorAlgEquiv (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i)) :
    (B : Type (max u v)) ≃ₐ[∀ i, A i]
      (∀ i, TensorProduct (∀ i, A i) (B : Type (max u v)) (A i)) := by
  letI : Algebra (∀ i, A i) (∀ i, A i) := Algebra.id _
  letI : CommRing (B : Type (max u v)) := B.commRing
  letI : Algebra (∀ i, A i) (B : Type (max u v)) := B.algebra
  exact (Algebra.TensorProduct.rid (∀ i, A i) (∀ i, A i) (B : Type (max u v))).symm.trans
    (Algebra.TensorProduct.piRight (∀ i, A i) (∀ i, A i) (B : Type (max u v)) A)

/-- The product-of-factors identification of an algebra is computed on elements by base
change. -/
lemma piAlgFactorAlgEquiv_apply (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i))
    (b : B) (i : Fin n) :
    piAlgFactorAlgEquiv n A B b i =
      b ⊗ₜ[∀ i, A i] (1 : A i) := by
  let : Algebra (∀ i, A i) (∀ i, A i) := Algebra.id _
  let : CommRing (B : Type (max u v)) := B.commRing
  let : Algebra (∀ i, A i) (B : Type (max u v)) := B.algebra
  change Algebra.TensorProduct.piRight (∀ i, A i) (∀ i, A i)
      (B : Type (max u v)) A (b ⊗ₜ[∀ i, A i] (1 : ∀ i, A i)) i = _
  rw [Algebra.TensorProduct.piRight_tmul]
  rfl

/-- The map of `i`-th factor algebras induced by a map of algebras over the product ring. -/
def factorAlgMap (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (B C : CommAlgCat.{max u v} (∀ i, A i)) (f : B ⟶ C) (i : Fin n) :
    factorAlg n A B i ⟶ factorAlg n A C i := by
  letI : Algebra (∀ j, A j) (B : Type (max u v)) := B.algebra
  letI : Algebra (∀ j, A j) (C : Type (max u v)) := C.algebra
  letI : Algebra (∀ j, A j) (A i) := (Pi.evalRingHom A i).toAlgebra
  letI : Algebra (∀ j, A j) (TensorProduct (∀ j, A j) (B : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.leftAlgebra (R := ∀ j, A j) (S := ∀ j, A j) (A := B)
      (B := A i)
  letI : Algebra (∀ j, A j) (TensorProduct (∀ j, A j) (C : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.leftAlgebra (R := ∀ j, A j) (S := ∀ j, A j) (A := C)
      (B := A i)
  letI : Algebra (A i) (TensorProduct (∀ j, A j) (B : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := B) (B := A i)
  letI : Algebra (A i) (TensorProduct (∀ j, A j) (C : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := C) (B := A i)
  let g := Algebra.TensorProduct.map f.hom (AlgHom.id (∀ j, A j) (A i))
  exact CommAlgCat.ofHom {
    toRingHom := g.toRingHom
    commutes' := fun a => by
      simp [g, Algebra.TensorProduct.right_algebraMap_apply] }

/-- Base changing to each factor, as a functor to the product of the factor categories. -/
def factorAlgFunctor (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)] :
    CommAlgCat.{max u v} (∀ i, A i) ⥤ (∀ i, CommAlgCat.{max u v} (A i)) where
  obj B i := factorAlg n A B i
  map f i := factorAlgMap n A _ _ f i
  map_id B := by
    funext i
    let : Algebra (A i)
        (TensorProduct (∀ j, A j) (B : Type (max u v)) (A i)) :=
      Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := B) (B := A i)
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b a => simp [factorAlgMap]
    | add x y hx hy => simp [hx, hy]
  map_comp {B C D} f g := by
    funext i
    let : Algebra (A i)
        (TensorProduct (∀ j, A j) (B : Type (max u v)) (A i)) :=
      Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := B) (B := A i)
    let : Algebra (A i)
        (TensorProduct (∀ j, A j) (C : Type (max u v)) (A i)) :=
      Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := C) (B := A i)
    let : Algebra (A i)
        (TensorProduct (∀ j, A j) (D : Type (max u v)) (A i)) :=
      Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := D) (B := A i)
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b a => simp [factorAlgMap]
    | add x y hx hy => simp [hx, hy]

/-- The product-of-factors identification of algebras is natural. -/
lemma piAlgFactorAlgEquiv_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B C : CommAlgCat.{max u v} (∀ i, A i))
    (f : B ⟶ C) (b : B) (i : Fin n) :
    factorAlgMap n A B C f i (piAlgFactorAlgEquiv n A B b i) =
      piAlgFactorAlgEquiv n A C (f.hom b) i := by
  simp [piAlgFactorAlgEquiv_apply, factorAlgMap]

/-- An algebra over the `i`-th factor, read as an algebra over the product ring along the
evaluation homomorphism. -/
def evalAlgFunctor (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (i : Fin n) : CommAlgCat.{max u v} (A i) ⥤
      CommAlgCat.{max u v} (∀ i, A i) where
  obj B := by
    letI : Algebra (∀ j, A j) (B : Type (max u v)) :=
      Algebra.compHom (B : Type (max u v)) (Pi.evalRingHom A i)
    exact CommAlgCat.of (∀ j, A j) (B : Type (max u v))
  map {B C} f := by
    letI : Algebra (∀ j, A j) (B : Type (max u v)) :=
      Algebra.compHom (B : Type (max u v)) (Pi.evalRingHom A i)
    letI : Algebra (∀ j, A j) (C : Type (max u v)) :=
      Algebra.compHom (C : Type (max u v)) (Pi.evalRingHom A i)
    letI : Algebra (A i) (B : Type (max u v)) := B.algebra
    letI : Algebra (A i) (C : Type (max u v)) := C.algebra
    letI : Algebra (∀ j, A j) (A i) := (Pi.evalRingHom A i).toAlgebra
    haveI : IsScalarTower (∀ j, A j) (A i) (B : Type (max u v)) :=
      .of_algebraMap_eq' rfl
    haveI : IsScalarTower (∀ j, A j) (A i) (C : Type (max u v)) :=
      .of_algebraMap_eq' rfl
    exact CommAlgCat.ofHom (f.hom.restrictScalars (∀ j, A j))
  map_id B := by
    apply CommAlgCat.hom_ext
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    rfl

/-- Reading a factor algebra over the product ring does not change its carrier. -/
private lemma evalAlgFunctor_obj_underlying (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) (B : CommAlgCat.{max u v} (A i)) :
    ((evalAlgFunctor n A i).obj B : Type (max u v)) = (B : Type (max u v)) := rfl

/-- Restricting a module-valued functor over the product ring to the algebras over the `i`-th
factor. -/
def restrictModuleFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) :
    ModuleValuedFunctor.{w, v} (∀ i, A i) ⥤
      ModuleValuedFunctor.{w, v} (A i) where
  obj F := {
    obj X := F.obj (((evalAlgFunctor n A i).op.op).obj X)
    map f := F.map (((evalAlgFunctor n A i).op.op).map f)
    map_id X := F.map_id (((evalAlgFunctor n A i).op.op).obj X)
    map_comp f g := F.map_comp (((evalAlgFunctor n A i).op.op).map f)
      (((evalAlgFunctor n A i).op.op).map g) }
  map η := {
    app X := η.app (((evalAlgFunctor n A i).op.op).obj X)
    naturality := by
      intro X Y f
      exact η.naturality (((evalAlgFunctor n A i).op.op).map f) }
  map_id F := by
    ext X x
    rfl
  map_comp η θ := by
    ext X x
    rfl

/-- Restriction to the `i`-th factor preserves adequacy. -/
lemma isAdequate_restrictModuleFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n)
    (F : ModuleValuedFunctor.{w, v} (∀ i, A i))
    (hF : IsAdequate (𝟭 _) F) :
    IsAdequate (𝟭 _) ((restrictModuleFunctor n A i).obj F) :=
  IsAdequate.of_iso (isAdequate_restrict (Pi.evalRingHom A i) F hF)
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; ext x; rfl))

/-- Restricting an adequate functor over the product ring to each factor, as a functor to the
product of the categories of adequate functors. -/
def adequateRestrictionFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    (ObjectProperty.FullSubcategory
      (fun F : ModuleValuedFunctor.{w, v} (∀ i, A i) =>
        IsAdequate (𝟭 _) F)) ⥤
      (∀ i : Fin n, ObjectProperty.FullSubcategory
        (fun F : ModuleValuedFunctor.{w, v} (A i) =>
          IsAdequate (𝟭 _) F)) where
  obj F i := ⟨(restrictModuleFunctor n A i).obj F.obj,
    isAdequate_restrictModuleFunctor n A i F.obj F.property⟩
  map η i := ObjectProperty.homMk ((restrictModuleFunctor n A i).map η.hom)
  map_id F := by
    funext i
    apply ObjectProperty.hom_ext
    exact (restrictModuleFunctor n A i).map_id _
  map_comp η θ := by
    funext i
    apply ObjectProperty.hom_ext
    exact (restrictModuleFunctor n A i).map_comp _ _

set_option linter.checkUnivs false in
/-- A module over the product ring is the product of its base changes to the factors. -/
private noncomputable def piModuleFactorEquiv (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i)) :
    (M : Type (max u v w)) ≃ₗ[∀ i, A i]
      (∀ i, TensorProduct (∀ i, A i) (M : Type (max u v w)) (A i)) := by
  let R := ∀ i, A i
  letI : Algebra R R := Algebra.id R
  letI (i : Fin n) : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  letI : Module R R := Pi.module (Fin n) A R
  exact (TensorProduct.rid R (M : Type (max u v w))).symm.trans
    (TensorProduct.piRight R R (M : Type (max u v w)) A)

/-- The product-of-factors identification of a module is computed on elements by base
change. -/
private lemma piModuleFactorEquiv_apply (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i))
    (m : M) (i : Fin n) :
    piModuleFactorEquiv.{w, v, u} n A M m i = m ⊗ₜ[∀ i, A i] (1 : A i) := by
  change TensorProduct.piRight (∀ i, A i) (∀ i, A i) (M : Type (max u v w)) A
      (m ⊗ₜ[∀ i, A i] (1 : ∀ i, A i)) i = _
  rfl

/-- The module decomposition commutes with maps after extension to every factor. -/
private lemma piModuleFactorEquiv_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ModuleCat.{max u v w} (∀ i, A i))
    (f : M ⟶ N) (m : M) (i : Fin n) :
    TensorProduct.map f.hom (LinearMap.id (R := ∀ i, A i) (M := A i))
        (piModuleFactorEquiv.{w, v, u} n A M m i) =
      piModuleFactorEquiv.{w, v, u} n A N (f.hom m) i := by
  rw [piModuleFactorEquiv_apply, piModuleFactorEquiv_apply]
  simp

set_option linter.checkUnivs false in
/-- The product of a family of modules over the factors, as a module over the product ring. -/
abbrev piModuleFamily (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i)) :
    ModuleCat.{max u v w} (∀ i, A i) := by
  let R := ∀ i, A i
  letI (i : Fin n) : Module R (M i) := Module.compHom (M i : Type (max u v w))
    (Pi.evalRingHom A i)
  letI : Module R (∀ i, (M i : Type (max u v w))) := Pi.module (Fin n)
    (fun i => (M i : Type (max u v w))) R
  exact ModuleCat.of R (∀ i, (M i : Type (max u v w)))

/-- The product of a family of linear maps of factor modules. -/
private def piModuleFamilyMap (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ∀ i, ModuleCat.{max u v w} (A i))
    (f : ∀ i, M i ⟶ N i) :
    piModuleFamily.{w, v, u} n A M ⟶ piModuleFamily.{w, v, u} n A N := by
  let R := ∀ i, A i
  letI (i : Fin n) : Module R (M i) := Module.compHom (M i : Type (max u v w))
    (Pi.evalRingHom A i)
  letI (i : Fin n) : Module R (N i) := Module.compHom (N i : Type (max u v w))
    (Pi.evalRingHom A i)
  letI : Module R (∀ i, (M i : Type (max u v w))) := Pi.module (Fin n)
    (fun i => (M i : Type (max u v w))) R
  letI : Module R (∀ i, (N i : Type (max u v w))) := Pi.module (Fin n)
    (fun i => (N i : Type (max u v w))) R
  exact ModuleCat.ofHom {
    toFun := fun x i => (f i).hom (x i)
    map_add' := by intro x y; funext i; exact map_add (f i).hom (x i) (y i)
    map_smul' := by
      intro r x
      funext i
      exact map_smul (f i).hom (r i) (x i) }

set_option linter.checkUnivs false in
/-- Taking the product of a family of factor modules, as a functor. -/
private def piModuleFamilyFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
  (∀ i, ModuleCat.{max u v w} (A i)) ⥤ ModuleCat.{max u v w} (∀ i, A i) where
  obj := piModuleFamily.{w, v, u} n A
  map := fun {M N} f => piModuleFamilyMap.{w, v, u} n A M N f
  map_id M := by
    apply ModuleCat.hom_ext
    ext i x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext i x
    rfl

set_option linter.checkUnivs false in
/-- The base change to the `i`-th factor of a module over the product ring. -/
private abbrev factorModule (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i)) (i : Fin n) :
    ModuleCat.{max u v w} (A i) := by
  let R := ∀ i, A i
  letI : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  letI : Module (A i) (TensorProduct R (A i) (M : Type (max u v w))) :=
    TensorProduct.leftModule
  exact ModuleCat.of (A i) (TensorProduct R (A i) (M : Type (max u v w)))

/-- The map of `i`-th factor modules induced by a map of modules over the product ring. -/
private def factorModuleMap (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ModuleCat.{max u v w} (∀ i, A i))
    (f : M ⟶ N) (i : Fin n) : factorModule.{w, v, u} n A M i ⟶
      factorModule.{w, v, u} n A N i := by
  let R := ∀ i, A i
  letI : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  exact ModuleCat.ofHom (f.hom.baseChange (A i))

set_option linter.checkUnivs false in
/-- Base changing a module to each factor, as a functor to the product of the factor
categories. -/
private def factorModuleFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    ModuleCat.{max u v w} (∀ i, A i) ⥤ (∀ i, ModuleCat.{max u v w} (A i)) where
  obj M i := factorModule.{w, v, u} n A M i
  map f i := factorModuleMap.{w, v, u} n A _ _ f i
  map_id M := by
    funext i
    change ModuleCat.ofHom ((LinearMap.id (R := ∀ j, A j) (M := M)).baseChange (A i)) = _
    simp
  map_comp f g := by
    funext i
    change ModuleCat.ofHom ((g.hom ∘ₗ f.hom).baseChange (A i)) = _
    rw [LinearMap.baseChange_comp]
    rfl

set_option linter.checkUnivs false in
/-- The product-of-factors identification of a module, with the factor written on the left of
the tensor product. -/
private noncomputable def piModuleFactorEquiv' (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i)) :
    (M : Type (max u v w)) ≃ₗ[∀ i, A i]
      (∀ i, TensorProduct (∀ j, A j) (A i) (M : Type (max u v w))) := by
  let R := ∀ i, A i
  letI : Module R R := Pi.module (Fin n) A R
  letI (i : Fin n) : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  letI (i : Fin n) : Module R (TensorProduct R (M : Type (max u v w)) (A i)) :=
    TensorProduct.leftModule
  letI : Module R (∀ i, TensorProduct R (M : Type (max u v w)) (A i)) :=
    Pi.module (Fin n) (fun i => TensorProduct R (M : Type (max u v w)) (A i)) R
  letI (i : Fin n) : Module R (TensorProduct R (A i) (M : Type (max u v w))) :=
    Module.compHom _ (Pi.evalRingHom A i)
  letI : Module R (∀ i, TensorProduct R (A i) (M : Type (max u v w))) :=
    Pi.module (Fin n) (fun i => TensorProduct R (A i) (M : Type (max u v w))) R
  let e₁ := piModuleFactorEquiv.{w, v, u} n A M
  let e₂ := LinearEquiv.piCongrRight fun i =>
    TensorProduct.comm R (M : Type (max u v w)) (A i)
  exact e₁.trans e₂

/-- The left-handed product-of-factors identification is computed on elements by base
change. -/
private lemma piModuleFactorEquiv'_apply (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i))
    (m : M) (i : Fin n) :
    piModuleFactorEquiv'.{w, v, u} n A M m i =
      (1 : A i) ⊗ₜ[∀ j, A j] m := by
  change TensorProduct.comm (∀ j, A j) (M : Type (max u v w)) (A i)
      (piModuleFactorEquiv.{w, v, u} n A M m i) = _
  rw [piModuleFactorEquiv_apply, TensorProduct.comm_tmul]

/-- The product-of-factors identification of a module, as an isomorphism of module objects. -/
private noncomputable def piModuleFactorIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i)) :
    M ≅ (piModuleFamilyFunctor.{w, v, u} n A).obj
      ((factorModuleFunctor.{w, v, u} n A).obj M) := by
  let R := ∀ i, A i
  letI : Algebra R R := Algebra.id R
  letI : Module R R := Pi.module (Fin n) A R
  letI (i : Fin n) : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  letI (i : Fin n) : Module R (TensorProduct R (M : Type (max u v w)) (A i)) :=
    TensorProduct.leftModule
  letI (i : Fin n) : Module R
      (TensorProduct R (A i) (M : Type (max u v w))) :=
    Module.compHom _ (Pi.evalRingHom A i)
  letI : Module R (∀ i, TensorProduct R (A i) (M : Type (max u v w))) :=
    Pi.module (Fin n) (fun i => TensorProduct R (A i) (M : Type (max u v w))) R
  exact (piModuleFactorEquiv'.{w, v, u} n A M).toModuleIso

/-- The left-handed product-of-factors identification is natural. -/
private lemma piModuleFactorEquiv'_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ModuleCat.{max u v w} (∀ i, A i))
    (f : M ⟶ N) (m : M) (i : Fin n) :
    f.hom.baseChange (A i) (piModuleFactorEquiv'.{w, v, u} n A M m i) =
      piModuleFactorEquiv'.{w, v, u} n A N (f.hom m) i := by
  rw [piModuleFactorEquiv'_apply, piModuleFactorEquiv'_apply]
  simp

/-- The product-of-factors isomorphism of modules is natural. -/
private lemma piModuleFactorIso_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ModuleCat.{max u v w} (∀ i, A i))
    (f : M ⟶ N) :
    (piModuleFactorIso.{w, v, u} n A M).hom ≫
        (piModuleFamilyFunctor.{w, v, u} n A).map
          ((factorModuleFunctor.{w, v, u} n A).map f) =
      f ≫ (piModuleFactorIso.{w, v, u} n A N).hom := by
  apply ModuleCat.hom_ext
  ext m
  change (fun i : Fin n => f.hom.baseChange (A i)
      (piModuleFactorEquiv'.{w, v, u} n A M m i)) =
    fun i : Fin n => piModuleFactorEquiv'.{w, v, u} n A N (f.hom m) i
  funext i
  exact piModuleFactorEquiv'_natural.{w, v, u} n A M N f m i

set_option linter.checkUnivs false in
/-- The `i`-th factor of a product of factor modules is the `i`-th member of the family. -/
noncomputable def piModuleFamilyFactorEquiv (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i)) (i : Fin n) :
    TensorProduct (∀ j, A j) (A i) (∀ j, (M j : Type (max u v w))) ≃ₗ[A i]
      (M i : Type (max u v w)) := by
  let R := ∀ j, A j
  letI (j : Fin n) : Module R (M j) := Module.compHom (M j : Type (max u v w))
    (Pi.evalRingHom A j)
  letI : Module R (∀ j, (M j : Type (max u v w))) :=
    inferInstance
  letI : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  letI : Module R (M i : Type (max u v w)) := Module.compHom (M i : Type (max u v w))
    (Pi.evalRingHom A i)
  letI : IsScalarTower R (A i) (M i : Type (max u v w)) := IsScalarTower.of_compHom R (A i)
    (M i : Type (max u v w))
  letI : TensorProduct.CompatibleSMul R R (A i) (∀ j, (M j : Type (max u v w))) :=
    ⟨fun r a x => Quotient.sound' <| AddConGen.Rel.of _ _ <|
      TensorProduct.Eqv.of_smul _ _ _⟩
  let f : (A i) →ₗ[A i] (∀ j, (M j : Type (max u v w))) →ₗ[R]
      (M i : Type (max u v w)) := {
    toFun := fun a => {
      toFun := fun x => a • x i
      map_add' x y := by simp [Pi.add_apply]
      map_smul' r x := by
        change a • ((r i) • x i) = (r i) • (a • x i)
        exact smul_comm a (r i) (x i) }
    map_add' a b := LinearMap.ext fun x => by simp [add_smul]
    map_smul' a b := LinearMap.ext fun x => by simp [mul_smul] }
  let e := TensorProduct.AlgebraTensorModule.lift f
  let g : (M i : Type (max u v w)) →ₗ[A i]
      TensorProduct R (A i) (∀ j, (M j : Type (max u v w))) := {
    toFun := fun x => (1 : A i) ⊗ₜ[R]
      (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x)
    map_add' x y := by rw [Pi.single_add, TensorProduct.tmul_add]
    map_smul' := by
      intro a x
      let r : R := Pi.single (M := fun j : Fin n => A j) i a
      have hsingle : (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i (a • x) :
          ∀ j : Fin n, (M j : Type (max u v w))) =
          (Pi.single (M := fun j : Fin n => A j) i a) •
            Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x := by
        ext j
        by_cases h : j = i
        · subst j
          simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne h]
      calc
        (1 : A i) ⊗ₜ[R]
            (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i (a • x) :
              ∀ j, (M j : Type (max u v w))) =
            (1 : A i) ⊗ₜ[R] (r •
              Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x) := by congr 1
        _ = r • ((1 : A i) ⊗ₜ[R]
            Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x) := by
              rw [TensorProduct.tmul_smul]
        _ = a • ((1 : A i) ⊗ₜ[R]
            Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x) := by
          change (r i) • ((1 : A i) ⊗ₜ[R]
            Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x) = _
          simp [r] }
  refine {
    toFun := e
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := e.map_add
    map_smul' := e.map_smul }
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul a y =>
      simp only [e, g, LinearMap.coe_mk,
        AddHom.coe_mk]
      let r : R := Pi.single (M := fun j : Fin n => A j) i a
      have hsingle : (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i
            (a • y i) : ∀ j : Fin n, (M j : Type (max u v w))) =
          (Pi.single (M := fun j : Fin n => A j) i a) • y := by
        ext j
        by_cases h : j = i
        · subst j
          simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne h]
      calc
        (1 : A i) ⊗ₜ[R]
            (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i (a • y i)) =
            (1 : A i) ⊗ₜ[R] (r • y) := by rw [hsingle]
        _ = r • ((1 : A i) ⊗ₜ[R] y) := by rw [TensorProduct.tmul_smul]
        _ = a ⊗ₜ[R] y := by
          change (r i : A i) • ((1 : A i) ⊗ₜ[R] y) = _
          simp [r, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [e.map_add, g.map_add, hx, hy]
  · intro x
    change (TensorProduct.AlgebraTensorModule.lift f)
      ((1 : A i) ⊗ₜ[R]
        (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x)) = x
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]
    change (1 : A i) •
      (Pi.single (M := fun j : Fin n => (M j : Type (max u v w))) i x) i = x
    rw [Pi.single_eq_same]
    exact one_smul _ _

/-- The factor identification sends `a ⊗ x` to `a • x i`. -/
lemma piModuleFamilyFactorEquiv_tmul (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i)) (i : Fin n)
    (a : A i) (x : ∀ j, (M j : Type (max u v w))) :
    piModuleFamilyFactorEquiv.{w, v, u} n A M i (a ⊗ₜ[∀ j, A j] x) = a • x i := by
  let R := ∀ j, A j
  let (j : Fin n) : Module R (M j) := Module.compHom (M j : Type (max u v w))
    (Pi.evalRingHom A j)
  let : Module R (∀ j, (M j : Type (max u v w))) := inferInstance
  let : Algebra R (A i) := (Pi.evalRingHom A i).toAlgebra
  let : Module R (M i : Type (max u v w)) := Module.compHom (M i : Type (max u v w))
    (Pi.evalRingHom A i)
  let : IsScalarTower R (A i) (M i : Type (max u v w)) :=
    IsScalarTower.of_compHom R (A i) (M i : Type (max u v w))
  let : TensorProduct.CompatibleSMul R R (A i) (∀ j, (M j : Type (max u v w))) :=
    ⟨fun r a x => Quotient.sound' <| AddConGen.Rel.of _ _ <|
      TensorProduct.Eqv.of_smul _ _ _⟩
  unfold piModuleFamilyFactorEquiv
  change (TensorProduct.AlgebraTensorModule.lift _) (a ⊗ₜ[∀ j, A j] x) = _
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  rfl

/-- The factor identification is compatible with a family of linear maps. -/
private lemma piModuleFamilyFactorEquiv_map_tmul (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ∀ i, ModuleCat.{max u v w} (A i))
    (f : ∀ i, M i ⟶ N i) (i : Fin n) (a : A i)
    (x : ∀ j, (M j : Type (max u v w))) :
    piModuleFamilyFactorEquiv.{w, v, u} n A N i
        (a ⊗ₜ[∀ j, A j] (fun j => (f j).hom (x j))) =
      (f i).hom (piModuleFamilyFactorEquiv.{w, v, u} n A M i
        (a ⊗ₜ[∀ j, A j] x)) := by
  rw [piModuleFamilyFactorEquiv_tmul, piModuleFamilyFactorEquiv_tmul]
  exact (f i).hom.map_smul a (x i) |>.symm

/-- The `i`-th factor of a product of factor modules is the `i`-th member of the family, as an
isomorphism of module objects. -/
private noncomputable def piModuleFamilyFactorIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i)) (i : Fin n) :
    (factorModuleFunctor.{w, v, u} n A).obj
      ((piModuleFamilyFunctor.{w, v, u} n A).obj M) i ≅ M i :=
  (piModuleFamilyFactorEquiv.{w, v, u} n A M i).toModuleIso

/-- The factor isomorphism of a product of modules is natural. -/
private lemma piModuleFamilyFactorIso_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M N : ∀ i, ModuleCat.{max u v w} (A i))
    (f : ∀ i, M i ⟶ N i) (i : Fin n) :
    ((factorModuleFunctor.{w, v, u} n A).map
      ((piModuleFamilyFunctor.{w, v, u} n A).map f) i) ≫
        (piModuleFamilyFactorIso.{w, v, u} n A N i).hom =
      (piModuleFamilyFactorIso.{w, v, u} n A M i).hom ≫ f i := by
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    change piModuleFamilyFactorEquiv.{w, v, u} n A N i
        ((a ⊗ₜ[∀ j, A j] fun j => (f j).hom (y j))) = _
    exact piModuleFamilyFactorEquiv_map_tmul.{w, v, u} n A M N f i a y
  | add x y hx hy =>
    let L := ModuleCat.Hom.hom
      ((factorModuleFunctor.{w, v, u} n A).map
        ((piModuleFamilyFunctor.{w, v, u} n A).map f) i ≫
        (piModuleFamilyFactorIso.{w, v, u} n A N i).hom)
    let R := ModuleCat.Hom.hom
      ((piModuleFamilyFactorIso.{w, v, u} n A M i).hom ≫ f i)
    calc
      L (x + y) = L x + L y := map_add L x y
      _ = R x + R y := by rw [hx, hy]
      _ = R (x + y) := (map_add R x y).symm

set_option linter.checkUnivs false in
/-- Modules over a finite product of rings are the product of the categories of modules over
the factors. -/
private noncomputable def moduleProductEquivalence (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    ModuleCat.{max u v w} (∀ i, A i) ≌ (∀ i, ModuleCat.{max u v w} (A i)) :=
  CategoryTheory.Equivalence.mk (factorModuleFunctor.{w, v, u} n A)
    (piModuleFamilyFunctor.{w, v, u} n A)
    (NatIso.ofComponents (piModuleFactorIso.{w, v, u} n A)
      (by intros M N f; exact (piModuleFactorIso_natural.{w, v, u} n A M N f).symm))
    (NatIso.ofComponents
      (fun M => CategoryTheory.Pi.isoMk (piModuleFamilyFactorIso.{w, v, u} n A M))
      (by intros M N f; funext i; exact piModuleFamilyFactorIso_natural.{w, v, u} n A M N f i))

end AdequateFunctor
