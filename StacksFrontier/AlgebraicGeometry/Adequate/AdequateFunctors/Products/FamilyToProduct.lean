module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Factors

/-!
# Adequate functors over finite products of rings: assembling a family of functors

A family of module-valued functors over the factors `A i` of a finite product of rings is
assembled into a single module-valued functor over the product, by taking products of the
componentwise values. This file constructs that functor, compares it with products of algebras,
with kernels and with universe lifts, and shows that it is adequate when every member of the
family is.

This is the second part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products`.
-/

@[expose] public section

open CategoryTheory
universe w v u u₁ v₁

namespace AdequateFunctor

open CategoryTheory.Limits

/-- The algebra structure over the `i`-th factor on the base change of an algebra. -/
instance factorAlgAlgebra (n : ℕ) (A : Fin n → Type u) [∀ i, CommRing (A i)]
    (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) :
    Algebra (A i) (factorAlg.{v, u} n A B i) :=
  Algebra.TensorProduct.rightAlgebra (R := ∀ j, A j) (A := B) (B := A i)

/-- The `i`-th factor of a product of factor algebras is the `i`-th member of the family. -/
noncomputable def factorAlgPiIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : ∀ i, CommAlgCat.{max u v} (A i)) (i : Fin n) :
    factorAlg n A (piAlgFamily n A B) i ≅ B i := by
  let R := ∀ j, A j
  letI : Algebra (A i) (TensorProduct R (∀ j, (B j : Type (max u v))) (A i)) :=
    Algebra.TensorProduct.rightAlgebra
  letI (j : Fin n) : Algebra R (B j) := Algebra.compHom (B j) (Pi.evalRingHom A j)
  letI : IsScalarTower R (A i) (B i) := .of_algebraMap_eq' rfl
  let q : (∀ j, (B j : Type (max u v))) →ₐ[R] B i :=
    { Pi.evalRingHom (fun j => (B j : Type (max u v))) i with commutes' := fun _ => rfl }
  let t := Algebra.TensorProduct.lift q (IsScalarTower.toAlgHom R (A i) (B i))
    (fun _ _ => Commute.all _ _)
  let f : factorAlg n A (piAlgFamily n A B) i →ₐ[A i] B i :=
    { t.toRingHom with
      commutes' := fun a => by
        change t ((1 : ∀ j, B j) ⊗ₜ[R] a) = algebraMap (A i) (B i) a
        simp [t] }
  let e := (TensorProduct.comm R (∀ j, (B j : Type (max u v))) (A i)).toAddEquiv.trans
    (piModuleFamilyFactorEquiv.{0, v, u} n A
      (fun j => ModuleCat.of (A j) (B j)) i).toAddEquiv
  have he : (f : factorAlg n A (piAlgFamily n A B) i → B i) = e := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero f).trans (map_zero e).symm
    | tmul b a =>
      change t (b ⊗ₜ[R] a) =
        piModuleFamilyFactorEquiv.{0, v, u} n A (fun j => ModuleCat.of (A j) (B j)) i
          (a ⊗ₜ[R] b)
      rw [piModuleFamilyFactorEquiv_tmul]
      simp only [t, Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply]
      rw [Algebra.smul_def]
      change b i * algebraMap (A i) (B i) a = algebraMap (A i) (B i) a * b i
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  exact CommAlgCat.isoMk (AlgEquiv.ofBijective f (he ▸ e.bijective))

/-- The factor identification of algebras sends `a ⊗ b` to `a • b`. -/
lemma factorAlgPiIso_hom_tmul (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : ∀ i, CommAlgCat.{max u v} (A i)) (i : Fin n)
    (b : ∀ j, B j) (a : A i) :
    (factorAlgPiIso n A B i).hom (b ⊗ₜ[∀ j, A j] a) =
      b i * algebraMap (A i) (B i) a := by
  simp [factorAlgPiIso]
  rfl

/-- The factor identification of algebras is natural. -/
private lemma factorAlgPiIso_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B C : ∀ i, CommAlgCat.{max u v} (A i))
    (f : ∀ i, B i ⟶ C i) (i : Fin n) :
    factorAlgMap n A _ _ (piAlgFamilyMap n A B C f) i ≫ (factorAlgPiIso n A C i).hom =
      (factorAlgPiIso n A B i).hom ≫ f i := by
  let : Algebra (A i) (TensorProduct (∀ j, A j) (∀ j, (B j : Type (max u v))) (A i)) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra (A i) (TensorProduct (∀ j, A j) (∀ j, (C j : Type (max u v))) (A i)) :=
    Algebra.TensorProduct.rightAlgebra
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    show (factorAlgPiIso n A C i).hom ((fun j => (f j).hom (b j)) ⊗ₜ[∀ j, A j] a) =
      (f i).hom ((factorAlgPiIso n A B i).hom (b ⊗ₜ[∀ j, A j] a))
    calc
      _ = (f i).hom (b i) * algebraMap (A i) (C i) a :=
        factorAlgPiIso_hom_tmul n A C i _ a
      _ = (f i).hom (b i * algebraMap (A i) (B i) a) := by
        rw [map_mul, AlgHom.commutes]
      _ = _ := congrArg (f i).hom (factorAlgPiIso_hom_tmul n A B i b a).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The value over the product ring of a family of module-valued functors, at an algebra. -/
noncomputable def moduleFamilyProductObj (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i))
    (M : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A B i)) :
    ModuleCat.{w} (B : Type (max u v)) := by
  let R := ∀ j, A j
  let S : Fin n → Type (max u v) := fun i => TensorProduct R (B : Type (max u v)) (A i)
  letI (i : Fin n) : Algebra R (S i) :=
    Algebra.TensorProduct.leftAlgebra (R := R) (S := R) (A := B) (B := A i)
  letI : Algebra R (∀ i, S i) := Pi.algebra (Fin n) S
  let e := piAlgFactorAlgEquiv.{v, u} n A B
  letI (i : Fin n) : Module (S i) (M i : Type w) := inferInstance
  letI (i : Fin n) : Module (∀ j, S j) (M i : Type w) :=
    Module.compHom (M i : Type w) (Pi.evalRingHom S i)
  letI : Module (∀ i, S i) (∀ i, (M i : Type w)) :=
    inferInstance
  letI : Module (B : Type (max u v)) (∀ i, (M i : Type w)) :=
    Module.compHom (∀ i, (M i : Type w)) e.toRingEquiv.toRingHom
  exact ModuleCat.of (B : Type (max u v)) (∀ i, (M i : Type w))

/-- Scalar multiplication in the assembled module is componentwise, through
`AdequateFunctor.piAlgFactorAlgEquiv`. -/
lemma moduleFamilyProductObj_smul_apply (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i))
    (M : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A B i))
    (b : B) (m : moduleFamilyProductObj.{w, v, u} n A B M) (i : Fin n) :
    (b • m) i = piAlgFactorAlgEquiv n A B b i • m i := rfl

/-- The transition map of the assembled module-valued functor. -/
noncomputable def moduleFamilyProductMap (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {B C : CommAlgCat.{max u v} (∀ i, A i)}
    (f : B ⟶ C) (M : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A B i))
    (N : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A C i))
    (g : ∀ i, M i ⟶ (ModuleCat.restrictScalars
      (factorAlgMap.{v, u} n A B C f i).hom.toRingHom).obj (N i)) :
    moduleFamilyProductObj.{w, v, u} n A B M ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (moduleFamilyProductObj.{w, v, u} n A C N) := by
  let R := ∀ j, A j
  let SB : Fin n → Type (max u v) := fun i => TensorProduct R (B : Type (max u v)) (A i)
  let SC : Fin n → Type (max u v) := fun i => TensorProduct R (C : Type (max u v)) (A i)
  letI (i : Fin n) : Algebra R (SB i) :=
    Algebra.TensorProduct.leftAlgebra (R := R) (S := R) (A := B) (B := A i)
  letI : Algebra R (∀ i, SB i) := Pi.algebra (Fin n) SB
  letI (i : Fin n) : Algebra R (SC i) :=
    Algebra.TensorProduct.leftAlgebra (R := R) (S := R) (A := C) (B := A i)
  letI : Algebra R (∀ i, SC i) := Pi.algebra (Fin n) SC
  let eB := piAlgFactorAlgEquiv.{v, u} n A B
  let eC := piAlgFactorAlgEquiv.{v, u} n A C
  letI (i : Fin n) : Module (SB i) (M i : Type w) := inferInstance
  letI (i : Fin n) : Module (SC i) (N i : Type w) := inferInstance
  letI : Module (∀ i, SB i) (∀ i, (M i : Type w)) := inferInstance
  letI : Module (B : Type (max u v)) (∀ i, (M i : Type w)) :=
    Module.compHom (∀ i, (M i : Type w)) eB.toRingEquiv.toRingHom
  letI : Module (∀ i, SC i) (∀ i, (N i : Type w)) := inferInstance
  letI : Module (C : Type (max u v)) (∀ i, (N i : Type w)) :=
    Module.compHom (∀ i, (N i : Type w)) eC.toRingEquiv.toRingHom
  letI : Module (B : Type (max u v)) (∀ i, (N i : Type w)) :=
    Module.compHom (∀ i, (N i : Type w)) f.hom.toRingHom
  exact ModuleCat.ofHom
    (X := moduleFamilyProductObj.{w, v, u} n A B M)
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj
      (moduleFamilyProductObj.{w, v, u} n A C N)) {
    toFun := fun x i => (g i).hom (x i)
    map_add' := by intro x y; funext i; exact map_add (g i).hom (x i) (y i)
    map_smul' := by
      intro b x
      funext i
      change (g i).hom (eB.toRingEquiv b i • x i) =
        eC.toRingEquiv (f.hom b) i • (g i).hom (x i)
      rw [(g i).hom.map_smul]
      have hn := piAlgFactorAlgEquiv_natural.{v, u} n A B C f b i
      exact congrArg (fun z => z • (g i).hom (x i)) hn.symm }

/-- Base change to the `i`-th factor sends the identity to the identity. -/
lemma factorAlgMap_id (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) :
    factorAlgMap.{v, u} n A B B (𝟙 B) i = 𝟙 (factorAlg.{v, u} n A B i) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp [factorAlgMap]
  | tmul b a => simp [factorAlgMap]
  | add x y hx hy => simp [factorAlgMap]

/-- Base change to the `i`-th factor sends the identity to the identity, read in the doubly
opposite category. -/
lemma factorAlgMap_id_opop (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) :
    (factorAlgMap.{v, u} n A B B (𝟙 B) i).op.op = 𝟙 _ := by
  simpa using congrArg (fun q => q.op.op) (factorAlgMap_id.{v, u} n A B i)

-- The composition law expands the scalar restrictions through the tensor-product algebras.
/-- Assembling a family of module-valued functors over the factors into one module-valued
functor over the product ring. -/
noncomputable def familyToProductFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    (∀ i, ModuleValuedFunctor.{w, v} (A i)) ⥤
      ModuleValuedFunctor.{w, v} (∀ i, A i) where
  obj G := {
    obj X :=
      let B := X.unop.unop
      moduleFamilyProductObj.{w, v, u} n A B
        (fun i => (G i).obj
          (Opposite.op (Opposite.op (factorAlg.{v, u} n A B i))))
    map {X Y} f := by
      let B := X.unop.unop
      let C := Y.unop.unop
      let f' : B ⟶ C := f.unop.unop
      exact moduleFamilyProductMap.{w, v, u} n A f'
        (fun i => (G i).obj (Opposite.op (Opposite.op (factorAlg.{v, u} n A B i))))
        (fun i => (G i).obj (Opposite.op (Opposite.op (factorAlg.{v, u} n A C i))))
        (fun i => (G i).map
          (factorAlgMap.{v, u} n A B C f' i).op.op)
    map_id X := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply funext
      intro i
      change (G i).map (factorAlgMap n A X.unop.unop X.unop.unop (𝟙 _) i).op.op
        (x i) = x i
      rw [factorAlgMap_id_opop, (G i).map_id]
      rfl
    map_comp {X Y Z} f g := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply funext
      intro i
      change (G i).map
        (factorAlgMap n A X.unop.unop Z.unop.unop (f.unop.unop ≫ g.unop.unop) i).op.op
          (x i) =
        (G i).map (factorAlgMap n A Y.unop.unop Z.unop.unop g.unop.unop i).op.op
          ((G i).map (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i).op.op (x i))
      have hfac : factorAlgMap.{v, u} n A X.unop.unop Z.unop.unop
          (f.unop.unop ≫ g.unop.unop) i =
          factorAlgMap.{v, u} n A X.unop.unop Y.unop.unop f.unop.unop i ≫
            factorAlgMap.{v, u} n A Y.unop.unop Z.unop.unop g.unop.unop i :=
        congrFun ((factorAlgFunctor.{v, u} n A).map_comp f.unop.unop g.unop.unop) i
      rw [congrArg (fun q => q.op.op) hfac]
      exact (G i).map_comp_apply
        (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i).op.op
        (factorAlgMap n A Y.unop.unop Z.unop.unop g.unop.unop i).op.op (x i)
  }
  map {G H} η := {
    app X := by
      let B := X.unop.unop
      let M : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A B i) := fun i =>
        (G i).obj (Opposite.op (Opposite.op (factorAlg.{v, u} n A B i)))
      let N : ∀ i, ModuleCat.{w} (factorAlg.{v, u} n A B i) := fun i =>
        (H i).obj (Opposite.op (Opposite.op (factorAlg.{v, u} n A B i)))
      exact moduleFamilyProductMap.{w, v, u} n A (𝟙 B) M N (fun i => by
        let q := factorAlgMap.{v, u} n A B B (𝟙 B) i
        have hq : q.hom.toRingHom = RingHom.id (factorAlg.{v, u} n A B i) :=
          congrArg (fun k => k.hom.toRingHom) (factorAlgMap_id.{v, u} n A B i)
        exact (η i).app (Opposite.op (Opposite.op (factorAlg.{v, u} n A B i))) ≫
          (ModuleCat.restrictScalarsId'App q.hom.toRingHom hq (N i)).inv)
    naturality := by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply funext
      intro i
      exact PresheafOfModules.naturality_apply (η i)
        (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i).op.op (x i)
  }
  map_id G := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro x
    apply funext
    intro i
    rfl
  map_comp η θ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply DFunLike.ext
    intro x
    apply funext
    intro i
    rfl

/-- The assembled functor commutes with the universe lift. -/
private noncomputable def familyToProductUliftIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i)) :
    (presheafOfModulesUliftFunctor.{max u v}
      (algebraRingDiagram.{v} (∀ i, A i))).obj
        ((familyToProductFunctor n A).obj G) ≅
      (familyToProductFunctor n A).obj (fun i =>
        (presheafOfModulesUliftFunctor.{max u v}
          (algebraRingDiagram.{v} (A i))).obj (G i)) := by
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · exact {
      hom := ConcreteCategory.ofHom {
        toFun := fun x i => ULift.up (x.down i)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
      inv := ConcreteCategory.ofHom {
        toFun := fun x => ULift.up (fun i => (x i).down)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by
        ext x
        funext i
        rfl }
  · intros
    ext x
    funext i
    rfl

/-- The assembled functor commutes with kernels. -/
private noncomputable def familyToProductKernelIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G H : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (f : G ⟶ H) :
    (familyToProductFunctor n A).obj (fun i => CategoryTheory.Limits.kernel (f i)) ≅
      CategoryTheory.Limits.kernel ((familyToProductFunctor n A).map f) := by
  let P := familyToProductFunctor n A
  let k : (fun i => CategoryTheory.Limits.kernel (f i)) ⟶ G :=
    fun i => CategoryTheory.Limits.kernel.ι (f i)
  have hzero : P.map k ≫ P.map f = 0 := by
    ext X x
    funext i
    exact congrArg (fun g => g.app
      (Opposite.op (Opposite.op (factorAlg n A X.unop.unop i))) (x i))
      (CategoryTheory.Limits.kernel.condition (f i))
  let c := CategoryTheory.Limits.KernelFork.ofι (P.map k) hzero
  have hc : CategoryTheory.Limits.IsLimit c := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro X
    have hex : Function.Exact ((P.map k).app X).hom ((P.map f).app X).hom := by
      intro x
      constructor
      · intro hx
        have h (i : Fin n) := (kernelApp_exact (f i)
          (Opposite.op (Opposite.op (factorAlg n A X.unop.unop i)))) (x i)
        choose y hy using fun i => (h i).mp (congrFun hx i)
        exact ⟨y, funext hy⟩
      · rintro ⟨y, rfl⟩
        exact congrArg (fun g => g.app X y) hzero
    have hinj : Function.Injective ((P.map k).app X).hom :=
      Function.Injective.piMap fun i => PresheafOfModules.injective_of_mono
        (CategoryTheory.Limits.kernel.ι (f i))
        (Opposite.op (Opposite.op (factorAlg n A X.unop.unop i)))
    exact (isLimitMapConeForkEquiv' (PresheafOfModules.evaluation _ X) hzero).symm
      (ModuleCat.isLimitKernelFork _ _ hex hinj)
  have e := hc.conePointUniqueUpToIso (CategoryTheory.Limits.kernelIsKernel (P.map f))
  exact e

/-- The comparison map from the value of the assembled functor to the product of the values. -/
noncomputable def familyToProductPiHom (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (B : ∀ i, CommAlgCat.{max u v} (A i)) :
    ((familyToProductFunctor n A).obj G).obj (Opposite.op (Opposite.op (piAlgFamily n A B))) ⟶
      ModuleCat.of (∀ i, (B i : Type (max u v)))
        (∀ i, ((G i).obj (Opposite.op (Opposite.op (B i))) : Type w)) := by
  exact ConcreteCategory.ofHom (C := ModuleCat (∀ i, (B i : Type (max u v)))) {
    toFun := fun x i => (G i).map (factorAlgPiIso n A B i).hom.op.op (x i)
    map_add' := by intro x y; funext i; exact map_add _ _ _
    map_smul' := by
      intro b x
      funext i
      change (G i).map (factorAlgPiIso n A B i).hom.op.op
        (piAlgFactorAlgEquiv n A (piAlgFamily n A B) b i • x i) =
          b i • (G i).map (factorAlgPiIso n A B i).hom.op.op (x i)
      rw [(G i).map_smul]
      change (factorAlgPiIso n A B i).hom
        (piAlgFactorAlgEquiv n A (piAlgFamily n A B) b i) • _ = _
      rw [piAlgFactorAlgEquiv_apply, factorAlgPiIso_hom_tmul]
      simp }

/-- The value of the assembled functor at a product of factor algebras is the product of the
values. -/
noncomputable def familyToProductPiIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (B : ∀ i, CommAlgCat.{max u v} (A i)) :
    ((familyToProductFunctor n A).obj G).obj (Opposite.op (Opposite.op (piAlgFamily n A B))) ≅
      ModuleCat.of (∀ i, (B i : Type (max u v)))
        (∀ i, ((G i).obj (Opposite.op (Opposite.op (B i))) : Type w)) := by
  have h (i : Fin n) : Function.Bijective
      (fun x => (G i).map (factorAlgPiIso n A B i).hom.op.op x) :=
    ConcreteCategory.bijective_of_isIso ((G i).presheaf.map (factorAlgPiIso n A B i).hom.op.op)
  apply LinearEquiv.toModuleIso (LinearEquiv.ofBijective (familyToProductPiHom n A G B).hom ?_)
  constructor
  · intro x y hxy
    apply funext
    intro i
    exact (h i).1 (congrFun hxy i)
  · intro y
    choose x hx using fun i => (h i).2 (y i)
    exact ⟨x, funext hx⟩

/-- The value identification of the assembled functor is computed coordinatewise. -/
private lemma familyToProductPiIso_hom_apply (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (B : ∀ i, CommAlgCat.{max u v} (A i))
    (x : ((familyToProductFunctor n A).obj G).obj
      (Opposite.op (Opposite.op (piAlgFamily n A B)))) (i : Fin n) :
    (familyToProductPiIso n A G B).hom x i =
      (G i).map (factorAlgPiIso n A B i).hom.op.op (x i) := rfl

/-- The value identification of the assembled functor is natural in the algebra. -/
lemma familyToProductPiIso_natural_algebra (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (B C : ∀ i, CommAlgCat.{max u v} (A i)) (f : ∀ i, B i ⟶ C i)
    (x : ((familyToProductFunctor n A).obj G).obj
      (Opposite.op (Opposite.op (piAlgFamily n A B)))) (i : Fin n) :
    (familyToProductPiIso n A G C).hom
      (((familyToProductFunctor n A).obj G).map (piAlgFamilyMap n A B C f).op.op x) i =
        (G i).map (f i).op.op ((familyToProductPiIso n A G B).hom x i) := by
  show (G i).map (factorAlgPiIso n A C i).hom.op.op
    ((G i).map (factorAlgMap n A _ _ (piAlgFamilyMap n A B C f) i).op.op (x i)) =
      (G i).map (f i).op.op ((G i).map (factorAlgPiIso n A B i).hom.op.op (x i))
  rw [← (G i).map_comp_apply, ← (G i).map_comp_apply]
  exact (G i).congr_map_apply
    (congrArg (fun f => f.op.op) (factorAlgPiIso_natural n A B C f i)) (x i)

/-- The value identification of the assembled functor is natural in the family. -/
lemma familyToProductPiIso_natural_family (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G H : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (η : G ⟶ H) (B : ∀ i, CommAlgCat.{max u v} (A i))
    (x : ((familyToProductFunctor n A).obj G).obj
      (Opposite.op (Opposite.op (piAlgFamily n A B)))) (i : Fin n) :
    (familyToProductPiIso n A H B).hom
      (((familyToProductFunctor n A).map η).app
        (Opposite.op (Opposite.op (piAlgFamily n A B))) x) i =
      (η i).app (Opposite.op (Opposite.op (B i))) ((familyToProductPiIso n A G B).hom x i) :=
  (PresheafOfModules.naturality_apply (η i) (factorAlgPiIso n A B i).hom.op.op (x i)).symm


/-- The assembled functor of a family of module-valued functors of modules is the
module-valued functor of the product module. -/
private noncomputable def productExtensionEquiv (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i))
    (B : CommAlgCat.{max u v} (∀ i, A i)) :
    ((moduleExtension.{max u v w, v} (∀ i, A i)
      (piModuleFamily.{w, v, u} n A M)).obj (Opposite.op (Opposite.op B))) ≃ₗ[B]
    (((familyToProductFunctor n A).obj
      (fun i => moduleExtension.{max u v w, v} (A i) (M i))).obj
        (Opposite.op (Opposite.op B))) := by
  let R := ∀ i, A i
  letI (i : Fin n) : Module R (M i) := Module.compHom _ (Pi.evalRingHom A i)
  letI (i : Fin n) : IsScalarTower R (A i) (M i) := IsScalarTower.of_compHom _ _ _
  let e := (TensorProduct.piRight R B B (fun i => (M i : Type (max u v w)))).trans
    (LinearEquiv.piCongrRight fun i =>
      (Algebra.IsPushout.cancelBaseChange R B (A i) (factorAlg n A B i) (M i)).symm)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro b x
  funext i
  change e (b • x) i = piAlgFactorAlgEquiv n A B b i • e x i
  rw [map_smul, piAlgFactorAlgEquiv_apply]
  exact (algebraMap_smul (factorAlg n A B i) b (e x i)).symm

/-- The identification of assembled module extensions is computed on pure tensors. -/
private lemma productExtensionEquiv_tmul (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i))
    (B : CommAlgCat.{max u v} (∀ i, A i)) (b : B) (m : ∀ i, M i) (i : Fin n) :
    productExtensionEquiv.{w, v, u} n A M B (b ⊗ₜ[∀ i, A i] m) i =
      (b ⊗ₜ[∀ i, A i] (1 : A i)) ⊗ₜ[A i] m i := by
  let : Module (∀ j, A j) (M i) := Module.compHom _ (Pi.evalRingHom A i)
  let : IsScalarTower (∀ j, A j) (A i) (M i) := IsScalarTower.of_compHom _ _ _
  show (Algebra.IsPushout.cancelBaseChange (∀ i, A i) B (A i)
    (factorAlg n A B i) (M i)).symm (b ⊗ₜ[∀ i, A i] m i) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

/-- The assembled functor of a family of module extensions is the module extension of the
product module. -/
private noncomputable def productExtensionIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ∀ i, ModuleCat.{max u v w} (A i)) :
    moduleExtension.{max u v w, v} (∀ i, A i) (piModuleFamily.{w, v, u} n A M) ≅
      (familyToProductFunctor n A).obj
        (fun i => moduleExtension.{max u v w, v} (A i) (M i)) := by
  refine PresheafOfModules.isoMk
    (fun X => (productExtensionEquiv.{w, v, u} n A M X.unop.unop).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul b m =>
    funext i
    change productExtensionEquiv.{w, v, u} n A M Y.unop.unop
      (f.unop.unop.hom b ⊗ₜ[∀ i, A i] m) i =
      (moduleExtension (A i) (M i)).map
        (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i).op.op
        (productExtensionEquiv.{w, v, u} n A M X.unop.unop (b ⊗ₜ[∀ i, A i] m) i)
    refine Eq.trans (productExtensionEquiv_tmul n A M Y.unop.unop _ m i) ?_
    refine Eq.trans ?_ (congrArg ((moduleExtension (A i) (M i)).map
      (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i).op.op)
      (productExtensionEquiv_tmul n A M X.unop.unop b m i).symm)
    rw [moduleExtension_map_tmul]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Assembling a family of adequate functors gives an adequate functor over the product
ring. -/
lemma isAdequate_familyToProduct (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (hG : ∀ i, IsAdequate (𝟭 _) (G i)) :
    IsAdequate (𝟭 _) ((familyToProductFunctor n A).obj G) := by
  choose M N f hf using hG
  classical
  let e := fun i => (hf i).some
  let : HasKernels (ModuleValuedFunctor.{max u v w, v} (∀ i, A i)) := inferInstance
  let P := familyToProductFunctor.{max u v w, v, u} n A
  let g : (fun i => moduleExtension (A i) (M i)) ⟶
      (fun i => moduleExtension (A i) (N i)) :=
    fun i => (moduleExtensionFunctor (A i)).map (f i)
  let t : moduleExtension.{max u v w, v} (∀ i, A i)
      (piModuleFamily.{w, v, u} n A M) ⟶
      moduleExtension.{max u v w, v} (∀ i, A i)
        (piModuleFamily.{w, v, u} n A N) :=
    (productExtensionIso.{w, v, u} n A M).hom ≫ P.map g ≫
      (productExtensionIso.{w, v, u} n A N).inv
  have ht : IsAdequate (𝟭 _) (kernel t) := (isAdequate_iff _).2
    ⟨piModuleFamily.{w, v, u} n A M, piModuleFamily.{w, v, u} n A N, t, ⟨Iso.refl _⟩⟩
  have ee : (presheafOfModulesUliftFunctor.{max u v}
      (algebraRingDiagram.{v} (∀ i, A i))).obj
        ((familyToProductFunctor n A).obj G) ≅ kernel t :=
    familyToProductUliftIso n A G ≪≫ P.mapIso (CategoryTheory.Pi.isoMk e) ≪≫
      familyToProductKernelIso n A _ _ g ≪≫
      kernel.mapIso (P.map g) t (productExtensionIso.{w, v, u} n A M).symm
        (productExtensionIso.{w, v, u} n A N).symm (by simp [t])
  obtain ⟨M', N', f', ⟨e'⟩⟩ := IsAdequate.of_iso ht ee
  exact ⟨M', N', f', ⟨(presheafOfModulesUliftIso _ _).symm ≪≫ e'⟩⟩

end AdequateFunctor
