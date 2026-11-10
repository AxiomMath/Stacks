module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.Factors
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products.FamilyToProduct

/-!
# Adequate functors over finite products of rings: the equivalence

The restriction of an adequate functor over a finite product of rings to the factors, and the
assembly of a family of adequate functors over the factors, are mutually inverse up to natural
isomorphism. This file builds the unit and counit isomorphisms and the resulting equivalence of
categories (Stacks Tag 06VB).

## Main definitions

* `AdequateFunctor.ProductEquivalenceSpecification` records a componentwise comparison
  natural in both the algebra and the factor functors.

## Main results

* `AdequateFunctor.adequateFunctorProductEquivalence` gives the equivalence of categories
  of adequate functors, together with its componentwise evaluation on products of algebras.

This is the third part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Products`.

## References

* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
-/

@[expose] public section

open CategoryTheory
universe w v u u₁ v₁

namespace AdequateFunctor

open CategoryTheory.Limits

/-- The projection of an algebra over the product ring onto its `i`-th factor. -/
private def factorProjection (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (B : CommAlgCat.{max u v} (∀ i, A i)) (i : Fin n) :
    B ⟶ (evalAlgFunctor n A i).obj (factorAlg n A B i) := by
  let q : B →+* TensorProduct (∀ j, A j) (B : Type (max u v)) (A i) :=
    Algebra.TensorProduct.includeLeftRingHom
  letI : Algebra (∀ j, A j) (factorAlg n A B i) :=
    Algebra.compHom (factorAlg n A B i) (Pi.evalRingHom A i)
  exact CommAlgCat.ofHom (R := ∀ j, A j) {
    toRingHom := q
    commutes' := by
      intro a
      change (algebraMap (∀ j, A j) B a) ⊗ₜ[∀ j, A j] (1 : A i) =
        (1 : B) ⊗ₜ[∀ j, A j] a i
      have h := TensorProduct.smul_tmul (R := ∀ j, A j) a (1 : B) (1 : A i)
      simp only [Algebra.smul_def] at h
      change ((algebraMap (∀ j, A j) B a) * 1) ⊗ₜ[∀ j, A j] (1 : A i) =
        (1 : B) ⊗ₜ[∀ j, A j] (a i * 1) at h
      simpa only [mul_one] using h }

/-- The projection onto the `i`-th factor is natural. -/
private lemma factorProjection_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {B C : CommAlgCat.{max u v} (∀ i, A i)}
    (f : B ⟶ C) (i : Fin n) :
    factorProjection n A B i ≫ (evalAlgFunctor n A i).map (factorAlgMap n A B C f i) =
      f ≫ factorProjection n A C i := by
  apply CommAlgCat.hom_ext
  ext b
  rfl

/-- The unit comparing a module-valued functor with the assembly of its restrictions. -/
private noncomputable def productRestrictionUnit (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (F : ModuleValuedFunctor.{w, v} (∀ i, A i)) :
    F ⟶ (familyToProductFunctor n A).obj (fun i => (restrictModuleFunctor n A i).obj F) where
  app X := ModuleCat.ofHom (X := F.obj X)
    (Y := ((familyToProductFunctor n A).obj (fun i => (restrictModuleFunctor n A i).obj F)).obj X) {
    toFun := fun x i => F.map (factorProjection n A X.unop.unop i).op.op x
    map_add' := by intro x y; funext i; exact map_add _ _ _
    map_smul' := by
      intro b x
      funext i
      refine Eq.trans (F.map_smul (factorProjection n A X.unop.unop i).op.op b x) ?_
      exact (moduleFamilyProductObj_smul_apply n A X.unop.unop _ b
        (fun j => F.map (factorProjection n A X.unop.unop j).op.op x) i).symm }
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change F.map (factorProjection n A Y.unop.unop i).op.op (F.map f x) =
      F.map ((evalAlgFunctor n A i).map
        (factorAlgMap n A X.unop.unop Y.unop.unop f.unop.unop i)).op.op
        (F.map (factorProjection n A X.unop.unop i).op.op x)
    rw [← F.map_comp_apply, ← F.map_comp_apply]
    exact F.congr_map_apply
      (congrArg (fun f => f.op.op) (factorProjection_natural n A f.unop.unop i).symm) x

/-- The restriction unit is natural. -/
private lemma productRestrictionUnit_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {F G : ModuleValuedFunctor.{w, v} (∀ i, A i)}
    (η : F ⟶ G) (B : CommAlgCat.{max u v} (∀ i, A i)) (x : F.obj (Opposite.op (Opposite.op B)))
    (i : Fin n) :
    (productRestrictionUnit n A G).app _ (η.app _ x) i =
      η.app _ ((productRestrictionUnit n A F).app _ x i) :=
  (PresheafOfModules.naturality_apply η (factorProjection n A B i).op.op x).symm

/-- The restriction unit is bijective on a module extension. -/
private lemma productRestrictionUnit_extension_bijective (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (M : ModuleCat.{max u v w} (∀ i, A i))
    (B : CommAlgCat.{max u v} (∀ i, A i)) :
    Function.Bijective ((productRestrictionUnit n A
      (moduleExtension.{max u v w, v} (∀ i, A i) M)).app
        (Opposite.op (Opposite.op B))) := by
  let R := ∀ i, A i
  let K := fun i => (evalAlgFunctor n A i).obj (factorAlg n A B i)
  let (i : Fin n) : Algebra R (K i) := (K i).algebra
  let eAdd : B ≃+ (∀ i, K i) := by
    let (i : Fin n) : Algebra R (TensorProduct R (B : Type (max u v)) (A i)) :=
      Algebra.TensorProduct.leftAlgebra
    let : Algebra R (∀ i, TensorProduct R (B : Type (max u v)) (A i)) :=
      Pi.algebra (Fin n) _
    exact (piAlgFactorAlgEquiv n A B).toAddEquiv
  let L := LinearMap.pi (fun i => (factorProjection n A B i).hom.toLinearMap)
  have hL : (L : B → ∀ i, K i) = eAdd := by
    funext b i
    exact (piAlgFactorAlgEquiv_apply n A B b i).symm
  let e₀ := LinearEquiv.ofBijective L (hL.symm ▸ eAdd.bijective)
  let e := (TensorProduct.congr e₀ (LinearEquiv.refl R M)).trans
    (TensorProduct.piLeft R M (fun i => (K i : Type (max u v))))
  have he : ⇑((productRestrictionUnit n A
      (moduleExtension.{max u v w, v} R M)).app
        (Opposite.op (Opposite.op B))) = e := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      funext i
      rfl
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      rfl
  exact he ▸ e.bijective


/-- The restriction unit of a source is injective if that of the target is and the map is mono. -/
private lemma productRestrictionUnit_injective_of_mono (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {F G : ModuleValuedFunctor.{w, v} (∀ i, A i)}
    (f : F ⟶ G) [Mono f] (B : CommAlgCat.{max u v} (∀ i, A i))
    (hG : Function.Injective ((productRestrictionUnit n A G).app (Opposite.op (Opposite.op B)))) :
    Function.Injective ((productRestrictionUnit n A F).app (Opposite.op (Opposite.op B))) := by
  intro x y hxy
  apply PresheafOfModules.injective_of_mono f (Opposite.op (Opposite.op B))
  apply hG
  funext i
  rw [productRestrictionUnit_natural, productRestrictionUnit_natural]
  exact congrArg (f.app _) (congrFun hxy i)

/-- The restriction unit is bijective on a kernel of module extensions. -/
private lemma productRestrictionUnit_kernel_bijective (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {F G : ModuleValuedFunctor.{w, v} (∀ i, A i)}
    (f : F ⟶ G) (B : CommAlgCat.{max u v} (∀ i, A i))
    (hF : Function.Bijective ((productRestrictionUnit n A F).app (Opposite.op (Opposite.op B))))
    (hG : Function.Injective ((productRestrictionUnit n A G).app (Opposite.op (Opposite.op B)))) :
    Function.Bijective ((productRestrictionUnit n A (kernel f)).app
      (Opposite.op (Opposite.op B))) := by
  let X := Opposite.op (Opposite.op B)
  let Xi := fun i => Opposite.op (Opposite.op ((evalAlgFunctor n A i).obj (factorAlg n A B i)))
  let k := kernel.ι f
  refine ⟨productRestrictionUnit_injective_of_mono n A k B hF.1, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := hF.2 (fun i => k.app (Xi i) (y i))
    have hzero : f.app X z = 0 := by
      apply hG
      funext i
      rw [productRestrictionUnit_natural, map_zero]
      change f.app (Xi i) ((productRestrictionUnit n A F).app X z i) = 0
      rw [congrFun hz i]
      exact congrArg (fun q => q.app (Xi i) (y i)) (kernel.condition f)
    obtain ⟨x, hx⟩ := (kernelApp_exact f X z).mp hzero
    refine ⟨x, ?_⟩
    funext i
    apply PresheafOfModules.injective_of_mono k (Xi i)
    exact (productRestrictionUnit_natural n A k B x i).symm.trans
      ((congrArg (fun z => (productRestrictionUnit n A F).app X z i) hx).trans
        (congrFun hz i))

/-- Bijectivity of the restriction unit transports along an isomorphism of functors. -/
private lemma productRestrictionUnit_bijective_of_iso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] {F G : ModuleValuedFunctor.{w, v} (∀ i, A i)}
    (e : F ≅ G) (B : CommAlgCat.{max u v} (∀ i, A i))
    (hG : Function.Bijective ((productRestrictionUnit n A G).app (Opposite.op (Opposite.op B)))) :
    Function.Bijective ((productRestrictionUnit n A F).app (Opposite.op (Opposite.op B))) := by
  let X := Opposite.op (Opposite.op B)
  let Xi := fun i => Opposite.op (Opposite.op ((evalAlgFunctor n A i).obj (factorAlg n A B i)))
  refine ⟨productRestrictionUnit_injective_of_mono n A e.hom B hG.1, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := hG.2 (fun i => e.hom.app (Xi i) (y i))
    refine ⟨e.inv.app X z, ?_⟩
    funext i
    rw [productRestrictionUnit_natural, congrFun hz i]
    exact congrArg (fun q => q.app (Xi i) (y i)) e.hom_inv_id

/-- The restriction unit is bijective on an adequate functor. -/
private lemma productRestrictionUnit_adequate_bijective (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (F : ModuleValuedFunctor.{w, v} (∀ i, A i))
    (hF : IsAdequate (𝟭 _) F) (B : CommAlgCat.{max u v} (∀ i, A i)) :
    Function.Bijective ((productRestrictionUnit n A F).app (Opposite.op (Opposite.op B))) := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hF
  have hh := productRestrictionUnit_bijective_of_iso n A e B
    (productRestrictionUnit_kernel_bijective n A _ B
      (productRestrictionUnit_extension_bijective n A M B)
      (productRestrictionUnit_extension_bijective n A N B).1)
  constructor
  · intro x y hxy
    have ht : (ULift.up x : ULift.{max u v} _) = ULift.up y := by
      apply hh.1
      funext i
      exact congrArg ULift.up (congrFun hxy i)
    exact congrArg ULift.down ht
  · intro y
    obtain ⟨x, hx⟩ := hh.2 (fun i => ULift.up (y i))
    exact ⟨x.down, funext (fun i => congrArg ULift.down (congrFun hx i))⟩


/-- The `i`-th factor of an algebra read over the product ring is the algebra itself. -/
private noncomputable def factorEvalIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) (B : CommAlgCat.{max u v} (A i)) :
    factorAlg n A ((evalAlgFunctor n A i).obj B) i ≅ B := by
  let R := ∀ j, A j
  letI : Algebra R B := Algebra.compHom B (Pi.evalRingHom A i)
  letI : IsScalarTower R (A i) B := .of_algebraMap_eq' rfl
  letI : Algebra (A i) (TensorProduct R (B : Type (max u v)) (A i)) :=
    Algebra.TensorProduct.rightAlgebra
  let t := Algebra.TensorProduct.lift (AlgHom.id R B)
    (IsScalarTower.toAlgHom R (A i) B) (fun _ _ => Commute.all _ _)
  let f : factorAlg n A ((evalAlgFunctor n A i).obj B) i →ₐ[A i] B :=
    { t.toRingHom with
      commutes' := fun a => by
        change t ((1 : B) ⊗ₜ[R] a) = algebraMap (A i) B a
        simp [t] }
  have ht (b : B) (a : A i) :
      (b ⊗ₜ[R] a) = (b * algebraMap (A i) B a) ⊗ₜ[R] (1 : A i) := by
    have h := TensorProduct.smul_tmul (R := R) (Pi.single i a) b (1 : A i)
    simp only [Algebra.smul_def] at h
    change (algebraMap (A i) B ((Pi.single i a) i) * b) ⊗ₜ[R] (1 : A i) =
      b ⊗ₜ[R] ((Pi.single i a) i * 1) at h
    simpa only [Pi.single_eq_same, mul_one, mul_comm] using h.symm
  -- Stated over the spelled-out tensor product rather than over
  -- `factorAlg n A ((evalAlgFunctor n A i).obj B) i`, so that the induction's `b` carries the
  -- scalar structure of `B` itself.
  have hinv (x : TensorProduct R (B : Type (max u v)) (A i)) :
      f x ⊗ₜ[R] (1 : A i) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      change t (b ⊗ₜ[R] a) ⊗ₜ[R] (1 : A i) = _
      have he : t (b ⊗ₜ[R] a) = Mul.mul (α := B) b (algebraMap (A i) B a) :=
        Algebra.TensorProduct.lift_tmul _ _ _ b a
      exact (congrArg (fun b => b ⊗ₜ[R] (1 : A i)) he).trans (ht b a).symm
    | add x y hx hy =>
      change t (x + y) ⊗ₜ[R] (1 : A i) = x + y
      rw [map_add, TensorProduct.add_tmul]
      exact congrArg₂ (· + ·) hx hy
  apply CommAlgCat.isoMk (AlgEquiv.ofBijective f ?_)
  constructor
  · intro x y hxy
    rw [← hinv x, ← hinv y, hxy]
  · intro b
    refine ⟨b ⊗ₜ[R] (1 : A i), ?_⟩
    change t (b ⊗ₜ[R] (1 : A i)) = b
    simp [t]

/-- The factor identification of a read-back algebra is computed on pure tensors. -/
private lemma factorEvalIso_hom_tmul (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) (B : CommAlgCat.{max u v} (A i))
    (b : B) (a : A i) :
    (factorEvalIso n A i B).hom (b ⊗ₜ[∀ j, A j] a) =
      b * algebraMap (A i) B a := by
  let : Algebra (∀ j, A j) B := Algebra.compHom B (Pi.evalRingHom A i)
  let : IsScalarTower (∀ j, A j) (A i) B := .of_algebraMap_eq' rfl
  exact Algebra.TensorProduct.lift_tmul (AlgHom.id (∀ j, A j) B)
    (IsScalarTower.toAlgHom (∀ j, A j) (A i) B) (fun _ _ => Commute.all _ _) b a

/-- The factor identification of a read-back algebra is natural. -/
private lemma factorEvalIso_natural (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) {B C : CommAlgCat.{max u v} (A i)} (f : B ⟶ C) :
    factorAlgMap n A _ _ ((evalAlgFunctor n A i).map f) i ≫ (factorEvalIso n A i C).hom =
      (factorEvalIso n A i B).hom ≫ f := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
    change (factorEvalIso n A i C).hom (f.hom b ⊗ₜ[∀ j, A j] a) =
      f.hom ((factorEvalIso n A i B).hom (b ⊗ₜ[∀ j, A j] a))
    exact (factorEvalIso_hom_tmul n A i C (f.hom b) a).trans
      (((congrArg (fun c : C => f.hom b * c) (f.hom.commutes a).symm).trans
        (map_mul f.hom b (algebraMap (A i) B a)).symm).trans
        (congrArg f.hom (factorEvalIso_hom_tmul n A i B b a)).symm)
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- The other factors of an algebra read over the product ring vanish. -/
private lemma factorEval_subsingleton (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i j : Fin n) (h : i ≠ j) (B : CommAlgCat.{max u v} (A i)) :
    Subsingleton (factorAlg n A ((evalAlgFunctor n A i).obj B) j) := by
  let : Algebra (∀ j, A j) B := Algebra.compHom B (Pi.evalRingHom A i)
  apply subsingleton_of_zero_eq_one
  change (0 : TensorProduct (∀ j, A j) (B : Type (max u v)) (A j)) =
    (1 : B) ⊗ₜ[∀ j, A j] (1 : A j)
  have ht := TensorProduct.smul_tmul (R := ∀ j, A j) (Pi.single i (1 : A i)) (1 : B) (1 : A j)
  simp only [Algebra.smul_def] at ht
  change (algebraMap (A i) B ((Pi.single i (1 : A i)) i) * 1) ⊗ₜ[∀ j, A j] (1 : A j) =
    (1 : B) ⊗ₜ[∀ j, A j] ((Pi.single i (1 : A i)) j * 1) at ht
  simpa [Pi.single_eq_of_ne h.symm] using ht.symm

/-- Transporting the `i`-th component of a scalar through `AdequateFunctor.factorEvalIso`
returns the scalar. -/
private lemma factorEvalIso_hom_piAlgFactorAlgEquiv (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (i : Fin n) (B : CommAlgCat.{max u v} (A i)) (b : B) :
    (factorEvalIso n A i B).hom
        (piAlgFactorAlgEquiv n A ((evalAlgFunctor n A i).obj B) b i) = b := by
  refine Eq.trans (congrArg
    (fun z : factorAlg n A ((evalAlgFunctor n A i).obj B) i =>
      (factorEvalIso n A i B).hom z)
    (piAlgFactorAlgEquiv_apply n A ((evalAlgFunctor n A i).obj B) b i)) ?_
  refine Eq.trans (factorEvalIso_hom_tmul n A i B b (1 : A i)) ?_
  rw [map_one, mul_one]

/-- The component at a section of the counit comparing the `i`-th restriction of an assembled
functor with the `i`-th member of the family: project onto the `i`-th coordinate and transport
along `AdequateFunctor.factorEvalIso`. -/
private noncomputable def productRestrictionCounitApp (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (i : Fin n) (X : ((CommAlgCat.{max u v} (A i))ᵒᵖ)ᵒᵖ) :
    ((restrictModuleFunctor n A i).obj ((familyToProductFunctor n A).obj G)).obj X ⟶
      (G i).obj X :=
  ModuleCat.ofHom (R := (algebraRingDiagram.{v} (A i)).obj X)
    (X := ((restrictModuleFunctor n A i).obj ((familyToProductFunctor n A).obj G)).obj X)
    (Y := (G i).obj X) {
    toFun := fun x => (G i).map (factorEvalIso n A i X.unop.unop).hom.op.op (x i)
    map_add' := by intro x y; exact map_add _ _ _
    map_smul' := by
      intro b x
      change (G i).map (factorEvalIso n A i X.unop.unop).hom.op.op
        (piAlgFactorAlgEquiv n A ((evalAlgFunctor n A i).obj X.unop.unop) b i • x i) = _
      rw [(G i).map_smul]
      exact congrArg (fun r : (algebraRingDiagram.{v} (A i)).obj X =>
          r • ((G i).map (factorEvalIso n A i X.unop.unop).hom.op.op (x i)))
        (factorEvalIso_hom_piAlgFactorAlgEquiv n A i X.unop.unop b) }

/-- `AdequateFunctor.productRestrictionCounitApp` is natural in the algebra. -/
private lemma productRestrictionCounitApp_naturality (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (i : Fin n) {X Y : ((CommAlgCat.{max u v} (A i))ᵒᵖ)ᵒᵖ} (f : X ⟶ Y) :
    ((restrictModuleFunctor n A i).obj ((familyToProductFunctor n A).obj G)).map f ≫
        (ModuleCat.restrictScalars
            (RingCat.Hom.hom ((algebraRingDiagram.{v} (A i)).map f))).map
          (productRestrictionCounitApp n A G i Y) =
      productRestrictionCounitApp n A G i X ≫ (G i).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (G i).map (factorEvalIso n A i Y.unop.unop).hom.op.op
    ((G i).map (factorAlgMap n A _ _ ((evalAlgFunctor n A i).map f.unop.unop) i).op.op
      (x i)) =
    (G i).map f ((G i).map (factorEvalIso n A i X.unop.unop).hom.op.op (x i))
  rw [← (G i).map_comp_apply, ← (G i).map_comp_apply]
  exact (G i).congr_map_apply
    (congrArg (fun f => f.op.op) (factorEvalIso_natural n A i f.unop.unop)) (x i)

/-- The counit comparing the `i`-th restriction of an assembled functor with the `i`-th member
of the family. -/
private noncomputable def productRestrictionCounitHom (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (i : Fin n) :
    (restrictModuleFunctor n A i).obj ((familyToProductFunctor n A).obj G) ⟶ G i where
  app X := productRestrictionCounitApp n A G i X
  naturality f := productRestrictionCounitApp_naturality n A G i f

/-- The `i`-th restriction of an assembled functor is the `i`-th member of the family. -/
private noncomputable def productRestrictionCounitIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] (G : ∀ i, ModuleValuedFunctor.{w, v} (A i))
    (i : Fin n) :
    (restrictModuleFunctor n A i).obj ((familyToProductFunctor n A).obj G) ≅ G i := by
  classical
  let f := productRestrictionCounitHom n A G i
  have hb (X) : Function.Bijective (f.app X) := by
    have hi := ConcreteCategory.bijective_of_isIso
      ((G i).presheaf.map (factorEvalIso n A i X.unop.unop).hom.op.op)
    constructor
    · intro x y hxy
      funext j
      by_cases h : i = j
      · subst j
        exact hi.1 hxy
      · have := factorEval_subsingleton n A i j h X.unop.unop
        exact @Subsingleton.elim _ (Module.subsingleton
          (factorAlg n A ((evalAlgFunctor n A i).obj X.unop.unop) j)
          ((G j).obj (Opposite.op (Opposite.op
            (factorAlg n A ((evalAlgFunctor n A i).obj X.unop.unop) j))))) (x j) (y j)
    · intro y
      obtain ⟨x, hx⟩ := hi.2 y
      -- The family must be given explicitly: inferred from `x` alone it is solved as a
      -- constant function, which then does not match the dependent one in the goal.
      obtain ⟨z, hz⟩ : ∃ z : ∀ j, (G j).presheaf.obj (Opposite.op (Opposite.op
          (factorAlg n A ((evalAlgFunctor n A i).obj X.unop.unop) j))), z i = x :=
        ⟨Pi.single i x, Pi.single_eq_same
          (M := fun j => ↑((G j).presheaf.obj (Opposite.op (Opposite.op
            (factorAlg n A ((evalAlgFunctor n A i).obj X.unop.unop) j))))) i x⟩
      refine ⟨z, Eq.trans ?_ hx⟩
      exact congrArg (ConcreteCategory.hom ((G i).presheaf.map
        (factorEvalIso n A i X.unop.unop).hom.op.op)) hz
  exact PresheafOfModules.isoMk
    (fun X => (LinearEquiv.ofBijective (f.app X).hom (hb X)).toModuleIso)
    (by intros; exact f.naturality _)


/-- Assembling a family of adequate functors over the factors into an adequate functor over
the product ring. -/
private noncomputable def adequateAssemblyFunctor (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    (∀ i : Fin n, ObjectProperty.FullSubcategory
        (fun F : ModuleValuedFunctor.{w, v} (A i) =>
          IsAdequate (𝟭 _) F)) ⥤
    (ObjectProperty.FullSubcategory
      (fun F : ModuleValuedFunctor.{w, v} (∀ i, A i) =>
        IsAdequate (𝟭 _) F)) where
  obj G := ⟨(familyToProductFunctor n A).obj (fun i => (G i).obj),
    isAdequate_familyToProduct n A _ (fun i => (G i).property)⟩
  map η := ObjectProperty.homMk ((familyToProductFunctor n A).map (fun i => (η i).hom))
  map_id G := by
    apply ObjectProperty.hom_ext
    exact (familyToProductFunctor n A).map_id _
  map_comp η θ := by
    apply ObjectProperty.hom_ext
    exact (familyToProductFunctor n A).map_comp _ _

/-- The unit of the equivalence between adequate functors over the product ring and families
of adequate functors over the factors. -/
private noncomputable def adequateProductUnitIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    𝟭 _ ≅ adequateRestrictionFunctor.{w, v, u} n A ⋙ adequateAssemblyFunctor n A := by
  refine NatIso.ofComponents (fun F => ObjectProperty.isoMk _ ?_) ?_
  · let f := productRestrictionUnit n A F.obj
    exact PresheafOfModules.isoMk (fun X =>
      (LinearEquiv.ofBijective (f.app X).hom
        (productRestrictionUnit_adequate_bijective n A F.obj F.property X.unop.unop)).toModuleIso)
      (by intros; exact f.naturality _)
  · intro F G η
    apply ObjectProperty.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact productRestrictionUnit_natural n A η.hom X.unop.unop x i

/-- The counit of the equivalence between adequate functors over the product ring and families
of adequate functors over the factors. -/
private noncomputable def adequateProductCounitIso (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :
    adequateAssemblyFunctor.{w, v, u} n A ⋙ adequateRestrictionFunctor n A ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun G => CategoryTheory.Pi.isoMk
    (fun i => ObjectProperty.isoMk _ (productRestrictionCounitIso n A (fun j => (G j).obj) i))) ?_
  intro G H η
  funext i
  apply ObjectProperty.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (PresheafOfModules.naturality_apply (η i).hom
    (factorEvalIso n A i X.unop.unop).hom.op.op (x i)).symm

/-- The equivalence between adequate functors over the product ring and families of adequate
functors over the factors. -/
private noncomputable def adequateProductEquivalence (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)] :=
  CategoryTheory.Equivalence.mk (adequateRestrictionFunctor.{w, v, u} n A)
    (adequateAssemblyFunctor n A) (adequateProductUnitIso n A) (adequateProductCounitIso n A)


/-- The componentwise comparison for the inverse equivalence, coherent in both the algebra and
the family of functors. -/
public def ProductEquivalenceSpecification (n : ℕ) (A : Fin n → Type u)
    [∀ i, CommRing (A i)]
    (e : (ObjectProperty.FullSubcategory
        (fun F : ModuleValuedFunctor.{w, v} (∀ i, A i) =>
          IsAdequate (𝟭 _) F)) ≌
        (∀ i : Fin n,
          ObjectProperty.FullSubcategory
            (fun F : ModuleValuedFunctor.{w, v} (A i) =>
              IsAdequate (𝟭 _) F))) : Prop :=
  ∃ (φ : ∀ (G : ∀ i : Fin n,
        ObjectProperty.FullSubcategory
          (fun F : ModuleValuedFunctor.{w, v} (A i) =>
            IsAdequate (𝟭 _) F))
      (B : ∀ i, CommAlgCat.{max u v} (A i)),
      ((e.inverse.obj G).obj.obj
        (Opposite.op (Opposite.op
          (CommAlgCat.of (∀ i, A i) (∀ i, (B i : Type (max u v))))))) ≅
      ModuleCat.of (∀ i, (B i : Type (max u v)))
        (∀ i, ((G i).obj.obj
          (Opposite.op (Opposite.op (B i))) : Type w))),
    (∀ (G : ∀ i : Fin n,
        ObjectProperty.FullSubcategory
          (fun F : ModuleValuedFunctor.{w, v} (A i) =>
            IsAdequate (𝟭 _) F))
      (B C : ∀ i, CommAlgCat.{max u v} (A i)) (f : ∀ i, B i ⟶ C i)
      (x : (e.inverse.obj G).obj.obj
        (Opposite.op (Opposite.op
          (CommAlgCat.of (∀ i, A i) (∀ i, (B i : Type (max u v)))))))
      (i : Fin n),
      ((φ G C).hom
        ((e.inverse.obj G).obj.map
          (CommAlgCat.ofHom (piAlgHom n A B C f)).op.op x)) i =
      (G i).obj.map (f i).op.op ((φ G B).hom x i)) ∧
    (∀ (G H : ∀ i : Fin n,
        ObjectProperty.FullSubcategory
          (fun F : ModuleValuedFunctor.{w, v} (A i) =>
            IsAdequate (𝟭 _) F)) (η : G ⟶ H)
      (B : ∀ i, CommAlgCat.{max u v} (A i))
      (x : (e.inverse.obj G).obj.obj
        (Opposite.op (Opposite.op
          (CommAlgCat.of (∀ i, A i) (∀ i, (B i : Type (max u v)))))))
      (i : Fin n),
      ((φ H B).hom
        (((e.inverse.map η).hom.app
          (Opposite.op (Opposite.op
            (CommAlgCat.of (∀ i, A i) (∀ i, (B i : Type (max u v))))))) x)) i =
      ((η i).hom.app (Opposite.op (Opposite.op (B i)))) ((φ G B).hom x i))

/-- Adequate module-valued functors over a finite product of rings correspond to families of
adequate module-valued functors over its factors. The inverse equivalence has a componentwise
comparison natural in both the algebra and the family of factors. -/
@[stacks 06VB]
public noncomputable def adequateFunctorProductEquivalence (n : ℕ)
    (A : Fin n → Type u) [∀ i, CommRing (A i)] :
    { e : (ObjectProperty.FullSubcategory
        (fun F : ModuleValuedFunctor.{w, v} (∀ i, A i) =>
          IsAdequate (𝟭 _) F)) ≌
        (∀ i : Fin n,
          ObjectProperty.FullSubcategory
            (fun F : ModuleValuedFunctor.{w, v} (A i) =>
              IsAdequate (𝟭 _) F)) //
      ProductEquivalenceSpecification n A e } :=
  Classical.choice (by
    exact ⟨⟨adequateProductEquivalence n A,
    ⟨fun G B => familyToProductPiIso n A (fun i => (G i).obj) B,
      (fun G B C f x i => familyToProductPiIso_natural_algebra n A
        (fun i => (G i).obj) B C f x i),
      (fun G H η B x i => familyToProductPiIso_natural_family n A
        (fun i => (G i).obj) (fun i => (H i).obj) (fun i => (η i).hom) B x i)⟩⟩⟩)

end AdequateFunctor
