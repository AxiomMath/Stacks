module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.WeightSpaces

/-!
# Tag 06V0 for a module in the ring's own universe

This file is the third part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift`. It shows that the
module-valued functor of a module commutes with flat base change, identifies morphisms between
the module-valued functors of finite free modules with linear maps, and proves the lifting
property of Tag 06V0 for a module in the ring's own universe, together with the naturality
statement that a candidate lift agreeing at the universal solution algebra is a lift.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
-/

@[expose] public section

open CategoryTheory
universe w v u z u₁ v₁

namespace AdequateFunctor


open scoped DirectSum
open TensorProduct

/-- The small-universe module-valued functor of `M` is the library one applied to `M`. -/
private lemma moduleExtension_eq_cardUT (A : Type u) [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] :
    smallModuleExtension A M = moduleExtension A (ModuleCat.of A M) := rfl

/-- The module-valued functor of a module commutes with flat base change. -/
private lemma moduleExtension_preservesFlatBaseChange (A : Type z) [CommRing A]
    (M : Type z) [AddCommGroup M] [Module A M] :
    Laurent.PreservesFlatBaseChange A (smallModuleExtension A M) := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hflat
  refine ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M, ?_⟩
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M)
          (1 ⊗ₜ[B] (b ⊗ₜ[A] m)) = f b ⊗ₜ[A] m
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      simp only [Algebra.smul_def, mul_one]
      rw [show algebraMap B C b = f b from rfl]
  | add x y hx hy =>
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M)
          (1 ⊗ₜ[B] (x + y)) =
        (TensorProduct.map f.toLinearMap LinearMap.id) (x + y)
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M)
          (1 ⊗ₜ[B] x) = (TensorProduct.map f.toLinearMap LinearMap.id) x at hx
      change (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M)
          (1 ⊗ₜ[B] y) = (TensorProduct.map f.toLinearMap LinearMap.id) y at hy
      rw [TensorProduct.tmul_add, map_add, hx, hy]
      rw [← map_add]

/-- A linear map of modules in the ring's own universe, read as a morphism of the associated
module-valued functors. -/
private noncomputable def smallModuleExtensionHom (A : Type u) [CommRing A]
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) : smallModuleExtension A M ⟶ smallModuleExtension A N := by
  change (moduleExtensionFunctor.{u, u} A).obj (ModuleCat.of A M) ⟶
    (moduleExtensionFunctor.{u, u} A).obj (ModuleCat.of A N)
  exact (moduleExtensionFunctor.{u, u} A).map (ModuleCat.ofHom f)

/-- The base ring `A`, as an object of the category indexing module-valued functors. -/
private abbrev baseAlgebraObject {A : Type u} [CommRing A] :
    ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op (CommAlgCat.of A A))

/-- Two morphisms between module-valued functors of modules agree as soon as they agree at the
base algebra. -/
private lemma moduleExtension_hom_ext_atBase {A : Type u} [CommRing A]
    {M N : ModuleCat.{u} A}
    (η θ : (moduleExtensionFunctor.{u, u} A).obj M ⟶
      (moduleExtensionFunctor.{u, u} A).obj N)
    (h : η.app (baseAlgebraObject (A := A)) = θ.app (baseAlgebraObject (A := A))) :
    η = θ := by
  ext X x
  let B : CommAlgCat.{u} A := X.unop.unop
  let g : baseAlgebraObject (A := A) ⟶ X :=
    (CommAlgCat.ofHom (Algebra.ofId A (B : Type u))).op.op
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
      have hη := PresheafOfModules.naturality_apply η g (1 ⊗ₜ[A] m)
      have hθ := PresheafOfModules.naturality_apply θ g (1 ⊗ₜ[A] m)
      have hm : ((moduleExtensionFunctor.{u, u} A).obj M).map g
          (1 ⊗ₜ[A] m) = 1 ⊗ₜ[A] m := by
        change algebraMap A B 1 ⊗ₜ[A] m = 1 ⊗ₜ[A] m
        simp
      have hη' := hη
      rw [hm] at hη'
      have hθ' := hθ
      rw [hm] at hθ'
      have ht : b • (1 ⊗ₜ[A] m) = b ⊗ₜ[A] m := by
        change (b * 1) ⊗ₜ[A] m = b ⊗ₜ[A] m
        simp
      rw [← ht]
      rw [(η.app X).hom.map_smul, (θ.app X).hom.map_smul, hη', hθ', h]
  | add x y hx hy => rw [(η.app X).hom.map_add, (θ.app X).hom.map_add, hx, hy]

/-- The linear map of finite free modules underlying a morphism of their module-valued
functors. -/
private noncomputable def matrixOfNaturalMap {n m : ℕ} (A : Type u) [CommRing A]
    (d : smallModuleExtension A (Fin n → A) ⟶ smallModuleExtension A (Fin m → A)) :
    (Fin n → A) →ₗ[A] (Fin m → A) :=
  ((TensorProduct.lid A (Fin m → A)).toLinearMap).comp
    ((d.app (baseAlgebraObject (A := A))).hom.comp
      (TensorProduct.lid A (Fin n → A)).symm.toLinearMap)

/-- A morphism between the module-valued functors of finite free modules is the one induced by
its underlying linear map. -/
private lemma moduleExtensionHom_matrixOfNaturalMap {n m : ℕ} (A : Type u)
    [CommRing A] (d : smallModuleExtension A (Fin n → A) ⟶ smallModuleExtension A (Fin m → A)) :
    d = smallModuleExtensionHom A (matrixOfNaturalMap A d) := by
  change (moduleExtensionFunctor.{u, u} A).obj (ModuleCat.of A (Fin n → A)) ⟶
      (moduleExtensionFunctor.{u, u} A).obj (ModuleCat.of A (Fin m → A)) at d
  apply moduleExtension_hom_ext_atBase
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
      apply (TensorProduct.lid A (Fin m → A)).injective
      change (TensorProduct.lid A (Fin m → A))
          ((d.app (baseAlgebraObject (A := A))).hom (a ⊗ₜ[A] v)) =
        (TensorProduct.lid A (Fin m → A))
          (a ⊗ₜ[A] (matrixOfNaturalMap A d v))
      have harg : (TensorProduct.lid A (Fin n → A)).symm (a • v) =
          a ⊗ₜ[A] v := by
        simp [TensorProduct.lid_symm_apply, TensorProduct.smul_tmul']
      calc
        (TensorProduct.lid A (Fin m → A))
            ((d.app (baseAlgebraObject (A := A))).hom (a ⊗ₜ[A] v)) =
          matrixOfNaturalMap A d (a • v) := by
            change (TensorProduct.lid A (Fin m → A))
                ((d.app (baseAlgebraObject (A := A))).hom (a ⊗ₜ[A] v)) =
              (TensorProduct.lid A (Fin m → A))
                ((d.app (baseAlgebraObject (A := A))).hom
                  ((TensorProduct.lid A (Fin n → A)).symm (a • v)))
            rw [harg]
        _ = a • matrixOfNaturalMap A d v :=
          (matrixOfNaturalMap A d).map_smul _ _
        _ = (TensorProduct.lid A (Fin m → A))
            (a ⊗ₜ[A] (matrixOfNaturalMap A d v)) := by simp
  | add x y hx hy => simp [hx, hy]

/-- The linear map `(Fin n → A) → (Fin m → A)` underlying a morphism between the
module-valued functors of finite free modules. -/
noncomputable def finiteFreeExtensionMap {n m : ℕ} (A : Type u)
    [CommRing A]
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m)) :
    (Fin n → A) →ₗ[A] (Fin m → A) := by
  let dM : finiteFreeModule.{w} A n ⟶
      finiteFreeModule.{w} A m :=
    moduleHomOfExtensionNatTrans.{max u w, v} d
  let f := (ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM
  exact f.hom

/-- The underlying linear map of `AdequateFunctor.finiteFreeExtensionMap` induces the given
morphism. -/
private lemma finiteFreeExtensionMap_spec {n m : ℕ} (A : Type u) [CommRing A]
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m)) :
    let dM : finiteFreeModule.{w} A n ⟶
        finiteFreeModule.{w} A m :=
      moduleHomOfExtensionNatTrans.{max u w, v} d
    let f := (ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM
    d = (moduleExtensionFunctor.{max u w, v} A).map dM ∧
      dM = (ModuleCat.uliftFunctor.{w, u} A).map f := by
  dsimp only
  constructor
  · exact moduleExtension_natTrans_eq_map d
  · exact ((ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).map_preimage _).symm

/-- A morphism between the module-valued functors of finite free modules is the image of its
underlying linear map. -/
lemma finiteFreeExtensionNatTrans_eq_map {n m : ℕ} (A : Type u)
    [CommRing A]
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m)) :
    d = (moduleExtensionFunctor.{max u w, v} A).map
      ((ModuleCat.uliftFunctor.{w, u} A).map
        (ModuleCat.ofHom (finiteFreeExtensionMap A d))) := by
  obtain ⟨hd, hdM⟩ := finiteFreeExtensionMap_spec A d
  let dM : finiteFreeModule.{w} A n ⟶
      finiteFreeModule.{w} A m :=
    moduleHomOfExtensionNatTrans.{max u w, v} d
  have hf : ModuleCat.ofHom (finiteFreeExtensionMap A d) =
      (ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM := by
    apply ModuleCat.hom_ext
    rfl
  calc
    d = (moduleExtensionFunctor.{max u w, v} A).map dM := hd
    _ = (moduleExtensionFunctor.{max u w, v} A).map
        ((ModuleCat.uliftFunctor.{w, u} A).map
          (ModuleCat.ofHom (finiteFreeExtensionMap A d))) := by
      apply congrArg ((moduleExtensionFunctor.{max u w, v} A).map)
      exact hdM.trans (congrArg (ModuleCat.uliftFunctor.{w, u} A).map hf.symm)


/-- The coordinate tuple element of `B ⊗[A] (finiteFreeModule A n)`. -/
noncomputable def tupleTensorFiniteFree {n : ℕ} (A : Type u)
    (B : Type (max u v)) [CommRing A] [CommRing B] [Algebra A B]
    (x : Fin n → B) : TensorProduct A B (finiteFreeModule.{w, u} A n) :=
  ∑ i, x i ⊗ₜ[A] (⟨Pi.single i 1⟩ : finiteFreeModule.{w, u} A n)

/-- The universe-lifted finite free module is `Fin n → A`. -/
noncomputable def finiteFreeDownEquiv {n : ℕ} (A : Type u) [CommRing A] :
    finiteFreeModule.{w, u} A n ≃ₗ[A] (Fin n → A) :=
  ULift.moduleEquiv

/-- Descending the universe lift sends the coordinate tuple element to the coordinate tuple
element. -/
lemma tupleTensorFiniteFree_down {n : ℕ} (A : Type u)
    (B : Type (max u v)) [CommRing A] [CommRing B] [Algebra A B]
    (x : Fin n → B) :
    TensorProduct.map LinearMap.id (finiteFreeDownEquiv.{w, u} A).toLinearMap
      (tupleTensorFiniteFree A B x) = tupleTensor A B x := by
  classical
  simp only [tupleTensorFiniteFree, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact TensorProduct.map_tmul LinearMap.id (finiteFreeDownEquiv.{w, u} A).toLinearMap (x i)
    (⟨Pi.single i 1⟩ : finiteFreeModule.{w, u} A n)

/-- The tuple of universe-lifted universal solutions is killed by the base change of `d`. -/
lemma universalSolution_tuple_in_ker_lifted {n m : ℕ} (A : Type u)
    [CommRing A] (d : (Fin n → A) →ₗ[A] (Fin m → A)) :
    d.baseChange (universalSolutionAlgebraLifted A d)
      (tupleTensor A (universalSolutionAlgebraLifted A d)
        (universalSolutionVariableLifted A d)) = 0 := by
  apply (TensorProduct.piScalarRight A (universalSolutionAlgebraLifted A d)
    (universalSolutionAlgebraLifted A d) (Fin m)).injective
  ext j
  rw [piScalarRight_baseChange_tupleTensor]
  exact universalSolution_relation_lifted A d j

/-- A linear map of modules in a larger universe, read as a morphism of the associated
module-valued functors. -/
noncomputable def moduleExtensionHomLarge (A : Type u) [CommRing A]
    {M N : Type (max u w)} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    moduleExtensionOfCarrier A M ⟶ moduleExtensionOfCarrier A N :=
  (moduleExtensionFunctor.{max u w, v} A).map (ModuleCat.ofHom f)

/-- A tuple satisfying the relations of `d` induces an algebra map out of the universe-lifted
universal solution algebra. -/
noncomputable def universalSolutionAlgHomLifted {n m : ℕ} (A : Type u)
    (C : Type (max u v)) [CommRing A] [CommRing C] [Algebra A C]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → C)
    (hrel : ∀ j, ∑ i, d (Pi.single i 1) j • x i = 0) :
    universalSolutionAlgebraLifted A d →ₐ[A] C :=
  SymmetricAlgebra.lift ((universalSolutionLinearMap A C d x hrel).comp
    (ULift.moduleEquiv.{u, u, v}.toLinearMap))

/-- The induced algebra map sends the `i`-th universe-lifted universal solution to the `i`-th
entry of the tuple. -/
lemma universalSolutionAlgHomLifted_variable {n m : ℕ} (A : Type u)
    (C : Type (max u v)) [CommRing A] [CommRing C] [Algebra A C]
    (d : (Fin n → A) →ₗ[A] (Fin m → A)) (x : Fin n → C)
    (hrel : ∀ j, ∑ i, d (Pi.single i 1) j • x i = 0) (i : Fin n) :
    universalSolutionAlgHomLifted A C d x hrel (universalSolutionVariableLifted A d i) = x i := by
  simp [universalSolutionAlgHomLifted, universalSolutionVariableLifted,
    SymmetricAlgebra.lift_ι_apply, universalSolutionLinearMap,
    Submodule.liftQ_apply, linearMapOfTuple_single]

/-- Exactness of a short complex of presheaves of modules can be tested on sections. -/
private lemma exact_component_preimage_aux {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (S : ShortComplex (PresheafOfModules.{v} R)) (hS : S.Exact)
    (X : Cᵒᵖ) (x : S.X₂.obj X) (hx : S.g.app X x = 0) :
    ∃ y : S.X₁.obj X, S.f.app X y = x := by
  let E := PresheafOfModules.evaluation R X
  let : CategoryTheory.Limits.PreservesFiniteLimits E := inferInstance
  let : CategoryTheory.Limits.PreservesFiniteColimits E := inferInstance
  let : E.PreservesZeroMorphisms := inferInstance
  have hE : (S.map E).Exact := hS.map E
  have hx' : ((S.map E).g.hom) x = 0 := hx
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget (S := S.map E)).mp hE x hx'
  exact ⟨y, hy⟩

/-- Exactness of a short complex of module-valued functors can be tested on sections. -/
private lemma exact_component_preimage (A : Type u) [CommRing A]
    (S : ShortComplex (Laurent.ModuleValuedFunctor A)) (hS : S.Exact)
    (X : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ)
    (x : S.X₂.obj X) (hx : S.g.app X x = 0) :
    ∃ y : S.X₁.obj X, S.f.app X y = x :=
  exact_component_preimage_aux S hS X x hx

/-- Exactness of a short complex of module-valued functors can be tested on sections, with
independent universes. -/
public lemma exact_component_preimage_large (A : Type u) [CommRing A]
    (S : ShortComplex (ModuleValuedFunctor.{max u v w, v} A)) (hS : S.Exact)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
    (x : S.X₂.obj X) (hx : S.g.app X x = 0) :
    ∃ y : S.X₁.obj X, S.f.app X y = x :=
  exact_component_preimage_aux S hS X x hx

/-- The coordinate tuple of an element of `C ⊗[A] (Fin n → A)` recovers that element. -/
private lemma tupleTensor_piScalarRight {n : ℕ} (A : Type u) {C : Type z} [CommRing A]
    [CommRing C] [Algebra A C] (ξ : TensorProduct A C (Fin n → A)) :
    tupleTensor A C (TensorProduct.piScalarRight A C C (Fin n) ξ) = ξ := by
  apply (TensorProduct.piScalarRight A C C (Fin n)).injective
  ext j
  simp [tupleTensor, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Pi.single_apply]

/-- A coordinate tuple killed by the base change of `d` satisfies the relations of `d`. -/
private lemma relation_of_baseChange_tupleTensor_eq_zero {n m : ℕ} (A : Type u) {C : Type z}
    [CommRing A] [CommRing C] [Algebra A C] (d : (Fin n → A) →ₗ[A] (Fin m → A))
    (x : Fin n → C) (h : d.baseChange C (tupleTensor A C x) = 0) (j : Fin m) :
    ∑ i, d (Pi.single i 1) j • x i = 0 := by
  have hc := congrArg (fun z => TensorProduct.piScalarRight A C C (Fin m) z j) h
  rw [piScalarRight_baseChange_tupleTensor] at hc
  exact hc

/-- A composite of presheaf morphisms with zero composite vanishes on sections. -/
private lemma comp_apply_eq_zero {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {L P N : PresheafOfModules.{v} R} (i : L ⟶ P) (d : P ⟶ N) (hd : i ≫ d = 0) {X : Cᵒᵖ}
    (ξ : L.obj X) : (d.app X).hom ((i.app X).hom ξ) = 0 := by
  simpa using congrArg (fun η => (η.app X).hom ξ) hd

/-- If a section `ξ` of the source of a monomorphism `i` is sent to the pullback of the image of
`ℓ`, and `ψ` agrees with `φ` on that image, then `ψ ∘ i` agrees with `φ` at `ξ`. -/
private lemma comp_apply_eq_of_eq_map {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {L P N : PresheafOfModules.{v} R} (i : L ⟶ P) [Mono i] (φ : L ⟶ N) (ψ : P ⟶ N)
    {X₀ X : Cᵒᵖ} (u : X₀ ⟶ X) (ℓ : L.obj X₀) (ξ : L.obj X)
    (hξ : (i.app X).hom ξ = P.map u ((i.app X₀).hom ℓ))
    (hψ : (ψ.app X₀).hom ((i.app X₀).hom ℓ) = (φ.app X₀).hom ℓ) :
    (ψ.app X).hom ((i.app X).hom ξ) = (φ.app X).hom ξ := by
  have hL : L.map u ℓ = ξ := PresheafOfModules.injective_of_mono i X
    (by rw [hξ]; exact PresheafOfModules.naturality_apply i u ℓ)
  subst hL
  rw [PresheafOfModules.naturality_apply i u ℓ, PresheafOfModules.naturality_apply ψ u,
    hψ, PresheafOfModules.naturality_apply φ u ℓ]

/-- **Stacks Lemma 06V0.** A morphism from the kernel of a morphism between finite free
module-valued functors to a module-valued functor extends to the middle finite free functor. -/
private theorem exists_lift_from_finite_free_kernel_small
    (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    (n m : ℕ) (L : Laurent.ModuleValuedFunctor A)
    (i : L ⟶ smallModuleExtension A (Fin n → A))
    (d : smallModuleExtension A (Fin n → A) ⟶ smallModuleExtension A (Fin m → A))
    (φ : L ⟶ smallModuleExtension A M) [Mono i] (hd : i ≫ d = 0)
    (h : (ShortComplex.mk i d hd).Exact) :
    ∃ ψ : smallModuleExtension A (Fin n → A) ⟶ smallModuleExtension A M, i ≫ ψ = φ := by
  let f := matrixOfNaturalMap A d
  let B := universalSolutionAlgebra A f
  let X₀ : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A B))
  let x := tupleTensor A B (universalSolutionVariable A f)
  let S := ShortComplex.mk i d hd
  have hS : S.Exact := by simpa [S] using h
  have hx : (d.app X₀).hom x = 0 := by
    rw [moduleExtensionHom_matrixOfNaturalMap A d]
    change f.baseChange B x = 0
    exact universalSolution_tuple_in_ker A f
  obtain ⟨ℓ, hℓ⟩ := exact_component_preimage A S hS X₀ x hx
  let Y : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))
  let g := Laurent.gradedLaurentMap A B (symmetricPower A (universalSolutionModule A f))
  let c := Laurent.constantLaurentMap A B
  let uG := (CommAlgCat.ofHom g).op.op
  let uC := (CommAlgCat.ofHom c).op.op
  have hvars (j : Fin n) : g (universalSolutionVariable A f j) =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) *
        c (universalSolutionVariable A f j) := by
    change Laurent.gradedLaurentMap A B
        (symmetricPower A (universalSolutionModule A f))
        (SymmetricAlgebra.ι A (universalSolutionModule A f)
          (Submodule.mkQ (LinearMap.range (transposeLinearMap A f)) (Pi.single j 1))) =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) *
        Laurent.constantLaurentMap A B
          (SymmetricAlgebra.ι A (universalSolutionModule A f)
            (Submodule.mkQ (LinearMap.range (transposeLinearMap A f)) (Pi.single j 1)))
    rw [gradedLaurentMap_symmetricAlgebra_generator]
    change LaurentPolynomial.C _ * LaurentPolynomial.T (1 : ℤ) =
      LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.C _
    exact mul_comm _ _
  have hscale : (smallModuleExtension A (Fin n → A)).map uG x =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (smallModuleExtension A (Fin n → A)).map uC x := by
    change (TensorProduct.map g.toLinearMap LinearMap.id) x =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (TensorProduct.map c.toLinearMap LinearMap.id) x
    simp only [x, tupleTensor, map_sum, TensorProduct.map_tmul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change g (universalSolutionVariable A f j) ⊗ₜ[A] Pi.single j 1 =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (c (universalSolutionVariable A f j) ⊗ₜ[A] Pi.single j 1)
    rw [hvars j, TensorProduct.smul_tmul']
    rfl
  have hLscale : L.map uG ℓ =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) • L.map uC ℓ := by
    apply PresheafOfModules.injective_of_mono i Y
    have hNatG : (i.app Y).hom (L.map uG ℓ) =
        (smallModuleExtension A (Fin n → A)).map uG x := by
      rw [← hℓ]
      exact PresheafOfModules.naturality_apply i uG ℓ
    have hNatC : (i.app Y).hom (L.map uC ℓ) =
        (smallModuleExtension A (Fin n → A)).map uC x := by
      rw [← hℓ]
      exact PresheafOfModules.naturality_apply i uC ℓ
    rw [hNatG, hscale, ← hNatC]
    exact ((i.app Y).hom.map_smul _ _).symm
  let y : TensorProduct A B M := (φ.app X₀).hom ℓ
  have hyWeight : y ∈ Laurent.weightSpace A B (smallModuleExtension A M)
      (symmetricPower A (universalSolutionModule A f)) 1 := by
    change (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (smallModuleExtension A M).map uC y = (smallModuleExtension A M).map uG y
    let T : LaurentPolynomial B := LaurentPolynomial.T 1
    have hLscale' : (L.map uG ℓ : L.obj Y) =
        T • (L.map uC ℓ : L.obj Y) := hLscale
    have hphiScale : (φ.app Y).hom (L.map uG ℓ : L.obj Y) =
        T • (φ.app Y).hom (L.map uC ℓ : L.obj Y) := by
      have hh := congrArg (φ.app Y).hom hLscale'
      have hms := (φ.app Y).hom.map_smul T (L.map uC ℓ : L.obj Y)
      exact hh.trans hms
    have hPhiG : (φ.app Y).hom (L.map uG ℓ : L.obj Y) =
        ((smallModuleExtension A M).map uG y : (smallModuleExtension A M).obj Y) := by
      simpa only [y] using PresheafOfModules.naturality_apply φ uG ℓ
    have hPhiC : (φ.app Y).hom (L.map uC ℓ : L.obj Y) =
        ((smallModuleExtension A M).map uC y : (smallModuleExtension A M).obj Y) := by
      simpa only [y] using PresheafOfModules.naturality_apply φ uC ℓ
    exact (congrArg (fun z : (smallModuleExtension A M).obj Y => T • z) hPhiC.symm).trans
      (hphiScale.symm.trans hPhiG)
  have hyDegree : y ∈ DirectSum.decomposeTensor
      (symmetricPower A (universalSolutionModule A f)) M 1 :=
    moduleExtension_weightOne_mem_degreeOne A B M
      (symmetricPower A (universalSolutionModule A f))
      (fun d x hx => gradedLaurentMap_symmetricPower_mem A
        (universalSolutionModule A f) d x hx)
      (moduleExtension_preservesFlatBaseChange A M) y hyWeight
  rw [DirectSum.decomposeTensor_apply] at hyDegree
  obtain ⟨z, hz⟩ := hyDegree
  let Q := universalSolutionModule A f
  let q : (Fin n → A) →ₗ[A] Q :=
    Submodule.mkQ (LinearMap.range (transposeLinearMap A f))
  let ρ : Q →ₗ[A] ↥(symmetricPower A Q 1) :=
    (SymmetricAlgebra.ι A Q).codRestrict _ (fun a => by
      simp [symmetricPower])
  have hρ : Function.Surjective ρ := by
    intro z
    have hz' : (z : SymmetricAlgebra A Q) ∈ LinearMap.range (SymmetricAlgebra.ι A Q) := by
      simpa [symmetricPower] using z.property
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hz'
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨zQ, hzQ⟩ := TensorProduct.map_surjective hρ
    (g' := LinearMap.id) (fun x : M => ⟨x, rfl⟩) z
  obtain ⟨zV, hzV⟩ := TensorProduct.map_surjective
    (Submodule.mkQ_surjective (LinearMap.range (transposeLinearMap A f)))
    (g' := LinearMap.id) (fun x : M => ⟨x, rfl⟩) zQ
  let mvec : Fin n → M := TensorProduct.piScalarRight A A M (Fin n)
    (TensorProduct.comm A (Fin n → A) M zV)
  have hmvec : mvec = ∑ i, Pi.single i (mvec i) := by
    ext i
    simp [Pi.single_apply]
  have hcomm : TensorProduct.comm A (Fin n → A) M zV =
      (TensorProduct.piScalarRight A A M (Fin n)).symm mvec := by
    dsimp [mvec]
    exact ((TensorProduct.piScalarRight A A M (Fin n)).symm_apply_apply _).symm
  have hzVrep : zV = ∑ i, Pi.single i 1 ⊗ₜ[A] mvec i := by
    apply (TensorProduct.comm A (Fin n → A) M).injective
    rw [hcomm, hmvec]
    simp [TensorProduct.piScalarRight_symm_single]
  have hz' : z = TensorProduct.map ρ LinearMap.id
      (TensorProduct.map q LinearMap.id zV) := by
    calc
      z = TensorProduct.map ρ LinearMap.id zQ := hzQ.symm
      _ = TensorProduct.map ρ LinearMap.id (TensorProduct.map q LinearMap.id zV) :=
        congrArg (TensorProduct.map ρ LinearMap.id) hzV.symm
  have hcomp : ((symmetricPower A Q 1).subtype.comp ρ).comp q =
      (SymmetricAlgebra.ι A Q).comp q := by
    ext a
    rfl
  have hzRep : y = ∑ i, universalSolutionVariable A f i ⊗ₜ[A] mvec i := by
    rw [hz.symm, hz']
    change TensorProduct.map (symmetricPower A Q 1).subtype LinearMap.id
      (TensorProduct.map ρ LinearMap.id (TensorProduct.map q LinearMap.id zV)) = _
    rw [TensorProduct.map_map, TensorProduct.map_map, hcomp, hzVrep]
    simp [universalSolutionVariable, Q, q]
  let mMap := linearMapOfTuple A M mvec
  let ψ := smallModuleExtensionHom A mMap
  have hψx : (ψ.app X₀).hom x = y := by
    change (TensorProduct.map LinearMap.id mMap) x = y
    change (TensorProduct.map LinearMap.id mMap) (tupleTensor A B
      (universalSolutionVariable A f)) = y
    dsimp [tupleTensor]
    simp only [map_sum, TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq, linearMapOfTuple_single, mMap]
    rw [hzRep]
  refine ⟨ψ, ?_⟩
  ext X ξ
  rcases X with ⟨⟨C⟩⟩
  let XC : ((CommAlgCat.{u} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A (C : Type u)))
  let xC : Fin n → C := TensorProduct.piScalarRight A C C (Fin n)
    ((i.app XC).hom ξ)
  have hiξ : tupleTensor A C xC = (i.app XC).hom ξ := tupleTensor_piScalarRight A _
  have hker := comp_apply_eq_zero i d hd (X := XC) ξ
  rw [moduleExtensionHom_matrixOfNaturalMap A d] at hker
  have hrel : ∀ j, ∑ i, f (Pi.single i 1) j • xC i = 0 :=
    relation_of_baseChange_tupleTensor_eq_zero A f xC (by rw [hiξ]; exact hker)
  let e := universalSolutionAlgHom A C f xC hrel
  let u := (CommAlgCat.ofHom e).op.op
  have hvarsC (j : Fin n) : e (universalSolutionVariable A f j) = xC j :=
    universalSolutionAlgHom_variable A C f xC hrel j
  have hiNaturality : (i.app XC).hom ξ =
      (smallModuleExtension A (Fin n → A)).map u x := by
    have hFmap : (smallModuleExtension A (Fin n → A)).map u x =
        tupleTensor A C xC := by
      change (TensorProduct.map e.toLinearMap LinearMap.id)
          (tupleTensor A B (universalSolutionVariable A f)) = tupleTensor A C xC
      dsimp [tupleTensor]
      simp [hvarsC]
    exact hiξ.symm.trans hFmap.symm
  exact comp_apply_eq_of_eq_map i φ ψ u ℓ ξ (by rw [hℓ]; exact hiNaturality)
    (by rw [hℓ]; exact hψx)

/-- Naturality half of `AdequateFunctor.exists_lift_from_finite_free_kernel_large`: a
candidate lift `ψ` of `φ` along `i` that agrees with `φ` on the universal tuple over the
universal solution algebra of `f` agrees with it on every section. -/
lemma lift_eq_of_eq_at_universalSolution
    (A : Type u) [CommRing A] (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (n m : ℕ) (L : ModuleValuedFunctor.{max u v w, v} A)
    (i : L ⟶ moduleExtensionOfCarrier A (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrier A M)
    (ψ : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A M)
    [Mono i] (hd : i ≫ d = 0)
    (f : (Fin n → A) →ₗ[A] (Fin m → A))
    (hbase : d = (moduleExtensionFunctor.{max u w, v} A).map
      ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)))
    (ℓ : L.obj (Opposite.op (Opposite.op
      (CommAlgCat.of A (universalSolutionAlgebraLifted A f)))))
    (hℓ : (i.app (Opposite.op (Opposite.op
        (CommAlgCat.of A (universalSolutionAlgebraLifted A f))))).hom ℓ =
      tupleTensorFiniteFree A (universalSolutionAlgebraLifted A f)
        (universalSolutionVariableLifted A f))
    (hψx : (ψ.app (Opposite.op (Opposite.op
        (CommAlgCat.of A (universalSolutionAlgebraLifted A f))))).hom
        (tupleTensorFiniteFree A (universalSolutionAlgebraLifted A f)
          (universalSolutionVariableLifted A f)) =
      (φ.app (Opposite.op (Opposite.op
        (CommAlgCat.of A (universalSolutionAlgebraLifted A f))))).hom ℓ) :
    i ≫ ψ = φ := by
  let B := universalSolutionAlgebraLifted A f
  let vars := universalSolutionVariableLifted A f
  let X₀ : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A B))
  let x := tupleTensorFiniteFree A B vars
  let y : TensorProduct A B M := (φ.app X₀).hom ℓ
  ext X ξ
  rcases X with ⟨⟨C⟩⟩
  let XC : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A (C : Type (max u v))))
  let eₙ := finiteFreeDownEquiv.{w, u} (A := A) (n := n)
  let eₘ := finiteFreeDownEquiv.{w, u} (A := A) (n := m)
  let ξ₀ : TensorProduct A C (Fin n → A) :=
    TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₙ.toLinearMap ((i.app XC).hom ξ)
  let xC : Fin n → C := TensorProduct.piScalarRight A C C (Fin n) ξ₀
  have htuple : tupleTensor A C xC = ξ₀ := tupleTensor_piScalarRight A ξ₀
  have hiξ : tupleTensorFiniteFree A C xC = (i.app XC).hom ξ := by
    apply (TensorProduct.congr (LinearEquiv.refl A C) eₙ).injective
    change TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₙ.toLinearMap
        (tupleTensorFiniteFree A C xC) =
      TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₙ.toLinearMap ((i.app XC).hom ξ)
    rw [tupleTensorFiniteFree_down]
    exact htuple
  have hker := comp_apply_eq_zero i d hd (X := XC) ξ
  have hmap : eₘ.toLinearMap.comp
      ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom =
        f.comp eₙ.toLinearMap := by
    ext z
    cases z
    rfl
  have heval :
      ((moduleExtensionFunctor.{max u w, v} A).map
        ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f))).app XC
        ((i.app XC).hom ξ) =
      (TensorProduct.map (LinearMap.id : C →ₗ[A] C)
        ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom)
        ((i.app XC).hom ξ) := by
    induction ((i.app XC).hom ξ) using TensorProduct.inductionOn with
    | tmul b z =>
        rw [moduleExtensionFunctor_map_app_tmul.{max u w, v}
          A ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)) XC b z]
        rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  have hD : (d.app XC).hom ((i.app XC).hom ξ) =
      TensorProduct.map (LinearMap.id : C →ₗ[A] C)
        ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom
        ((i.app XC).hom ξ) := by
    rw [hbase]
    exact heval
  have hdown : f.baseChange C ξ₀ =
      TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₘ.toLinearMap
        ((d.app XC).hom ((i.app XC).hom ξ)) := by
    have hcomp₁ : TensorProduct.map (LinearMap.id : C →ₗ[A] C) f ξ₀ =
        TensorProduct.map (LinearMap.id : C →ₗ[A] C) (f.comp eₙ.toLinearMap)
          ((i.app XC).hom ξ) := by
      have hfun :
          (TensorProduct.map (LinearMap.id : C →ₗ[A] C) f).comp
              (TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₙ.toLinearMap) =
            TensorProduct.map (LinearMap.id : C →ₗ[A] C) (f.comp eₙ.toLinearMap) := by
        ext b z
        rfl
      dsimp [ξ₀]
      exact congrArg (fun F => F ((i.app XC).hom ξ)) hfun
    have hcomp₂ : TensorProduct.map (LinearMap.id : C →ₗ[A] C)
          (eₘ.toLinearMap.comp
            ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom)
          ((i.app XC).hom ξ) =
        TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₘ.toLinearMap
          (TensorProduct.map (LinearMap.id : C →ₗ[A] C)
            ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom
            ((i.app XC).hom ξ)) := by
      have hfun :
          (TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₘ.toLinearMap).comp
              (TensorProduct.map (LinearMap.id : C →ₗ[A] C)
                ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom) =
            TensorProduct.map (LinearMap.id : C →ₗ[A] C)
              (eₘ.toLinearMap.comp
                ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom) := by
        ext b z
        rfl
      exact congrArg (fun F => F ((i.app XC).hom ξ)) hfun.symm
    calc
      f.baseChange C ξ₀ = TensorProduct.map (LinearMap.id : C →ₗ[A] C) f ξ₀ := rfl
      _ = TensorProduct.map (LinearMap.id : C →ₗ[A] C) (f.comp eₙ.toLinearMap)
          ((i.app XC).hom ξ) := hcomp₁
      _ = TensorProduct.map (LinearMap.id : C →ₗ[A] C)
          (eₘ.toLinearMap.comp
            ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom)
          ((i.app XC).hom ξ) := by rw [hmap]
      _ = TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₘ.toLinearMap
          (TensorProduct.map (LinearMap.id : C →ₗ[A] C)
            ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)).hom
            ((i.app XC).hom ξ)) := hcomp₂
      _ = TensorProduct.map (LinearMap.id : C →ₗ[A] C) eₘ.toLinearMap
          ((d.app XC).hom ((i.app XC).hom ξ)) := by rw [← hD]
  have hzero : f.baseChange C (tupleTensor A C xC) = 0 := by
    rw [← htuple] at hdown
    rw [hdown, hker]
    simp
  have hrel : ∀ j, ∑ k, f (Pi.single k 1) j • xC k = 0 :=
    relation_of_baseChange_tupleTensor_eq_zero A f xC hzero
  let e := universalSolutionAlgHomLifted A C f xC hrel
  let u := (CommAlgCat.ofHom e).op.op
  have hvarsC (j : Fin n) : e (vars j) = xC j :=
    universalSolutionAlgHomLifted_variable A C f xC hrel j
  have hiNaturality : (i.app XC).hom ξ =
      (moduleExtensionOfCarrier A (finiteFreeModule.{w} A n)).map u x := by
    have hFmap : (moduleExtensionOfCarrier A (finiteFreeModule.{w} A n)).map u x =
        tupleTensorFiniteFree A C xC := by
      change (TensorProduct.map e.toLinearMap LinearMap.id)
          (tupleTensorFiniteFree A B vars) = tupleTensorFiniteFree A C xC
      simp only [tupleTensorFiniteFree, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change e (vars j) ⊗ₜ[A] (⟨Pi.single j 1⟩ : finiteFreeModule.{w} A n) =
        xC j ⊗ₜ[A] (⟨Pi.single j 1⟩ : finiteFreeModule.{w} A n)
      rw [hvarsC j]
    exact hiξ.symm.trans hFmap.symm
  exact comp_apply_eq_of_eq_map i φ ψ u ℓ ξ (by rw [hℓ]; exact hiNaturality)
    (by rw [hℓ]; exact hψx)

end AdequateFunctor
