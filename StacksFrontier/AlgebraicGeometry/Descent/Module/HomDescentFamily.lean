module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.HomDescent
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Descent of elements and of linear maps along a finite jointly faithfully flat family

Let `R` be a commutative ring and `(B i)` a finite family of `R`-algebras whose product is
faithfully flat over `R`.  For an `R`-module `N`, an element of each `B i ⊗[R] N` such that the
images in all `B i ⊗[R] B j ⊗[R] N` agree comes from an element of `N`; this is the exactness of
the Amitsur complex of the product (Stacks 023M) read on the factors.

## Main results

* `Stacks.Descent.exists_tmul_eq_family`: descent of elements.
* `Stacks.Descent.exists_linearMap_eq_family_of_pushout`: descent of linear maps `M → B i ⊗ N`,
  with the overlaps given by arbitrary pushouts.
* `Stacks.Descent.bijective_productMap_of_isPushout`: the tensor product of the two legs of a
  pushout square of commutative rings is its tip.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open scoped TensorProduct

universe u v w w'

namespace Stacks.Descent

open TensorProduct

variable {R : Type u} [CommRing R] {ι : Type*} [Finite ι] (B : ι → Type*)
  [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  {M : Type w} [AddCommGroup M] [Module R M] {N : Type w'} [AddCommGroup N] [Module R N]

/-- The projection `(∏ B) ⊗ (∏ B) ⟶ B i ⊗ B j`. -/
noncomputable abbrev piPairProj (i j : ι) :
    (∀ k, B k) ⊗[R] (∀ k, B k) →ₗ[R] B i ⊗[R] B j :=
  TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)

/-- **The projections of `((∏ B) ⊗ (∏ B)) ⊗ N` to the `(B i ⊗ B j) ⊗ N` are jointly
injective**, the index being finite. -/
theorem eq_zero_of_rTensor_piPairProj_eq_zero
    (x : ((∀ k, B k) ⊗[R] (∀ k, B k)) ⊗[R] N)
    (h : ∀ i j, LinearMap.rTensor N (piPairProj B i j) x = 0) : x = 0 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let G : ((∀ k, B k) ⊗[R] (∀ k, B k)) ⊗[R] N ≃ₗ[R] ∀ i, ∀ j, (B i ⊗[R] B j) ⊗[R] N :=
    TensorProduct.assoc R _ _ N ≪≫ₗ
      TensorProduct.piLeft (R := R) (N := (∀ k, B k) ⊗[R] N) (M := B) ≪≫ₗ
      LinearEquiv.piCongrRight fun i =>
        LinearEquiv.lTensor (B i) (TensorProduct.piLeft (R := R) (N := N) (M := B)) ≪≫ₗ
          TensorProduct.piRight (R := R) (S := R) (N := B i) (M := fun j => B j ⊗[R] N) ≪≫ₗ
            LinearEquiv.piCongrRight fun j => (TensorProduct.assoc R (B i) (B j) N).symm
  have hG : ∀ i j, (LinearMap.proj j ∘ₗ LinearMap.proj i ∘ₗ G.toLinearMap) =
      LinearMap.rTensor N (piPairProj B i j) := by
    intro i j
    ext p q n
    simp [G]
  refine G.injective (G.map_zero.symm ▸ funext fun i => funext fun j => ?_)
  have := congrArg (fun φ => φ x) (hG i j)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
  exact this.trans (h i j)

omit [Finite ι] in
/-- The projection to a factor, after `TensorProduct.piLeft`, is the factor. -/
theorem rTensor_proj_piLeft_symm [Fintype ι] [DecidableEq ι] (z : ∀ i, B i ⊗[R] N) (i : ι) :
    LinearMap.rTensor N (LinearMap.proj i : (∀ k, B k) →ₗ[R] B i)
        ((TensorProduct.piLeft (R := R) (N := N) (M := B)).symm z) = z i := by
  obtain ⟨y, rfl⟩ := (TensorProduct.piLeft (R := R) (N := N) (M := B)).surjective z
  rw [LinearEquiv.symm_apply_apply]
  have : (LinearMap.rTensor N (LinearMap.proj i : (∀ k, B k) →ₗ[R] B i)) =
      LinearMap.proj i ∘ₗ (TensorProduct.piLeft (R := R) (N := N) (M := B)).toLinearMap := by
    ext p n
    simp
  exact congrArg (fun φ => φ y) this

/-- **Descent of elements along a finite jointly faithfully flat family of algebras.**  A family
of elements `ξ i ∈ B i ⊗[R] N` whose images in every `B i ⊗[R] B j ⊗[R] N` agree comes from one
element of `N`. -/
theorem exists_tmul_eq_family [Module.FaithfullyFlat R (∀ i, B i)] (ξ : ∀ i, B i ⊗[R] N)
    (h : ∀ i j,
      LinearMap.rTensor N (Algebra.TensorProduct.includeLeft : B i →ₐ[R] B i ⊗[R] B j).toLinearMap
          (ξ i) =
        LinearMap.rTensor N
          (Algebra.TensorProduct.includeRight : B j →ₐ[R] B i ⊗[R] B j).toLinearMap (ξ j)) :
    ∃ n : N, ∀ i, ξ i = 1 ⊗ₜ n := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let Ξ : (∀ k, B k) ⊗[R] N := (TensorProduct.piLeft (R := R) (N := N) (M := B)).symm ξ
  have hφ : ∀ i, LinearMap.rTensor N (LinearMap.proj i : (∀ k, B k) →ₗ[R] B i) Ξ = ξ i :=
    fun i => rTensor_proj_piLeft_symm B ξ i
  have hsub : ∀ i j, piPairProj B i j ∘ₗ Algebra.TensorProduct.includeLeftSubRight R (∀ k, B k) =
      (Algebra.TensorProduct.includeLeft : B i →ₐ[R] B i ⊗[R] B j).toLinearMap ∘ₗ
          LinearMap.proj i -
        (Algebra.TensorProduct.includeRight : B j →ₐ[R] B i ⊗[R] B j).toLinearMap ∘ₗ
          LinearMap.proj j := by
    intro i j
    ext p
    simp [Algebra.TensorProduct.includeLeftSubRight]
  have hz : LinearMap.rTensor N (Algebra.TensorProduct.includeLeftSubRight R (∀ k, B k)) Ξ = 0 :=
    eq_zero_of_rTensor_piPairProj_eq_zero B _ fun i j => by
      rw [← LinearMap.rTensor_comp_apply, hsub, LinearMap.rTensor_sub, LinearMap.sub_apply,
        LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply, hφ, hφ, h i j, sub_self]
  obtain ⟨n, hn⟩ := (kerIncludeLeftSubRightEquiv R (∀ k, B k) (N := N)).surjective ⟨Ξ, hz⟩
  refine ⟨n, fun i => ?_⟩
  have hn' : (1 : ∀ k, B k) ⊗ₜ[R] n = Ξ := congrArg Subtype.val hn
  rw [← hφ i, ← hn']
  simp

omit [Finite ι] in
/-- An equality in a pushout `C` of `B i` and `B j`, read in `B i ⊗[R] B j`. -/
theorem rTensor_include_eq_of_pushout {i j : ι} {C : Type*} [CommRing C] [Algebra R C]
    (inl : B i →ₐ[R] C) (inr : B j →ₐ[R] C)
    (hC : Function.Bijective (Algebra.TensorProduct.productMap inl inr))
    {x : B i ⊗[R] N} {y : B j ⊗[R] N}
    (h : LinearMap.rTensor N inl.toLinearMap x = LinearMap.rTensor N inr.toLinearMap y) :
    LinearMap.rTensor N (Algebra.TensorProduct.includeLeft : B i →ₐ[R] B i ⊗[R] B j).toLinearMap x =
      LinearMap.rTensor N
        (Algebra.TensorProduct.includeRight : B j →ₐ[R] B i ⊗[R] B j).toLinearMap y := by
  let e := LinearEquiv.ofBijective (Algebra.TensorProduct.productMap inl inr).toLinearMap hC
  refine (LinearEquiv.rTensor N e).injective ?_
  have hl : e.toLinearMap ∘ₗ
      (Algebra.TensorProduct.includeLeft : B i →ₐ[R] B i ⊗[R] B j).toLinearMap =
      inl.toLinearMap := by
    ext x
    change Algebra.TensorProduct.productMap inl inr (x ⊗ₜ 1) = _
    simp
  have hr : e.toLinearMap ∘ₗ
      (Algebra.TensorProduct.includeRight : B j →ₐ[R] B i ⊗[R] B j).toLinearMap =
      inr.toLinearMap := by
    ext x
    change Algebra.TensorProduct.productMap inl inr (1 ⊗ₜ x) = _
    simp
  change LinearMap.rTensor N e.toLinearMap _ = LinearMap.rTensor N e.toLinearMap _
  rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, hl, hr]
  exact h

/-- **Descent of linear maps into base changes along a finite jointly faithfully flat family**,
with the overlaps given by arbitrary pushouts.  A family of `R`-linear maps `L i : M → B i ⊗[R] N`
whose images in every pushout `C i j` agree is the family `m ↦ 1 ⊗ f m` of one `R`-linear map
`f : M → N`. -/
theorem exists_linearMap_eq_family_of_pushout [Module.FaithfullyFlat R (∀ i, B i)]
    (C : ι → ι → Type*) [∀ i j, CommRing (C i j)] [∀ i j, Algebra R (C i j)]
    (inl : ∀ i j, B i →ₗ[R] C i j) (inr : ∀ i j, B j →ₗ[R] C i j)
    (inlA : ∀ i j, B i →ₐ[R] C i j) (inrA : ∀ i j, B j →ₐ[R] C i j)
    (hinl : ∀ i j, (inlA i j).toLinearMap = inl i j)
    (hinr : ∀ i j, (inrA i j).toLinearMap = inr i j)
    (hC : ∀ i j, Function.Bijective (Algebra.TensorProduct.productMap (inlA i j) (inrA i j)))
    (L : ∀ i, M →ₗ[R] B i ⊗[R] N)
    (h : ∀ i j m, LinearMap.rTensor N (inl i j) (L i m) = LinearMap.rTensor N (inr i j) (L j m)) :
    ∃ f : M →ₗ[R] N, ∀ i m, L i m = 1 ⊗ₜ f m := by
  classical
  have hex : ∀ m, ∃ n : N, ∀ i, L i m = 1 ⊗ₜ n := fun m =>
    exists_tmul_eq_family B (fun i => L i m) fun i j =>
      rTensor_include_eq_of_pushout B (inlA i j) (inrA i j) (hC i j) (by
        rw [hinl, hinr]; exact h i j m)
  choose n hn using hex
  have hinj : ∀ a b : N, (∀ i, (1 : B i) ⊗ₜ[R] a = 1 ⊗ₜ b) → a = b := by
    intro a b hab
    let _ : Fintype ι := Fintype.ofFinite ι
    have hab' : (1 : ∀ i, B i) ⊗ₜ[R] a = 1 ⊗ₜ b :=
      (TensorProduct.piLeft (R := R) (N := N) (M := B)).injective (funext fun i => by
        simpa using hab i)
    exact Module.FaithfullyFlat.tensorProduct_mk_injective N hab'
  refine ⟨{ toFun := n, map_add' := fun a b => ?_, map_smul' := fun r a => ?_ }, fun i m => hn m i⟩
  · refine hinj _ _ fun i => ?_
    rw [← hn, TensorProduct.tmul_add, ← hn, ← hn, map_add]
  · refine hinj _ _ fun i => ?_
    rw [← hn, map_smul, hn, RingHom.id_apply, TensorProduct.tmul_smul]

/-- **The canonical map out of the tensor product of the two legs of a pushout square of
commutative rings is bijective.** -/
theorem bijective_productMap_of_isPushout {R' A B C : Type u} [CommRing R'] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R' A] [Algebra R' B] [Algebra R' C]
    (inl : A →ₐ[R'] C) (inr : B →ₐ[R'] C)
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap R' A))
      (CommRingCat.ofHom (algebraMap R' B)) (CommRingCat.ofHom inl.toRingHom)
      (CommRingCat.ofHom inr.toRingHom)) :
    Function.Bijective (Algebra.TensorProduct.productMap inl inr) := by
  let t := CommRingCat.isPushout_tensorProduct R' A B
  let φ := t.isoPushout ≪≫ h.isoPushout.symm
  have hl : ∀ a : A, φ.hom (a ⊗ₜ 1) = inl a := fun a => by
    have e1 := congr($(t.inl_isoPushout_hom).hom a)
    have e2 := congr($(h.inl_isoPushout_inv).hom a)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at e1 e2
    change h.isoPushout.inv (t.isoPushout.hom (Algebra.TensorProduct.includeLeftRingHom a)) = _
    rw [e1, e2]
    rfl
  have hr : ∀ b : B, φ.hom (1 ⊗ₜ b) = inr b := fun b => by
    have e1 := congr($(t.inr_isoPushout_hom).hom b)
    have e2 := congr($(h.inr_isoPushout_inv).hom b)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at e1 e2
    change h.isoPushout.inv (t.isoPushout.hom (Algebra.TensorProduct.includeRight.toRingHom b)) = _
    rw [e1, e2]
    rfl
  have heq : ∀ x, Algebra.TensorProduct.productMap inl inr x = φ.hom x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have : (a ⊗ₜ[R'] b : A ⊗[R'] B) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by simp
      rw [this, map_mul, map_mul, hl, hr]
      simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hb : Function.Bijective φ.hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso φ.hom)
  exact (funext heq ▸ hb : _)

end Stacks.Descent

end
