module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.CategoryTheory.Sites.Point.FiniteGerms

/-!
# Germs of tensor products at a point of a site

Let `Φ` be a point of a site, let `P` be a presheaf of commutative rings, and let `Γ` be a ring
mapping compatibly to all the rings of sections `P(X)` — the ring of global sections of `P`, say
— and to the fibre `P_Φ`.  For a `Γ`-module `M`, tensoring with `M` commutes with taking the
fibre at `Φ`: the maps `P(X) ⊗_Γ M ⟶ P_Φ ⊗_Γ M` induced by the germ maps exhibit `P_Φ ⊗_Γ M`
as the filtered colimit of the `P(X) ⊗_Γ M` over the neighbourhoods of `Φ`.  This file proves
the two elementwise halves of that statement.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.germTensor`: the map `P(X) ⊗_Γ M ⟶ P_Φ ⊗_Γ M`.
* `CategoryTheory.GrothendieckTopology.Point.restrictTensor`: the restriction
  `P(X) ⊗_Γ M ⟶ P(Y) ⊗_Γ M` along `Y ⟶ X`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.exists_germTensor_eq`: every element of
  `P_Φ ⊗_Γ M` is the germ of an element over a neighbourhood refining a given one.
* `CategoryTheory.GrothendieckTopology.Point.exists_restrictTensor_eq_zero`: an element whose
  germ vanishes vanishes on a smaller neighbourhood.

## Implementation notes

The vanishing statement is first proved for a free module `ι →₀ Γ`, where
`TensorProduct.finsuppScalarRight` reduces it to finitely many coordinates, and then for an
arbitrary `M` by right exactness of the tensor product (`LinearMap.lTensor_exact`) applied to the
canonical presentation `(K →₀ Γ) ⟶ (M →₀ Γ) ⟶ M ⟶ 0`, with `K` the kernel of the second map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w v u t

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ CommRingCat.{w}) {Γ : Type t} [CommRing Γ]
  (ε : ∀ X : C, Γ →+* P.obj (op X))
  (hε : ∀ {X Y : C} (f : Y ⟶ X) (γ : Γ), P.map f.op (ε X γ) = ε Y γ)
  (εΦ : Γ →+* (Φ.presheafFiber (A := CommRingCat.{w})).obj P)
  (hεΦ : ∀ (X : C) (x : Φ.fiber.obj X) (γ : Γ), Φ.toPresheafFiber X x P (ε X γ) = εΦ γ)

/-- The germ map at a neighbourhood, as a `Γ`-linear map. -/
noncomputable def germLinear (X : C) (x : Φ.fiber.obj X) :
    letI := (ε X).toAlgebra
    letI := εΦ.toAlgebra
    P.obj (op X) →ₗ[Γ] (Φ.presheafFiber (A := CommRingCat.{w})).obj P :=
  letI := (ε X).toAlgebra
  letI := εΦ.toAlgebra
  { toFun := Φ.toPresheafFiber X x P
    map_add' := map_add _
    map_smul' := fun γ o => (map_mul _ (ε X γ) o).trans (congrArg (· * _) (hεΦ X x γ)) }

/-- The restriction map along `f : Y ⟶ X`, as a `Γ`-linear map. -/
noncomputable def restrictLinear {X Y : C} (f : Y ⟶ X) :
    letI := (ε X).toAlgebra
    letI := (ε Y).toAlgebra
    P.obj (op X) →ₗ[Γ] P.obj (op Y) :=
  letI := (ε X).toAlgebra
  letI := (ε Y).toAlgebra
  { toFun := P.map f.op
    map_add' := map_add _
    map_smul' := fun γ o => (map_mul _ (ε X γ) o).trans (congrArg (· * _) (hε f γ)) }

variable (M : Type*) [AddCommGroup M] [Module Γ M]

/-- **The germ map on tensor products** `P(X) ⊗_Γ M ⟶ P_Φ ⊗_Γ M`. -/
noncomputable def germTensor (X : C) (x : Φ.fiber.obj X) :
    letI := (ε X).toAlgebra
    letI := εΦ.toAlgebra
    P.obj (op X) ⊗[Γ] M →ₗ[Γ] (Φ.presheafFiber (A := CommRingCat.{w})).obj P ⊗[Γ] M :=
  letI := (ε X).toAlgebra
  letI := εΦ.toAlgebra
  (germLinear Φ P ε εΦ hεΦ X x).rTensor M

/-- **The restriction map on tensor products** `P(X) ⊗_Γ M ⟶ P(Y) ⊗_Γ M` along `Y ⟶ X`. -/
noncomputable def restrictTensor {X Y : C} (f : Y ⟶ X) :
    letI := (ε X).toAlgebra
    letI := (ε Y).toAlgebra
    P.obj (op X) ⊗[Γ] M →ₗ[Γ] P.obj (op Y) ⊗[Γ] M :=
  letI := (ε X).toAlgebra
  letI := (ε Y).toAlgebra
  (restrictLinear P ε hε f).rTensor M

omit [LocallySmall.{w, v, u} C] in
/-- The germ map on tensor products sends `o ⊗ₜ m` to the germ of `o` at `x` tensored with `m`. -/
theorem germTensor_tmul (X : C) (x : Φ.fiber.obj X) (o : P.obj (op X)) (m : M) :
    letI := (ε X).toAlgebra
    letI := εΦ.toAlgebra
    germTensor Φ P ε εΦ hεΦ M X x (o ⊗ₜ m) = Φ.toPresheafFiber X x P o ⊗ₜ m :=
  rfl

omit [LocallySmall.{w, v, u} C] in
/-- The restriction map on tensor products sends `o ⊗ₜ m` to the restriction of `o` tensored with
`m`. -/
theorem restrictTensor_tmul {X Y : C} (f : Y ⟶ X) (o : P.obj (op X)) (m : M) :
    letI := (ε X).toAlgebra
    letI := (ε Y).toAlgebra
    restrictTensor P ε hε M f (o ⊗ₜ m) = P.map f.op o ⊗ₜ m :=
  rfl

omit [LocallySmall.{w, v, u} C] in
/-- Germs of restrictions are germs. -/
theorem germTensor_restrictTensor {X Y : C} (f : Y ⟶ X) (y : Φ.fiber.obj Y)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] M) :
    germTensor Φ P ε εΦ hεΦ M Y y (restrictTensor P ε hε M f t) =
      germTensor Φ P ε εΦ hεΦ M X (Φ.fiber.map f y) t := by
  let := (ε X).toAlgebra
  let := (ε Y).toAlgebra
  let := εΦ.toAlgebra
  have : germLinear Φ P ε εΦ hεΦ Y y ∘ₗ restrictLinear P ε hε f =
      germLinear Φ P ε εΦ hεΦ X (Φ.fiber.map f y) :=
    LinearMap.ext fun o => Φ.toPresheafFiber_w_apply f y P o
  exact LinearMap.congr_fun (LinearMap.rTensor_comp (R := Γ) (M := M) .. |>.symm.trans
    (congrArg (LinearMap.rTensor M) this)) t

omit [LocallySmall.{w, v, u} C] in
/-- Restriction along a composite is the composite of restrictions. -/
theorem restrictTensor_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] M) :
    restrictTensor P ε hε M (g ≫ f) t =
      restrictTensor P ε hε M g (restrictTensor P ε hε M f t) := by
  let := (ε X).toAlgebra
  let := (ε Y).toAlgebra
  let := (ε Z).toAlgebra
  have : restrictLinear P ε hε (g ≫ f) = restrictLinear P ε hε g ∘ₗ restrictLinear P ε hε f :=
    LinearMap.ext fun o => by
      simp only [restrictLinear, op_comp, P.map_comp]; rfl
  exact LinearMap.congr_fun ((congrArg (LinearMap.rTensor M) this).trans
    (LinearMap.rTensor_comp ..)) t

/-- **Every element of `P_Φ ⊗_Γ M` comes from a neighbourhood**, which may be chosen below any
given neighbourhood. -/
theorem exists_germTensor_eq {X₀ : C} (x₀ : Φ.fiber.obj X₀)
    (ξ : letI := εΦ.toAlgebra; (Φ.presheafFiber (A := CommRingCat.{w})).obj P ⊗[Γ] M) :
    ∃ (X : C) (g : X ⟶ X₀) (x : Φ.fiber.obj X), Φ.fiber.map g x = x₀ ∧
      ∃ t : (letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] M),
        germTensor Φ P ε εΦ hεΦ M X x t = ξ := by
  let := εΦ.toAlgebra
  obtain ⟨T, rfl⟩ := TensorProduct.exists_finset ξ
  obtain ⟨X, g, x, hx, s, hs⟩ := Φ.exists_toPresheafFiber_eq_fin x₀ T.card
    (fun k => (T.equivFin.symm k).1.1)
  let := (ε X).toAlgebra
  refine ⟨X, g, x, hx, ∑ k : Fin T.card, s k ⊗ₜ (T.equivFin.symm k).1.2, ?_⟩
  simp only [map_sum, germTensor_tmul, hs]
  rw [← Finset.sum_coe_sort T fun i => i.1 ⊗ₜ[Γ] i.2]
  exact Fintype.sum_equiv T.equivFin.symm _ _ (fun _ => rfl)

/-- **The vanishing for a free module**: an element of `P(X) ⊗_Γ (ι →₀ Γ)` whose germ vanishes
vanishes on a smaller neighbourhood. -/
theorem exists_restrictTensor_eq_zero_finsupp {ι : Type*} {X : C} (x : Φ.fiber.obj X)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] (ι →₀ Γ))
    (ht : germTensor Φ P ε εΦ hεΦ (ι →₀ Γ) X x t = 0) :
    ∃ (Y : C) (h : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map h y = x ∧
      restrictTensor P ε hε (ι →₀ Γ) h t = 0 := by
  classical
  let := (ε X).toAlgebra
  let := εΦ.toAlgebra
  let e := TensorProduct.finsuppScalarRight Γ Γ (P.obj (op X)) ι
  let eΦ := TensorProduct.finsuppScalarRight Γ Γ
    ((Φ.presheafFiber (A := CommRingCat.{w})).obj P) ι
  have hcoord : ∀ (t' : P.obj (op X) ⊗[Γ] (ι →₀ Γ)) i,
      Φ.toPresheafFiber X x P (e t' i) = eΦ (germTensor Φ P ε εΦ hεΦ _ X x t') i := by
    intro t' i
    induction t' using TensorProduct.induction_on with
    | zero => simp
    | tmul o p =>
      simp only [e, eΦ, germTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply]
      exact (germLinear Φ P ε εΦ hεΦ X x).map_smul (p i) o
    | add a b ha hb =>
      rw [map_add, Finsupp.add_apply, map_add, ha, hb, map_add, map_add, Finsupp.add_apply]
  have hzero : ∀ i, Φ.toPresheafFiber X x P (e t i) = 0 := fun i => by
    rw [hcoord t, ht, map_zero, Finsupp.zero_apply]
  let S := (e t).support
  obtain ⟨Y, h, y, hy, hvan⟩ := Φ.exists_map_eq_zero_fin x S.card
    (fun k => e t (S.equivFin.symm k).1) (fun k => hzero _)
  let := (ε Y).toAlgebra
  let eY := TensorProduct.finsuppScalarRight Γ Γ (P.obj (op Y)) ι
  refine ⟨Y, h, y, hy, eY.injective ?_⟩
  rw [map_zero]
  ext i
  have hres : ∀ t' : P.obj (op X) ⊗[Γ] (ι →₀ Γ),
      eY (restrictTensor P ε hε _ h t') i = P.map h.op (e t' i) := by
    intro t'
    induction t' using TensorProduct.induction_on with
    | zero => simp
    | tmul o p =>
      simp only [eY, e, restrictTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply]
      exact ((restrictLinear P ε hε h).map_smul (p i) o).symm
    | add a b ha hb =>
      rw [map_add, map_add, Finsupp.add_apply, ha, hb, map_add, Finsupp.add_apply, map_add]
  rw [hres t, Finsupp.zero_apply]
  by_cases hi : i ∈ S
  · simpa only [Equiv.symm_apply_apply] using hvan (S.equivFin ⟨i, hi⟩)
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero]

omit [LocallySmall.{w, v, u} C] in
/-- The germ map on tensor products is natural in the module. -/
theorem germTensor_lTensor {N N' : Type*} [AddCommGroup N] [Module Γ N] [AddCommGroup N']
    [Module Γ N'] (φ : N →ₗ[Γ] N') (X : C) (x : Φ.fiber.obj X)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] N) :
    letI := (ε X).toAlgebra
    letI := εΦ.toAlgebra
    germTensor Φ P ε εΦ hεΦ N' X x (φ.lTensor _ t) =
      φ.lTensor _ (germTensor Φ P ε εΦ hεΦ N X x t) := by
  let := (ε X).toAlgebra
  let := εΦ.toAlgebra
  exact LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor ..|>.trans
    (LinearMap.lTensor_comp_rTensor ..).symm) t

omit [LocallySmall.{w, v, u} C] in
/-- The restriction map on tensor products is natural in the module. -/
theorem restrictTensor_lTensor {N N' : Type*} [AddCommGroup N] [Module Γ N] [AddCommGroup N']
    [Module Γ N'] (φ : N →ₗ[Γ] N') {X Y : C} (f : Y ⟶ X)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] N) :
    letI := (ε X).toAlgebra
    letI := (ε Y).toAlgebra
    restrictTensor P ε hε N' f (φ.lTensor _ t) = φ.lTensor _ (restrictTensor P ε hε N f t) := by
  let := (ε X).toAlgebra
  let := (ε Y).toAlgebra
  exact LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor ..|>.trans
    (LinearMap.lTensor_comp_rTensor ..).symm) t

/-- **An element whose germ vanishes vanishes on a smaller neighbourhood.** -/
theorem exists_restrictTensor_eq_zero {X : C} (x : Φ.fiber.obj X)
    (t : letI := (ε X).toAlgebra; P.obj (op X) ⊗[Γ] M)
    (ht : germTensor Φ P ε εΦ hεΦ M X x t = 0) :
    ∃ (Y : C) (h : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map h y = x ∧
      restrictTensor P ε hε M h t = 0 := by
  classical
  let := (ε X).toAlgebra
  let := εΦ.toAlgebra
  let π : (M →₀ Γ) →ₗ[Γ] M := Finsupp.linearCombination Γ _root_.id
  have hπ : Function.Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let K := LinearMap.ker π
  let ψ : (K →₀ Γ) →ₗ[Γ] (M →₀ Γ) := Finsupp.linearCombination Γ K.subtype
  have hπψ : π ∘ₗ ψ = 0 := by
    ext k
    simp [ψ, π]
  have hexact : Function.Exact ψ π := fun y =>
    ⟨fun hy => ⟨Finsupp.single ⟨y, hy⟩ 1, by simp [ψ]⟩,
      by rintro ⟨z, rfl⟩; exact LinearMap.congr_fun hπψ z⟩
  obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective (P.obj (op X)) hπ t
  have h1 : π.lTensor _ (germTensor Φ P ε εΦ hεΦ (M →₀ Γ) X x s) = 0 := by
    rwa [← germTensor_lTensor]
  obtain ⟨z, hz⟩ := (lTensor_exact ((Φ.presheafFiber (A := CommRingCat.{w})).obj P)
    hexact hπ _).mp h1
  obtain ⟨X₁, g₁, x₁, hx₁, z₁, hz₁⟩ := exists_germTensor_eq Φ P ε εΦ hεΦ (K →₀ Γ) x z
  let := (ε X₁).toAlgebra
  let d := restrictTensor P ε hε (M →₀ Γ) g₁ s - ψ.lTensor _ z₁
  have hd : germTensor Φ P ε εΦ hεΦ (M →₀ Γ) X₁ x₁ d = 0 := by
    rw [map_sub, germTensor_restrictTensor, hx₁, germTensor_lTensor, hz₁, hz, sub_self]
  obtain ⟨Y, h, y, hy, hvan⟩ :=
    exists_restrictTensor_eq_zero_finsupp Φ P ε hε εΦ hεΦ x₁ d hd
  let := (ε Y).toAlgebra
  refine ⟨Y, h ≫ g₁, y, by rw [Functor.map_comp_apply, hy, hx₁], ?_⟩
  have hs : restrictTensor P ε hε (M →₀ Γ) g₁ s = d + ψ.lTensor _ z₁ := by
    simp only [d, sub_add_cancel]
  rw [restrictTensor_lTensor, restrictTensor_comp, hs, map_add, hvan, zero_add,
    restrictTensor_lTensor, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπψ,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

end CategoryTheory.GrothendieckTopology.Point

end
