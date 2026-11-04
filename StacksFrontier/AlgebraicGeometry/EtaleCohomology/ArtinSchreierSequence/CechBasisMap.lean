module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechMultiplication
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FreeAdditiveSheaf
public import StacksFrontier.Homology.QuasiIsoFromSingle

/-!
# The map `𝐆_a^r[-q] ⟶ f_* Č` given by Čech cocycles

Let `f : X ⟶ S` be a morphism of schemes, `U` a family of opens of `X` and `z₁, …, z_r` cocycles
of degree `q` of the Čech complex of `V ↦ Γ((S ×_S X) ×_X V)`. Multiplication by the `zᵢ` is a
morphism of complexes of abelian sheaves on the small étale site of `S` from `𝐆_a^r` placed in
degree `q` to the Čech complex of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})`. Its counterpart on the Čech complex
of `Γ(S)`-modules is the map `A^r[-q] ⟶ Č` sending the basis vectors to the `zᵢ`.

## Main definitions

* `Stacks.ArtinSchreier.basisMap`: the morphism of complexes of sheaves.
* `Stacks.ArtinSchreier.moduleBasisMap`: the morphism of complexes of `Γ(S)`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type} (U : ι → X.Opens)

/-- Multiplication by the zero Čech cochain is the zero morphism. -/
theorem cochainMult_zero {n : ℕ} : cochainMult f U (0 : (baseCech f U).X n) = 0 := by
  refine hom_ext U _ fun x => ?_
  rw [cochainMult_comp_π, zero_comp, map_zero]
  exact multMap_zero f (inter U x)

variable {q r : ℕ} (z : Fin r → (baseCech f U).X q)
  (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)

/-- The degree-`q` component of `basisMap`: `b ↦ ∑ᵢ bᵢ zᵢ`. -/
def basisMapDeg : freeAdditiveSheaf S r ⟶ (directImageCech f U).X q :=
  ∑ i, freeAdditiveProj S r i ≫ cochainMult f U (z i)

include hz in
/-- For cocycles `zᵢ`, the degree-`q` component of `basisMap` composed with the Čech differential
is zero. -/
theorem basisMapDeg_comp_d : basisMapDeg f U z ≫ (directImageCech f U).d q (q + 1) = 0 := by
  rw [basisMapDeg, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Category.assoc, cochainMult_comp_d, hz i, cochainMult_zero, comp_zero]

/-- **Multiplication by the cocycles `zᵢ`, `𝐆_a^r[-q] ⟶ Č(U, V ↦ f_*(ι_{V,*} 𝐆_{a,V}))`.** -/
def basisMap :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) q).obj (freeAdditiveSheaf S r) ⟶
      directImageCech f U :=
  HomologicalComplex.mkHomFromSingle (basisMapDeg f U z) (by
    rintro k (rfl : q + 1 = k)
    exact basisMapDeg_comp_d f U z hz)

/-- The degree-`q` component of `moduleBasisMap`: `b ↦ ∑ᵢ bᵢ zᵢ`. -/
def moduleBasisMapDeg : ModuleCat.of Γ(S, ⊤) (Fin r → Γ(S, ⊤)) ⟶ (baseCech f U).X q :=
  ModuleCat.ofHom
    { toFun := fun b => ∑ i, b i • z i
      map_add' := fun b b' => by
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := fun a b => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact Finset.smul_sum.symm }

/-- `moduleBasisMapDeg` sends the `i`-th basis vector to `zᵢ`. -/
theorem moduleBasisMapDeg_single (i : Fin r) :
    moduleBasisMapDeg f U z (Pi.single i (1 : Γ(S, ⊤)) : Fin r → Γ(S, ⊤)) = z i := by
  show ∑ j, (Pi.single i (1 : Γ(S, ⊤)) : Fin r → Γ(S, ⊤)) j • z j = z i
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

include hz in
/-- For cocycles `zᵢ`, the degree-`q` component of `moduleBasisMap` composed with the Čech
differential is zero. -/
theorem moduleBasisMapDeg_comp_d :
    moduleBasisMapDeg f U z ≫ (baseCech f U).d q (q + 1) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  show ((baseCech f U).d q (q + 1)).hom (∑ i, b i • z i) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, hz i, smul_zero]

/-- **The map `A^r[-q] ⟶ Č` sending the basis vectors to the cocycles `zᵢ`**, `A = Γ(S)`. -/
def moduleBasisMap :
    (HomologicalComplex.single _ (ComplexShape.up ℕ) q).obj
        (ModuleCat.of Γ(S, ⊤) (Fin r → Γ(S, ⊤))) ⟶ baseCech f U :=
  HomologicalComplex.mkHomFromSingle (moduleBasisMapDeg f U z) (by
    rintro k (rfl : q + 1 = k)
    exact moduleBasisMapDeg_comp_d f U z hz)

end Stacks.ArtinSchreier

end
