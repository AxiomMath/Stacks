module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences

/-!
# The commutativity constraint of the tensor product of correspondences

Comparison of blocks of the decompositions into equidimensional parts with different indices,
the tensor product on pure tensors of pure blocks, and commutativity: transporting `c ⊗ c'`
along the factor switches gives `c' ⊗ c` (Stacks 0FG7).

## Main results

* `Stacks.WeilCohomology.corrEquivOfIso_tensor_swap`: commutativity.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-! ### Comparing blocks with different indices -/

section Blocks

variable {P Q : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S) (sQ : Q ⟶ (fieldChowSituation k).S)
  [Smooth sP] [IsSeparated sP] [Smooth sQ] [IsSeparated sQ]

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Congruence for pure blocks. -/
theorem lof_lof_congr {r : ℤ} {n m : ℕ}
    {z z' : Correspondence (fieldChowSituation k) (partBase sP n) (partBase sQ m) m r}
    (h : z = z') :
    (DirectSum.lof ℚ ℕ _ n (DirectSum.lof ℚ ℕ _ m z) : Corr k sP sQ r) =
      DirectSum.lof ℚ ℕ _ n (DirectSum.lof ℚ ℕ _ m z') := by
  rw [h]

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Two pure blocks of correspondences with equal indices and heterogeneously equal classes
agree, up to the identification of degrees. -/
theorem lof_lof_eq_corrCongr {r r' : ℤ} (h : r' = r) {n n' m m' : ℕ} (hn : n = n')
    (hm : m = m') (q : ℚ)
    (z : Correspondence (fieldChowSituation k) (partBase sP n) (partBase sQ m) m r)
    (z' : Correspondence (fieldChowSituation k) (partBase sP n') (partBase sQ m') m' r')
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sP n) (partBase sQ m)) ((m : ℤ) - r))
    (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sP n') (partBase sQ m'))
      ((m' : ℤ) - r'))
    (hz : z = q ⊗ₜ[ℤ] α) (hz' : z' = q ⊗ₜ[ℤ] α') (hα : α ≍ α') :
    (DirectSum.lof ℚ ℕ _ n (DirectSum.lof ℚ ℕ _ m z) : Corr k sP sQ r) =
      corrCongr k sP sQ h (DirectSum.lof ℚ ℕ _ n' (DirectSum.lof ℚ ℕ _ m' z')) := by
  subst hn hm h hz hz'
  rw [corrCongr_self, eq_of_heq hα]

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Pushforwards into two blocks of `P × Q` with equal indices agree when the two morphisms agree
on `P × Q`. -/
theorem properChowPushforward_parts_heq {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType sW] {n n' m m' : ℕ} (hn : n = n') (hm : m = m')
    (u : W ⟶ Limits.pullback (partBase sP n) (partBase sQ m)) [IsProper u]
    (hu : u ≫ prodBase (partBase sP n) (partBase sQ m) = sW)
    (u' : W ⟶ Limits.pullback (partBase sP n') (partBase sQ m')) [IsProper u']
    (hu' : u' ≫ prodBase (partBase sP n') (partBase sQ m') = sW)
    (h : u ≫ prodHom sP sQ (partBase sP n) (partBase sQ m) (dimPart sP n).ι (dimPart sQ m).ι rfl
        rfl = u' ≫ prodHom sP sQ (partBase sP n') (partBase sQ m') (dimPart sP n').ι
          (dimPart sQ m').ι rfl rfl)
    {i i' : ℤ} (hi : i = i') (α : chowGroup (fieldChowSituation k) sW i)
    (α' : chowGroup (fieldChowSituation k) sW i') (hα : α ≍ α') :
    pf[sW, prodBase (partBase sP n) (partBase sQ m), u, hu, i] α ≍
      pf[sW, prodBase (partBase sP n') (partBase sQ m'), u', hu', i'] α' := by
  subst hn hm hi
  obtain rfl := eq_of_heq hα
  obtain rfl : u = u' := (cancel_mono _).1 h
  rfl

/-- Linear maps out of correspondences of mixed dimension agree once they agree on pure tensors of
pure blocks. -/
private theorem linearMap_ext_of_lof_lof {P₁ Q₁ : Scheme.{u}}
    (sP₁ : P₁ ⟶ (fieldChowSituation k).S) (sQ₁ : Q₁ ⟶ (fieldChowSituation k).S) [Smooth sP₁]
    [Smooth sQ₁] {M : Type*} [AddCommMonoid M] [Module ℚ M] {r : ℤ}
    (F G : Corr k sP₁ sQ₁ r →ₗ[ℚ] M)
    (h : ∀ (d e : ℕ) (q : ℚ)
      (α : chowGroup (fieldChowSituation k) (prodBase (partBase sP₁ d) (partBase sQ₁ e))
        ((e : ℤ) - r)),
      F (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α))) =
        G (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))) :
    F = G := by
  refine DirectSum.linearMap_ext ℚ fun d ↦ DirectSum.linearMap_ext ℚ fun e ↦
    LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul q α => exact h d e q α

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Two `ℚ`-bilinear maps on correspondences of mixed dimension agree once they agree on pure
tensors of pure blocks. -/
theorem corr_bilinear_ext {P' Q' : Scheme.{u}} (sP' : P' ⟶ (fieldChowSituation k).S)
    (sQ' : Q' ⟶ (fieldChowSituation k).S) [Smooth sP'] [IsSeparated sP'] [Smooth sQ']
    [IsSeparated sQ'] {M : Type*} [AddCommMonoid M] [Module ℚ M] {r r' : ℤ}
    (F G : Corr k sP sQ r →ₗ[ℚ] Corr k sP' sQ' r' →ₗ[ℚ] M)
    (h : ∀ (d e d' e' : ℕ) (q q' : ℚ)
      (α : chowGroup (fieldChowSituation k) (prodBase (partBase sP d) (partBase sQ e))
        ((e : ℤ) - r))
      (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sP' d') (partBase sQ' e'))
        ((e' : ℤ) - r')),
      F (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α'))) =
        G (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α')))) :
    F = G :=
  linearMap_ext_of_lof_lof k sP sQ F G fun d e q α ↦
    linearMap_ext_of_lof_lof k sP' sQ' _ _ fun d' e' q' α' ↦ h d e d' e' q q' α α'

omit [IsSeparated sP] [IsSeparated sQ] in
/-- `Stacks.WeilCohomology.corr_bilinear_ext` for two bilinear maps followed by linear
equivalences, with the arguments of the second map exchanged. -/
theorem corr_bilinear_ext_swap {P' Q' : Scheme.{u}} (sP' : P' ⟶ (fieldChowSituation k).S)
    (sQ' : Q' ⟶ (fieldChowSituation k).S) [Smooth sP'] [IsSeparated sP'] [Smooth sQ']
    [IsSeparated sQ'] {M N₁ N₂ : Type*} [AddCommMonoid M] [Module ℚ M] [AddCommMonoid N₁]
    [Module ℚ N₁] [AddCommMonoid N₂] [Module ℚ N₂] {r r' : ℤ}
    (F : Corr k sP sQ r →ₗ[ℚ] Corr k sP' sQ' r' →ₗ[ℚ] N₁) (eF : N₁ ≃ₗ[ℚ] M)
    (G : Corr k sP' sQ' r' →ₗ[ℚ] Corr k sP sQ r →ₗ[ℚ] N₂) (eG : N₂ ≃ₗ[ℚ] M)
    (h : ∀ (d e d' e' : ℕ) (q q' : ℚ)
      (α : chowGroup (fieldChowSituation k) (prodBase (partBase sP d) (partBase sQ e))
        ((e : ℤ) - r))
      (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sP' d') (partBase sQ' e'))
        ((e' : ℤ) - r')),
      eF (F (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α')))) =
        eG (G (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α')))
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))))
    (a : Corr k sP sQ r) (b : Corr k sP' sQ' r') : eF (F a b) = eG (G b a) :=
  LinearMap.congr_fun₂ (corr_bilinear_ext k sP sQ sP' sQ' (F.compr₂ eF.toLinearMap)
    (G.flip.compr₂ eG.toLinearMap) h) a b

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Two `ℚ`-linear maps on correspondences of mixed dimension agree once they agree on pure
tensors of pure blocks. -/
theorem corr_linear_ext {M : Type*} [AddCommMonoid M] [Module ℚ M] {r : ℤ}
    (F G : Corr k sP sQ r →ₗ[ℚ] M)
    (h : ∀ (d e : ℕ) (q : ℚ)
      (α : chowGroup (fieldChowSituation k) (prodBase (partBase sP d) (partBase sQ e))
        ((e : ℤ) - r)),
      F (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α))) =
        G (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))) :
    F = G :=
  linearMap_ext_of_lof_lof k sP sQ F G h

omit [IsSeparated sP] [IsSeparated sQ] in
/-- Three `ℚ`-linear maps composed in two ways agree on correspondences of mixed dimension once
they agree on pure tensors of pure blocks. -/
theorem corr_trilinear_ext {P₂ Q₂ P₃ Q₃ : Scheme.{u}} (sP₂ : P₂ ⟶ (fieldChowSituation k).S)
    (sQ₂ : Q₂ ⟶ (fieldChowSituation k).S) (sP₃ : P₃ ⟶ (fieldChowSituation k).S)
    (sQ₃ : Q₃ ⟶ (fieldChowSituation k).S) [Smooth sP₂] [IsSeparated sP₂] [Smooth sQ₂]
    [IsSeparated sQ₂] [Smooth sP₃] [IsSeparated sP₃] [Smooth sQ₃] [IsSeparated sQ₃]
    {M N₁ N₂ N₁₂ N₂₃ : Type*} [AddCommMonoid M] [Module ℚ M] [AddCommMonoid N₁] [Module ℚ N₁]
    [AddCommMonoid N₂] [Module ℚ N₂] [AddCommMonoid N₁₂] [Module ℚ N₁₂] [AddCommMonoid N₂₃]
    [Module ℚ N₂₃] {r₁ r₂ r₃ : ℤ}
    (A : Corr k sP sQ r₁ →ₗ[ℚ] Corr k sP₂ sQ₂ r₂ →ₗ[ℚ] N₁₂)
    (B : N₁₂ →ₗ[ℚ] Corr k sP₃ sQ₃ r₃ →ₗ[ℚ] N₁) (eF : N₁ ≃ₗ[ℚ] M)
    (A' : Corr k sP₂ sQ₂ r₂ →ₗ[ℚ] Corr k sP₃ sQ₃ r₃ →ₗ[ℚ] N₂₃)
    (B' : Corr k sP sQ r₁ →ₗ[ℚ] N₂₃ →ₗ[ℚ] N₂) (eG : N₂ ≃ₗ[ℚ] M)
    (h : ∀ (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ) (q₁ q₂ q₃ : ℚ)
      (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sP d₁) (partBase sQ e₁))
        ((e₁ : ℤ) - r₁))
      (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sP₂ d₂) (partBase sQ₂ e₂))
        ((e₂ : ℤ) - r₂))
      (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sP₃ d₃) (partBase sQ₃ e₃))
        ((e₃ : ℤ) - r₃)),
      eF (B (A (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁)))
          (DirectSum.lof ℚ ℕ _ d₂ (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂))))
          (DirectSum.lof ℚ ℕ _ d₃ (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃)))) =
        eG (B' (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁)))
          (A' (DirectSum.lof ℚ ℕ _ d₂ (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂)))
            (DirectSum.lof ℚ ℕ _ d₃ (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃))))))
    (a₁ : Corr k sP sQ r₁) (a₂ : Corr k sP₂ sQ₂ r₂) (a₃ : Corr k sP₃ sQ₃ r₃) :
    eF (B (A a₁ a₂) a₃) = eG (B' a₁ (A' a₂ a₃)) := by
  have key : A.compr₂ (B.compr₂ eF.toLinearMap) =
      (LinearMap.llcomp ℚ (Corr k sP₃ sQ₃ r₃) N₂₃ M).compl₁₂ (B'.compr₂ eG.toLinearMap) A' :=
    corr_bilinear_ext k sP sQ sP₂ sQ₂ _ _ fun d₁ e₁ d₂ e₂ q₁ q₂ α₁ α₂ ↦
      corr_linear_ext k sP₃ sQ₃ _ _ fun d₃ e₃ q₃ α₃ ↦ h d₁ e₁ d₂ e₂ d₃ e₃ q₁ q₂ q₃ α₁ α₂ α₃
  exact LinearMap.congr_fun (LinearMap.congr_fun₂ key a₁ a₂) a₃

end Blocks

/-! ### The tensor product on pure tensors of pure blocks -/

section Tmul

variable {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY']

/-- The tensor product of two pure tensors of pure blocks: `pr₁₃^* α · pr₂₄^* α'` pushed into the
block of the product. -/
theorem tensor_lof_lof_tmul (Δ : DiagonalClassFamily k) (r r' : ℤ) (d e d' e' : ℕ) (q q' : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sX d) (partBase sY e)) ((e : ℤ) - r))
    (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sX' d') (partBase sY' e'))
      ((e' : ℤ) - r')) :
    tensor k sX sX' sY sY' Δ r r' (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
        (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α'))) =
      DirectSum.lof ℚ ℕ _ (d + d') (DirectSum.lof ℚ ℕ _ (e + e') ((q * q') ⊗ₜ[ℤ]
        pf[tensorBase (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e'),
          prodBase (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e')),
          tensorBlockHom k sX sX' sY sY' d d' e e',
          tensorBlockHom_comp_prodBase k sX sX' sY sY' d d' e e', ((e + e' : ℕ) : ℤ) - (r + r')]
          (tensorInt k (partBase sX d) (partBase sX' d') (partBase sY e) (partBase sY' e') Δ
            (relativeDimension_partBase sX d) (relativeDimension_partBase sX' d')
            (relativeDimension_partBase sY e) (relativeDimension_partBase sY' e') r r' α α'))) := by
  rw [tensor_lof_lof, tensorBlock_tmul, tensorBlockInclusion_tmul]

end Tmul

/-! ### Commutativity -/

section Swap

variable {A A' B B' : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  [Smooth sA] [IsSeparated sA] [Smooth sA'] [IsSeparated sA'] [Smooth sB] [IsSeparated sB]
  [Smooth sB'] [IsSeparated sB'] [IsProper sA] [IsProper sA'] [IsProper sB] [IsProper sB']

omit [IsSeparated sA] [IsSeparated sA'] [IsSeparated sB] [IsSeparated sB'] [IsProper sA]
  [IsProper sA'] [IsProper sB] [IsProper sB'] in
/-- The factor switches on a block of the fourfold product, read in the fourfold product. -/
theorem tensorBlockHom_swap (d d' e e' : ℕ) :
    (tensorBlockHom k sA sA' sB sB' d d' e e' ≫
        prodHom (partBase (prodBase sA' sA) (d + d')) (partBase (prodBase sB' sB) (e + e'))
          (partBase (prodBase sA sA') (d + d')) (partBase (prodBase sB sB') (e + e'))
          (partMap (prodBase sA' sA) (prodBase sA sA') (pullbackSymmetry sA sA').hom
            (pullbackSymmetry_hom_comp_base sA sA') (d + d'))
          (partMap (prodBase sB' sB) (prodBase sB sB') (pullbackSymmetry sB sB').hom
            (pullbackSymmetry_hom_comp_base sB sB') (e + e'))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)) ≫
        prodHom (prodBase sA' sA) (prodBase sB' sB) (partBase (prodBase sA' sA) (d + d'))
          (partBase (prodBase sB' sB) (e + e')) (dimPart (prodBase sA' sA) (d + d')).ι
          (dimPart (prodBase sB' sB) (e + e')).ι rfl rfl =
      (tensorSwap k (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e') ≫
        tensorBlockHom k sA' sA sB' sB d' d e' e) ≫
        prodHom (prodBase sA' sA) (prodBase sB' sB) (partBase (prodBase sA' sA) (d' + d))
          (partBase (prodBase sB' sB) (e' + e)) (dimPart (prodBase sA' sA) (d' + d)).ι
          (dimPart (prodBase sB' sB) (e' + e)).ι rfl rfl := by
  apply Limits.pullback.hom_ext <;> apply Limits.pullback.hom_ext <;>
    simp [tensorBlockHom, tensorSwap]

/-- Commutativity on a block, on integral Chow groups: the factor switch of `c ⊗ c'`, read in the
block of the product, is `c' ⊗ c`. -/
theorem tensorInt_swap_parts_heq (r r' : ℤ) (d e d' e' : ℕ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e)) ((e : ℤ) - r))
    (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sA' d') (partBase sB' e'))
      ((e' : ℤ) - r')) :
    pf[tensorBase (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e'),
        prodBase (partBase (prodBase sA' sA) (d + d')) (partBase (prodBase sB' sB) (e + e')),
        tensorBlockHom k sA sA' sB sB' d d' e e' ≫
          prodHom (partBase (prodBase sA' sA) (d + d')) (partBase (prodBase sB' sB) (e + e'))
            (partBase (prodBase sA sA') (d + d')) (partBase (prodBase sB sB') (e + e'))
            (partMap (prodBase sA' sA) (prodBase sA sA') (pullbackSymmetry sA sA').hom
              (pullbackSymmetry_hom_comp_base sA sA') (d + d'))
            (partMap (prodBase sB' sB) (prodBase sB sB') (pullbackSymmetry sB sB').hom
              (pullbackSymmetry_hom_comp_base sB sB') (e + e'))
            (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _),
        by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase],
        ((e + e' : ℕ) : ℤ) - (r + r')]
        (tensorInt k (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e')
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA d)
          (relativeDimension_partBase sA' d') (relativeDimension_partBase sB e)
          (relativeDimension_partBase sB' e') r r' α α') ≍
      pf[tensorBase (partBase sA' d') (partBase sA d) (partBase sB' e') (partBase sB e),
        prodBase (partBase (prodBase sA' sA) (d' + d)) (partBase (prodBase sB' sB) (e' + e)),
        tensorBlockHom k sA' sA sB' sB d' d e' e,
        tensorBlockHom_comp_prodBase k sA' sA sB' sB d' d e' e, ((e' + e : ℕ) : ℤ) - (r' + r)]
        (tensorInt k (partBase sA' d') (partBase sA d) (partBase sB' e') (partBase sB e)
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA' d')
          (relativeDimension_partBase sA d) (relativeDimension_partBase sB' e')
          (relativeDimension_partBase sB e) r' r α' α) := by
  have hsymm := tensorInt_symm k (partBase sA d) (partBase sA' d') (partBase sB e)
    (partBase sB' e') (relativeDimension_partBase sA d) (relativeDimension_partBase sA' d')
    (relativeDimension_partBase sB e) (relativeDimension_partBase sB' e') r r' α α'
  have hcomp := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _
    (tensorSwap k (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e'))
    (tensorBlockHom k sA' sA sB' sB d' d e' e) _ rfl (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (tensorBlockHom_comp_prodBase k sA' sA sB' sB d' d e' e) (by
      rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase])
    (((e + e' : ℕ) : ℤ) - (r + r')) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (tensorInt k (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e')
      (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA d)
      (relativeDimension_partBase sA' d') (relativeDimension_partBase sB e)
      (relativeDimension_partBase sB' e') r r' α α')
  refine (properChowPushforward_parts_heq k (prodBase sA' sA) (prodBase sB' sB) _
    (Nat.add_comm d d') (Nat.add_comm e e') _ _
    (tensorSwap k (partBase sA d) (partBase sA' d') (partBase sB e) (partBase sB' e') ≫
      tensorBlockHom k sA' sA sB' sB d' d e' e)
    (by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase])
    (tensorBlockHom_swap k sA sA' sB sB' d d' e e') rfl _ _ HEq.rfl).trans ?_
  rw [hcomp]
  exact properChowPushforward_heq_congr (fieldChowSituation k) _ _
    (tensorBlockHom k sA' sA sB' sB d' d e' e)
    (tensorBlockHom_comp_prodBase k sA' sA sB' sB d' d e' e) (by push_cast; ring)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _ hsymm

/-- **Commutativity of the tensor product of correspondences** on pure blocks. -/
theorem corrEquivOfIso_tensor_swap_tmul (r r' : ℤ) (d e d' e' : ℕ) (q q' : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e)) ((e : ℤ) - r))
    (α' : chowGroup (fieldChowSituation k) (prodBase (partBase sA' d') (partBase sB' e'))
      ((e' : ℤ) - r')) :
    corrEquivOfIso k (prodBase sA' sA) (prodBase sA sA') (prodBase sB' sB) (prodBase sB sB')
        (pullbackSymmetry sA sA').hom (pullbackSymmetry sB sB').hom
        (pullbackSymmetry_hom_comp_base sA sA') (pullbackSymmetry_hom_comp_base sB sB') (r + r')
        (tensor k sA sA' sB sB' (canonicalDiagonalClassFamily k) r r'
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α')))) =
      corrCongr k (prodBase sA' sA) (prodBase sB' sB) (add_comm r' r)
        (tensor k sA' sA sB' sB (canonicalDiagonalClassFamily k) r' r
          (DirectSum.lof ℚ ℕ _ d' (DirectSum.lof ℚ ℕ _ e' (q' ⊗ₜ[ℤ] α')))
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))) := by
  simp only [tensor_lof_lof, corrEquivOfIso_lof_lof]
  refine lof_lof_eq_corrCongr k _ _ (add_comm r' r) (Nat.add_comm d d') (Nat.add_comm e e')
    (q * q') _ _ _ _ ?_ (by rw [tensorBlock_tmul, tensorBlockInclusion_tmul, mul_comm])
    (tensorInt_swap_parts_heq k sA sA' sB sB' r r' d e d' e' α α')
  rw [tensorBlock_tmul, tensorBlockInclusion_tmul, correspondenceEquivOfIso_tmul,
    ← properChowPushforward_eq_chowPushforwardOfIso _ _ _ _ _ _
      (properPushforwardDescends _ _ _ _ _ _),
    ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ _ _ _ rfl
      (tensorBlockHom_comp_prodBase k sA sA' sB sB' d d' e e')
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (by
        rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase]) _
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _)]
/-- **Commutativity of the tensor product of correspondences** (Stacks 0FG7): transporting
`c ⊗ c'` along the factor switches `A × A' ≅ A' × A` and `B × B' ≅ B' × B` gives `c' ⊗ c`, for the
canonical diagonal classes. -/
theorem corrEquivOfIso_tensor_swap (r r' : ℤ) (a : Corr k sA sB r) (b : Corr k sA' sB' r') :
    corrEquivOfIso k (prodBase sA' sA) (prodBase sA sA') (prodBase sB' sB) (prodBase sB sB')
        (pullbackSymmetry sA sA').hom (pullbackSymmetry sB sB').hom
        (pullbackSymmetry_hom_comp_base sA sA') (pullbackSymmetry_hom_comp_base sB sB') (r + r')
        (tensor k sA sA' sB sB' (canonicalDiagonalClassFamily k) r r' a b) =
      corrCongr k (prodBase sA' sA) (prodBase sB' sB) (add_comm r' r)
        (tensor k sA' sA sB' sB (canonicalDiagonalClassFamily k) r' r b a) :=
  corr_bilinear_ext_swap k sA sB sA' sB'
    (tensor k sA sA' sB sB' (canonicalDiagonalClassFamily k) r r')
    (corrEquivOfIso k (prodBase sA' sA) (prodBase sA sA') (prodBase sB' sB)
      (prodBase sB sB') (pullbackSymmetry sA sA').hom (pullbackSymmetry sB sB').hom
      (pullbackSymmetry_hom_comp_base sA sA') (pullbackSymmetry_hom_comp_base sB sB') (r + r'))
    (tensor k sA' sA sB' sB (canonicalDiagonalClassFamily k) r' r)
    (corrCongr k (prodBase sA' sA) (prodBase sB' sB) (add_comm r' r))
    (corrEquivOfIso_tensor_swap_tmul k sA sA' sB sB' r r') a b

end Swap

end Stacks.WeilCohomology

end
