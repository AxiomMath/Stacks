module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechFrobenius

/-!
# The Frobenius of `𝐆_a^r` given by a matrix, and the basis map

Let `p` vanish on `S` and let `a` be an `r × r` matrix of functions on `S`. The map
`b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ` is an endomorphism of `𝐆_a^r`. If Čech cocycles `zᵢ` satisfy
`zᵢ ^ p - ∑ⱼ aᵢⱼ zⱼ = d wᵢ`, then on homology in degree `q` the basis map of the `zᵢ` carries this
endomorphism to the Frobenius of the Čech complex of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})`.

## Main definitions

* `Stacks.ArtinSchreier.frobMatrixMap`: `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ`.

## Main results

* `Stacks.ArtinSchreier.homologyMap_basisMap_frobenius`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Morphisms of abelian sheaves on the small étale site agreeing on all sections are equal. -/
private theorem sheaf_hom_ext_apply {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {φ ψ : F ⟶ G} (h : ∀ (T : S.Etaleᵒᵖ) (b : F.obj.obj T), φ.hom.app T b = ψ.hom.app T b) :
    φ = ψ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun T => AddCommGrpCat.hom_ext (AddMonoidHom.ext (h T))))

/-- Multiplying `b` by the pullback of `a ∈ Γ(S)` times `c` is multiplying the pullback of `a`
times `b` by `c`. -/
theorem multFun_smul (V : X.Opens) (a : Γ(S, ⊤)) (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤))
    {T : Scheme.{u}} (t : T ⟶ S) (b : Γ(T, ⊤)) :
    multFun f V ((pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f).appTop.hom a * c)
        t b = multFun f V c t (t.appTop.hom a * b) := by
  unfold multFun
  have e := congrArg (fun φ => CommRingCat.Hom.hom φ a) (openFibreMap_appTop_comp f t V)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [map_mul, e, map_mul]
  ring

/-- Multiplying by a function `a` of `S` and then by `c` is multiplying by `a · c`. -/
theorem additiveSmul_comp_multMap (V : X.Opens) (a : Γ(S, ⊤))
    (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    additiveSmul.{u, 0} S a ≫ multMap f V c =
      multMap f V ((pullback.fst (pullback.snd (𝟙 S) f) V.ι ≫ pullback.fst (𝟙 S) f).appTop.hom a *
        c) := by
  refine sheaf_hom_ext_apply fun T b => ULift.ext ?_
  exact (multFun_smul f V a c T.unop.hom b.down).symm

section Cochain

variable {ι : Type} (U : ι → X.Opens)

/-- Multiplication by a cochain is additive in the cochain. -/
theorem cochainMult_add {n : ℕ} (z z' : (baseCech f U).X n) :
    cochainMult f U (z + z') = cochainMult f U z + cochainMult f U z' := by
  refine hom_ext U _ fun x => ?_
  rw [Preadditive.add_comp, cochainMult_comp_π, cochainMult_comp_π, cochainMult_comp_π, map_add]
  exact multMap_add f (inter U x) _ _

/-- Multiplication by cochains, as an additive map. -/
def cochainMultHom (n : ℕ) :
    (baseCech f U).X n →+ (additiveSheaf.{u, 0} S ⟶ (directImageCech f U).X n) where
  toFun := cochainMult f U
  map_zero' := cochainMult_zero f U
  map_add' := cochainMult_add f U

/-- Multiplying by a function `a` of `S` and then by a cochain `z` is multiplying by `a • z`. -/
theorem additiveSmul_comp_cochainMult {n : ℕ} (a : Γ(S, ⊤)) (z : (baseCech f U).X n) :
    additiveSmul.{u, 0} S a ≫ cochainMult f U z = cochainMult f U (a • z) := by
  refine hom_ext U _ fun x => ?_
  rw [Category.assoc, cochainMult_comp_π, cochainMult_comp_π, map_smul]
  exact additiveSmul_comp_multMap f (inter U x) a _

end Cochain

section Matrix

variable (S) {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) {r : ℕ}
  (a : Fin r → Fin r → Γ(S, ⊤))

/-- The function `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ` on `Γ(T)^r`, for `T` étale over `S`. -/
def frobMatrixFun (p : ℕ) (T : S.Etale) (b : Fin r → Γ(T.left, ⊤)) : Fin r → Γ(T.left, ⊤) :=
  fun j => ∑ i, etaleFunction T (a i j) * b i ^ p

include hp hS in
/-- `frobMatrixFun` is additive, `p` being a prime vanishing on `S`. -/
theorem frobMatrixFun_add (T : S.Etale) (b b' : Fin r → Γ(T.left, ⊤)) :
    frobMatrixFun S a p T (b + b') = frobMatrixFun S a p T b + frobMatrixFun S a p T b' := by
  funext j
  simp only [frobMatrixFun, Pi.add_apply,
    add_pow_eq_of_natCast_eq_zero hp (natCast_eq_zero_of_etale S hS T), mul_add,
    Finset.sum_add_distrib]

include hp hS in
/-- **The Frobenius of `𝐆_a^r` given by a matrix**, `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ`. -/
def frobMatrixMap : freeAdditiveSheaf S r ⟶ freeAdditiveSheaf S r :=
  ⟨{ app T := AddCommGrpCat.ofHom
       { toFun := fun b => ULift.up (frobMatrixFun S a p T.unop b.down)
         map_zero' := ULift.ext (funext fun j => by
           change ∑ i, etaleFunction T.unop (a i j) * (0 : Γ(T.unop.left, ⊤)) ^ p = 0
           exact Finset.sum_eq_zero fun i _ => by rw [zero_pow hp.ne_zero, mul_zero])
         map_add' := fun b b' => ULift.ext (frobMatrixFun_add S hp hS a T.unop b.down b'.down) }
     naturality T₁ T₂ g := by
       refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext (funext fun j => ?_))
       change ∑ i, etaleFunction T₂.unop (a i j) * (g.unop.left.appTop.hom (b.down i)) ^ p =
         g.unop.left.appTop.hom (∑ i, etaleFunction T₁.unop (a i j) * b.down i ^ p)
       rw [map_sum]
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [map_mul, map_pow, appTop_etaleFunction] }⟩

/-- The `j`-th coordinate of `frobMatrixMap` is `b ↦ ∑ᵢ aᵢⱼ bᵢ ^ p`. -/
theorem frobMatrixMap_comp_proj (j : Fin r) :
    frobMatrixMap S hp hS a ≫ freeAdditiveProj S r j =
      ∑ i, freeAdditiveProj S r i ≫ frobeniusMap.{u, 0} S hp hS ≫
        additiveSmul.{u, 0} S (a i j) := by
  refine sheaf_hom_ext_apply fun T b => ULift.ext ?_
  refine Eq.trans ?_ (congrArg ULift.down (sheafHom_sum_app _ _ T b)).symm
  refine Eq.trans ?_ (ulift_down_sum (M := ↑((T.unop.left).presheaf.obj (op ⊤))) _ _).symm
  change ∑ i, etaleFunction T.unop (a i j) * b.down i ^ p =
    ∑ i, (((freeAdditiveProj S r i ≫ frobeniusMap.{u, 0} S hp hS ≫
      additiveSmul.{u, 0} S (a i j)).hom.app T) b).down
  exact Finset.sum_congr rfl fun i _ => rfl

end Matrix

section Basis

variable {ι : Type} (U : ι → X.Opens) {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) {q r : ℕ}
  (z : Fin r → (baseCech f U).X q) (a : Fin r → Fin r → Γ(S, ⊤))

/-- `frobMatrixMap` followed by `basisMapDeg` is `b ↦ ∑ᵢ bᵢ ^ p · (∑ⱼ aᵢⱼ zⱼ)`. -/
theorem frobMatrixMap_comp_basisMapDeg :
    frobMatrixMap S hp hS a ≫ basisMapDeg f U z =
      ∑ i, freeAdditiveProj S r i ≫ frobeniusMap.{u, 0} S hp hS ≫
        cochainMult f U (∑ j, a i j • z j) := by
  simp only [basisMapDeg, Preadditive.comp_sum, ← Category.assoc, frobMatrixMap_comp_proj,
    Preadditive.sum_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show cochainMult f U (∑ j, a i j • z j) = ∑ j, cochainMult f U (a i j • z j) from
    map_sum (cochainMultHom f U q) _ _, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Category.assoc]
  rw [additiveSmul_comp_cochainMult]

/-- `basisMapDeg` followed by the Frobenius of the Čech complex is `b ↦ ∑ᵢ bᵢ ^ p · zᵢ ^ p`, the
cochains being raised to the `p`-th power componentwise. -/
theorem basisMapDeg_comp_frobenius :
    basisMapDeg f U z ≫ (directImageCechFrobenius f hp hS U).f q =
      ∑ i, freeAdditiveProj S r i ≫ frobeniusMap.{u, 0} S hp hS ≫
        cochainMult f U (cochainPow f U p (z i)) := by
  simp only [basisMapDeg, Preadditive.sum_comp, Category.assoc, cochainMult_comp_frobenius]

/-- Multiplication by a cochain commutes with the Čech differential from degree `q - 1` to `q`. -/
theorem cochainMult_comp_d_pred (w : (baseCech f U).X (q - 1)) :
    cochainMult f U w ≫ (directImageCech f U).d (q - 1) q =
      cochainMult f U ((baseCech f U).d (q - 1) q w) := by
  cases q with
  | zero =>
    rw [(directImageCech f U).shape 0 0 (by simp), comp_zero,
      (baseCech f U).shape 0 0 (by simp)]
    exact (cochainMult_zero f U).symm
  | succ n => exact cochainMult_comp_d f U w

open Stacks.QuasiIsoFromSingle in
/-- **On homology in degree `q`, the basis map carries the matrix Frobenius to the Frobenius of the
Čech complex**, when `zᵢ ^ p - ∑ⱼ aᵢⱼ zⱼ = d wᵢ`. -/
theorem homologyMap_basisMap_comp_frobenius (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)
    (w : Fin r → (baseCech f U).X (q - 1))
    (hw : ∀ i, cochainPow f U p (z i) - ∑ j, a i j • z j = (baseCech f U).d (q - 1) q (w i)) :
    HomologicalComplex.homologyMap (basisMap f U z hz ≫ directImageCechFrobenius f hp hS U) q =
      HomologicalComplex.homologyMap
        ((HomologicalComplex.single _ (ComplexShape.up ℕ) q).map (frobMatrixMap S hp hS a) ≫
          basisMap f U z hz) q := by
  rw [basisMap, mkHomFromSingle_comp, single_map_comp_mkHomFromSingle]
  refine homologyMap_mkHomFromSingle_eq_of_boundary _ _ _ _ _ _
    (h := ∑ i, freeAdditiveProj S r i ≫ frobeniusMap.{u, 0} S hp hS ≫ cochainMult f U (w i)) ?_
  rw [basisMapDeg_comp_frobenius, frobMatrixMap_comp_basisMapDeg, ← Finset.sum_sub_distrib,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Preadditive.comp_sub, ← Preadditive.comp_sub, Category.assoc, Category.assoc,
    cochainMult_comp_d_pred, ← hw i]
  congr 2
  exact (map_sub (cochainMultHom f U q) _ _).symm

open Stacks.QuasiIsoFromSingle in
include hp hS in
/-- **The Frobenius in terms of a basis.** If the classes of the cocycles `zᵢ` form a basis of the
degree-`q` homology, there are a matrix `a` of functions on `S` and cochains `wᵢ` with
`zᵢ ^ p - ∑ⱼ aᵢⱼ zⱼ = d wᵢ`. -/
theorem exists_frobenius_relation (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)
    (hT : IsIso ((baseCech f U).liftCycles (moduleBasisMapDeg f U z) (q + 1) (by simp)
      (moduleBasisMapDeg_comp_d f U z hz) ≫ (baseCech f U).homologyπ q)) :
    ∃ (a : Fin r → Fin r → Γ(S, ⊤)) (w : Fin r → (baseCech f U).X (q - 1)),
      ∀ i, cochainPow f U p (z i) - ∑ j, a i j • z j = (baseCech f U).d (q - 1) q (w i) := by
  have hzp : ∀ i, (baseCech f U).d q (q + 1) (cochainPow f U p (z i)) = 0 := fun i => by
    rw [d_cochainPow f hp hS U, hz i]
    refine baseCech_ext f U fun y => ?_
    rw [π_cochainPow, map_zero]
    exact zero_pow (M₀ := Γ(pullback (pullback.snd (𝟙 S) f) (inter U y).ι, ⊤)) hp.ne_zero
  have : Projective (ModuleCat.of Γ(S, ⊤) (Fin r → Γ(S, ⊤))) :=
    ModuleCat.projective_of_free (Pi.basisFun Γ(S, ⊤) (Fin r))
  obtain ⟨N, w', h⟩ := exists_sub_eq_boundary (baseCech f U) q (moduleBasisMapDeg f U z)
    (fun _ hk => hk ▸ moduleBasisMapDeg_comp_d f U z hz)
    (moduleBasisMapDeg f U fun i => cochainPow f U p (z i))
    (fun _ hk => hk ▸ moduleBasisMapDeg_comp_d f U _ hzp) hT
  refine ⟨fun i j => N (Pi.single i 1) j, fun i => w' (Pi.single i 1), fun i => ?_⟩
  have hi := congrArg (fun g => g (Pi.single i (1 : Γ(S, ⊤)) : Fin r → Γ(S, ⊤))) h
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rwa [moduleBasisMapDeg_single] at hi

end Basis

end Stacks.ArtinSchreier

end
