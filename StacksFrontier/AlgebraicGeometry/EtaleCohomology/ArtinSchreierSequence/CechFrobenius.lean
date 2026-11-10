module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechBasisSections

/-!
# The Frobenius of the Zariski Čech complex of `𝐆_a` and the basis map

Let `p` be a prime vanishing on `S`, `f : X ⟶ S`, `U` a family of opens of `X`. The Frobenius
`x ↦ x ^ p` of `𝐆_a` acts termwise on the Čech complex of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})` and on the
Čech complex of `V ↦ Γ((S ×_S X) ×_X V)`, and multiplication by a cochain intertwines them:
`F(b · c) = F(b) · F(c)`.

## Main definitions

* `Stacks.ArtinSchreier.directImageCechFrobenius`: the Frobenius of `directImageCech`.

## Main results

* `Stacks.ArtinSchreier.multMap_comp_frobenius`: `F ∘ (b ↦ b · c) = (b ↦ b · c ^ p) ∘ F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

/-- Multiplication by `c ^ p` sends `b ^ p` to `(b · c) ^ p`. -/
theorem multFun_pow (V : X.Opens) (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤))
    {T : Scheme.{u}} (t : T ⟶ S) (b : Γ(T, ⊤)) :
    multFun f V (c ^ p) t (b ^ p) = (multFun f V c t b) ^ p := by
  unfold multFun
  rw [map_pow, map_pow, mul_pow]

include f hS in
/-- `p` vanishes on `X`. -/
theorem natCast_eq_zero_source : (p : Γ(X, ⊤)) = 0 :=
  natCast_eq_zero_of_hom f hS

/-- **The Frobenius commutes with multiplication by a function**:
`F (b · c) = F(b) · c ^ p`. -/
theorem multMap_comp_frobenius (V : X.Opens) (c : Γ(pullback (pullback.snd (𝟙 S) f) V.ι, ⊤)) :
    multMap f V c ≫ (etaleAbelianDirectImage.{u, 0} f).map
        ((openDirectImageFrobenius X hp (natCast_eq_zero_source f hS)).app (op V)) =
      frobeniusMap.{u, 0} S hp hS ≫ multMap f V (c ^ p) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun T => ?_)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext ?_)
  exact (multFun_pow f V c T.unop.hom b.down).symm

section Cochain

variable {ι : Type} (U : ι → X.Opens)

/-- The componentwise `p`-th power of a Čech cochain of `V ↦ Γ((S ×_S X) ×_X V)`. -/
def cochainPow (p : ℕ) {n : ℕ} (z : (baseCech f U).X n) : (baseCech f U).X n :=
  (ModuleCat.piIsoPi fun x : Fin (n + 1) → ι =>
      (baseSectionsPresheaf f).obj (op (inter U x))).inv
    fun x => (show Γ(pullback (pullback.snd (𝟙 S) f) (inter U x).ι, ⊤) from
      π U (baseSectionsPresheaf f) n x z) ^ p

/-- The `x`-component of `cochainPow f U p z` is the `p`-th power of the `x`-component of `z`. -/
theorem π_cochainPow (p : ℕ) {n : ℕ} (z : (baseCech f U).X n) (x : Fin (n + 1) → ι) :
    π U (baseSectionsPresheaf f) n x (cochainPow f U p z) =
      (show Γ(pullback (pullback.snd (𝟙 S) f) (inter U x).ι, ⊤) from
        π U (baseSectionsPresheaf f) n x z) ^ p :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply
    (fun x : Fin (n + 1) → ι => (baseSectionsPresheaf f).obj (op (inter U x))) x _

/-- Two cochains agree when all their components agree. -/
theorem baseCech_ext {n : ℕ} {a b : (baseCech f U).X n}
    (h : ∀ x, π U (baseSectionsPresheaf f) n x a = π U (baseSectionsPresheaf f) n x b) : a = b := by
  have hinj := (ModuleCat.piIsoPi fun x : Fin (n + 1) → ι =>
      (baseSectionsPresheaf f).obj (op (inter U x))).toLinearEquiv.injective
  refine hinj (funext fun x => ?_)
  have key (c : (baseCech f U).X n) := ModuleCat.piIsoPi_hom_ker_subtype_apply
    (fun x : Fin (n + 1) → ι => (baseSectionsPresheaf f).obj (op (inter U x))) x c
  exact (key a).trans ((h x).trans (key b).symm)

/-- The `y`-component of the Čech differential of `w` is the alternating sum of the restrictions
of the components of `w` at the faces of `y`. -/
theorem π_d_apply {n : ℕ} (w : (baseCech f U).X n) (y : Fin (n + 2) → ι) :
    π U (baseSectionsPresheaf f) (n + 1) y ((baseCech f U).d n (n + 1) w) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (pullbackOpenMap (pullback.snd (𝟙 S) f) (interMap U y i.succAbove).le).appTop.hom
          (π U (baseSectionsPresheaf f) n (y ∘ i.succAbove) w) := by
  have hz := congrArg (fun φ => φ w) (d_comp_π U (baseSectionsPresheaf f) n y)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  exact hz

include hp hS in
/-- **The componentwise `p`-th power commutes with the Čech differential**, `p` vanishing on
`S`. -/
theorem d_cochainPow {n : ℕ} (z : (baseCech f U).X n) :
    (baseCech f U).d n (n + 1) (cochainPow f U p z) =
      cochainPow f U p ((baseCech f U).d n (n + 1) z) := by
  refine baseCech_ext f U fun y => ?_
  rw [π_d_apply, π_cochainPow, π_d_apply]
  have hR : (p : Γ(pullback (pullback.snd (𝟙 S) f) (inter U y).ι, ⊤)) = 0 :=
    natCast_eq_zero_of_hom (pullback.fst _ (inter U y).ι ≫ pullback.fst (𝟙 S) f) hS
  let F := frobeniusRingHom Γ(pullback (pullback.snd (𝟙 S) f) (inter U y).ι, ⊤) hp hR
  change _ = F _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, π_cochainPow]
  change _ = _ • ((pullbackOpenMap (pullback.snd (𝟙 S) f) (interMap U y i.succAbove).le).appTop.hom
    _) ^ p
  rw [map_pow]

/-- **The Frobenius of the Čech complex of `V ↦ f_*(ι_{V,*} 𝐆_{a,V})`**, termwise. -/
abbrev directImageCechFrobenius : directImageCech f U ⟶ directImageCech f U :=
  (cechComplexFunctor U).map (Functor.whiskerRight
    (openDirectImageFrobenius X hp (natCast_eq_zero_source f hS))
    (etaleAbelianDirectImage.{u, 0} f))

/-- **Multiplication by a cochain intertwines the Frobenius of `𝐆_a` with that of the Čech
complex**, the cochain being raised to the `p`-th power componentwise. -/
theorem cochainMult_comp_frobenius {n : ℕ} (z : (baseCech f U).X n) :
    cochainMult f U z ≫ (directImageCechFrobenius f hp hS U).f n =
      frobeniusMap.{u, 0} S hp hS ≫ cochainMult f U (cochainPow f U p z) := by
  refine hom_ext U _ fun x => ?_
  rw [Category.assoc, Stacks.AlgebraicGeometry.CoveringResolution.cech_map_f_comp_π,
    ← Category.assoc, cochainMult_comp_π, Category.assoc, cochainMult_comp_π, π_cochainPow]
  exact multMap_comp_frobenius f hp hS (inter U x) _

end Cochain

end Stacks.ArtinSchreier

end
