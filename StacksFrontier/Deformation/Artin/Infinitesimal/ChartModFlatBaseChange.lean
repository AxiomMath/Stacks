module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ChartTangentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ModBaseChange

/-!
# Flat base change of the modules of the groupoid of a chart along `X[M] → Y[N]`

Let `g : X → Y` be a map of small `A'`-algebras, `ψ : M → N` a `g`-semilinear map of coefficients
and `j : F → Y` a map from a flat `A'`-algebra such that `X[M] ⊗[A'] F → Y[N]`,
`z ⊗ f ↦ (g, ψ)(z) · j(f)`, is bijective. Then the thickening `X[M] ⊗[A'] F → Y` is the base
change of `X[M] → X` along `F` (`AlgebraicGeometry.Stack.GroupoidLift.IsBaseChange`), and
composing the flat base change of `Mod` (`AlgebraicGeometry.Stack.GroupoidLift.modBC_bijective`,
which uses a formally étale chart of the arrows near the identity) with the identification of
`X[M] ⊗[A'] F → Y` with `Y[N] → Y` gives a bijection `F ⊗[A'] Mod w ≃ Mod (g ∘ w)`, which on
`f ⊗ m` is `j(f) • (g, ψ)_* m` (`Deformation.Artin.ChartLift.exists_bijective_modBaseChange`).
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent

namespace Deformation.Artin.ChartLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P]
  {G : Groupoid A' κ P}

section Iso

variable {C' C D' D : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D}

/-- If `φ' ∘ φ` is the identity on the top algebras, then `modMap φ'` is a left inverse of
`modMap φ`. -/
private theorem modMap_modMap_of_left_inverse (φ : SqZero.Hom e e₂) (φ' : SqZero.Hom e₂ e)
    (h : ∀ x, φ'.top.hom.hom (φ.top.hom.hom x) = x) {w : P →ₐ[A'] C.obj}
    {w₂ : P →ₐ[A'] D.obj} (hw : φ.bot.hom.hom.comp w = w₂) (hw' : φ'.bot.hom.hom.comp w₂ = w)
    (m : Mod G e w) : modMap (G := G) φ' hw' (modMap φ hw m) = m := by
  induction m using Submodule.Quotient.induction_on with
  | H D'' =>
  obtain ⟨Dv, hD⟩ := D''
  exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext fun x ↦ h (Dv x)))

/-- **A map of thickenings with an inverse induces a bijection of the modules `Mod`.** -/
theorem modMap_bijective_of_inverse (φ : SqZero.Hom e e₂) (φ' : SqZero.Hom e₂ e)
    (h₁ : ∀ x, φ'.top.hom.hom (φ.top.hom.hom x) = x)
    (h₂ : ∀ y, φ.top.hom.hom (φ'.top.hom.hom y) = y) {w : P →ₐ[A'] C.obj}
    {w₂ : P →ₐ[A'] D.obj} (hw : φ.bot.hom.hom.comp w = w₂) (hw' : φ'.bot.hom.hom.comp w₂ = w) :
    Function.Bijective (modMap (G := G) φ hw) :=
  ⟨fun a b h ↦ by rw [← modMap_modMap_of_left_inverse φ φ' h₁ hw hw' a,
      ← modMap_modMap_of_left_inverse φ φ' h₁ hw hw' b, h],
    fun m ↦ ⟨_, modMap_modMap_of_left_inverse φ' φ h₂ hw' hw m⟩⟩

end Iso

/-- A map of thickenings induces an `A'`-linear map of the modules `Mod`. -/
def modMapₗ {C' C D' D : SmallAlg A' κ} {e : SqZero C' C} {e₂ : SqZero D' D}
    (φ : SqZero.Hom e e₂) {w : P →ₐ[A'] C.obj} {w₂ : P →ₐ[A'] D.obj}
    (hw : φ.bot.hom.hom.comp w = w₂) : Mod G e w →ₗ[A'] Mod G e₂ w₂ where
  toFun := modMap (G := G) φ hw
  map_add' := map_add _
  map_smul' a m := by
    have h0 : a • m = (algebraMap A' C'.obj a) • m :=
      (IsScalarTower.algebraMap_smul (A := (C'.obj : Type u)) a m).symm
    rw [h0, map_smulₛₗ, RingHom.id_apply]
    have h1 : (φ.top.hom.hom : C'.obj →+* D'.obj) (algebraMap A' C'.obj a) =
        algebraMap A' D'.obj a := φ.top.hom.hom.commutes a
    rw [h1, IsScalarTower.algebraMap_smul]

section Coord

variable (X : SmallAlg A' κ) (M : ModuleCat.{u} X.obj)
  (hM : Cardinal.mk (TrivSqZeroExt X.obj M) < κ)

/-- The coefficient component of an element of `X[M]`. -/
def sqzSnd (z : (sqzAlg X M hM).obj) : M := TrivSqZeroExt.snd (R := X.obj) (M := M) z

/-- The element `(0, m)` of `X[M]`. -/
def sqzInr (m : M) : (sqzAlg X M hM).obj := (TrivSqZeroExt.inr m : TrivSqZeroExt X.obj M)

/-- The coefficient component `sqzSnd` of `X[M]` is additive. -/
theorem sqzSnd_add (z z' : (sqzAlg X M hM).obj) :
    sqzSnd X M hM (z + z') = sqzSnd X M hM z + sqzSnd X M hM z' := rfl

/-- Every `z ∈ X[M]` is the sum of `(z₀, 0)` and `(0, z₁)` for its components `z₀`, `z₁`. -/
theorem sqzInl_add_sqzInr (z : (sqzAlg X M hM).obj) :
    sqzInl X M hM ((sqzFst X M hM).hom.hom z) + sqzInr X M hM (sqzSnd X M hM z) = z :=
  TrivSqZeroExt.inl_fst_add_inr_snd_eq (R := X.obj) (M := M) z

/-- The element `(0, m)` of `X[M]` has zero `X`-component. -/
theorem sqzFst_sqzInr (m : M) : (sqzFst X M hM).hom.hom (sqzInr X M hM m) = 0 := rfl

/-- Two elements of `X[M]` with the same `X`- and `M`-components are equal. -/
theorem sqz_ext {z z' : (sqzAlg X M hM).obj}
    (h₁ : (sqzFst X M hM).hom.hom z = (sqzFst X M hM).hom.hom z')
    (h₂ : sqzSnd X M hM z = sqzSnd X M hM z') : z = z' :=
  TrivSqZeroExt.ext (R := X.obj) (M := M) h₁ h₂

end Coord

section BaseChange

variable {X Y : SmallAlg A' κ} (g : X ⟶ Y) {M : ModuleCat.{u} X.obj} {N : ModuleCat.{u} Y.obj}
  (ψ : M ⟶ (ModuleCat.restrictScalars (g.hom.hom : X.obj →+* Y.obj)).obj N)
  (hM : Cardinal.mk (TrivSqZeroExt X.obj M) < κ) (hN : Cardinal.mk (TrivSqZeroExt Y.obj N) < κ)
  {F : Type u} [CommRing F] [Algebra A' F] (j : F →ₐ[A'] Y.obj)

/-- The map `X[M] → Y[N]` induced by `(g, ψ)` sends `(c, 0)` to `(g c, 0)`. -/
theorem sqzBaseMap_inl (c : X.obj) :
    (sqzBaseMap g ψ hM hN).hom.hom (sqzInl X M hM c) = sqzInl Y N hN (g.hom.hom c) :=
  TrivSqZeroExt.ext rfl ψ.hom.map_zero

/-- The map `X[M] ⊗[A'] F → Y[N]`, `z ⊗ f ↦ (g, ψ)(z) · j(f)`. -/
def sqzTensorLift : (sqzAlg X M hM).obj ⊗[A'] F →ₐ[A'] (sqzAlg Y N hN).obj :=
  Algebra.TensorProduct.lift (sqzBaseMap g ψ hM hN).hom.hom ((sqzInl Y N hN).comp j)
    (fun _ _ ↦ Commute.all _ _)

/-- The map `X[M] ⊗[A'] F → Y[N]` sends `z ⊗ 1` to `(g, ψ)(z)`. -/
theorem sqzTensorLift_tmul_one (z : (sqzAlg X M hM).obj) :
    sqzTensorLift g ψ hM hN j (z ⊗ₜ[A'] (1 : F)) = (sqzBaseMap g ψ hM hN).hom.hom z := by
  rw [sqzTensorLift, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

/-- The map `X[M] ⊗[A'] F → Y[N]` sends `1 ⊗ f` to `(j f, 0)`. -/
theorem sqzTensorLift_one_tmul (f : F) :
    sqzTensorLift g ψ hM hN j ((1 : (sqzAlg X M hM).obj) ⊗ₜ[A'] f) = sqzInl Y N hN (j f) := by
  rw [sqzTensorLift, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

variable (hL : Function.Bijective (sqzTensorLift g ψ hM hN j))

include hL in
/-- If `X[M] ⊗[A'] F → Y[N]` is bijective, then `X[M] ⊗[A'] F` is small (of cardinality
`< κ`). -/
theorem card_sqzTensor_lt : Cardinal.mk ((sqzAlg X M hM).obj ⊗[A'] F) < κ :=
  lt_of_eq_of_lt (Cardinal.mk_congr (Equiv.ofBijective _ hL)) hN

/-- The thickening `X[M] ⊗[A'] F → Y`. -/
def sqzTensorE : SqZero (SmallAlg.mk ((sqzAlg X M hM).obj ⊗[A'] F)
    (card_sqzTensor_lt g ψ hM hN j hL)) Y where
  q := SmallAlg.homMk ((sqzFst Y N hN).hom.hom.comp (sqzTensorLift g ψ hM hN j))
  surj y := by
    obtain ⟨t, ht⟩ := hL.2 (sqzInl Y N hN y)
    exact ⟨t, (congrArg (fun z ↦ (sqzFst Y N hN).hom.hom z) ht).trans rfl⟩
  sq := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Submodule.mem_bot]
    have ha' : sqzTensorLift g ψ hM hN j a ∈
        RingHom.ker ((sqzE Y N hN).q.hom.hom : (sqzAlg Y N hN).obj →+* Y.obj) := ha
    have hb' : sqzTensorLift g ψ hM hN j b ∈
        RingHom.ker ((sqzE Y N hN).q.hom.hom : (sqzAlg Y N hN).obj →+* Y.obj) := hb
    have hab := Ideal.mul_mem_mul ha' hb'
    rw [← pow_two, (sqzE Y N hN).sq, Ideal.mem_bot, ← map_mul] at hab
    exact hL.1 (hab.trans (map_zero _).symm)

/-- The structure map of the thickening `X[M] ⊗[A'] F → Y` is the composite of
`X[M] ⊗[A'] F → Y[N]` with the projection `Y[N] → Y`. -/
theorem sqzTensorE_q_apply (t : (sqzAlg X M hM).obj ⊗[A'] F) :
    (sqzTensorE g ψ hM hN j hL).q.hom.hom t =
      (sqzFst Y N hN).hom.hom (sqzTensorLift g ψ hM hN j t) := rfl

/-- The map of thickenings `(X[M] → X) ⟶ (X[M] ⊗[A'] F → Y)`. -/
def sqzTensorHom : SqZero.Hom (sqzE X M hM) (sqzTensorE g ψ hM hN j hL) where
  top := SmallAlg.homMk Algebra.TensorProduct.includeLeft
  bot := g
  w := by
    ext z
    exact (congrArg (fun z ↦ (sqzFst Y N hN).hom.hom z) (sqzTensorLift_tmul_one g ψ hM hN j z))

/-- The thickening `X[M] ⊗[A'] F → Y` is the base change of `X[M] → X` along `F`. -/
theorem isBaseChange_sqzTensor :
    IsBaseChange (sqzE X M hM) F (sqzTensorE g ψ hM hN j hL) (sqzTensorHom g ψ hM hN j hL) where
  ker_eq := by
    have hle : extIdeal F (RingHom.ker ((sqzE X M hM).q.hom.hom :
          (sqzAlg X M hM).obj →+* X.obj)) ≤
        RingHom.ker ((sqzTensorE g ψ hM hN j hL).q.hom.hom :
          ((sqzAlg X M hM).obj ⊗[A'] F) →+* Y.obj) := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      have hz' : (sqzFst X M hM).hom.hom z = 0 := hz
      change (sqzTensorE g ψ hM hN j hL).q.hom.hom (z ⊗ₜ[A'] (1 : F)) = 0
      rw [sqzTensorE_q_apply, sqzTensorLift_tmul_one]
      exact (congrArg g.hom.hom hz').trans (map_zero _)
    refine le_antisymm (fun t ht ↦ ?_) hle
    have key : ∀ t : (sqzAlg X M hM).obj ⊗[A'] F, ∃ t₂ ∈ extIdeal F
        (RingHom.ker ((sqzE X M hM).q.hom.hom : (sqzAlg X M hM).obj →+* X.obj)),
        sqzSnd Y N hN (sqzTensorLift g ψ hM hN j (t - t₂)) = 0 := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul z f =>
        refine ⟨sqzInr X M hM (sqzSnd X M hM z) ⊗ₜ[A'] f,
          tmul_mem_extIdeal _ (sqzFst_sqzInr X M hM _) f, ?_⟩
        have hz : z ⊗ₜ[A'] f - sqzInr X M hM (sqzSnd X M hM z) ⊗ₜ[A'] f =
            sqzInl X M hM ((sqzFst X M hM).hom.hom z) ⊗ₜ[A'] f := by
          rw [← TensorProduct.sub_tmul]
          congr 1
          exact sub_eq_iff_eq_add.mpr (sqzInl_add_sqzInr X M hM z).symm
        rw [hz, sqzTensorLift, Algebra.TensorProduct.lift_tmul, sqzBaseMap_inl, AlgHom.comp_apply,
          ← map_mul]
        rfl
      | add t₁ t₂ h₁ h₂ =>
        obtain ⟨s₁, hs₁, k₁⟩ := h₁
        obtain ⟨s₂, hs₂, k₂⟩ := h₂
        refine ⟨s₁ + s₂, add_mem hs₁ hs₂, ?_⟩
        rw [show t₁ + t₂ - (s₁ + s₂) = (t₁ - s₁) + (t₂ - s₂) by abel, map_add, sqzSnd_add, k₁, k₂,
          add_zero]
    obtain ⟨t₂, ht₂, hsnd⟩ := key t
    have h₁ : (sqzTensorE g ψ hM hN j hL).q.hom.hom (t - t₂) = 0 := by
      rw [map_sub, show (sqzTensorE g ψ hM hN j hL).q.hom.hom t = 0 from ht,
        show (sqzTensorE g ψ hM hN j hL).q.hom.hom t₂ = 0 from hle ht₂, sub_zero]
    have h0 : sqzTensorLift g ψ hM hN j (t - t₂) = 0 := sqz_ext Y N hN h₁ hsnd
    have : t - t₂ = 0 := hL.1 (h0.trans (map_zero _).symm)
    rw [sub_eq_zero.mp this]
    exact ht₂
  top_apply _ := rfl

/-- The identification of the thickening `X[M] ⊗[A'] F → Y` with `Y[N] → Y`. -/
def sqzTensorIso : SqZero.Hom (sqzTensorE g ψ hM hN j hL) (sqzE Y N hN) where
  top := SmallAlg.homMk (sqzTensorLift g ψ hM hN j)
  bot := 𝟙 Y
  w := by
    ext t <;> rfl

/-- The inverse identification. -/
def sqzTensorIsoInv : SqZero.Hom (sqzE Y N hN) (sqzTensorE g ψ hM hN j hL) where
  top := SmallAlg.homMk (AlgEquiv.ofBijective (sqzTensorLift g ψ hM hN j) hL).symm.toAlgHom
  bot := 𝟙 Y
  w := by
    ext y
    change (sqzFst Y N hN).hom.hom (sqzTensorLift g ψ hM hN j
      ((AlgEquiv.ofBijective (sqzTensorLift g ψ hM hN j) hL).symm y)) = (sqzFst Y N hN).hom.hom y
    exact congrArg (fun z ↦ (sqzFst Y N hN).hom.hom z)
      ((AlgEquiv.ofBijective (sqzTensorLift g ψ hM hN j) hL).apply_symm_apply y)

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.Flat A' F]
  {Q : Type u} [CommRing Q] [Algebra A' Q] [Module.FinitePresentation Q Ω[Q⁄A']]
  {b : Chart G.arr Q} (hb : b.IsFormallyEtale) {sV tV : P →ₐ[A'] Q}
  (hsV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.src (b.app C v) = v.comp sV)
  (htV : ∀ (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj), G.tgt (b.app C v) = v.comp tV)

include hL hb hsV htV in
/-- **Flat base change of `Mod` along `X[M] → Y[N]`**: given a formally étale chart of the arrows
near the identity of `w`, the map `F ⊗[A'] Mod w → Mod (g ∘ w)`, `f ⊗ m ↦ j(f) • (g, ψ)_* m`, is
bijective. -/
theorem exists_bijective_modBaseChange {w : P →ₐ[A'] X.obj} {v : Q →ₐ[A'] X.obj}
    (hv : b.app X v = G.idt w) :
    ∃ β : F ⊗[A'] Mod G (sqzE X M hM) w →ₗ[A'] Mod G (sqzE Y N hN) (g.hom.hom.comp w),
      Function.Bijective β ∧ ∀ (f : F) (m : Mod G (sqzE X M hM) w),
        β (f ⊗ₜ m) = sqzInl Y N hN (j f) • modMap (G := G) (sqzBaseHom g ψ hM hN) rfl m := by
  have hB := isBaseChange_sqzTensor g ψ hM hN j hL
  have hℓ : (sqzE X M hM).q.hom.hom.comp ((sqzInl X M hM).comp w) = w := by
    ext; rfl
  have hm : (sqzE X M hM).q.hom.hom.comp ((sqzInl X M hM).comp v) = v := by
    ext; rfl
  have hbc := modBC_bijective (G := G) hB hb hsV htV ((sqzInl X M hM).comp w) hℓ
    (w₂ := g.hom.hom.comp w) rfl hv ((sqzInl X M hM).comp v) hm
  have hiso := modMap_bijective_of_inverse (G := G) (sqzTensorIso g ψ hM hN j hL)
    (sqzTensorIsoInv g ψ hM hN j hL)
    (fun x ↦ (AlgEquiv.ofBijective (sqzTensorLift g ψ hM hN j) hL).symm_apply_apply x)
    (fun y ↦ (AlgEquiv.ofBijective (sqzTensorLift g ψ hM hN j) hL).apply_symm_apply y)
    (w := g.hom.hom.comp w) rfl rfl
  let β₁ : F ⊗[A'] Mod G (sqzE X M hM) w →ₗ[A'] Mod G (sqzTensorE g ψ hM hN j hL)
      (g.hom.hom.comp w) :=
    modBC (G := G) (hY := card_sqzTensor_lt g ψ hM hN j hL) (φ := sqzTensorHom g ψ hM hN j hL)
      (w₂ := g.hom.hom.comp w) rfl
  let β₂ : Mod G (sqzTensorE g ψ hM hN j hL) (g.hom.hom.comp w) →ₗ[A']
      Mod G (sqzE Y N hN) (g.hom.hom.comp w) :=
    modMapₗ (G := G) (sqzTensorIso g ψ hM hN j hL) (w := g.hom.hom.comp w)
      (w₂ := g.hom.hom.comp w) rfl
  refine ⟨β₂.comp β₁, hiso.comp hbc, fun f m ↦ ?_⟩
  have e₁ : β₁ (f ⊗ₜ m) = ((1 : (sqzAlg X M hM).obj) ⊗ₜ[A'] f : (sqzAlg X M hM).obj ⊗[A'] F) •
      modMap (G := G) (sqzTensorHom g ψ hM hN j hL) rfl m := modBC_tmul _ f m
  have e₂ : ∀ (c : (sqzAlg X M hM).obj ⊗[A'] F) (n : Mod G (sqzTensorE g ψ hM hN j hL)
      (g.hom.hom.comp w)), β₂ (c • n) = sqzTensorLift g ψ hM hN j c • β₂ n :=
    fun c n ↦ map_smulₛₗ (modMap (G := G) (sqzTensorIso g ψ hM hN j hL) rfl) c n
  have e₃ : β₂ (modMap (G := G) (sqzTensorHom g ψ hM hN j hL) rfl m) =
      modMap (G := G) (sqzBaseHom g ψ hM hN) rfl m :=
    modMap_modMap (G := G) (sqzTensorHom g ψ hM hN j hL) (sqzTensorIso g ψ hM hN j hL)
      (sqzBaseHom g ψ hM hN) (fun x ↦ (sqzTensorLift_tmul_one g ψ hM hN j x).symm) rfl rfl rfl m
  refine (congrArg β₂ e₁).trans ((e₂ _ _).trans ?_)
  rw [e₃, sqzTensorLift_one_tmul]
  rfl

end BaseChange

end Deformation.Artin.ChartLift

end
