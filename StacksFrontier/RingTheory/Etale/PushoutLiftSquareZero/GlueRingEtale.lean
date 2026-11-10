module

public import StacksFrontier.RingTheory.Etale.PushoutLiftSquareZero.GlueRing

/-!
# The glued ring is an étale lift

For the glued ring `SquareZero.glueRing` of the square-zero case of Stacks 0ALT, the `J`-parts of
the rings it glues are read as base changes of the single `B₀`-module `B₀ ⊗[A] J`. From this the
reduction map onto `B₀` is surjective with kernel `J` times the glued ring, and the glued ring is
étale over `A` away from `V(I)` and maps étale onto `C`.

## Main results

* `SquareZero.exists_lift_to_glueRing`: every element of `B₀` lifts to the glued ring.
* `SquareZero.ker_glueReduction`: the kernel of the reduction is `J` times the glued ring.
* `SquareZero.etale_glueRing`: the glued ring maps étale onto `C`.
* `SquareZero.isEtaleAt_glueRing`: the glued ring is étale over `A` off `V(I)`. These are the
  square-zero case of Stacks 0ALT, extended to `J ^ (n + 1) = 0` in
  `Stacks.Etale.exists_etale_lift_of_pow_eq_bot`.
-/

@[expose] public noncomputable section

open TensorProduct

universe u v

namespace SquareZero

variable {A : Type u} [CommRing A] (J : Ideal A) (T : Type v) [CommRing T] [Algebra A T]

section Reduction

variable {A : Type u} [CommRing A] {J : Ideal A} {r : ℕ} {f : Fin r → A}
  {B₀ : Type u} [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
  (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]

/-- `(C ⧸ JC)[1/g_s]` is the localization of the `B₀`-module `C ⧸ JC` at the Čech submonoid
of `s`. -/
theorem isLocalizedModule_locC₀ (s : Finset (Fin r)) :
    IsLocalizedModule (Cech.cechSub (genB J f B₀) s)
      (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)).toLinearMap := by
  rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Cech.cechSub,
    Submonoid.map_powers]
  have h : IsLocalization (Submonoid.powers (Ideal.Quotient.mk (J.map (algebraMap A C))
      (algebraMap A C (prodGen f s)))) (locC₀ J f C s) := inferInstance
  refine IsLocalization.of_submonoid_eq (S := locC₀ J f C s) (M := Submonoid.powers
    (Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f s)))) ?_
  congr 1
  rw [map_prod]
  simp only [algebraMap_genB, prodGen, map_prod]

variable (J f B₀) in
omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `B₀[1/g_s]` is the localization of `B₀` at the Čech submonoid of `s`. -/
theorem isLocalization_locB (s : Finset (Fin r)) :
    IsLocalization (Cech.cechSub (genB J f B₀) s) (locB J f B₀ s) := by
  have h : IsLocalization (Submonoid.powers
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s)))) (locB J f B₀ s) :=
    inferInstance
  exact IsLocalization.of_submonoid_eq (S := locB J f B₀ s)
    (M := Submonoid.powers (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s))))
    (by rw [genB_prod])

/-- `locC₀Res` as a `B₀`-linear map. -/
def locC₀ResLin {t s : Finset (Fin r)} (h : t ⊆ s) : locC₀ J f C t →ₗ[B₀] locC₀ J f C s where
  toFun := locC₀Res J f C h
  map_add' := map_add _
  map_smul' := fun b x ↦ by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    rw [IsScalarTower.algebraMap_apply B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C t),
      locC₀Res_algebraMap, ← IsScalarTower.algebraMap_apply]

variable (J f B₀) in
/-- The `B₀`-module `B₀ ⊗[A] J` whose glueing complex controls the `J`-parts. -/
abbrev modJ : Type u := B₀ ⊗[A] J

/-- `(B₀ ⊗[A] J) ⊗[B₀] (C ⧸ JC) = (C ⧸ JC) ⊗[A] J`. -/
noncomputable def thetaJ : modJ J B₀ ⊗[B₀] (C ⧸ J.map (algebraMap A C)) ≃ₗ[B₀]
    (C ⧸ J.map (algebraMap A C)) ⊗[A] J :=
  (TensorProduct.comm B₀ (modJ J B₀) (C ⧸ J.map (algebraMap A C))).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B₀ (C ⧸ J.map (algebraMap A C))
      (C ⧸ J.map (algebraMap A C)) J).restrictScalars B₀)

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- On pure tensors, `thetaJ` sends `(b ⊗ j) ⊗ c` to `b c ⊗ j`. -/
theorem thetaJ_tmul (b : B₀) (j : J) (c : C ⧸ J.map (algebraMap A C)) :
    thetaJ (J := J) C ((b ⊗ₜ j) ⊗ₜ c) = (algebraMap B₀ _ b * c) ⊗ₜ j := by
  simp [thetaJ, Algebra.smul_def]

variable (J f B₀) in
/-- The model of `(B₀ ⊗[A] J)_{g_s}`. -/
noncomputable def modelL (s : Finset (Fin r)) : modJ J B₀ →ₗ[B₀] locB J f B₀ s ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J (Algebra.linearMap B₀ (locB J f B₀ s))

/-- The model of `((B₀ ⊗[A] J) ⊗[B₀] (C ⧸ JC))_{g_s}`. -/
noncomputable def modelLS (s : Finset (Fin r)) :
    modJ J B₀ ⊗[B₀] (C ⧸ J.map (algebraMap A C)) →ₗ[B₀] locC₀ J f C s ⊗[A] J :=
  (TensorProduct.AlgebraTensorModule.rTensor A J
    (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)).toLinearMap).comp
      (thetaJ (J := J) C).toLinearMap

omit [IsScalarTower A (A ⧸ J) B₀] in
/-- `modelL` is the localization of `B₀ ⊗[A] J` at the Čech submonoid of `s`. -/
theorem isLocalizedModule_modelL (s : Finset (Fin r)) :
    IsLocalizedModule (Cech.cechSub (genB J f B₀) s) (modelL J f B₀ s) := by
  have := isLocalization_locB J f B₀ s
  unfold modelL
  infer_instance

/-- `modelLS` is the localization of `(B₀ ⊗[A] J) ⊗[B₀] (C ⧸ JC)` at the Čech submonoid of `s`. -/
theorem isLocalizedModule_modelLS (s : Finset (Fin r)) :
    IsLocalizedModule (Cech.cechSub (genB J f B₀) s)
      (modelLS (J := J) (f := f) (B₀ := B₀) C s) := by
  have := isLocalizedModule_locC₀ (J := J) (f := f) (B₀ := B₀) C s
  unfold modelLS
  exact IsLocalizedModule.of_linearEquiv_right _ _ _

variable (J f B₀) in
/-- The restriction model `locB t ⊗ J → locB s ⊗ J`. -/
noncomputable def modelRes {t s : Finset (Fin r)} (h : t ⊆ s) :
    locB J f B₀ t ⊗[A] J →ₗ[B₀] locB J f B₀ s ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J (locBResLin h)

/-- The restriction model `locC₀ t ⊗ J → locC₀ s ⊗ J`. -/
noncomputable def modelResS {t s : Finset (Fin r)} (h : t ⊆ s) :
    locC₀ J f C t ⊗[A] J →ₗ[B₀] locC₀ J f C s ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J (locC₀ResLin (B₀ := B₀) C h)

/-- The comparison model `locB s ⊗ J → locC₀ s ⊗ J`. -/
noncomputable def modelκ (s : Finset (Fin r)) :
    locB J f B₀ s ⊗[A] J →ₗ[B₀] locC₀ J f C s ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J (locBCLin C s)

omit [IsScalarTower A (A ⧸ J) B₀] in
/-- The restriction model `modelRes` is compatible with the localization maps `modelL`. -/
theorem modelRes_comp {t s : Finset (Fin r)} (h : t ⊆ s) :
    modelRes J f B₀ h ∘ₗ modelL J f B₀ t = modelL J f B₀ s := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext b
  simp [modelRes, modelL, locBResLin]

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- The restriction model `modelResS` is compatible with the localization maps `modelLS`. -/
theorem modelResS_comp {t s : Finset (Fin r)} (h : t ⊆ s) :
    modelResS (J := J) (B₀ := B₀) C h ∘ₗ modelLS (J := J) (f := f) C t =
      modelLS (J := J) (f := f) C s := by
  apply TensorProduct.ext'
  intro x c
  induction x using TensorProduct.inductionOn with
  | tmul b j =>
    simp [modelResS, modelLS, thetaJ_tmul, locC₀ResLin, locC₀Res_algebraMap]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The comparison model `modelκ` after `modelL` is `modelLS` applied to `m ⊗ 1`. -/
theorem modelκ_comp (s : Finset (Fin r)) :
    modelκ (J := J) (B₀ := B₀) (f := f) C s ∘ₗ modelL J f B₀ s =
      modelLS (J := J) (f := f) C s ∘ₗ (TensorProduct.mk B₀ (modJ J B₀)
        (C ⧸ J.map (algebraMap A C))).flip 1 := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext b
  simp [modelκ, modelLS, modelL, thetaJ_tmul, locBCLin]

/-- The kernel of the reduction of `liftE` onto `B₀[1/g_s]` is `J` times `liftE`. -/
theorem ker_liftEπ (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    RingHom.ker (liftEπ σ s hs : liftE σ s hs →+* locB J f B₀ s) =
      J.map (algebraMap A (liftE σ s hs)) := by
  have := σ.etale s hs
  exact ker_etaleLiftπ J (locB J f B₀ s)

/-- The push of the `J`-part of an étale lift. -/
noncomputable def pushE (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    locB J f B₀ s ⊗[A] J →ₗ[A] liftE σ s hs :=
  pushOf J σ.sq_eq_bot (liftEπ σ s hs) (surjective_liftEπ σ s hs) (ker_liftEπ σ s hs)

/-- The push of the `J`-part of a localization of `C`. -/
noncomputable def pushC (σ : Setup J f B₀) (s : Finset (Fin r)) :
    locC₀ J f C s ⊗[A] J →ₗ[A] locC f C s :=
  pushOf J σ.sq_eq_bot (redC J f C s) (surjective_redC J f C s) (ker_redC J f C s)

/-- The push of the `J`-part of `C`. -/
noncomputable def pushC₀ (σ : Setup J f B₀) : (C ⧸ J.map (algebraMap A C)) ⊗[A] J →ₗ[A] C :=
  pushOf J σ.sq_eq_bot (Ideal.Quotient.mkₐ A (J.map (algebraMap A C)))
    (Ideal.Quotient.mkₐ_surjective A _) (by rw [Ideal.Quotient.mkₐ_ker])

/-- `pushE` is compatible with the restrictions `locBRes` and `resE`. -/
theorem pushE_restrict (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (h : t ⊆ s) (w : locB J f B₀ t ⊗[A] J) :
    pushE σ s hs ((locBRes J f B₀ h).toLinearMap.rTensor J w) =
      resE σ ht hs h (pushE σ t ht w) :=
  pushOf_naturality J σ.sq_eq_bot _ _ _ _ _ _ _ _ (liftEπ_resE σ ht hs h) w

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))] in
/-- `pushC` is compatible with the restrictions `locC₀Res` and `locCRes`. -/
theorem pushC_restrict (σ : Setup J f B₀) {t s : Finset (Fin r)} (h : t ⊆ s)
    (w : locC₀ J f C t ⊗[A] J) :
    pushC C σ s ((locC₀Res J f C h).toLinearMap.rTensor J w) = locCRes f C h (pushC C σ t w) :=
  pushOf_naturality J σ.sq_eq_bot _ _ _ _ _ _ _ _
    (fun x ↦ by rw [← AlgHom.comp_apply, redC_locCRes, AlgHom.comp_apply]) w

/-- `pushC` and `pushE` are compatible with the maps `locBC` and `ψ_s`. -/
theorem pushC_psi (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty)
    (w : locB J f B₀ s ⊗[A] J) :
    pushC C σ s ((locBC C s).toLinearMap.rTensor J w) = psi C σ s hs (pushE σ s hs w) :=
  pushOf_naturality J σ.sq_eq_bot _ _ _ _ _ _ _ _ (redC_psi C σ s hs) w

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))] in
/-- `pushC` is compatible with `pushC₀` and the localization maps of `C ⧸ JC` and `C`. -/
theorem pushC_algebraMap (σ : Setup J f B₀) (s : Finset (Fin r))
    (w : (C ⧸ J.map (algebraMap A C)) ⊗[A] J) :
    pushC C σ s ((IsScalarTower.toAlgHom A (C ⧸ J.map (algebraMap A C))
      (locC₀ J f C s)).toLinearMap.rTensor J w) =
      algebraMap C (locC f C s) (pushC₀ C σ w) :=
  pushOf_naturality J σ.sq_eq_bot _ _ _ _ _ _ (IsScalarTower.toAlgHom A C (locC f C s)) _
    (fun c ↦ by
      change redC J f C s (algebraMap C (locC f C s) c) = _
      rw [redC_algebraMap]; rfl) w

/-- `pushE` is injective. -/
private theorem injective_pushE (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    Function.Injective (pushE σ s hs) :=
  injective_pushOf J σ.sq_eq_bot _ _ _

/-- An element lies in the image of `pushOf` iff its reduction vanishes. -/
private theorem mem_range_pushOf_iff {T₁ T₂ : Type u} [CommRing T₁] [CommRing T₂] [Algebra A T₁]
    [Algebra A T₂] {hJ : J ^ 2 = ⊥} {π : T₁ →ₐ[A] T₂} {hπ : Function.Surjective π}
    {hker : RingHom.ker (π : T₁ →+* T₂) = J.map (algebraMap A T₁)} {x : T₁} :
    x ∈ LinearMap.range (pushOf J hJ π hπ hker) ↔ π x = 0 := by
  rw [← SetLike.mem_coe, range_pushOf, SetLike.mem_coe, ← hker, RingHom.mem_ker]
  rfl

omit [IsScalarTower A (A ⧸ J) B₀] in
/-- `modelRes` is `locBRes ⊗ J`. -/
theorem modelRes_apply {t s : Finset (Fin r)} (h : t ⊆ s) (w : locB J f B₀ t ⊗[A] J) :
    modelRes J f B₀ h w = (locBRes J f B₀ h).toLinearMap.rTensor J w := by
  rfl

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `modelResS` is `locC₀Res ⊗ J`. -/
theorem modelResS_apply {t s : Finset (Fin r)} (h : t ⊆ s) (w : locC₀ J f C t ⊗[A] J) :
    modelResS (B₀ := B₀) C h w = (locC₀Res J f C h).toLinearMap.rTensor J w := by
  rfl

/-- `modelκ` is `locBC ⊗ J`. -/
theorem modelκ_apply (s : Finset (Fin r)) (w : locB J f B₀ s ⊗[A] J) :
    modelκ C s w = (locBC C s).toLinearMap.rTensor J w := by
  rfl

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `modelLS` is `thetaJ` followed by the localization map of `C ⧸ JC`, tensored with `J`. -/
theorem modelLS_apply (s : Finset (Fin r)) (w : modJ J B₀ ⊗[B₀] (C ⧸ J.map (algebraMap A C))) :
    modelLS (J := J) (f := f) C s w =
      (IsScalarTower.toAlgHom A (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)).toLinearMap.rTensor J
        (thetaJ (J := J) C w) := by
  rfl

/-- **Every element of `B₀` lifts to the glued ring.** The defect of componentwise lifts is a
cocycle of the glueing complex of `B₀ ⊗[A] J`, which is a coboundary by the third-term exactness of
formal glueing; correcting the lifts by it gives a compatible family. -/
theorem exists_lift_to_glueRing (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s))
    (b₀ : B₀) : ∃ x : glueRing C σ, glueReduction σ hflat hq x = b₀ := by
  classical
  have hne1 : ∀ i : Fin r, ({i} : Finset (Fin r)).Nonempty := fun i ↦ Finset.singleton_nonempty i
  have hne2 : ∀ a b : Fin r, ({a, b} : Finset (Fin r)).Nonempty := fun a b ↦
    Finset.insert_nonempty a {b}
  -- componentwise lifts
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b₀)
  choose e he using fun i ↦ surjective_liftEπ σ {i} (hne1 i) (algebraMap B₀ (locB J f B₀ {i}) b₀)
  -- the defects lie in the `J`-parts, hence are pushes
  have hD₁ : ∀ i, psi C σ {i} (hne1 i) (e i) - algebraMap C (locC f C {i}) c ∈
      LinearMap.range (pushC C σ {i}) := by
    intro i
    refine mem_range_pushOf_iff.2 ?_
    rw [map_sub, redC_psi, he, locBC_algebraMap, redC_algebraMap, hc,
      sub_self]
  have hD₂ : ∀ a b, resE σ (hne1 b) (hne2 a b) (singleton_subset_pair_right a b) (e b) -
      resE σ (hne1 a) (hne2 a b) (singleton_subset_pair_left a b) (e a) ∈
      LinearMap.range (pushE σ {a, b} (hne2 a b)) := by
    intro a b
    refine mem_range_pushOf_iff.2 ?_
    rw [map_sub, liftEπ_resE, liftEπ_resE, he, he, locBRes_algebraMap,
      locBRes_algebraMap, sub_self]
  choose y hy using hD₁
  choose x hx using hD₂
  -- injectivity of the pushes
  have hinjC : ∀ s : Finset (Fin r), s.Nonempty → Function.Injective (pushC C σ s) := fun s hs ↦
    have := hEtC s hs
    injective_pushOf J σ.sq_eq_bot _ _ _
  -- the cocycle conditions on the models
  have hcy : ∀ a b (hab : a < b),
      modelResS (B₀ := B₀) C (FormalGlueing.singleton_subset_pair_right' a b) (y b) -
        modelResS (B₀ := B₀) C (FormalGlueing.singleton_subset_pair_left' a b) (y a) =
      modelκ C {a, b} (x a b) := by
    intro a b hab
    apply hinjC {a, b} (hne2 a b)
    rw [map_sub, modelResS_apply, modelResS_apply, modelκ_apply, pushC_restrict, pushC_restrict,
      pushC_psi C σ {a, b} (hne2 a b), hy, hy, hx, map_sub, map_sub, map_sub,
      ← psi_resE_apply C σ (hne1 b) (hne2 a b), ← psi_resE_apply C σ (hne1 a) (hne2 a b),
      locCRes_algebraMap, locCRes_algebraMap]
    abel
  have hcx : ∀ a b c (hab : a < b) (hbc : b < c),
      modelRes J f B₀ (show ({b, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) (x b c) -
        modelRes J f B₀ (show ({a, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) (x a c) +
        modelRes J f B₀ (show ({a, b} : Finset (Fin r)) ⊆ {a, b, c} by
          intro t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) (x a b) = 0 := by
    intro a b c hab hbc
    apply injective_pushE σ {a, b, c} (Finset.insert_nonempty a _)
    rw [map_zero, map_add, map_sub, modelRes_apply, modelRes_apply, modelRes_apply,
      pushE_restrict σ (hne2 b c), pushE_restrict σ (hne2 a c), pushE_restrict σ (hne2 a b),
      hx, hx, hx]
    simp only [map_sub, resE_comp_apply]
    abel
  -- the defect is a coboundary
  obtain ⟨n, z, hn, hz⟩ := FormalGlueing.glueing_exact_third_of_models B₀
    (C ⧸ J.map (algebraMap A C)) (genB J f B₀) (modJ J B₀) hflat hq (modelL J f B₀)
    (fun s _ ↦ isLocalizedModule_modelL s) (modelLS (J := J) (f := f) C)
    (fun s _ ↦ isLocalizedModule_modelLS C s) (fun h ↦ modelRes J f B₀ h)
    (fun h ↦ modelRes_comp h) (fun h ↦ modelResS (B₀ := B₀) C h) (fun h ↦ modelResS_comp C h)
    (modelκ C) (modelκ_comp C) y (fun a b _ ↦ x a b) hcy hcx
  -- the corrected lifts
  let c' : C := c + pushC₀ C σ (thetaJ (J := J) C n)
  let e' : ∀ i, liftE σ {i} (hne1 i) := fun i ↦ e i + pushE σ {i} (hne1 i) (z i)
  have h₁ : ∀ i, psi C σ {i} (hne1 i) (e' i) = algebraMap C (locC f C {i}) c' := by
    intro i
    have key := congrArg (pushC C σ {i}) (hn i)
    rw [map_sub, modelLS_apply, pushC_algebraMap, modelκ_apply, pushC_psi C σ {i} (hne1 i),
      hy] at key
    simp only [e', c', map_add]
    linear_combination -key
  have h₂ : ∀ a b (hab : a < b),
      resE σ (hne1 a) (hne2 a b) (singleton_subset_pair_left a b) (e' a) =
        resE σ (hne1 b) (hne2 a b) (singleton_subset_pair_right a b) (e' b) := by
    intro a b hab
    have key := congrArg (pushE σ {a, b} (hne2 a b)) (hz a b hab)
    rw [map_sub, modelRes_apply, modelRes_apply, pushE_restrict σ (hne1 a) (hne2 a b),
      pushE_restrict σ (hne1 b) (hne2 a b), hx] at key
    simp only [e', map_add]
    linear_combination key
  have hmem : ((c', e') : C × ∀ i : Fin r, liftE σ {i} (hne1 i)) ∈ glueRing C σ := by
    refine ⟨h₁, fun i j ↦ ?_⟩
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact h₂ i j hij
    · rfl
    · have h := congrArg (resE σ (hne2 j i) (hne2 i j) (by
        intro t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)) (h₂ j i hij)
      rw [resE_comp_apply, resE_comp_apply] at h
      exact h.symm
  refine ⟨⟨(c', e'), hmem⟩, ?_⟩
  change (exists_reduction C σ hflat hq ⟨(c', e'), hmem⟩).choose = b₀
  apply eq_of_reductions C hflat hq
  · rw [(exists_reduction C σ hflat hq ⟨(c', e'), hmem⟩).choose_spec.1]
    change Ideal.Quotient.mk _ (c + pushC₀ C σ (thetaJ (J := J) C n)) = _
    rw [map_add, show Ideal.Quotient.mk _ (pushC₀ C σ _) = 0 from
        mem_range_pushOf_iff.1 (LinearMap.mem_range_self (pushC₀ C σ) _),
      add_zero, hc]
  · intro i
    rw [(exists_reduction C σ hflat hq ⟨(c', e'), hmem⟩).choose_spec.2 i]
    change liftEπ σ {i} (hne1 i) (e i + pushE σ {i} (hne1 i) (z i)) = _
    rw [map_add, show liftEπ σ {i} (hne1 i) (pushE σ {i} (hne1 i) _) = 0 from
      mem_range_pushOf_iff.1 (LinearMap.mem_range_self (pushE σ {i} (hne1 i)) _), add_zero, he]

/-- The base change `B₀ ⊗[A] J → (C ⧸ JC) ⊗[A] J`. -/
noncomputable def muJ : modJ J B₀ →ₗ[B₀] (C ⧸ J.map (algebraMap A C)) ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J
    (Algebra.linearMap B₀ (C ⧸ J.map (algebraMap A C)))

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `muJ` is the base change of `B₀ ⊗[A] J` along `B₀ → C ⧸ JC`. -/
theorem isBaseChange_muJ :
    IsBaseChange (C ⧸ J.map (algebraMap A C)) (muJ (J := J) (B₀ := B₀) C) := by
  refine IsBaseChange.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B₀ (C ⧸ J.map (algebraMap A C))
      (C ⧸ J.map (algebraMap A C)) J) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul b j => simp [muJ, Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The localization of `(C ⧸ JC) ⊗[A] J` at `f i`. -/
noncomputable def lSJ (i : Fin r) :
    (C ⧸ J.map (algebraMap A C)) ⊗[A] J →ₗ[B₀] locC₀ J f C {i} ⊗[A] J :=
  TensorProduct.AlgebraTensorModule.rTensor A J
    (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})).toLinearMap

/-- `lSJ` is the localization of `(C ⧸ JC) ⊗[A] J` at the powers of `genB i`. -/
theorem isLocalizedModule_lSJ (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (genB J f B₀ i))
      (lSJ (J := J) (f := f) (B₀ := B₀) C i) := by
  have := isLocalizedModule_locC₀_singleton (J := J) (f := f) (B₀ := B₀) C i
  unfold lSJ
  infer_instance

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `lSJ` is the localization map of `C ⧸ JC` at `f i`, tensored with `J`. -/
theorem lSJ_apply (i : Fin r) (w : (C ⧸ J.map (algebraMap A C)) ⊗[A] J) :
    lSJ (J := J) (f := f) (B₀ := B₀) C i w =
      (IsScalarTower.toAlgHom A (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})).toLinearMap.rTensor
        J w := by
  rfl

/-- The image in `C ⧸ JC` of the reduction of `x` is the class of its `C`-component. -/
theorem algebraMap_glueReduction (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map)) (x : glueRing C σ) :
    algebraMap B₀ (C ⧸ J.map (algebraMap A C)) (glueReduction σ hflat hq x) =
      Ideal.Quotient.mk (J.map (algebraMap A C)) x.1.1 :=
  (exists_reduction C σ hflat hq x).choose_spec.1

/-- The image in `B₀[1/g_i]` of the reduction of `x` is the reduction of its `i`-th component. -/
theorem algebraMap_locB_glueReduction (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map)) (x : glueRing C σ)
    (i : Fin r) :
    algebraMap B₀ (locB J f B₀ {i}) (glueReduction σ hflat hq x) =
      liftEπ σ {i} (Finset.singleton_nonempty i) (x.1.2 i) :=
  (exists_reduction C σ hflat hq x).choose_spec.2 i

/-- The two maps `B₀ ⊗[A] J → (C ⧸ JC)[1/g_i] ⊗[A] J`, through `B₀[1/g_i] ⊗[A] J` and through
`(C ⧸ JC) ⊗[A] J`, agree. -/
theorem modelκ_comp_muJ (i : Fin r) :
    modelκ (J := J) (B₀ := B₀) (f := f) C {i} ∘ₗ modelL J f B₀ {i} =
      lSJ (J := J) (f := f) (B₀ := B₀) C i ∘ₗ muJ C := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext b
  simp [modelκ, modelL, lSJ, muJ, locBCLin]

/-- Exactness of the glueing complex of `B₀ ⊗[A] J` at its second term, for the models. -/
private theorem exists_modelL_eq
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (y : (C ⧸ J.map (algebraMap A C)) ⊗[A] J) (x : ∀ i, locB J f B₀ {i} ⊗[A] J)
    (h₁ : ∀ i, lSJ (J := J) (f := f) (B₀ := B₀) C i y = modelκ C {i} (x i))
    (h₂ : ∀ i j, i ≠ j → modelRes J f B₀ (singleton_subset_pair_left i j) (x i) =
      modelRes J f B₀ (singleton_subset_pair_right i j) (x j)) :
    ∃ m : modJ J B₀, muJ C m = y ∧ ∀ i, modelL J f B₀ {i} m = x i :=
  have hL1 : ∀ i, IsLocalizedModule (Submonoid.powers (genB J f B₀ i)) (modelL J f B₀ {i}) :=
    fun i ↦ by
      have := isLocalization_locB_singleton J f B₀ i
      unfold modelL
      infer_instance
  have hLS : ∀ i, IsLocalizedModule (Submonoid.powers (genB J f B₀ i))
      (lSJ (J := J) (f := f) (B₀ := B₀) C i) := fun i ↦ isLocalizedModule_lSJ C i
  FormalGlueing.glueing_exact_middle_of_models B₀
    (C ⧸ J.map (algebraMap A C)) (genB J f B₀) (modJ J B₀) hflat hq (muJ C) (isBaseChange_muJ C)
    (fun i ↦ modelL J f B₀ {i}) (fun i j ↦ modelL J f B₀ {i, j})
    (fun i j hij ↦ by
      have := isLocalization_locB_pair J f B₀ hij
      unfold modelL
      infer_instance)
    (fun i ↦ lSJ (J := J) (f := f) (B₀ := B₀) C i)
    (fun i j ↦ modelRes J f B₀ (singleton_subset_pair_left i j))
    (fun i j ↦ modelRes_comp _)
    (fun i j ↦ modelRes J f B₀ (singleton_subset_pair_right i j))
    (fun i j ↦ modelRes_comp _)
    (fun i ↦ modelκ C {i}) (fun i ↦ modelκ_comp_muJ C i) y x h₁ h₂

/-- **The kernel of the reduction is `J` times the glued ring.** -/
theorem ker_glueReduction (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s)) :
    RingHom.ker (glueReduction σ hflat hq : glueRing C σ →+* B₀) =
      J.map (algebraMap A (glueRing C σ)) := by
  classical
  have hne1 : ∀ i : Fin r, ({i} : Finset (Fin r)).Nonempty := fun i ↦ Finset.singleton_nonempty i
  have hne2 : ∀ a b : Fin r, ({a, b} : Finset (Fin r)).Nonempty := fun a b ↦
    Finset.insert_nonempty a {b}
  have hinjC : ∀ s : Finset (Fin r), s.Nonempty → Function.Injective (pushC C σ s) := fun s hs ↦
    have := hEtC s hs
    injective_pushOf J σ.sq_eq_bot _ _ _
  -- every element of `B₀ ⊗[A] J` is the `J`-part of an element of `J · glueRing`
  have hgen : ∀ m : modJ J B₀, ∃ X ∈ J.map (algebraMap A (glueRing C σ)),
      X.1.1 = pushC₀ C σ (muJ C m) ∧ ∀ i, X.1.2 i = pushE σ {i} (hne1 i) (modelL J f B₀ {i} m) := by
    intro m
    induction m using TensorProduct.inductionOn with
    | tmul b j =>
      obtain ⟨Y, hY⟩ := exists_lift_to_glueRing C σ hflat hq hEtC b
      refine ⟨algebraMap A (glueRing C σ) j * Y,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2), ?_, fun i ↦ ?_⟩
      · change algebraMap A C j * Y.1.1 = _
        rw [muJ, TensorProduct.AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply, ← hY,
          algebraMap_glueReduction]
        exact (pushOf_tmul J σ.sq_eq_bot (Ideal.Quotient.mkₐ A (J.map (algebraMap A C)))
          (Ideal.Quotient.mkₐ_surjective A _) (by rw [Ideal.Quotient.mkₐ_ker]) Y.1.1 j).symm
      · change algebraMap A (liftE σ {i} (hne1 i)) j * Y.1.2 i = _
        rw [modelL, TensorProduct.AlgebraTensorModule.rTensor_tmul, Algebra.linearMap_apply, ← hY,
          algebraMap_locB_glueReduction, pushE, pushOf_tmul]
    | add m m' hm hm' =>
      obtain ⟨X, hX, hX₁, hX₂⟩ := hm
      obtain ⟨X', hX', hX'₁, hX'₂⟩ := hm'
      refine ⟨X + X', Submodule.add_mem _ hX hX', ?_, fun i ↦ ?_⟩
      · change X.1.1 + X'.1.1 = _
        rw [hX₁, hX'₁, map_add, map_add]
      · change X.1.2 i + X'.1.2 i = _
        rw [hX₂, hX'₂, map_add, map_add]
  apply le_antisymm
  · intro x hx
    replace hx : glueReduction σ hflat hq x = 0 := hx
    -- the components lie in the `J`-parts
    have h₀ : x.1.1 ∈ LinearMap.range (pushC₀ C σ) := by
      refine mem_range_pushOf_iff.2 ?_
      change Ideal.Quotient.mk _ x.1.1 = 0
      rw [← algebraMap_glueReduction C σ hflat hq x, hx, map_zero]
    have hi : ∀ i, x.1.2 i ∈ LinearMap.range (pushE σ {i} (hne1 i)) := fun i ↦ by
      refine mem_range_pushOf_iff.2 ?_
      change liftEπ σ {i} (hne1 i) _ = 0
      rw [← algebraMap_locB_glueReduction C σ hflat hq x, hx, map_zero]
    obtain ⟨w₀, hw₀⟩ := h₀
    choose w hw using hi
    -- the `J`-parts form a compatible family of the models
    obtain ⟨m, hm₀, hm⟩ := exists_modelL_eq C hflat hq w₀ w
      (fun i ↦ hinjC {i} (hne1 i) <| by
        rw [lSJ_apply, modelκ_apply, pushC_algebraMap, pushC_psi C σ {i} (hne1 i), hw, hw₀]
        exact (x.2.1 i).symm)
      (fun i j _ ↦ injective_pushE σ {i, j} (hne2 i j) <| by
        rw [modelRes_apply, modelRes_apply, pushE_restrict σ (hne1 i) (hne2 i j),
          pushE_restrict σ (hne1 j) (hne2 i j), hw, hw]
        exact x.2.2 i j)
    obtain ⟨X, hX, hX₁, hX₂⟩ := hgen m
    rwa [show x = X from Subtype.ext <| Prod.ext (by rw [hX₁, hm₀, hw₀])
      (funext fun i ↦ by rw [hX₂, hm, hw])]
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change glueReduction σ hflat hq (algebraMap A _ a) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ J) B₀,
      Ideal.Quotient.algebraMap_eq, (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]

omit [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- The base change `B₀ ⊗[A] J → (C ⧸ JC) ⊗[A] J` along `B₀ → C ⧸ JC` is `muJ`. -/
theorem rTensor_toAlgHom_eq_muJ (m : B₀ ⊗[A] J) :
    (IsScalarTower.toAlgHom A B₀ (C ⧸ J.map (algebraMap A C))).toLinearMap.rTensor J m =
      muJ C m := by
  rfl

variable {C} in
/-- The projection of the glued ring onto `C`. -/
noncomputable def glueToC (σ : Setup J f B₀) : glueRing C σ →ₐ[A] C :=
  (AlgHom.fst A C _).comp (glueRing C σ).val

variable {C} in
/-- The projection of the glued ring onto the `i`-th étale lift. -/
noncomputable def glueEval (σ : Setup J f B₀) (i : Fin r) :
    glueRing C σ →ₐ[A] liftE σ {i} (Finset.singleton_nonempty i) :=
  (Pi.evalAlgHom A (fun i : Fin r ↦ liftE σ {i} (Finset.singleton_nonempty i)) i).comp
    ((AlgHom.snd A C _).comp (glueRing C σ).val)

variable {C} in
/-- The push of the `J`-part of the glued ring. -/
noncomputable def pushB (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s)) :
    B₀ ⊗[A] J →ₗ[A] glueRing C σ :=
  pushOf J σ.sq_eq_bot (glueReduction σ hflat hq)
    (fun b ↦ exists_lift_to_glueRing C σ hflat hq hEtC b) (ker_glueReduction C σ hflat hq hEtC)

/-- The `C`-component of `pushB m` is `pushC₀ (muJ m)`. -/
theorem glueToC_pushB (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s)) (m : B₀ ⊗[A] J) :
    glueToC σ (pushB σ hflat hq hEtC m) = pushC₀ C σ (muJ C m) := by
  have h := pushOf_naturality J σ.sq_eq_bot (glueReduction σ hflat hq)
    (fun b ↦ exists_lift_to_glueRing C σ hflat hq hEtC b) (ker_glueReduction C σ hflat hq hEtC)
    (Ideal.Quotient.mkₐ A (J.map (algebraMap A C))) (Ideal.Quotient.mkₐ_surjective A _)
    (by rw [Ideal.Quotient.mkₐ_ker]) (glueToC σ)
    (IsScalarTower.toAlgHom A B₀ (C ⧸ J.map (algebraMap A C)))
    (fun x ↦ (algebraMap_glueReduction C σ hflat hq x).symm) m
  refine h.symm.trans ?_
  change pushC₀ C σ _ = _
  rw [rTensor_toAlgHom_eq_muJ]

/-- The `i`-th component of `pushB m` is `pushE` of the localization of `m` at `f i`. -/
theorem glueEval_pushB (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s)) (m : B₀ ⊗[A] J)
    (i : Fin r) :
    glueEval σ i (pushB σ hflat hq hEtC m) =
      pushE σ {i} (Finset.singleton_nonempty i) (modelL J f B₀ {i} m) := by
  have h := pushOf_naturality J σ.sq_eq_bot (glueReduction σ hflat hq)
    (fun b ↦ exists_lift_to_glueRing C σ hflat hq hEtC b) (ker_glueReduction C σ hflat hq hEtC)
    (liftEπ σ {i} (Finset.singleton_nonempty i)) (surjective_liftEπ σ {i} _)
    (ker_liftEπ σ {i} _) (glueEval σ i) (IsScalarTower.toAlgHom A B₀ (locB J f B₀ {i}))
    (fun x ↦ (algebraMap_locB_glueReduction C σ hflat hq x i).symm) m
  refine h.symm.trans ?_
  change pushE σ {i} _ _ = _
  congr 1

/-- **The glued ring maps étale onto `C`.** -/
theorem etale_glueRing (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s))
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra (glueRing C σ) C] [IsScalarTower A (glueRing C σ) C]
    (hC : ∀ x, algebraMap (glueRing C σ) C x = glueToC σ x) :
    Algebra.Etale (glueRing C σ) C := by
  classical
  have hne1 : ∀ i : Fin r, ({i} : Finset (Fin r)).Nonempty := fun i ↦ Finset.singleton_nonempty i
  have hinjC : ∀ s : Finset (Fin r), s.Nonempty → Function.Injective (pushC C σ s) := fun s hs ↦
    have := hEtC s hs
    injective_pushOf J σ.sq_eq_bot _ _ _
  refine etale_of_pushOf J σ.sq_eq_bot (glueReduction σ hflat hq)
    (fun b ↦ exists_lift_to_glueRing C σ hflat hq hEtC b) (ker_glueReduction C σ hflat hq hEtC)
    (Ideal.Quotient.mkₐ A (J.map (algebraMap A C))) (Ideal.Quotient.mkₐ_surjective A _)
    (by rw [Ideal.Quotient.mkₐ_ker])
    (fun x ↦ by rw [hC]; exact (algebraMap_glueReduction C σ hflat hq x).symm) ?_
  intro w hw
  replace hw : pushC₀ C σ w = 0 := hw
  have hloc : ∀ i, lSJ (J := J) (f := f) (B₀ := B₀) C i w = 0 := by
    intro i
    apply hinjC {i} (hne1 i)
    rw [lSJ_apply, pushC_algebraMap, hw, map_zero, map_zero]
  obtain ⟨m, hm₀, hm⟩ := exists_modelL_eq C hflat hq w (fun _ ↦ 0)
    (fun i ↦ by rw [hloc, map_zero]) (fun i j _ ↦ by rw [map_zero, map_zero])
  refine ⟨m, ?_, ?_⟩
  · rw [← hm₀, rTensor_toAlgHom_eq_muJ]
  · change pushB σ hflat hq hEtC m = 0
    apply Subtype.ext
    apply Prod.ext
    · change glueToC σ (pushB σ hflat hq hEtC m) = 0
      rw [glueToC_pushB, hm₀, hw]
    · funext i
      change glueEval σ i (pushB σ hflat hq hEtC m) = 0
      rw [glueEval_pushB, hm, map_zero]


/-- **The glued ring is étale over `A` away from `V(f_i)`**: its localization at `f_i` is the
étale lift of `B₀[1/f_i]`. -/
theorem etale_localizationAway_glueRing (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s)) (i : Fin r) :
    Algebra.Etale A (Localization.Away (algebraMap A (glueRing C σ) (f i))) := by
  have hne : ({i} : Finset (Fin r)).Nonempty := Finset.singleton_nonempty i
  have hred : glueReduction σ hflat hq (algebraMap A (glueRing C σ) (f i)) = genB J f B₀ i := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq]
  have : IsLocalization.Away (glueReduction σ hflat hq (algebraMap A (glueRing C σ) (f i)))
      (locB J f B₀ {i}) := by
    rw [hred]; exact isLocalization_locB_singleton J f B₀ i
  exact etale_localizationAway_of_thickening J σ.sq_eq_bot (glueReduction σ hflat hq)
    (fun b ↦ exists_lift_to_glueRing C σ hflat hq hEtC b) (ker_glueReduction C σ hflat hq hEtC)
    (algebraMap A (glueRing C σ) (f i)) (liftEπ σ {i} hne) (surjective_liftEπ σ {i} hne)
    (ker_liftEπ σ {i} hne) (glueEval σ i)
    (fun x ↦ (algebraMap_locB_glueReduction C σ hflat hq x i).symm)

/-- **The glued ring is étale over `A` at every prime off `V(I)`.** -/
theorem isEtaleAt_glueRing (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (locC f C s))
    {I : Ideal A} (hI : I ≤ Ideal.span (Set.range f))
    (q : Ideal (glueRing C σ)) [q.IsPrime] (hq' : ¬ I ≤ q.comap (algebraMap A (glueRing C σ))) :
    Algebra.IsEtaleAt A q := by
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ q.comap (algebraMap A (glueRing C σ)) := by
    by_contra h
    push Not at h
    exact hq' (hI.trans (Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
  have := etale_localizationAway_glueRing C σ hflat hq hEtC i
  have hsub := (Algebra.basicOpen_subset_etaleLocus_iff (R := A)
    (f := algebraMap A (glueRing C σ) (f i))).mpr inferInstance
  exact hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum _) ∈
    PrimeSpectrum.basicOpen (algebraMap A (glueRing C σ) (f i)) from hi)

end Reduction

end SquareZero
