module

public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftClassCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpensSiteSquares

/-!
# The squares of trivial square-zero extensions along a cover

Ring-theoretic input for `Deformation.Artin.liftClassRowExact_of_cover`: the square-zero
immersion `Spec A ⟶ Spec A[M]` is a deformation situation on global sections
(`Deformation.Artin.isDeformationSituation_squareZeroArrow`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Deformation.Artin

universe u

/-- A deformation situation of rings stays one on the global sections of the spectra. -/
theorem isDeformationSituation_appTop_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (h : IsDeformationSituation φ.hom) : IsDeformationSituation (Spec.map φ).appTop.hom := by
  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [e]
  have hR : Function.Bijective (Scheme.ΓSpecIso R).hom.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hS : Function.Bijective (Scheme.ΓSpecIso S).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨hS.2.comp (h.1.comp hR.2), ?_⟩
  change (RingHom.ker ((Scheme.ΓSpecIso S).inv.hom.comp
    (φ.hom.comp (Scheme.ΓSpecIso R).hom.hom))) ^ 2 = ⊥
  rw [RingHom.ker_comp_of_injective _ hS.1, ← RingHom.comap_ker]
  refine le_bot_iff.mp ((Ideal.le_comap_pow _ 2).trans ?_)
  rw [h.2, Ideal.comap_bot_of_injective _ hR.1]

section SquareZeroArrow

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- **The square-zero immersion `Spec A ⟶ Spec A[M]` is a deformation situation** on global
sections: `A[M] → A` is surjective with kernel `M`, of square zero. -/
theorem isDeformationSituation_squareZeroArrow (M : SiteModule A B) :
    IsDeformationSituation ((BigFppfOver.toScheme B S hS).map
      (squareZeroArrow A B S hS toS hA M)).appTop.hom := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom A A M.obj) := fun r ↦
    ⟨(TrivSqZeroExt.inl r : TrivSqZeroExt A M.obj), TrivSqZeroExt.fst_inl M.obj r⟩
  refine isDeformationSituation_appTop_specMap
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) ⟨hs, ?_⟩
  refine le_bot_iff.mp ?_
  rw [pow_two]
  refine Ideal.mul_le.mpr fun x hx y hy ↦ ?_
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  refine (Submodule.mem_bot _).mpr (TrivSqZeroExt.ext ?_ ?_)
  · simp [hx']
  · simp [hx', hy']

end SquareZeroArrow

/-! ### The square-zero extension of a base change is a pushout -/

section Pushout

open CategoryTheory.Limits TensorProduct

variable {A A₁ : Type u} [CommRing A] [CommRing A₁] [Algebra A A₁]
  {M : ModuleCat.{u} A} {M₁ : ModuleCat.{u} A₁}

/-- An additive identification `A₁ ⊗_A M ≅ M₁` sending `c ⊗ m` to `c • ψ m` is `A₁`-linear. -/
theorem addEquiv_smul_of_tmul (ψ : (M : Type u) →+ (M₁ : Type u)) (e : A₁ ⊗[A] M ≃+ M₁)
    (he : ∀ (c : A₁) (m : M), e (c ⊗ₜ m) = c • ψ m) (c : A₁) (t : A₁ ⊗[A] M) :
    e (c • t) = c • e t := by
  induction t using TensorProduct.inductionOn with
  | tmul c' m => rw [TensorProduct.smul_tmul', he, he, smul_eq_mul, mul_smul]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The inverse of an additive identification `A₁ ⊗_A M ≅ M₁` sending `c ⊗ m` to `c • ψ m` is
`A₁`-linear. -/
theorem addEquiv_symm_smul_of_tmul (ψ : (M : Type u) →+ (M₁ : Type u)) (e : A₁ ⊗[A] M ≃+ M₁)
    (he : ∀ (c : A₁) (m : M), e (c ⊗ₜ m) = c • ψ m) (c : A₁) (n : M₁) :
    e.symm (c • n) = c • e.symm n :=
  e.symm_apply_eq.mpr (by rw [addEquiv_smul_of_tmul ψ e he, AddEquiv.apply_symm_apply])

variable {R : Type u} [CommRing R]

/-- The additive map `A₁ ⊗_A M → R`, `c ⊗ m ↦ u(c) v(m)`, out of the base change of the
coefficients, for ring maps `u : A₁ → R` and `v : A[M] → R` agreeing on `A`. -/
def sqzTensorDescAdd (uu : A₁ →+* R) (v : TrivSqZeroExt A M →+* R)
    (huv : ∀ r, uu (algebraMap A A₁ r) = v (TrivSqZeroExt.inl r)) : A₁ ⊗[A] M →+ R :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun c ↦ AddMonoidHom.mk' (fun m ↦ uu c * v (TrivSqZeroExt.inr m))
      (fun m m' ↦ by rw [TrivSqZeroExt.inr_add, map_add, mul_add]))
      (fun c c' ↦ by ext m; simp only [map_add, add_mul, AddMonoidHom.mk'_apply,
        AddMonoidHom.add_apply]))
    (fun r c m ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, huv, ← TrivSqZeroExt.inl_mul_inr, map_mul]
      ring)

variable (uu : A₁ →+* R) (v : TrivSqZeroExt A M →+* R)
  (huv : ∀ r, uu (algebraMap A A₁ r) = v (TrivSqZeroExt.inl r))

/-- `sqzTensorDescAdd` sends `c ⊗ m` to `u(c) v(m)`. -/
theorem sqzTensorDescAdd_tmul (c : A₁) (m : M) :
    sqzTensorDescAdd uu v huv (c ⊗ₜ m) = uu c * v (TrivSqZeroExt.inr m) := rfl

/-- `sqzTensorDescAdd` is semilinear along `u`: it sends `c • t` to `u(c)` times the image of
`t`. -/
theorem sqzTensorDescAdd_smul (c : A₁) (t : A₁ ⊗[A] M) :
    sqzTensorDescAdd uu v huv (c • t) = uu c * sqzTensorDescAdd uu v huv t := by
  induction t using TensorProduct.inductionOn with
  | tmul c' m => rw [TensorProduct.smul_tmul', sqzTensorDescAdd_tmul, sqzTensorDescAdd_tmul,
      smul_eq_mul, map_mul, mul_assoc]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', mul_add]

/-- Any two values of `sqzTensorDescAdd` multiply to zero. -/
theorem sqzTensorDescAdd_mul (t t' : A₁ ⊗[A] M) :
    sqzTensorDescAdd uu v huv t * sqzTensorDescAdd uu v huv t' = 0 := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_zero]
  | tmul c m =>
    induction t' using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, add_zero]
    | tmul c' m' =>
      rw [sqzTensorDescAdd_tmul, sqzTensorDescAdd_tmul, mul_mul_mul_comm, ← map_mul v,
        TrivSqZeroExt.inr_mul_inr, map_zero, mul_zero]

/-- The ring map `A₁[M₁] → R` out of the square-zero extension of a base change, induced by
ring maps `u : A₁ → R` and `v : A[M] → R` agreeing on `A`. -/
def sqzPushoutDesc (e : A₁ ⊗[A] M ≃+ M₁) (hs : ∀ (c : A₁) (n : M₁), e.symm (c • n) = c • e.symm n) :
    TrivSqZeroExt A₁ M₁ →+* R where
  toFun z := uu z.fst + sqzTensorDescAdd uu v huv (e.symm z.snd)
  map_one' := by
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_one, map_zero, map_zero, add_zero]
  map_zero' := by
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, map_zero, map_zero, add_zero]
  map_add' z z' := by
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, map_add, map_add]
    ring
  map_mul' z z' := by
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, map_add, hs, hs, map_add,
      sqzTensorDescAdd_smul, sqzTensorDescAdd_smul, map_mul]
    have h0 := sqzTensorDescAdd_mul uu v huv (e.symm z.snd) (e.symm z'.snd)
    linear_combination (-1 : R) * h0

/-- A ring map out of `A₁[M₁]` is determined by its values on `A₁` and on `M₁`. -/
theorem sqz_ringHom_apply (φ : TrivSqZeroExt A₁ M₁ →+* R) (z : TrivSqZeroExt A₁ M₁) :
    φ z = φ (TrivSqZeroExt.inl z.fst) + φ (TrivSqZeroExt.inr z.snd) := by
  rw [← map_add, TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-- **`A₁[A₁ ⊗_A M] = A₁ ⊗_A A[M]`.** For an identification `A₁ ⊗_A M ≅ M₁` sending `c ⊗ m`
to `c • ψ m`, the square of `A → A₁`, `A → A[M]`, `A₁ → A₁[M₁]` and the map
`A[M] → A₁[M₁]` of `ψ` is a pushout of commutative rings. -/
theorem isPushout_squareZero_of_addEquiv
    (ψ : M ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj M₁)
    (e : A₁ ⊗[A] M ≃+ M₁)
    (he : ∀ (c : A₁) (m : M), e (c ⊗ₜ m) = c • restrictScalarsAddHom (algebraMap A A₁) ψ m) :
    IsPushout (CommRingCat.ofHom (algebraMap A A₁))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A₁ M₁))
      (CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₁)
        (restrictScalarsAddHom _ ψ) (restrictScalarsAddHom_smul _ ψ))) := by
  have hw : CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom A₁ M₁) =
      CommRingCat.ofHom (TrivSqZeroExt.inlHom A M) ≫ CommRingCat.ofHom (squareZeroRingBaseMap
        (algebraMap A A₁) (restrictScalarsAddHom _ ψ) (restrictScalarsAddHom_smul _ ψ)) := by
    apply CommRingCat.hom_ext
    ext r
    · rfl
    · change (0 : M₁) = restrictScalarsAddHom _ ψ 0
      rw [map_zero]
  have hs := addEquiv_symm_smul_of_tmul _ e he
  have hψ : ∀ m : M, e.symm (restrictScalarsAddHom (algebraMap A A₁) ψ m) = (1 : A₁) ⊗ₜ m :=
    fun m ↦ e.symm_apply_eq.mpr (by rw [he, one_smul])
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (sqzPushoutDesc s.inl.hom s.inr.hom (fun r ↦
      congrArg (fun g ↦ g.hom r) s.condition) e hs)) (fun s ↦ ?_) (fun s ↦ ?_)
      (fun s φ h₁ h₂ ↦ ?_))
  · apply CommRingCat.hom_ext
    ext c
    change s.inl.hom c + sqzTensorDescAdd _ _ _ (e.symm 0) = s.inl.hom c
    rw [map_zero, map_zero, add_zero]
  · apply CommRingCat.hom_ext
    ext z
    change s.inl.hom (algebraMap A A₁ z.fst) +
      sqzTensorDescAdd _ _ _ (e.symm (restrictScalarsAddHom (algebraMap A A₁) ψ z.snd)) =
      s.inr.hom z
    rw [hψ]
    refine (congrArg (s.inl.hom (algebraMap A A₁ z.fst) + ·)
      ((sqzTensorDescAdd_tmul (M := M) _ _ _ 1 z.snd).trans (by rw [map_one, one_mul]))).trans ?_
    have hc : s.inl.hom (algebraMap A A₁ z.fst) = s.inr.hom (TrivSqZeroExt.inl z.fst) :=
      congrArg (fun g : CommRingCat.of A ⟶ s.pt ↦ g.hom z.fst) s.condition
    rw [hc]
    exact (sqz_ringHom_apply (A₁ := A) (M₁ := M) s.inr.hom z).symm
  · have hl : ∀ c, φ.hom (TrivSqZeroExt.inl c) = s.inl.hom c := fun c ↦
      congrArg (fun g : CommRingCat.of A₁ ⟶ s.pt ↦ g.hom c) h₁
    have hr : ∀ m : M, φ.hom (TrivSqZeroExt.inr (restrictScalarsAddHom (algebraMap A A₁) ψ m)) =
        s.inr.hom (TrivSqZeroExt.inr m) :=
      fun m ↦ by
      refine Eq.trans ?_ (congrArg (fun g : CommRingCat.of (TrivSqZeroExt A M) ⟶ s.pt ↦
        g.hom (TrivSqZeroExt.inr m)) h₂)
      exact congrArg φ.hom (TrivSqZeroExt.ext (map_zero (algebraMap A A₁)).symm rfl)
    have ht : ∀ t : A₁ ⊗[A] M, φ.hom (TrivSqZeroExt.inr (e t)) =
        sqzTensorDescAdd s.inl.hom s.inr.hom (fun r ↦ congrArg (fun g ↦ g.hom r) s.condition) t :=
      fun t ↦ by
      induction t using TensorProduct.inductionOn with
      | add t t' h h' => rw [map_add, TrivSqZeroExt.inr_add, map_add, h, h', map_add]
      | tmul c m =>
        rw [he, ← TrivSqZeroExt.inl_mul_inr, map_mul, hl]
        exact (congrArg _ (hr m)).trans (sqzTensorDescAdd_tmul _ _ _ c m).symm
    apply CommRingCat.hom_ext
    ext z
    refine (sqz_ringHom_apply φ.hom z).trans ?_
    have h := ht (e.symm z.snd)
    rw [AddEquiv.apply_symm_apply] at h
    rw [hl, h]
    rfl

end Pushout

/-! ### Pasting the squares of square-zero extensions -/

section Pasting

variable {C : Type*} [Category C]

/-- **The reduction square of a pushout of square-zero extensions.** If `A₁[M₁]` is the
pushout of `A → A₁` and `A → A[M]`, and `A[M] → A`, `A₁[M₁] → A₁` are retractions of the
inclusions compatible with the maps, then `A₁ = A ⊔_{A[M]} A₁[M₁]`. -/
theorem isPushout_reduction_of_isPushout {X X₁ Y Y₁ : C} {g : X ⟶ X₁} {i : X ⟶ Y} {i₁ : X₁ ⟶ Y₁}
    {σ : Y ⟶ Y₁} (h : IsPushout g i i₁ σ) {r : Y ⟶ X} {r₁ : Y₁ ⟶ X₁} (hr : i ≫ r = 𝟙 X)
    (hr₁ : i₁ ≫ r₁ = 𝟙 X₁) (hσ : σ ≫ r₁ = r ≫ g) : IsPushout r σ g r₁ := by
  refine IsPushout.of_left (h₁₁ := i) (h₂₁ := i₁) (v₁₁ := g) ?_ hσ.symm h.flip
  rw [hr, hr₁]
  exact IsPushout.of_id_fst

/-- **The double overlap of a cover of square-zero extensions.** If `A₁[M₁] = A₁ ⊔_A A[M]`,
`A₂ = A₁ ⊔_A A₁` (through `a`, `b`), `A₂[M₂] = A₂ ⊔_{A₁} A₁[M₁]` along `b`, and the maps
`σa, σb : A₁[M₁] → A₂[M₂]` over `a`, `b` agree on `A[M]`, then
`A₂[M₂] = A₁[M₁] ⊔_{A[M]} A₁[M₁]`. -/
theorem isPushout_doubleOverlap {X X₁ X₂ Y Y₁ Y₂ : C} {f : X ⟶ X₁} {i : X ⟶ Y} {i₁ : X₁ ⟶ Y₁}
    {i₂ : X₂ ⟶ Y₂} {σ : Y ⟶ Y₁} {a b : X₁ ⟶ X₂} {σa σb : Y₁ ⟶ Y₂} (h : IsPushout f i i₁ σ)
    (h₂ : IsPushout f f b a) (hb : IsPushout b i₁ i₂ σb) (ha : i₁ ≫ σa = a ≫ i₂)
    (hab : σ ≫ σa = σ ≫ σb) : IsPushout σ σ σa σb := by
  have hD := IsPushout.paste_horiz h₂ hb.flip
  have hE : IsPushout (i ≫ σ) f σb (i₁ ≫ σa) := by
    rw [ha, ← h.w]
    exact hD
  exact (IsPushout.of_left hE hab.symm h.flip).flip

end Pasting

/-! ### The squares in the site -/

section Site

open CategoryTheory.Limits

variable {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))}
  {f : A →+* A₁} (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS₁)
  {M : SiteModule A B} {M₁ : SiteModule A₁ B}
  (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj M₁.obj)

include hf in
/-- **`Spec A₁ = Spec A ×_{Spec A[M]} Spec A₁[M₁]`**, in the site, as soon as
`A₁[M₁] = A₁ ⊗_A A[M]`. -/
theorem isPullback_squareZeroArrow_of_isPushout
    (h : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A₁ M₁.obj))
      (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)))) :
    IsPullback (algebraOverMapOfRingHom f B S hS toS toS₁ hA hA₁ hf)
      (squareZeroArrow A₁ B S hS toS₁ hA₁ M₁) (squareZeroArrow A B S hS toS hA M)
      (tangentPullbackBase f hf ψ) := by
  apply BigFppfOver.isPullback_of_toScheme
  refine isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_reduction_of_isPushout h ?_ ?_ ?_)
  all_goals exact CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)

include hf in
/-- A property of morphisms stable under base change passes from `Spec A₁ ⟶ Spec A` to
`Spec A₁[M₁] ⟶ Spec A[M]` as soon as `A₁[M₁] = A₁ ⊗_A A[M]`. -/
theorem squareZero_of_isPushout (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (h : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A₁ M₁.obj))
      (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ))))
    (hP : P (Spec.map (CommRingCat.ofHom f))) :
    P ((BigFppfOver.toScheme B S hS).map (tangentPullbackBase f hf ψ)) :=
  P.of_isPullback (isPullback_SpecMap_of_isPushout _ _ _ _ h) hP

variable {a b : A₁ →+* A₂} (hfa : Spec.map (CommRingCat.ofHom a) ≫ toS₁ = toS₂)
  (hfb : Spec.map (CommRingCat.ofHom b) ≫ toS₁ = toS₂) {M₂ : SiteModule A₂ B}
  (ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj)
  (ψb : M₁.obj ⟶ (ModuleCat.restrictScalars b).obj M₂.obj)

include hf hfa hfb in
/-- **The double overlap `Spec A₂[M₂] = Spec A₁[M₁] ×_{Spec A[M]} Spec A₁[M₁]`** in the site,
from the corresponding pushout of rings. -/
theorem isPullback_doubleOverlap_of_isPushout
    (h : IsPushout (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)))
      (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)))
      (CommRingCat.ofHom (squareZeroRingBaseMap a (restrictScalarsAddHom a ψa)
        (restrictScalarsAddHom_smul a ψa)))
      (CommRingCat.ofHom (squareZeroRingBaseMap b (restrictScalarsAddHom b ψb)
        (restrictScalarsAddHom_smul b ψb)))) :
    IsPullback (P := squareZeroOver A₂ B S hS toS₂ M₂)
      (X := squareZeroOver A₁ B S hS toS₁ M₁) (Y := squareZeroOver A₁ B S hS toS₁ M₁)
      (Z := squareZeroOver A B S hS toS M) (tangentPullbackBase a hfa ψa)
      (tangentPullbackBase b hfb ψb) (tangentPullbackBase f hf ψ) (tangentPullbackBase f hf ψ) :=
  BigFppfOver.isPullback_of_toScheme B S hS (isPullback_SpecMap_of_isPushout _ _ _ _ h)

include hf hfa in
/-- **The reduction of the double overlap, `Spec A₂ = Spec A ×_{Spec A[M]} Spec A₂[M₂]`**, in
the site, as soon as `A₂[M₂] = A₂ ⊗_A A[M]` through the composite maps. -/
theorem isPullback_squareZeroArrow_comp_of_isPushout
    (h : IsPushout (CommRingCat.ofHom f ≫ CommRingCat.ofHom a)
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom A₂ M₂.obj))
      (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)) ≫
        CommRingCat.ofHom (squareZeroRingBaseMap a (restrictScalarsAddHom a ψa)
        (restrictScalarsAddHom_smul a ψa)))) :
    IsPullback (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa ≫
        algebraOverMapOfRingHom f B S hS toS toS₁ hA hA₁ hf)
      (squareZeroArrow A₂ B S hS toS₂ hA₂ M₂) (squareZeroArrow A B S hS toS hA M)
      (tangentPullbackBase a hfa ψa ≫ tangentPullbackBase f hf ψ) := by
  apply BigFppfOver.isPullback_of_toScheme
  have h' := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_reduction_of_isPushout h
    (r := CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
    (r₁ := CommRingCat.ofHom (TrivSqZeroExt.fstHom A₂ A₂ M₂.obj).toRingHom)
    (CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)) (CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl))
    (CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)))
  rw [Spec.map_comp, Spec.map_comp] at h'
  rw [Functor.map_comp, Functor.map_comp]
  exact h'

end Site

/-! ### The base-changed coefficients `A₁ ⊗_A M` -/

section TensorCoeff

open TensorProduct

variable {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂] [Algebra A A₁]
  [Algebra A A₂] {B : BigFppfSite.{u}}

/-- The base change `A₁ ⊗_A M` of a site module along `A → A₁` is a site module as soon as
`Spec A₁` is in the site. -/
theorem isSiteModule_tensor (hA₁ : B.Contains (Spec (.of A₁))) (M : SiteModule A B) :
    IsSiteModule A₁ B (ModuleCat.of A₁ (A₁ ⊗[A] M.obj)) := by
  have h₁ : Cardinal.mk A₁ < B.cutoff := by
    have h : (Spec (.of A₁)).size < B.cutoff := hA₁
    rw [Scheme.size_Spec] at h
    exact lt_of_le_of_lt (le_max_right _ _) h
  have hM : Cardinal.mk (M.obj : Type u) < B.cutoff := by
    have h : (Spec (squareZeroRing A M.obj)).size < B.cutoff := M.property
    rw [Scheme.size_Spec] at h
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (le_max_right _ _) h)
    change Cardinal.mk (M.obj : Type u) ≤ Cardinal.mk (A × (M.obj : Type u))
    exact Cardinal.mk_le_of_injective (f := fun m : M.obj ↦ ((0 : A), m))
      (fun m n h ↦ (Prod.mk.inj h).2)
  have hT : Cardinal.mk (A₁ ⊗[A] M.obj) < B.cutoff := by
    refine lt_of_le_of_lt (AlgebraicGeometry.Stack.GroupoidLift.card_tensorProduct_le A A₁ M.obj)
      (max_lt B.aleph0_lt_cutoff ?_)
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact lt_of_le_of_lt (Cardinal.mul_le_max _ _)
      (max_lt (max_lt h₁ hM) B.aleph0_lt_cutoff)
  have hR : Cardinal.mk (squareZeroRing A₁ (ModuleCat.of A₁ (A₁ ⊗[A] M.obj))) < B.cutoff := by
    change Cardinal.mk (A₁ × (A₁ ⊗[A] M.obj)) < B.cutoff
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact lt_of_le_of_lt (Cardinal.mul_le_max _ _) (max_lt (max_lt h₁ hT) B.aleph0_lt_cutoff)
  change (Spec (squareZeroRing A₁ (ModuleCat.of A₁ (A₁ ⊗[A] M.obj)))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff hR

/-- The coefficient map `M → A₁ ⊗_A M`, `m ↦ 1 ⊗ m`, over `algebraMap A A₁`. -/
noncomputable def tensorCoeff (M : ModuleCat.{u} A) :
    M ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj (ModuleCat.of A₁ (A₁ ⊗[A] M)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap A A₁)).obj
      (ModuleCat.of A₁ (A₁ ⊗[A] M)))
    ({ toFun := fun m ↦ (1 : A₁) ⊗ₜ m
       map_add' := fun m m' ↦ TensorProduct.tmul_add _ _ _
       map_smul' := fun r m ↦ by
         change (1 : A₁) ⊗ₜ (r • m) = algebraMap A A₁ r • ((1 : A₁) ⊗ₜ[A] m)
         rw [TensorProduct.tmul_smul, algebraMap_smul] } :
      M →ₗ[A] (ModuleCat.restrictScalars (algebraMap A A₁)).obj (ModuleCat.of A₁ (A₁ ⊗[A] M)))

/-- `tensorCoeff` sends `m` to `1 ⊗ m`. -/
theorem tensorCoeff_apply (M : ModuleCat.{u} A) (m : M) :
    restrictScalarsAddHom (algebraMap A A₁) (tensorCoeff (A₁ := A₁) M) m = (1 : A₁) ⊗ₜ m := rfl

/-- The coefficient map `A₁ ⊗_A M → A₂ ⊗_A M`, `c ⊗ m ↦ g(c) ⊗ m`, over an `A`-algebra map
`g : A₁ → A₂`. -/
noncomputable def tensorCoeffMap (g : A₁ →ₐ[A] A₂) (M : ModuleCat.{u} A) :
    ModuleCat.of A₁ (A₁ ⊗[A] M) ⟶
      (ModuleCat.restrictScalars g.toRingHom).obj (ModuleCat.of A₂ (A₂ ⊗[A] M)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g.toRingHom).obj (ModuleCat.of A₂ (A₂ ⊗[A] M)))
    ({ toFun := fun t ↦ TensorProduct.map g.toLinearMap LinearMap.id t
       map_add' := fun t t' ↦ map_add _ t t'
       map_smul' := fun c t ↦ by
         change TensorProduct.map g.toLinearMap LinearMap.id (c • t) =
           g c • TensorProduct.map g.toLinearMap LinearMap.id t
         induction t using TensorProduct.inductionOn with
         | tmul c' m => rw [TensorProduct.smul_tmul', TensorProduct.map_tmul,
             TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
             AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_mul]
         | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add] } :
      ModuleCat.of A₁ (A₁ ⊗[A] M) →ₗ[A₁]
        (ModuleCat.restrictScalars g.toRingHom).obj (ModuleCat.of A₂ (A₂ ⊗[A] M)))

/-- `tensorCoeffMap g` sends `1 ⊗ m` to `1 ⊗ m`: it commutes with the coefficient maps
`tensorCoeff`. -/
theorem tensorCoeffMap_apply_tensorCoeff (g : A₁ →ₐ[A] A₂) (M : ModuleCat.{u} A) (m : M) :
    restrictScalarsAddHom g.toRingHom (tensorCoeffMap g M)
      (restrictScalarsAddHom (algebraMap A A₁) (tensorCoeff (A₁ := A₁) M) m) =
      (1 : A₂) ⊗ₜ m := by
  change TensorProduct.map g.toLinearMap LinearMap.id ((1 : A₁) ⊗ₜ m) = _
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

/-- **The coefficient maps are functorial.** For `A`-algebra maps with `g₂ ∘ g₁ = g₄ ∘ g₃`, the
composites `tensorCoeffMap g₂ ∘ tensorCoeffMap g₁` and `tensorCoeffMap g₄ ∘ tensorCoeffMap g₃`
agree. -/
theorem tensorCoeffMap_comp_apply {A₃ A₄ : Type u} [CommRing A₃] [CommRing A₄] [Algebra A A₃]
    [Algebra A A₄] (M : ModuleCat.{u} A) (g₁ : A₁ →ₐ[A] A₂) (g₂ : A₂ →ₐ[A] A₃)
    (g₃ : A₁ →ₐ[A] A₄) (g₄ : A₄ →ₐ[A] A₃) (h : g₂.comp g₁ = g₄.comp g₃) (t : A₁ ⊗[A] M) :
    (tensorCoeffMap g₂ M).hom ((tensorCoeffMap g₁ M).hom t) =
      (tensorCoeffMap g₄ M).hom ((tensorCoeffMap g₃ M).hom t) := by
  change TensorProduct.map g₂.toLinearMap LinearMap.id
      (TensorProduct.map g₁.toLinearMap LinearMap.id t) =
    TensorProduct.map g₄.toLinearMap LinearMap.id (TensorProduct.map g₃.toLinearMap LinearMap.id t)
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, ← AlgHom.comp_toLinearMap, ← AlgHom.comp_toLinearMap, h]

end TensorCoeff

/-! ### Exact rows of lift classes along an fppf cover `A → A₁` -/

section RowExact

open CategoryTheory.Limits TensorProduct AlgebraicGeometry.Stack
open AlgebraicGeometry.Stack.GroupoidLift

universe w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra A A₂]
  {a b : A₁ →+* A₂}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom a) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom b) ≫ toS₁ = toS₂}
  {x x₁ x₂ : 𝒳.val.obj}
  {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
  {hx₁ : 𝒳.val.p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : 𝒳.val.p.obj x₂ = algebraOver A₂ B S hS toS₂ hA₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : 𝒳.val.p.IsHomLift
    (algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {M : SiteModule A B} {M₁ : SiteModule A₁ B} {M₂ : SiteModule A₂ B}
  {ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj M₁.obj}
  {ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj}
  {ψb : M₁.obj ⟶ (ModuleCat.restrictScalars b).obj M₂.obj}

/-- The composite of the coefficient maps `M → M₁ → M₂` along `A → A₁ → A₂`, as a map over
`algebraMap A A₂`. -/
noncomputable def coeffCompOfEq (ha : a.comp (algebraMap A A₁) = algebraMap A A₂)
    (ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj M₁.obj)
    (ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj) :
    M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A A₂)).obj M₂.obj :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap A A₂)).obj M₂.obj)
    ({ toFun := fun m ↦ restrictScalarsAddHom a ψa (restrictScalarsAddHom _ ψ₀₁ m)
       map_add' := fun m m' ↦ by rw [map_add, map_add]; rfl
       map_smul' := fun r m ↦ by
         change _ = (algebraMap A A₂ r) • restrictScalarsAddHom a ψa (restrictScalarsAddHom _ ψ₀₁ m)
         rw [restrictScalarsAddHom_smul, restrictScalarsAddHom_smul, ← ha]
         rfl } : M.obj →ₗ[A] (ModuleCat.restrictScalars (algebraMap A A₂)).obj M₂.obj)

/-- `coeffCompOfEq` applies the two coefficient maps in turn. -/
theorem coeffCompOfEq_apply (ha : a.comp (algebraMap A A₁) = algebraMap A A₂)
    (ψ₀₁ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap A A₁)).obj M₁.obj)
    (ψa : M₁.obj ⟶ (ModuleCat.restrictScalars a).obj M₂.obj) (m : M.obj) :
    restrictScalarsAddHom (algebraMap A A₂) (coeffCompOfEq ha ψ₀₁ ψa) m =
      restrictScalarsAddHom a ψa (restrictScalarsAddHom _ ψ₀₁ m) := rfl

/-- **The rows of lift classes are exact along an fppf cover `A → A₁`**, for an algebraic stack
locally of finite presentation over `S`: if `Spec A₁ → Spec A` is flat, surjective and locally of
finite presentation, `A₂ = A₁ ⊗_A A₁` through `a`, `b`, and the coefficients are the base changes
`M₁ = A₁ ⊗_A M`, `M₂ = A₂ ⊗_A M`, then `F(A[M]) → F(A₁[M₁]) ⇉ F(A₂[M₂])` is exact. This is the
sheaf condition of Stacks 0DNS for the covering `A[M] → A₁[M₁]`, the input of the first paragraph
of the proof of Stacks 0DNT. -/
theorem liftClassRowExact_of_tensor (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hFl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hSu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hLp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap A A₁)) (CommRingCat.ofHom (algebraMap A A₁))
      (CommRingCat.ofHom b) (CommRingCat.ofHom a))
    (ha : a.comp (algebraMap A A₁) = algebraMap A A₂)
    (hb : b.comp (algebraMap A A₁) = algebraMap A A₂)
    (e₁ : A₁ ⊗[A] M.obj ≃+ M₁.obj)
    (he₁ : ∀ (c : A₁) (m : M.obj), e₁ (c ⊗ₜ m) = c • restrictScalarsAddHom _ ψ₀₁ m)
    (e₂ : A₂ ⊗[A] M.obj ≃+ M₂.obj)
    (he₂ : ∀ (c : A₂) (m : M.obj),
      e₂ (c ⊗ₜ m) = c • restrictScalarsAddHom a ψa (restrictScalarsAddHom _ ψ₀₁ m))
    (hψab : ∀ m : M.obj, restrictScalarsAddHom a ψa (restrictScalarsAddHom _ ψ₀₁ m) =
      restrictScalarsAddHom b ψb (restrictScalarsAddHom _ ψ₀₁ m))
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) :
    LiftClassRowExact 𝒳.isFiberedInGroupoids hφ₀₁ hα hβ ψ₀₁ ψa ψb (hx := hx) (hx₁ := hx₁)
      (hx₂ := hx₂) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (squareZeroOver A B S hS toS M)) :=
    inferInstanceAs (IsAffine (Spec _))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (squareZeroOver A₁ B S hS toS₁ M₁)) :=
    inferInstanceAs (IsAffine (Spec _))
  have P0f := isPushout_squareZero_of_addEquiv ψ₀₁ e₁ he₁
  have P02 := isPushout_squareZero_of_addEquiv (coeffCompOfEq ha ψ₀₁ ψa) e₂
    (fun c m ↦ (he₂ c m).trans (by rw [coeffCompOfEq_apply]))
  have key : ∀ (c : A₁ →+* A₂) (ψc : M₁.obj ⟶ (ModuleCat.restrictScalars c).obj M₂.obj)
      (hc : c.comp (algebraMap A A₁) = algebraMap A A₂),
      (∀ m, restrictScalarsAddHom c ψc (restrictScalarsAddHom _ ψ₀₁ m) =
        restrictScalarsAddHom (algebraMap A A₂) (coeffCompOfEq ha ψ₀₁ ψa) m) →
      CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom c =
          CommRingCat.ofHom (algebraMap A A₂) ∧
        CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₁)
            (restrictScalarsAddHom _ ψ₀₁) (restrictScalarsAddHom_smul _ ψ₀₁)) ≫
          CommRingCat.ofHom (squareZeroRingBaseMap c (restrictScalarsAddHom c ψc)
            (restrictScalarsAddHom_smul c ψc)) =
          CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₂)
            (restrictScalarsAddHom _ (coeffCompOfEq ha ψ₀₁ ψa))
            (restrictScalarsAddHom_smul _ (coeffCompOfEq ha ψ₀₁ ψa))) ∧
        IsPushout (CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom c)
          (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))
          (CommRingCat.ofHom (TrivSqZeroExt.inlHom A₂ M₂.obj))
          (CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₁)
              (restrictScalarsAddHom _ ψ₀₁) (restrictScalarsAddHom_smul _ ψ₀₁)) ≫
            CommRingCat.ofHom (squareZeroRingBaseMap c (restrictScalarsAddHom c ψc)
              (restrictScalarsAddHom_smul c ψc))) := by
    intro c ψc hc hm
    have hcc : CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom c =
        CommRingCat.ofHom (algebraMap A A₂) := by rw [← CommRingCat.ofHom_comp, hc]
    have hσ : CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₁)
          (restrictScalarsAddHom _ ψ₀₁) (restrictScalarsAddHom_smul _ ψ₀₁)) ≫
        CommRingCat.ofHom (squareZeroRingBaseMap c (restrictScalarsAddHom c ψc)
          (restrictScalarsAddHom_smul c ψc)) =
        CommRingCat.ofHom (squareZeroRingBaseMap (algebraMap A A₂)
          (restrictScalarsAddHom _ (coeffCompOfEq ha ψ₀₁ ψa))
          (restrictScalarsAddHom_smul _ (coeffCompOfEq ha ψ₀₁ ψa))) := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      exact RingHom.ext fun z ↦
        TrivSqZeroExt.ext (congrArg (· z.fst) (congrArg DFunLike.coe hc)) (hm z.snd)
    exact ⟨hcc, hσ, by rw [hcc, hσ]; exact P02⟩
  have inl_comp : ∀ (c : A₁ →+* A₂) (ψc : M₁.obj ⟶ (ModuleCat.restrictScalars c).obj M₂.obj),
      CommRingCat.ofHom (TrivSqZeroExt.inlHom A₁ M₁.obj) ≫ CommRingCat.ofHom
        (squareZeroRingBaseMap c (restrictScalarsAddHom c ψc) (restrictScalarsAddHom_smul c ψc)) =
      CommRingCat.ofHom c ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom A₂ M₂.obj) := fun c ψc ↦
    CommRingCat.hom_ext (RingHom.ext fun _ ↦ TrivSqZeroExt.ext rfl (map_zero _))
  obtain ⟨hcA, hσA, Pa⟩ := key a ψa ha fun _ ↦ rfl
  obtain ⟨hcB, hσB, Pb⟩ := key b ψb hb fun m ↦
    (hψab m).symm.trans (coeffCompOfEq_apply ha ψ₀₁ ψa m).symm
  have P0b := IsPushout.of_left Pb (inl_comp b ψb).symm P0f
  have hD := isPushout_doubleOverlap P0f hpush P0b (inl_comp a ψa) (hσA.trans hσB.symm)
  have hab : algebraOverMapOfRingHom b B S hS toS₁ toS₂ hA₁ hA₂ hfb ≫
      algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁ =
      algebraOverMapOfRingHom a B S hS toS₁ toS₂ hA₁ hA₂ hfa ≫
      algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, hcA, hcB]
  exact liftClassRowExact_of_cover h𝒳 f hf
    (isDeformationSituation_squareZeroArrow A hS toS hA M)
    (isDeformationSituation_squareZeroArrow A₁ hS toS₁ hA₁ M₁)
    (isPullback_squareZeroArrow_of_isPushout hf₀₁ ψ₀₁ P0f)
    (squareZero_of_isPushout hf₀₁ ψ₀₁ @Flat P0f hFl)
    (squareZero_of_isPushout hf₀₁ ψ₀₁ @Surjective P0f hSu)
    (squareZero_of_isPushout hf₀₁ ψ₀₁ @LocallyOfFinitePresentation P0f hLp)
    (isPullback_doubleOverlap_of_isPushout hf₀₁ ψ₀₁ hfa hfb ψa ψb hD)
    (isPullback_squareZeroArrow_comp_of_isPushout hf₀₁ ψ₀₁ hfa ψa Pa) hab hγ

end RowExact

section RowExactTensor

open CategoryTheory.Limits TensorProduct AlgebraicGeometry.Stack
open AlgebraicGeometry.Stack.GroupoidLift

universe w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A A₁ A₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra A A₂]
  {a b : A₁ →ₐ[A] A₂}
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of A₂) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of A₂))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ toS₁ = toS₂}
  {x x₁ x₂ : 𝒳.val.obj}
  {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
  {hx₁ : 𝒳.val.p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : 𝒳.val.p.obj x₂ = algebraOver A₂ B S hS toS₂ hA₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : 𝒳.val.p.IsHomLift
    (algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom a.toRingHom B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom b.toRingHom B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {M : SiteModule A B}

/-- **The rows of lift classes are exact along an fppf cover `A → A₁`, with the coefficients
`A₁ ⊗_A M` and `A₂ ⊗_A M`**, where `A₂` is the pushout `A₁ ⊗_A A₁` through `A`-algebra maps
`a`, `b`. This is the form in which the first paragraph of the proof of Stacks 0DNT uses the
sheaf property of Stacks 0DNS. -/
theorem liftClassRowExact_of_tensorProduct (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hFl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hSu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hLp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap A A₁)) (CommRingCat.ofHom (algebraMap A A₁))
      (CommRingCat.ofHom b.toRingHom) (CommRingCat.ofHom a.toRingHom))
    (hM₁ : IsSiteModule A₁ B (ModuleCat.of A₁ (A₁ ⊗[A] M.obj)))
    (hM₂ : IsSiteModule A₂ B (ModuleCat.of A₂ (A₂ ⊗[A] M.obj)))
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) :
    LiftClassRowExact 𝒳.isFiberedInGroupoids hφ₀₁ hα hβ (M₁ := ⟨_, hM₁⟩) (M₂ := ⟨_, hM₂⟩)
      (tensorCoeff M.obj) (tensorCoeffMap a M.obj) (tensorCoeffMap b M.obj) (hx := hx)
      (hx₁ := hx₁) (hx₂ := hx₂) :=
  liftClassRowExact_of_tensor h𝒳 f hf hFl hSu hLp hpush a.comp_algebraMap b.comp_algebraMap
    (AddEquiv.refl _) (fun c m ↦ by
      change c ⊗ₜ m = c • ((1 : A₁) ⊗ₜ[A] m)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (AddEquiv.refl _) (fun c m ↦ by
      change c ⊗ₜ m = c • restrictScalarsAddHom a.toRingHom (tensorCoeffMap a M.obj)
        (restrictScalarsAddHom (algebraMap A A₁) (tensorCoeff (A₁ := A₁) M.obj) m)
      rw [tensorCoeffMap_apply_tensorCoeff, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (fun m ↦ by rw [tensorCoeffMap_apply_tensorCoeff, tensorCoeffMap_apply_tensorCoeff]) hγ

end RowExactTensor

end Deformation.Artin

end
