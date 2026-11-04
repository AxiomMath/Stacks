module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupCanDualSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DottedArrow

/-!
# The `DottedArrowSituation` of Tag 0GAD on the blowup

Let `p : X → Spec(A)` be the blowup of a Noetherian ring `A` in `I` and `n = m + 1`. This file
builds `Stacks.LocalCohomology.UniformityIII.DottedArrowSituation`, the data of the dotted-arrow
argument of [Stacks, Tag 0GAD], on top of the `CanDualSituation` of the blowup
(`blowupCanDualSituation`), every field being the honest geometric object:

* `H¹` of the twists of `(p^*M)^∨` and of the image of `can`, and `H²` of the twists of its
  kernel; the factorizations of the twisting maps that Tag 0GA9 gives for them, the cokernel and
  the kernel of `can` being killed by `I^c` (Remark 0GAB);
* for a map `u : M ⟶ M'` of `(A, n, c)`-modules, the dual `D_u = (p^*u)^∨ = blowupDualMap`, the
  sections of the twists of its image and cokernel, and, for `M → M' → M'' → 0` exact, the
  connecting map of `0 → (p^*M'')^∨ → (p^*M')^∨ → im(D_u) → 0`: `D_v` is a kernel of `D_u`
  (`isLimitBlowupDualMap`), because a map into a dual is determined by, and can be built from,
  its evaluations at the sections `p^*z` (`blowupDual_hom_ext`, `blowupDualLift`);
* the cokernel of `D_u` is killed by `a` whenever multiplication by `a` on `M` factors through
  `u`, since then `D_h ≫ D_u = D_{a • 𝟙} = a` (`globalSmulCenter_app_cokernel_blowupDualMap`).

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupDottedArrowSituation`, and
  `blowupDottedArrowSituationQS` at `q₀ = q(S)`, `d = d(S)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The kernel and the cokernel of `D_u` -/

section DualMap

variable (n : ℕ)

/-- `D_0 = 0`. -/
theorem blowupDualMap_zero (N N' : ModuleCat.{u} (A ⧸ I ^ n)) :
    blowupDualMap I n (0 : N ⟶ N') = 0 := by
  simpa using blowupDualMap_add I n (0 : N ⟶ N') 0

/-- `D_v ≫ D_u = 0` when `u ≫ v = 0`. -/
theorem blowupDualMap_comp_eq_zero {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N')
    (v : N' ⟶ N'') (w : u ≫ v = 0) : blowupDualMap I n v ≫ blowupDualMap I n u = 0 := by
  rw [← blowupDualMap_comp, w, blowupDualMap_zero]

/-- On the sections `p^*z`, a map into `(p^*M')^∨` killed by `D_u` evaluates equally at two
points with the same image under `v`, when `M --u--> M' --v--> M''` is exact. -/
theorem comp_blowupDualEval_eq_of_exact {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N')
    (v : N' ⟶ N'') (hex : Function.Exact u.hom v.hom) {E : (blowupScheme I).Modules}
    (k : E ⟶ blowupDual I n N') (hk : k ≫ blowupDualMap I n u = 0)
    {z₁ z₂ : resModule I n N'} (hz : resMap I n v z₁ = resMap I n v z₂) :
    k ≫ blowupDualEval I n N' z₁ = k ≫ blowupDualEval I n N' z₂ := by
  have hz' : resMap I n v (z₁ - z₂) = 0 := by rw [map_sub, hz, sub_self]
  obtain ⟨w, hw⟩ := (hex (z₁ - z₂)).1 hz'
  have h₁ : z₁ = z₂ + resMap I n u w := eq_add_of_sub_eq' hw.symm
  calc k ≫ blowupDualEval I n N' z₁ = k ≫ blowupDualEval I n N' (z₂ + resMap I n u w) := by
        rw [← h₁]
    _ = k ≫ blowupDualEval I n N' z₂ + k ≫ (blowupDualMap I n u ≫ blowupDualEval I n N w) := by
        rw [blowupDualEval_add, Preadditive.comp_add]
        exact congrArg (fun x => k ≫ blowupDualEval I n N' z₂ + k ≫ x)
          (blowupDualMap_comp_blowupDualEval I n u w).symm
    _ = k ≫ blowupDualEval I n N' z₂ := by
        rw [← Category.assoc, hk, zero_comp, add_zero]

/-- A chosen preimage under a surjection `v`, read in the underlying `A`-modules. -/
def surjPreimage {N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} {v : N' ⟶ N''}
    (hv : Function.Surjective v.hom) (z : resModule I n N'') : resModule I n N' :=
  (hv z).choose

/-- The map `v` sends `surjPreimage I n hv z` to `z`. -/
theorem resMap_surjPreimage {N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} {v : N' ⟶ N''}
    (hv : Function.Surjective v.hom) (z : resModule I n N'') :
    resMap I n v (surjPreimage I n hv z) = z :=
  (hv z).choose_spec

/-- **`D_v` is a kernel of `D_u`** for `M --u--> M' --v--> M'' → 0` exact: a map `k` into
`(p^*M')^∨` killed by `D_u` has evaluations at the points of `M'` which only depend on their
images in `M''`, and the map into `(p^*M'')^∨` with these evaluations (`blowupDualLift`) is the
unique factorization of `k` through `D_v`. -/
def isLimitBlowupDualMap {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N') (v : N' ⟶ N'')
    (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom) :
    IsLimit (KernelFork.ofι (blowupDualMap I n v) (blowupDualMap_comp_eq_zero I n u v
      (ModuleCat.hom_ext (LinearMap.ext fun x => hex.apply_apply_eq_zero x)))) := by
  let lift : ∀ {E : (blowupScheme I).Modules} (k : E ⟶ blowupDual I n N'),
      k ≫ blowupDualMap I n u = 0 → (E ⟶ blowupDual I n N'') := fun {E} k hk =>
    blowupDualLift I n (fun z => k ≫ blowupDualEval I n N' (surjPreimage I n hv z))
      (fun z z' => by
        refine (comp_blowupDualEval_eq_of_exact I n u v hex k hk
          (z₂ := surjPreimage I n hv z + surjPreimage I n hv z') ?_).trans ?_
        · rw [map_add, resMap_surjPreimage, resMap_surjPreimage, resMap_surjPreimage]
        · rw [blowupDualEval_add, Preadditive.comp_add])
      (fun a z => by
        refine (comp_blowupDualEval_eq_of_exact I n u v hex k hk
          (z₂ := a • surjPreimage I n hv z) ?_).trans ?_
        · rw [map_smul, resMap_surjPreimage, resMap_surjPreimage]
        · calc k ≫ blowupDualEval I n N' (a • surjPreimage I n hv z)
              = k ≫ (blowupDualEval I n N' (surjPreimage I n hv z) ≫
                  (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
                    (thickeningSheaf I n)) := by rw [blowupDualEval_smul]
            _ = k ≫ ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
                  (blowupDual I n N') ≫ blowupDualEval I n N' (surjPreimage I n hv z)) :=
                congrArg (k ≫ ·) ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
                  (blowupDualEval I n N' (surjPreimage I n hv z)))
            _ = (k ≫ (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
                  (blowupDual I n N')) ≫ blowupDualEval I n N' (surjPreimage I n hv z) :=
                (Category.assoc _ _ _).symm
            _ = ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E ≫ k) ≫
                  blowupDualEval I n N' (surjPreimage I n hv z) :=
                congrArg (· ≫ blowupDualEval I n N' (surjPreimage I n hv z))
                  ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality k)
            _ = _ := Category.assoc _ _ _)
  have hlift : ∀ {E : (blowupScheme I).Modules} (k : E ⟶ blowupDual I n N')
      (hk : k ≫ blowupDualMap I n u = 0) (z : resModule I n N'),
      lift k hk ≫ blowupDualEval I n N'' (resMap I n v z) = k ≫ blowupDualEval I n N' z :=
    fun k hk z => (blowupDualLift_comp_blowupDualEval I n _ _ _ (resMap I n v z)).trans
      (comp_blowupDualEval_eq_of_exact I n u v hex k hk (resMap_surjPreimage I n hv _))
  refine KernelFork.IsLimit.ofι _ _ (fun k hk => lift k hk) (fun {E} k hk => ?_)
    (fun {E} k hk m hm => ?_)
  · refine blowupDual_hom_ext I n fun z => ?_
    rw [Category.assoc]
    exact (congrArg (lift k hk ≫ ·) (blowupDualMap_comp_blowupDualEval I n v z)).trans
      (hlift k hk z)
  · refine blowupDual_hom_ext I n fun z => ?_
    rw [← resMap_surjPreimage I n hv z, hlift k hk, ← hm, Category.assoc]
    exact congrArg (m ≫ ·) (blowupDualMap_comp_blowupDualEval I n v _).symm

/-- `D_v` is a monomorphism when `v` is surjective and `M → M' → M'' → 0` is exact. -/
theorem mono_blowupDualMap {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N') (v : N' ⟶ N'')
    (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom) :
    Mono (blowupDualMap I n v) :=
  mono_of_isLimit_fork (isLimitBlowupDualMap I n u v hex hv)

/-- `D_v ≫` (the projection of `(p^*M')^∨` onto the image of `D_u`) is zero. -/
theorem blowupDualMap_comp_factorThruImage {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N')
    (v : N' ⟶ N'') (w : u ≫ v = 0) :
    blowupDualMap I n v ≫ Abelian.factorThruImage (blowupDualMap I n u) = 0 := by
  refine (cancel_mono (Abelian.image.ι (blowupDualMap I n u))).1 ?_
  rw [Category.assoc, Abelian.image.fac, zero_comp]
  exact blowupDualMap_comp_eq_zero I n u v w

/-- **`0 → (p^*M'')^∨ → (p^*M')^∨ → im(D_u) → 0` is short exact** for `M → M' → M'' → 0`
exact. -/
theorem shortExact_blowupDualMap {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N')
    (v : N' ⟶ N'') (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom) :
    (ShortComplex.mk (blowupDualMap I n v) (Abelian.factorThruImage (blowupDualMap I n u))
      (blowupDualMap_comp_factorThruImage I n u v
        (ModuleCat.hom_ext (LinearMap.ext fun x => hex.apply_apply_eq_zero x)))).ShortExact := by
  have hlim := isLimitBlowupDualMap I n u v hex hv
  have := mono_blowupDualMap I n u v hex hv
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ ?_) inferInstance
    inferInstance
  refine KernelFork.IsLimit.ofι _ _
    (fun k hk => hlim.lift (KernelFork.ofι k (by
      rw [← Abelian.image.fac (blowupDualMap I n u), ← Category.assoc, hk, zero_comp])))
    (fun k hk => Fork.IsLimit.lift_ι hlim) (fun k hk m hm => ?_)
  refine Fork.IsLimit.hom_ext hlim ?_
  rwa [Fork.IsLimit.lift_ι hlim]

/-- **The cokernel of `D_u` is killed by `a`** when multiplication by `a` on `M` factors as
`u ≫ h`: multiplication by `a` on `(p^*M)^∨` is `D_{u ≫ h} = D_h ≫ D_u`. -/
theorem globalSmulCenter_app_cokernel_blowupDualMap {N N' : ModuleCat.{u} (A ⧸ I ^ n)}
    (u : N ⟶ N') (a : A) (h : N' ⟶ N) (hh : u ≫ h = Ideal.Quotient.mk (I ^ n) a • 𝟙 N) :
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
      (cokernel (blowupDualMap I n u)) = 0 := by
  have hq : (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupDual I n N) =
      blowupDualMap I n h ≫ blowupDualMap I n u := by
    rw [← blowupDualMap_comp, hh, blowupDualMap_smul_id]
  rw [← cancel_epi (cokernel.π (blowupDualMap I n u)), comp_zero]
  refine ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (cokernel.π (blowupDualMap I n u))).trans ?_
  show (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupDual I n N) ≫ _ = 0
  rw [hq, Category.assoc, cokernel.condition, comp_zero]

/-- **Tag 0GA9 for the cokernel of `D_u`** on sections: when multiplication by every `a ∈ I^c`
on `M` factors through `u`, the cokernel is killed by `I^c`, so its twisting map
`coker(D_u)(q) ⟶ coker(D_u)(e)` is zero on `H⁰` for `e + c = q`. -/
theorem blowupHmodMap_cokernel_blowupDualMap_twistLE_eq_zero {c : ℕ}
    {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N')
    (hfac : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c), ∃ h : N' ⟶ N, u ≫ h = a • 𝟙 N)
    (q e : ℕ) (he : e ≤ q) (hec : e + c = q) :
    blowupHmodMap I 0 (cokernel (blowupDualMap I n u) ◁ blowupTwistLE I (Nat.cast_le.2 he)) =
      0 := by
  refine blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero I 0 _ (fun a ha => ?_) _
    (by rw [← hec]; push_cast; exact le_refl _)
  obtain ⟨h', hh'⟩ := hfac _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ n)) ha)
  exact globalSmulCenter_app_cokernel_blowupDualMap I n u a h' hh'

end DualMap

variable [IsNoetherianRing A]

/-! ### The factorizations of the twisting maps through the image of `can` -/

section Can

variable {m c : ℕ} (M : ANCModule I (m + 1) c)

/-- **`(p^*M)^∨(q) → (p^*M)^∨(e)` factors through `im(can)(e)`** for `e + c = q`: its composite
with the projection onto `coker(can)(e)` is the twisting map of `coker(can)`, which vanishes
(Tag 0GA9, the cokernel being killed by `I^c`). -/
def dualToImageTwist (q e : ℕ) (he : e + c = q) :
    blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q ⟶
      Abelian.image (blowupCanM I M) ⊗ blowupTwistInt I e :=
  (shortExact_twist_image I (blowupCanM I M) e).fIsKernel.lift
    (KernelFork.ofι (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (by omega : (e : ℤ) ≤ q)) (by
      change _ ≫ (cokernel.π (blowupCanM I M) ▷ blowupTwistInt I e) = 0
      refine (whisker_exchange _ _).trans ((congrArg (_ ≫ ·)
        (whiskerLeft_blowupTwistLE_eq_zero I (cokernel (blowupCanM I M))
          (fun _ ha => globalSmulCenter_app_cokernel_blowupCan M.2 ha) _ ?_)).trans comp_zero)
      omega))

/-- `dualToImageTwist` followed by the inclusion of `im(can)(e)` into `(p^*M)^∨(e)` is the
twisting map `(p^*M)^∨(q) → (p^*M)^∨(e)`. -/
theorem dualToImageTwist_comp (q e : ℕ) (he : e + c = q) :
    dualToImageTwist I M q e he ≫ (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I e) =
      blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (by omega : (e : ℤ) ≤ q) :=
  Fork.IsLimit.lift_ι _

/-- **`im(can)(q) → im(can)(e)` factors through `p^*(M^∨)(e)`** for `e + c = q`: the twisting
map of `p^*(M^∨)` kills `ker(can)(q)`, the kernel being killed by `I^c` (Tag 0GA9), so it
descends to the image. -/
def imageToPullbackTwist (q e : ℕ) (he : e + c = q) :
    Abelian.image (blowupCanM I M) ⊗ blowupTwistInt I q ⟶
      (thickeningPullback I (m + 1)).obj M.dual.1 ⊗ blowupTwistInt I e :=
  (shortExact_twist_kernel I (blowupCanM I M) q).gIsCokernel.desc
    (CokernelCofork.ofπ ((thickeningPullback I (m + 1)).obj M.dual.1 ◁
      blowupTwistLE I (by omega : (e : ℤ) ≤ q)) (by
      change (kernel.ι (blowupCanM I M) ▷ blowupTwistInt I q) ≫ _ = 0
      refine (whisker_exchange _ _).symm.trans ((congrArg (· ≫ _)
        (whiskerLeft_blowupTwistLE_eq_zero I (kernel (blowupCanM I M))
          (fun _ ha => globalSmulCenter_app_kernel_blowupCan M.2 ha) _ ?_)).trans zero_comp)
      omega))

/-- The projection of `p^*(M^∨)(q)` onto `im(can)(q)` followed by `imageToPullbackTwist` is the
twisting map `p^*(M^∨)(q) → p^*(M^∨)(e)`. -/
theorem factorThruImage_comp_imageToPullbackTwist (q e : ℕ) (he : e + c = q) :
    (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q) ≫
        imageToPullbackTwist I M q e he =
      (thickeningPullback I (m + 1)).obj M.dual.1 ◁ blowupTwistLE I (by omega : (e : ℤ) ≤ q) :=
  (shortExact_twist_kernel I (blowupCanM I M) q).gIsCokernel.fac _ WalkingParallelPair.one

/-- `imageToPullbackTwist` followed by the projection of `p^*(M^∨)(e)` onto `im(can)(e)` is the
twisting map `im(can)(q) → im(can)(e)`. -/
theorem imageToPullbackTwist_comp (q e : ℕ) (he : e + c = q) :
    imageToPullbackTwist I M q e he ≫
        (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I e) =
      Abelian.image (blowupCanM I M) ◁ blowupTwistLE I (by omega : (e : ℤ) ≤ q) := by
  have := (shortExact_twist_kernel I (blowupCanM I M) q).epi_g
  rw [← cancel_epi (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q),
    ← Category.assoc, factorThruImage_comp_imageToPullbackTwist, whisker_exchange]

end Can

/-! ### The connecting map of the dual of a right exact sequence, twisted -/

section Connecting

variable (n : ℕ) {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)} (u : N ⟶ N') (v : N' ⟶ N'')
  (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom)

include hv

/-- The twisted short exact sequence `0 → (p^*M'')^∨(t) → (p^*M')^∨(t) → im(D_u)(t) → 0`. -/
theorem shortExact_blowupDualMap_twist (t : ℤ) :
    (ShortComplex.mk (blowupDualMap I n v ▷ blowupTwistInt I t)
      (Abelian.factorThruImage (blowupDualMap I n u) ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (blowupDualMap_comp_factorThruImage I n u v
        (ModuleCat.hom_ext (LinearMap.ext fun x => hex.apply_apply_eq_zero x))) _)).ShortExact :=
  shortExact_whiskerRight_blowupTwistInt I _ _ _ (shortExact_blowupDualMap I n u v hex hv) t

/-- The twisting maps, as a morphism from the twist by `t` to the twist by `t'` of that
sequence. -/
def blowupDualMapTwistSeqMap {t t' : ℤ} (h : t' ≤ t) :
    ShortComplex.mk (blowupDualMap I n v ▷ blowupTwistInt I t)
        (Abelian.factorThruImage (blowupDualMap I n u) ▷ blowupTwistInt I t)
        (whiskerRight_comp_whiskerRight_eq_zero I _ _ (blowupDualMap_comp_factorThruImage I n u v
          (ModuleCat.hom_ext (LinearMap.ext fun x => hex.apply_apply_eq_zero x))) _) ⟶
      ShortComplex.mk (blowupDualMap I n v ▷ blowupTwistInt I t')
        (Abelian.factorThruImage (blowupDualMap I n u) ▷ blowupTwistInt I t')
        (whiskerRight_comp_whiskerRight_eq_zero I _ _ (blowupDualMap_comp_factorThruImage I n u v
          (ModuleCat.hom_ext (LinearMap.ext fun x => hex.apply_apply_eq_zero x))) _) where
  τ₁ := blowupDual I n N'' ◁ blowupTwistLE I h
  τ₂ := blowupDual I n N' ◁ blowupTwistLE I h
  τ₃ := Abelian.image (blowupDualMap I n u) ◁ blowupTwistLE I h
  comm₁₂ := whisker_exchange _ _
  comm₂₃ := whisker_exchange _ _

/-- The connecting map of the twisted dual sequence is natural in the twist. -/
theorem blowupDualMap_δ_naturality {t t' : ℤ} (h : t' ≤ t)
    (x : blowupHmod I 0 (Abelian.image (blowupDualMap I n u) ⊗ blowupTwistInt I t)) :
    (blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I n u v hex hv t') 0
        (blowupHmodMap I 0 (Abelian.image (blowupDualMap I n u) ◁ blowupTwistLE I h) x) =
      blowupHmodMap I 1 (blowupDual I n N'' ◁ blowupTwistLE I h)
        ((blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I n u v hex hv t) 0 x) :=
  ConcreteCategory.congr_hom ((blowupDeltaMod I).δ_naturality
    (shortExact_blowupDualMap_twist I n u v hex hv t)
    (shortExact_blowupDualMap_twist I n u v hex hv t') (blowupDualMapTwistSeqMap I n u v hex h)
    0) x

/-- The long exact sequence of the twisted dual sequence at `H⁰(X, im(D_u)(q))`. -/
theorem exact_blowupDualMap_δ (q : ℕ) :
    Function.Exact (blowupHmodMap I 0
        (Abelian.factorThruImage (blowupDualMap I n u) ▷ blowupTwistInt I q)).hom
      ((blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I n u v hex hv q) 0).hom :=
  exact_blowupHmodMap_δ I _ _ _ (shortExact_blowupDualMap_twist I n u v hex hv q) 0

/-- The naturality of the connecting map, at natural-number twists. -/
theorem blowupDualMap_δ_naturality_nat {q q' : ℕ} (hq : q' ≤ q)
    (x : blowupHmod I 0 (Abelian.image (blowupDualMap I n u) ⊗ blowupTwistInt I q)) :
    ((blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I n u v hex hv q') 0).hom
        ((blowupHmodMap I 0 (Abelian.image (blowupDualMap I n u) ◁
          blowupTwistLE I (Nat.cast_le.2 hq))).hom x) =
      (blowupHmodMap I 1 (blowupDual I n N'' ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
        (((blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I n u v hex hv q) 0).hom x) :=
  blowupDualMap_δ_naturality I n u v hex hv (Nat.cast_le.2 hq) x

end Connecting

/-! ### The remaining fields, as standalone statements -/

section Fields

variable {m c : ℕ}

/-- `H¹(X, (p^*M)^∨(q)) = 0` when `d(S) = 0`, the dual being quasi-coherent. -/
theorem subsingleton_blowupHmod_one_blowupDual (M : ANCModule I (m + 1) c) (q : ℕ)
    (hd : fibreDim I < 1) :
    Subsingleton (blowupHmod I 1 (blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q)) := by
  have := finitePresentation_resModule I M
  have := isQuasicoherent_blowupDual I (m + 1) M.1
  exact subsingleton_blowupHmod_of_fibreDim_lt I _ hd

/-- `H²(X, ker(can)(q)) = 0` when `d(S) ≤ 1`. -/
theorem subsingleton_blowupHmod_two_kernel_blowupCan (M : ANCModule I (m + 1) c) (q : ℕ)
    (hd : fibreDim I < 2) :
    Subsingleton (blowupHmod I 2 (kernel (blowupCanM I M) ⊗ blowupTwistInt I q)) := by
  have := finitePresentation_resModule I M
  have := isQuasicoherent_blowupDual I (m + 1) M.1
  exact subsingleton_blowupHmod_twist_kernel I (blowupCanM I M) q hd

/-- The twisting map on the sections of `coker(D_u)` vanishes after `c` steps, as a linear map. -/
theorem blowupHmodMap_cokernel_blowupDualMap_hom_eq_zero {M M' : ANCModule I (m + 1) c}
    (u : M.1 ⟶ M'.1)
    (hfac : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ (m + 1))) (I ^ c),
      ∃ h : M'.1 ⟶ M.1, u ≫ h = a • 𝟙 M.1)
    (q e : ℕ) (he : e ≤ q) (hec : e + c = q) :
    (blowupHmodMap I 0 (cokernel (blowupDualMap I (m + 1) u) ◁
      blowupTwistLE I (Nat.cast_le.2 he))).hom = 0 := by
  rw [blowupHmodMap_cokernel_blowupDualMap_twistLE_eq_zero I (m + 1) u hfac q e he hec]
  rfl

/-- Evaluating `D_u(τ)` against `z ∈ M` is evaluating `τ` against `u(z)`, on sections. -/
theorem blowupEvDual_imgDToDual_dualToImgD {q₀ : ℕ} (h : IsBaseThreshold I q₀)
    {M M' : ANCModule I (m + 1) c} (u : M.1 ⟶ M'.1) (q : ℕ) (hq : q₀ ≤ q)
    (τ : blowupHmod I 0 (blowupDual I (m + 1) M'.1 ⊗ blowupTwistInt I q)) :
    blowupEvDual I m h hq M.1
        ((blowupHmodMap I 0
          (Abelian.image.ι (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom
          ((blowupHmodMap I 0
            (Abelian.factorThruImage (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom τ)) =
      (blowupEvDual I m h hq M'.1 τ).comp (resMap I (m + 1) u) := by
  refine LinearMap.ext fun z => ?_
  show blowupEvDual I m h hq M.1 _ z = blowupEvDual I m h hq M'.1 τ (resMap I (m + 1) u z)
  have key : (Abelian.factorThruImage (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q) ≫
      (Abelian.image.ι (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q) ≫
        (blowupDualEval I (m + 1) M.1 z ▷ blowupTwistInt I q) =
      blowupDualEval I (m + 1) M'.1 (resMap I (m + 1) u z) ▷ blowupTwistInt I q := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, ← Category.assoc, Abelian.image.fac,
      blowupDualMap_comp_blowupDualEval]
    rfl
  rw [blowupEvDual_apply, blowupEvDual_apply, ← key, blowupHmodMap_comp_apply,
    blowupHmodMap_comp_apply]

/-- The inclusion of the twisted image of `D_u` is natural in the twist. -/
theorem blowupDualMap_imgDToDual_HimgDtr {M M' : ANCModule I (m + 1) c} (u : M.1 ⟶ M'.1)
    (q q' : ℕ) (hq : q' ≤ q)
    (t : blowupHmod I 0 (Abelian.image (blowupDualMap I (m + 1) u) ⊗ blowupTwistInt I q)) :
    (blowupHmodMap I 0 (Abelian.image.ι (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q')).hom
        ((blowupHmodMap I 0 (Abelian.image (blowupDualMap I (m + 1) u) ◁
          blowupTwistLE I (Nat.cast_le.2 hq))).hom t) =
      (blowupHmodMap I 0 (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
        ((blowupHmodMap I 0
          (Abelian.image.ι (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom t) :=
  (blowupHmodMap_whiskerRight_whiskerLeft_apply I 0 (Abelian.image.ι (blowupDualMap I (m + 1) u))
    (Nat.cast_le.2 hq) t).symm

/-- The projection onto the twisted cokernel of `D_u` is natural in the twist. -/
theorem blowupDualMap_dualToCokerD_Hdualtr {M M' : ANCModule I (m + 1) c} (u : M.1 ⟶ M'.1)
    (q q' : ℕ) (hq : q' ≤ q)
    (σ : blowupHmod I 0 (blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q)) :
    (blowupHmodMap I 0 (cokernel.π (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q')).hom
        ((blowupHmodMap I 0 (blowupDual I (m + 1) M.1 ◁
          blowupTwistLE I (Nat.cast_le.2 hq))).hom σ) =
      (blowupHmodMap I 0 (cokernel (blowupDualMap I (m + 1) u) ◁
          blowupTwistLE I (Nat.cast_le.2 hq))).hom
        ((blowupHmodMap I 0
          (cokernel.π (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom σ) :=
  (blowupHmodMap_whiskerRight_whiskerLeft_apply I 0 (cokernel.π (blowupDualMap I (m + 1) u))
    (Nat.cast_le.2 hq) σ).symm

end Fields

/-! ### The `DottedArrowSituation` -/

/-- **The `DottedArrowSituation` of Tag 0GAD on the blowup**, for `n = m + 1` and any threshold
`q₀` with the defining property of `q(S)`, extending `blowupCanDualSituation`. -/
def blowupDottedArrowSituation (m c : ℕ) (hcn : c ≤ m + 1) {q₀ : ℕ}
    (h : IsBaseThreshold I q₀) : DottedArrowSituation A I (m + 1) c where
  toCanDualSituation := blowupCanDualSituation I m c hcn h
  Hdual₁ M q := blowupHmod I 1 (blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q)
  Hdual₁tr M _ _ hq :=
    (blowupHmodMap I 1 (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  Hdual₁tr_trans M _ _ _ hq hq' x :=
    blowupHmodMap_whiskerLeft_blowupTwistLE_trans _ 1 _ _ _ x
  Himg₁ M q := blowupHmod I 1 (Abelian.image (blowupCanM I M) ⊗ blowupTwistInt I q)
  Himg₁tr M _ _ hq :=
    (blowupHmodMap I 1 (Abelian.image (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  Himg₁tr_trans M _ _ _ hq hq' x :=
    blowupHmodMap_whiskerLeft_blowupTwistLE_trans _ 1 _ _ _ x
  Hker₂ M q := blowupHmod I 2 (kernel (blowupCanM I M) ⊗ blowupTwistInt I q)
  img₁ToDual₁ M q :=
    (blowupHmodMap I 1 (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q)).hom
  img₁ToDual₁_Himg₁tr M q q' hq x :=
    (blowupHmodMap_whiskerRight_whiskerLeft_apply I 1 (Abelian.image.ι (blowupCanM I M))
      (Nat.cast_le.2 hq) x).symm
  dual₁ToImg₁ M q e he := (blowupHmodMap I 1 (dualToImageTwist I M q e he)).hom
  img₁ToDual₁_dual₁ToImg₁ M q e he x :=
    (blowupHmodMap_comp_apply I 1 _ _ x).symm.trans
      (congrArg (fun φ => blowupHmodMap I 1 φ x) (dualToImageTwist_comp I M q e he))
  canToImg₁ M q :=
    (blowupHmodMap I 1 (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q)).hom
  canToImg₁_Htr M q q' hq hq' x :=
    blowupHmodMap_whiskerRight_whiskerLeft_apply I 1 (Abelian.factorThruImage (blowupCanM I M))
      hq' x
  img₁ToPullback₁ M q e he := (blowupHmodMap I 1 (imageToPullbackTwist I M q e he)).hom
  canToImg₁_img₁ToPullback₁ M q e he x :=
    (blowupHmodMap_comp_apply I 1 _ _ x).symm.trans
      (congrArg (fun φ => blowupHmodMap I 1 φ x) (imageToPullbackTwist_comp I M q e he))
  canToImg₁δ M q := ((blowupDeltaMod I).δ (shortExact_twist_kernel I (blowupCanM I M) q) 1).hom
  exact_canToImg₁ M q :=
    exact_blowupHmodMap_δ I _ _ _ (shortExact_twist_kernel I (blowupCanM I M) q) 1
  vanishing_Hdual₁ M q hd := subsingleton_blowupHmod_one_blowupDual I M q hd
  vanishing_Hker₂ M q hd := subsingleton_blowupHmod_two_kernel_blowupCan I M q hd
  HimgD u q := blowupHmod I 0 (Abelian.image (blowupDualMap I (m + 1) u) ⊗ blowupTwistInt I q)
  HimgDtr u _ _ hq := (blowupHmodMap I 0
    (Abelian.image (blowupDualMap I (m + 1) u) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  HcokerD u q := blowupHmod I 0 (cokernel (blowupDualMap I (m + 1) u) ⊗ blowupTwistInt I q)
  HcokerDtr u _ _ hq := (blowupHmodMap I 0
    (cokernel (blowupDualMap I (m + 1) u) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  dualToImgD u q := (blowupHmodMap I 0
    (Abelian.factorThruImage (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom
  imgDToDual u q := (blowupHmodMap I 0
    (Abelian.image.ι (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom
  dualToCokerD u q := (blowupHmodMap I 0
    (cokernel.π (blowupDualMap I (m + 1) u) ▷ blowupTwistInt I q)).hom
  imgDToDual_HimgDtr u q q' hq t := blowupDualMap_imgDToDual_HimgDtr I u q q' hq t
  dualToCokerD_Hdualtr u q q' hq σ := blowupDualMap_dualToCokerD_Hdualtr I u q q' hq σ
  exact_imgDToDual u q := exact_twist_image_cokernel I (blowupDualMap I (m + 1) u) q
  HcokerDtr_eq_zero u hfac q e he hec :=
    blowupHmodMap_cokernel_blowupDualMap_hom_eq_zero I u hfac q e he hec
  evDual_imgDToDual_dualToImgD u q hq τ := blowupEvDual_imgDToDual_dualToImgD I h u q hq τ
  imgDδ u v hex hv q :=
    ((blowupDeltaMod I).δ (shortExact_blowupDualMap_twist I (m + 1) u v hex hv q) 0).hom
  imgDδ_HimgDtr u v hex hv q q' hq t :=
    blowupDualMap_δ_naturality_nat I (m + 1) u v hex hv hq t
  exact_imgDδ u v hex hv q := exact_blowupDualMap_δ I (m + 1) u v hex hv q

/-- `blowupDottedArrowSituation` at `q₀ = q(S)`. -/
def blowupDottedArrowSituationQS (m c : ℕ) (hcn : c ≤ m + 1) : DottedArrowSituation A I (m + 1) c :=
  blowupDottedArrowSituation I m c hcn (isBaseThreshold_qS I)

/-- The integer `d` of `blowupDottedArrowSituationQS` is `d(S)`. -/
@[simp] theorem blowupDottedArrowSituationQS_d (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupDottedArrowSituationQS I m c hcn).d = fibreDim I :=
  rfl

/-- The threshold of `blowupDottedArrowSituationQS` is `q(S)`. -/
@[simp] theorem blowupDottedArrowSituationQS_q₀ (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupDottedArrowSituationQS I m c hcn).q₀ = qS I :=
  rfl

end Stacks.LocalCohomology.UniformityIII

end
