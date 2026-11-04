module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualTwistSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualSection

/-!
# The `CanDualSituation` of Tag 0GAC on the blowup

Let `p : X → Spec(A)` be the blowup of a Noetherian ring `A` in `I`, `n = m + 1`, and `M` an
`(A, n, c)`-module. This file assembles the data of the duality step of
[Stacks, Tag 0GAC] on the blowup, as an instance of
`Stacks.LocalCohomology.UniformityIII.CanDualSituation`, with every field the honest geometric
object:

* `Hdual M q = H⁰(X, (p^*M)^∨(q))` for the dual `(p^*M)^∨ = SheafHom(p^*M, 𝒪_{Yₙ})`
  (`blowupDual`), with evaluation `blowupEvDual` and the section `blowupSecDual` attached to a
  homomorphism `M → I^q/I^{q+n}`;
* `can : p^*(M^∨) ⟶ (p^*M)^∨` is `blowupCan`, and `Himg`, `Hcoker` are `H⁰` and `Hker` is `H¹`
  of the twists of its image, cokernel and kernel, with the maps of
  `StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.CanTwistCohomology`;
* the vanishing of the twisting maps on the cokernel and the kernel is Tag 0GA9 on cohomology
  (`blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero`) fed with the annihilation of Tag 0GAB
  (`globalSmulCenter_app_cokernel_blowupCan`, `globalSmulCenter_app_kernel_blowupCan`), and the
  vanishing of `H¹` of the kernel for `d(S) = 0` is the fibre dimension bound, the dual being
  quasi-coherent because `M` is finitely presented over `A`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupCanDualSituation`: the `CanDualSituation` on the
  blowup, for any threshold `q₀` with the defining property of `q(S)`.
* `Stacks.LocalCohomology.UniformityIII.blowupCanDualSituationQS`: the same at `q₀ = q(S)`, with
  `d = d(S)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.finitePresentation_resModule`: an `(A, n, c)`-module is
  finitely presented over `A`.
* `Stacks.LocalCohomology.UniformityIII.blowupEvDual_imgToDual_canToImg`: the commuting square
  `e_{p^*z} ∘ can = p^*e_z` on sections (the field `evDual_can`).

Applying `CanDualSituation.exists_sum_powQuotSmul` to `blowupCanDualSituationQS` gives
[Stacks, Tag 0GAC] for the blowup at the source's own integers `q(S)` and `d(S)`.

## References

* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GA9](https://stacks.math.columbia.edu/tag/0GA9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Finiteness -/

/-- An `A/Iⁿ`-module finite over `A/Iⁿ` is finite over `A`: a surjection from `(A/Iⁿ)^r` lifts
to one from `A^r`. -/
theorem finite_resModule (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n))
    [Module.Finite (A ⧸ I ^ n) N] : Module.Finite A (resModule I n N) := by
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) N
  let g : (Fin r → A) →ₗ[A] resModule I n N :=
    { toFun := fun x => f (fun i => Ideal.Quotient.mk (I ^ n) (x i))
      map_add' := fun x y => (congrArg f (funext fun i => map_add _ _ _)).trans (f.map_add _ _)
      map_smul' := fun a x => (congrArg f (funext fun i =>
        (map_mul (Ideal.Quotient.mk (I ^ n)) a (x i)))).trans
          (f.map_smul (Ideal.Quotient.mk (I ^ n) a) _) }
  refine Module.Finite.of_surjective g fun y => ?_
  obtain ⟨v, rfl⟩ := hf y
  exact ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
    congrArg f (funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec)⟩

/-- **An `(A, n, c)`-module is finitely presented over `A`**, for `A` Noetherian: it is finite over
`A/Iⁿ`, hence over `A`. -/
theorem finitePresentation_resModule [IsNoetherianRing A] {n c : ℕ} (M : ANCModule I n c) :
    Module.FinitePresentation A (resModule I n M.1) :=
  have : Module.Finite (A ⧸ I ^ n) M.1 := M.2.1
  have := finite_resModule I n M.1
  Module.finitePresentation_of_finite A _

variable [IsNoetherianRing A]

/-! ### The fields of the duality step -/

section Fields

variable {m c : ℕ} (M : ANCModule I (m + 1) c)

/-- `can : p^*(M^∨) ⟶ (p^*M)^∨` at an `(A, m + 1, c)`-module. -/
abbrev blowupCanM : (thickeningPullback I (m + 1)).obj M.dual.1 ⟶ blowupDual I (m + 1) M.1 :=
  blowupCan I (m + 1) M.1

/-- **Evaluating `can(t)` against `z ∈ M` is evaluating `t` against `z`** (the field
`evDual_can`): on the twists, `p^*(M^∨) ⟶ im(can) ⟶ (p^*M)^∨ ⟶ 𝒪_{Yₙ}` is `p^*e_z`, by
`blowupDualEval_comp_blowupCan`. -/
theorem blowupEvDual_imgToDual_canToImg {q₀ : ℕ} (h : IsBaseThreshold I q₀) (q : ℕ)
    (hq : q₀ ≤ q)
    (t : blowupHmod I 0 ((thickeningPullback I (m + 1)).obj M.dual.1 ⊗ blowupTwistInt I q)) :
    blowupEvDual I m h hq M.1
        ((blowupHmodMap I 0 (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q)).hom
          ((blowupHmodMap I 0
            (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q)).hom t)) =
      blowupDualEv I m h hq M.1 t := by
  refine LinearMap.ext fun z => ?_
  have key : (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q) ≫
      (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q) ≫
        (blowupDualEval I (m + 1) M.1 z ▷ blowupTwistInt I q) =
      ((thickeningPullback I (m + 1)).map (dualEvalAt I M.1 z) ≫
        (thickeningPullbackUnitIso I (m + 1)).hom) ▷ blowupTwistInt I q := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, ← Category.assoc, Abelian.image.fac]
    exact congrArg (· ▷ blowupTwistInt I q) (blowupDualEval_comp_blowupCan I (m + 1) M.1 z)
  rw [blowupEvDual_apply]
  exact congrArg (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm
    (((blowupHmodMap_comp_apply I 0 _ _ _).symm.trans
      (blowupHmodMap_comp_apply I 0 _ _ t).symm).trans
      (congrArg (fun φ => blowupHmodMap I 0 φ t) key))

/-- The inclusion of the twisted image of `can` is natural in the twist (the field
`imgToDual_Himgtr`). -/
theorem blowupCan_imgToDual_Himgtr (q q' : ℕ) (hq : q' ≤ q)
    (t : blowupHmod I 0 (Abelian.image (blowupCanM I M) ⊗ blowupTwistInt I q)) :
    (blowupHmodMap I 0 (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q')).hom
        ((blowupHmodMap I 0
          (Abelian.image (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom t) =
      (blowupHmodMap I 0 (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
        ((blowupHmodMap I 0 (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q)).hom t) :=
  (blowupHmodMap_whiskerRight_whiskerLeft_apply I 0 (Abelian.image.ι (blowupCanM I M))
    (Nat.cast_le.2 hq) t).symm

/-- The projection onto the twisted cokernel of `can` is natural in the twist (the field
`dualToCoker_Hdualtr`). -/
theorem blowupCan_dualToCoker_Hdualtr (q q' : ℕ) (hq : q' ≤ q)
    (σ : blowupHmod I 0 (blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q)) :
    (blowupHmodMap I 0 (cokernel.π (blowupCanM I M) ▷ blowupTwistInt I q')).hom
        ((blowupHmodMap I 0
          (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom σ) =
      (blowupHmodMap I 0 (cokernel (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
        ((blowupHmodMap I 0 (cokernel.π (blowupCanM I M) ▷ blowupTwistInt I q)).hom σ) :=
  (blowupHmodMap_whiskerRight_whiskerLeft_apply I 0 (cokernel.π (blowupCanM I M))
    (Nat.cast_le.2 hq) σ).symm

/-- **Tag 0GA9 for the cokernel of `can`** on sections: the cokernel is killed by `I^c`
(Tag 0GAB), so `coker(can)(q) ⟶ coker(can)(e)` is zero on `H⁰` for `e + c = q`. -/
theorem blowupHmodMap_cokernel_blowupCan_twistLE_eq_zero (q e : ℕ) (he : e ≤ q)
    (hec : e + c = q) :
    blowupHmodMap I 0 (cokernel (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 he)) = 0 :=
  blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero I 0 (cokernel (blowupCanM I M))
    (fun _ ha => globalSmulCenter_app_cokernel_blowupCan M.2 ha) (Nat.cast_le.2 he)
    (by rw [← hec]; push_cast; exact le_refl _)

/-- **Tag 0GA9 for the kernel of `can`** on `H¹`: the kernel is killed by `I^c` (Tag 0GAB), so
`ker(can)(q) ⟶ ker(can)(e)` is zero on `H¹` for `e + c = q`. -/
theorem blowupHmodMap_kernel_blowupCan_twistLE_eq_zero (q e : ℕ) (he : e ≤ q)
    (hec : e + c = q) :
    blowupHmodMap I 1 (kernel (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 he)) = 0 :=
  blowupHmodMap_whiskerLeft_blowupTwistLE_eq_zero I 1 (kernel (blowupCanM I M))
    (fun _ ha => globalSmulCenter_app_kernel_blowupCan M.2 ha) (Nat.cast_le.2 he)
    (by rw [← hec]; push_cast; exact le_refl _)

/-- `H¹(X, ker(can)(q)) = 0` when the fibres of `p` have dimension `0`: `p^*(M^∨)` and
`(p^*M)^∨` are quasi-coherent, `M` being finitely presented over `A`, hence so is the kernel. -/
theorem subsingleton_blowupHmod_kernel_blowupCan (q : ℕ) (hd : fibreDim I < 1) :
    Subsingleton (blowupHmod I 1 (kernel (blowupCanM I M) ⊗ blowupTwistInt I q)) := by
  have := finitePresentation_resModule I M
  have := isQuasicoherent_blowupDual I (m + 1) M.1
  exact subsingleton_blowupHmod_twist_kernel I (blowupCanM I M) q hd

end Fields

/-! ### The `CanDualSituation` -/

/-- **The `CanDualSituation` of Tag 0GAC on the blowup**, for `n = m + 1` and any threshold `q₀`
with the defining property of `q(S)`: `(p^*M)^∨ = SheafHom(p^*M, 𝒪_{Yₙ})`, `can = blowupCan`,
the cohomology of the twists of its image, cokernel and kernel, the section `blowupSecDual`
attached to a homomorphism and the evaluation `blowupEvDual`. -/
def blowupCanDualSituation (m c : ℕ) (hcn : c ≤ m + 1) {q₀ : ℕ} (h : IsBaseThreshold I q₀) :
    CanDualSituation A I (m + 1) c where
  toDualSituation := blowupDualSituation I m c hcn h
  Hdual M q := blowupHmod I 0 (blowupDual I (m + 1) M.1 ⊗ blowupTwistInt I q)
  Hdualtr M _ _ hq :=
    (blowupHmodMap I 0 (blowupDual I (m + 1) M.1 ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  Himg M q := blowupHmod I 0 (Abelian.image (blowupCanM I M) ⊗ blowupTwistInt I q)
  Himgtr M _ _ hq :=
    (blowupHmodMap I 0 (Abelian.image (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  Hcoker M q := blowupHmod I 0 (cokernel (blowupCanM I M) ⊗ blowupTwistInt I q)
  Hcokertr M _ _ hq :=
    (blowupHmodMap I 0 (cokernel (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  Hker M q := blowupHmod I 1 (kernel (blowupCanM I M) ⊗ blowupTwistInt I q)
  Hkertr M _ _ hq :=
    (blowupHmodMap I 1 (kernel (blowupCanM I M) ◁ blowupTwistLE I (Nat.cast_le.2 hq))).hom
  secDual M q := blowupSecDual I m q M.1
  evDual M _ hq := blowupEvDual I m h hq M.1
  evDual_secDual M q hq φ := blowupEvDual_blowupSecDual I m q M.1 h hq φ
  evDual_Hdualtr M _ _ hq hq' hle σ :=
    blowupEvDual_whiskerLeft I m h hq hq' hle (Nat.cast_le.2 hle) M.1 σ
  canToImg M q :=
    (blowupHmodMap I 0 (Abelian.factorThruImage (blowupCanM I M) ▷ blowupTwistInt I q)).hom
  imgToDual M q :=
    (blowupHmodMap I 0 (Abelian.image.ι (blowupCanM I M) ▷ blowupTwistInt I q)).hom
  dualToCoker M q :=
    (blowupHmodMap I 0 (cokernel.π (blowupCanM I M) ▷ blowupTwistInt I q)).hom
  canToImgδ M q := ((blowupDeltaMod I).δ (shortExact_twist_kernel I (blowupCanM I M) q) 0).hom
  imgToDual_Himgtr M q q' hq t := blowupCan_imgToDual_Himgtr I M q q' hq t
  dualToCoker_Hdualtr M q q' hq σ := blowupCan_dualToCoker_Hdualtr I M q q' hq σ
  canToImgδ_Himgtr M _ _ hq t :=
    twist_kernel_δ_naturality I (blowupCanM I M) (Nat.cast_le.2 hq) t
  exact_imgToDual M q := exact_twist_image_cokernel I (blowupCanM I M) q
  exact_canToImg M q := exact_twist_factorThruImage_δ I (blowupCanM I M) q
  evDual_can M q hq t := blowupEvDual_imgToDual_canToImg I M h q hq t
  Hcokertr_eq_zero M q e he hec :=
    congrArg ModuleCat.Hom.hom (blowupHmodMap_cokernel_blowupCan_twistLE_eq_zero I M q e he hec)
  Hkertr_eq_zero M q e he hec :=
    congrArg ModuleCat.Hom.hom (blowupHmodMap_kernel_blowupCan_twistLE_eq_zero I M q e he hec)
  vanishing_Hker M q hd := subsingleton_blowupHmod_kernel_blowupCan I M q hd

/-- `blowupCanDualSituation` at `q₀ = q(S)`. -/
def blowupCanDualSituationQS (m c : ℕ) (hcn : c ≤ m + 1) : CanDualSituation A I (m + 1) c :=
  blowupCanDualSituation I m c hcn (isBaseThreshold_qS I)

/-- `blowupCanDualSituationQS` extends `blowupDualSituationQS`. -/
@[simp] theorem blowupCanDualSituationQS_toDualSituation (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupCanDualSituationQS I m c hcn).toDualSituation = blowupDualSituationQS I m c hcn :=
  rfl

/-- The integer `d` of `blowupCanDualSituationQS` is `d(S)`. -/
@[simp] theorem blowupCanDualSituationQS_d (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupCanDualSituationQS I m c hcn).d = fibreDim I :=
  rfl

/-- The threshold of `blowupCanDualSituationQS` is `q(S)`. -/
@[simp] theorem blowupCanDualSituationQS_q₀ (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupCanDualSituationQS I m c hcn).q₀ = qS I :=
  rfl

end Stacks.LocalCohomology.UniformityIII

end
