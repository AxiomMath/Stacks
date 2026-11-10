module

public import StacksFrontier.Deformation.Completed.SmoothModel
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.RingTheory.AdicCompletion.MaximalIdealLocalization
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# Points of the completion of an algebra at the kernel of a residue map

Let `R` be a `Λ`-algebra with a surjection `q : R → k` whose kernel `𝔪` is finitely generated,
and let `R^∧` be the completion of `R` at `𝔪`, a Noetherian complete local `Λ`-algebra with
residue field `k` (`Deformation.completionObjectOfSurjection`). For an Artinian local
`Λ`-algebra `A` with residue field `k`, the morphisms `R^∧ → A` of complete local algebras are
the `Λ`-algebra maps `R → A` lifting `q`: restriction along `R → R^∧` is a bijection, natural in
`A`. So `R^∧` prorepresents the functor `A ↦ {R → A lifting q}`. Moreover, if `R` is Noetherian,
`R^∧` has the dimension of the localization `R_𝔪`.

## Main results

* `Deformation.completionPointsEquiv`, `Deformation.completionPointsEquiv_naturality`.
* `Deformation.ringKrullDim_completionObjectOfSurjection`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Deformation

variable {Λ k R : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [CommRing R] [Algebra Λ R]
  (q : R →ₐ[Λ] k) (hq : Function.Surjective q) (hfg : (RingHom.ker q.toRingHom).FG)

/-- The canonical map from `R` to its completion at the kernel of `q`. -/
noncomputable def toCompletionObject : R →ₐ[Λ] completionObjectOfSurjection q hq hfg :=
  letI : IsScalarTower Λ R (AdicCompletion (RingHom.ker q.toRingHom) R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  IsScalarTower.toAlgHom Λ R (AdicCompletion (RingHom.ker q.toRingHom) R)

/-- The map `Deformation.toCompletionObject` is the algebra map of `R` into its adic completion. -/
theorem toCompletionObject_apply (x : R) :
    toCompletionObject q hq hfg x =
      algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R) x := rfl

/-- The residue of the image of `x ∈ R` in the completion is `q x`. -/
theorem completionObject_residue (x : R) :
    (completionObjectOfSurjection q hq hfg).residueEquiv
        (residue _ (toCompletionObject q hq hfg x)) = q x := by
  change AdicCompletion.kerProj hq (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R) x) =
    q x
  exact AdicCompletion.kerProj_of hq x

/-- A ring map sending `I` into `J` sends `I ^ n` into `J ^ n`. -/
private theorem map_pow_le_pow_of_map_le {S D : Type u} [CommRing S] [CommRing D] {I : Ideal S}
    {J : Ideal D} {f : S →+* D} (h : I.map f ≤ J) (n : ℕ) : (I ^ n).map f ≤ J ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' h n

/-- An algebra map out of `R` sending the kernel of `q` into an ideal for which the target is
adically complete extends to the completion. -/
noncomputable def extendToCompletion {D : Type u} [CommRing D] [Algebra Λ D]
    (J : Ideal D) [IsAdicComplete J D] (f : R →ₐ[Λ] D)
    (hIJ : (RingHom.ker q.toRingHom).map f.toRingHom ≤ J) :
    AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] D := by
  let I := RingHom.ker q.toRingHom
  have hpow (n : ℕ) : (I ^ n).map f.toRingHom ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hIJ n
  let fbar : (n : ℕ) → AdicCompletion I R →ₐ[Λ] D ⧸ J ^ n := fun n =>
    (Ideal.quotientMapₐ (J ^ n) f (Ideal.map_le_iff_le_comap.mp (hpow n))).comp
      ((AdicCompletion.evalₐ I n).restrictScalars Λ)
  have hfbar : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (fbar n) = fbar m := by
    intro m n hle
    apply AlgHom.ext
    intro x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simp only [fbar, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AdicCompletion.evalₐ_mk, Ideal.quotient_map_mkₐ,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.factorₐ_apply,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      rw [← map_sub]
      apply Ideal.map_le_iff_le_comap.mp (hpow m)
      simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (x.property hle).symm
  have : IsScalarTower Λ R (AdicCompletion I R) := IsScalarTower.of_algebraMap_eq' rfl
  exact IsAdicComplete.liftAlgHom J fbar hfbar

/-- The extension `Deformation.extendToCompletion` of `f` to the completion restricts to `f` on
`R`. -/
theorem extendToCompletion_algebraMap {D : Type u} [CommRing D] [Algebra Λ D]
    (J : Ideal D) [IsAdicComplete J D] (f : R →ₐ[Λ] D)
    (hIJ : (RingHom.ker q.toRingHom).map f.toRingHom ≤ J) (x : R) :
    extendToCompletion q J f hIJ (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R) x) =
      f x := by
  have : IsScalarTower Λ R (AdicCompletion (RingHom.ker q.toRingHom) R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h : (extendToCompletion q J f hIJ).comp
      (IsScalarTower.toAlgHom Λ R (AdicCompletion (RingHom.ker q.toRingHom) R)) = f := by
    unfold extendToCompletion
    apply IsAdicComplete.algHom_ext (I := J)
    intro n
    rw [← AlgHom.comp_assoc, IsAdicComplete.mkₐ_comp_liftAlgHom]
    refine AlgHom.ext fun y => ?_
    change Ideal.quotientMap (J ^ n) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp (map_pow_le_pow_of_map_le hIJ n))
      (AdicCompletion.evalₐ (RingHom.ker q.toRingHom) n
        (AdicCompletion.of (RingHom.ker q.toRingHom) R y)) = _
    rw [AdicCompletion.evalₐ_of]
    rfl
  exact DFunLike.congr_fun h x

include hfg in
/-- Two algebra maps out of the completion which agree on `R` and send the kernel of `q` into an
ideal for which the target is adically complete are equal. -/
theorem algHom_ext_completion {D : Type u} [CommRing D] [Algebra Λ D]
    (J : Ideal D) [IsAdicComplete J D]
    (f g : AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] D)
    (hf : (RingHom.ker q.toRingHom).map
      (f.toRingHom.comp (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R))) ≤ J)
    (hg : (RingHom.ker q.toRingHom).map
      (g.toRingHom.comp (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R))) ≤ J)
    (hfg' : ∀ x : R, f (algebraMap R _ x) = g (algebraMap R _ x)) : f = g := by
  let I := RingHom.ker q.toRingHom
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := J)]
  intro n
  rw [SModEq.sub_mem]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective ((I ^ n) • (⊤ : Submodule R R)) (x.val n)
  have hx : x - algebraMap R (AdicCompletion I R) r ∈
      (I ^ n) • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hr.symm
  have hmap (F : AdicCompletion I R →ₐ[Λ] D)
      (hF : I.map (F.toRingHom.comp (algebraMap R (AdicCompletion I R))) ≤ J) :
      F (x - algebraMap R (AdicCompletion I R) r) ∈ J ^ n • (⊤ : Submodule D D) := by
    have hx' : x - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hx
    have := Ideal.mem_map_of_mem (f := F.toRingHom) hx'
    rw [Ideal.map_map] at this
    simpa [Ideal.mul_top] using map_pow_le_pow_of_map_le hF n this
  rw [show f x - g x = f (x - algebraMap R (AdicCompletion I R) r) -
      g (x - algebraMap R (AdicCompletion I R) r) by
    rw [map_sub, map_sub, hfg' r]
    ring]
  exact Submodule.sub_mem (J ^ n • (⊤ : Submodule D D)) (hmap f hf) (hmap g hg)

/-- The residue condition `residue ∘ f = q` makes `f` send the kernel of `q` into the maximal
ideal. -/
theorem map_ker_le_maximalIdeal (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (f : R →ₐ[Λ] A)
    (hf : ∀ x, A.residueEquiv (residue A (f x)) = q x) :
    (RingHom.ker q.toRingHom).map f.toRingHom ≤ maximalIdeal A := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f x ∈ maximalIdeal A
  rw [← residue_eq_zero_iff]
  apply A.residueEquiv.injective
  rw [hf, map_zero]
  exact hx

include hq hfg in
/-- A map out of the completion whose restriction to `R` lifts `q` sends the kernel of `q` into
the maximal ideal. -/
theorem map_ker_le_maximalIdeal_of_completion (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (g : AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] A)
    (hg : ∀ x, A.residueEquiv (residue A (g (algebraMap R _ x))) = q x) :
    (RingHom.ker q.toRingHom).map
      (g.toRingHom.comp (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R))) ≤
        maximalIdeal A :=
  map_ker_le_maximalIdeal q A (g.comp (toCompletionObject q hq hfg)) hg

/-- **The points of the completion over an Artinian algebra.** Restriction along `R → R^∧` is a
bijection between morphisms `R^∧ → A` of complete local algebras and `Λ`-algebra maps `R → A`
lifting `q`. -/
noncomputable def completionPointsEquiv (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (completionObjectOfSurjection q hq hfg ⟶ artinianToComplete.obj A) ≃
      {f : R →ₐ[Λ] A // ∀ x, A.residueEquiv (residue A (f x)) = q x} :=
  haveI : IsAdicComplete (maximalIdeal A) A := (artinianToComplete.obj A).completeLocal.isComplete
  { toFun := fun β => ⟨β.hom.comp (toCompletionObject q hq hfg), fun x =>
      (β.residue_comm (toCompletionObject q hq hfg x)).trans (completionObject_residue q hq hfg x)⟩
    invFun := fun f =>
        have hres : ∀ a : AdicCompletion (RingHom.ker q.toRingHom) R,
            A.residueEquiv (residue A (extendToCompletion q (maximalIdeal A) f.1
              (map_ker_le_maximalIdeal q A f.1 f.2) a)) =
              (completionObjectOfSurjection q hq hfg).residueEquiv (residue _ a) := by
          let ext := extendToCompletion q (maximalIdeal A) f.1 (map_ker_le_maximalIdeal q A f.1 f.2)
          let g₁ : AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] k :=
            A.residueEquiv.toAlgHom.comp ((IsScalarTower.toAlgHom Λ A (ResidueField A)).comp ext)
          let g₂ : AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] k :=
            residueAlgHom (completionObjectOfSurjection q hq hfg)
          have hg₁ : ∀ x : R, g₁ (algebraMap R _ x) = q x := by
            intro x
            change A.residueEquiv (residue A (ext (algebraMap R _ x))) = q x
            rw [extendToCompletion_algebraMap]
            exact f.2 x
          have hg₂ : ∀ x : R, g₂ (algebraMap R _ x) = q x := by
            intro x
            exact (residueAlgHom_apply _ _).trans (completionObject_residue q hq hfg x)
          have hker : ∀ g : AdicCompletion (RingHom.ker q.toRingHom) R →ₐ[Λ] k,
              (∀ x : R, g (algebraMap R _ x) = q x) →
              (RingHom.ker q.toRingHom).map
                (g.toRingHom.comp (algebraMap R (AdicCompletion (RingHom.ker q.toRingHom) R))) ≤
                  ⊥ := by
            intro g hg
            rw [Ideal.map_le_iff_le_comap]
            intro x hx
            change g (algebraMap R _ x) ∈ (⊥ : Ideal k)
            rw [hg, Ideal.mem_bot]
            exact hx
          have h := algHom_ext_completion q hfg (⊥ : Ideal k) g₁ g₂ (hker g₁ hg₁) (hker g₂ hg₂)
            (fun x => (hg₁ x).trans (hg₂ x).symm)
          intro a
          exact congrArg (fun g => g a) h
        { hom := extendToCompletion (D := A) q (maximalIdeal A) f.1
            (map_ker_le_maximalIdeal q A f.1 f.2)
          isLocal := by
            refine ⟨fun a ha => ?_⟩
            have h1 : residue A (extendToCompletion q (maximalIdeal A) f.1
                (map_ker_le_maximalIdeal q A f.1 f.2) a) ≠ 0 := by
              rw [Ne, residue_eq_zero_iff]
              exact fun hm => (mem_maximalIdeal _).mp hm ha
            have h2 : residue (completionObjectOfSurjection q hq hfg) a ≠ 0 := by
              intro h0
              apply h1
              apply A.residueEquiv.injective
              rw [hres a, h0, map_zero, map_zero]
            rw [Ne, residue_eq_zero_iff, mem_maximalIdeal] at h2
            exact not_not.mp h2
          residue_comm := hres }
    left_inv := fun β => by
      have hβ : ∀ x, A.residueEquiv (residue A (β.hom (toCompletionObject q hq hfg x))) = q x :=
        fun x => (β.residue_comm (toCompletionObject q hq hfg x)).trans
          (completionObject_residue q hq hfg x)
      apply CompleteLocalAlgCat.Hom.ext
      exact algHom_ext_completion q hfg (D := A) (maximalIdeal A) _ _
        (map_ker_le_maximalIdeal_of_completion q hq hfg A _ (fun x => by
          rw [extendToCompletion_algebraMap]; exact hβ x))
        (map_ker_le_maximalIdeal_of_completion q hq hfg A β.hom hβ)
        (extendToCompletion_algebraMap (D := A) q (maximalIdeal A)
          (β.hom.comp (toCompletionObject q hq hfg)) (map_ker_le_maximalIdeal q A _ hβ))
    right_inv := fun f => Subtype.ext <| AlgHom.ext <|
      extendToCompletion_algebraMap (D := A) q (maximalIdeal A) f.1
        (map_ker_le_maximalIdeal q A f.1 f.2) }

/-- The bijection of `Deformation.completionPointsEquiv` is natural in the Artinian algebra. -/
theorem completionPointsEquiv_naturality {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k} (g : A ⟶ A')
    (β : completionObjectOfSurjection q hq hfg ⟶ artinianToComplete.obj A) :
    ((completionPointsEquiv q hq hfg A') (β ≫ artinianToComplete.map g)).1 =
      g.hom.comp ((completionPointsEquiv q hq hfg A) β).1 := rfl

/-- **The completion has the dimension of the localization.** For a Noetherian `R`, the
completion of `R` at the kernel of `q` has the Krull dimension of `R_𝔪`. -/
theorem ringKrullDim_completionObjectOfSurjection [IsNoetherianRing R] :
    letI : (RingHom.ker q.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective q.toRingHom hq
    ringKrullDim (completionObjectOfSurjection q hq hfg) =
      ringKrullDim (Localization.AtPrime (RingHom.ker q.toRingHom)) := by
  let : (RingHom.ker q.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective q.toRingHom hq
  obtain ⟨E, -⟩ := Stacks.MaximalLocalization.exists_adicCompletionAlgEquiv_localizationAtPrime
    (RingHom.ker q.toRingHom)
  change ringKrullDim (AdicCompletion (RingHom.ker q.toRingHom) R) = _
  rw [ringKrullDim_eq_of_ringEquiv E.toRingEquiv, Localization.AtPrime.map_eq_maximalIdeal]
  exact ringKrullDim_adicCompletion_maximalIdeal.symm

end Deformation

end
