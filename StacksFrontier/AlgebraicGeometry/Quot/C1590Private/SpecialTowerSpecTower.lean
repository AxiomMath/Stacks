module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerLimitTower
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.StabilizationGenericFibre
public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerLimit

/-!
# The spectrum of a tower is an étale limit tower

Let `⋯ → R₁ → R₀` be a tower of surjections with square-zero kernels `Ker(Rₙ → R₀)`. If étale base
change commutes with its limit (`AlgebraicGeometry.C1590Private.IsEtaleCompatibleTower`, true for
special towers), then `Spec Rₙ ⟶ Spec (lim Rₙ)` is an étale limit tower in the big fppf site
of `Spec ℤ` (`AlgebraicGeometry.C1590Private.IsEtaleLimitTower`): for `P` affine étale over
`Spec (lim Rₙ)` the base change `P ×_{Spec (lim Rₙ)} Spec Rₙ` is `Spec (Γ(P) ⊗ Rₙ)`.

## Main results

* `AlgebraicGeometry.C1590Private.isEtaleLimitTower_specSite`: if the transition maps are
  surjective, the kernels `Ker(Rₙ → R₀)` square to zero and the limit commutes with étale base
  change, then the tower `Spec Rₙ ⟶ Spec (lim Rₙ)` is an étale limit tower.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin
open Deformation.Artin.SquareZeroTower

universe u

namespace AlgebraicGeometry.C1590Private

section Ring

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- If every transition map `Rₙ₊₁ → Rₙ` is surjective, then the projection `lim Rₙ → R₀` is
surjective. -/
theorem towerLimitProj_zero_surjective (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (towerLimitProj f 0) := by
  intro x
  let lift : ∀ k, R k := fun k => Nat.rec (motive := fun k => R k) x
    (fun k y => (hf k y).choose) k
  exact ⟨⟨lift, fun k => (hf k _).choose_spec⟩, rfl⟩

/-- The projection `lim Rₙ → Rₙ₊₁` followed by the transition map `Rₙ₊₁ → Rₙ` is the projection
`lim Rₙ → Rₙ`. -/
theorem towerLimitProj_comp (n : ℕ) :
    (f n).comp (towerLimitProj f (n + 1)) = towerLimitProj f n :=
  RingHom.ext fun r => r.2 n

/-- If `Ker(Rₘ → R₀)` squares to zero, then every element of it is nilpotent of order two. -/
private theorem sq_eq_zero_of_toBase_eq_zero (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
    {m : ℕ} {z : R m} (h : toBase f m z = 0) : z ^ 2 = 0 := by
  rw [sq]
  exact mul_eq_zero_of_sq (hsq m) h h

/-- If every kernel `Ker(Rₙ → R₀)` squares to zero, then every element of `lim Rₙ` in the kernel
of the projection to `R₀` is nilpotent. -/
theorem isNilpotent_of_towerLimitProj_zero (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)
    {r : limit f} (hr : towerLimitProj f 0 r = 0) : IsNilpotent r := by
  refine ⟨2, Subtype.ext (funext fun m => ?_)⟩
  have hm : toBase f m ((r : ∀ n, R n) m) = 0 :=
    ((mem_sameBase f).1 (limit_le_sameBase f r.2) m).trans hr
  exact sq_eq_zero_of_toBase_eq_zero f hsq hm

/-- If every kernel `Ker(Rₙ → R₀)` squares to zero, then every element of the kernel of the
transition map `Rₙ₊₁ → Rₙ` is nilpotent. -/
theorem isNilpotent_of_transition (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) (n : ℕ)
    {z : R (n + 1)} (hz : f n z = 0) : IsNilpotent z := by
  have h : toBase f (n + 1) z = 0 := by rw [toBase_succ, hz, map_zero]
  exact ⟨2, sq_eq_zero_of_toBase_eq_zero f hsq h⟩

end Ring

/-- A surjective ring map whose kernel is nil induces a thickening of spectra. -/
theorem isThickening_specMap_of_isNilpotent {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') (hφ : Function.Surjective φ) (hker : ∀ a, φ a = 0 → IsNilpotent a) :
    Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ, ?_⟩
  change Function.Surjective (PrimeSpectrum.comap φ)
  intro p
  have hp : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ : Set A) := fun x hx =>
    nilradical_le_prime p.asIdeal (mem_nilradical.2 (hker x hx))
  rwa [← _root_.range_comap_of_surjective _ φ hφ] at hp

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- `Spec A`, as an object of the big fppf site of `Spec ℤ`. -/
abbrev specSite (A : Type u) [CommRing A] (h : B.Contains (Spec (.of A))) :
    BigFppfOver B integerBase hZ :=
  algebraOver A B integerBase hZ (specULiftZIsTerminal.from _) h

/-- The scheme underlying `specSite B hZ A h` is affine. -/
instance isAffine_specSite (A : Type u) [CommRing A] (h : B.Contains (Spec (.of A))) :
    IsAffine ((𝒯).obj (specSite B hZ A h)) :=
  show IsAffine (Spec (CommRingCat.of A)) from inferInstance

variable {B hZ} in
/-- `Spec` of a ring map, as a morphism of the big fppf site of `Spec ℤ`. -/
abbrev specSiteMap {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
    {h : B.Contains (Spec (.of A))} {h' : B.Contains (Spec (.of A'))} :
    specSite B hZ A' h' ⟶ specSite B hZ A h :=
  BigFppfOver.liftOfIntegers (Spec.map (CommRingCat.ofHom φ))

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- **The spectrum of a tower whose limit commutes with étale base change is an étale limit
tower.** -/
theorem isEtaleLimitTower_specSite (hf : ∀ n, Function.Surjective (f n))
    (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) (hB : IsEtaleCompatibleTower f)
    (hR : ∀ n, B.Contains (Spec (.of (R n)))) :
    IsEtaleLimitTower (V := specSite B hZ (limit f) (contains_limit f hR))
      (fun n => specSite B hZ (R n) (hR n)) (fun n => specSiteMap (towerLimitProj f n))
      (fun n => specSiteMap (f n)) where
  comp n := (𝒯).map_injective (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (towerLimitProj_comp f n)))
  isThickening_zero := isThickening_specMap_of_isNilpotent _ (towerLimitProj_zero_surjective f hf)
    (fun _ hr => isNilpotent_of_towerLimitProj_zero f hsq hr)
  isThickening_ℓ n := isThickening_specMap_of_isNilpotent _ (hf n)
    (fun _ hz => isNilpotent_of_transition f hsq n hz)
  isAffine := inferInstance
  existsUnique P e he hP Q a b c hpb hca hcb s hs := by
    let := fun m => (towerLimitProj f m).toAlgebra
    let C := Γ((𝒯).obj P, ⊤)
    let φ : limit f →+* C := ((Scheme.ΓSpecIso (.of (limit f))).inv ≫ ((𝒯).map e).appTop).hom
    let : Algebra (limit f) C := φ.toAlgebra
    have : IsAffine ((𝒯).obj P) := hP
    have : Etale ((𝒯).map e) := he
    have : Algebra.Etale (limit f) C := by
      have h1 : ((𝒯).map e).appTop.hom.Etale := HasRingHomProperty.appTop @Etale ((𝒯).map e) he
      have h2 : (Scheme.ΓSpecIso (.of (limit f))).inv.hom.Etale :=
        RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)
      exact RingHom.Etale.stableUnderComposition _ _ h2 h1
    let γ : ∀ m, Γ((𝒯).obj (specSite B hZ (R m) (hR m)), ⊤) ≅ CommRingCat.of (R m) :=
      fun m => Scheme.ΓSpecIso _
    have hQ : ∀ n, IsAffine ((𝒯).obj (Q n)) := fun n => .of_isPullback (hpb n)
    have hsq1 : ∀ n, IsPushout (CommRingCat.ofHom (algebraMap (limit f) C))
        (CommRingCat.ofHom (algebraMap (limit f) (R n))) ((𝒯).map (a n)).appTop
        ((γ n).inv ≫ ((𝒯).map (b n)).appTop) := fun n => by
      have := hQ n
      have h := isPushout_appTop_of_isPullback (hpb n)
      refine h.of_iso (Scheme.ΓSpecIso (.of (limit f))) (Iso.refl _) (γ n)
        (Iso.refl _) ?_ ?_ ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id, RingHom.algebraMap_toAlgebra, φ,
          CommRingCat.ofHom_hom]
        exact (Iso.hom_inv_id_assoc _ _).symm
      · exact Scheme.ΓSpecIso_naturality _
      · simp
      · simp only [Iso.refl_hom, Category.comp_id]
        exact (Iso.hom_inv_id_assoc _ _).symm
    let ε : ∀ n,
        Γ((𝒯).obj (Q n), ⊤) ≅ CommRingCat.of (TensorProduct (SquareZeroTower.limit f) C (R n)) :=
      fun n => (hsq1 n).isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct (limit f) C (R n))
    have hε : ∀ n, ((𝒯).map (a n)).appTop ≫ (ε n).hom =
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := fun n =>
      IsPushout.inl_isoIsPushout_hom _ _ (hsq1 n) _
    have hε' : ∀ n, ((γ n).inv ≫ ((𝒯).map (b n)).appTop) ≫ (ε n).hom =
        CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom := fun n =>
      IsPushout.inr_isoIsPushout_hom _ _ (hsq1 n) _
    let T := fun n => (Algebra.TensorProduct.map (AlgHom.id (limit f) C)
      (towerTransitionAlgHom f n)).toRingHom
    have htrans : ∀ n, ((𝒯).map (c n)).appTop ≫ (ε n).hom =
        (ε (n + 1)).hom ≫ CommRingCat.ofHom (T n) := fun n => by
      apply (hsq1 (n + 1)).hom_ext
      · rw [← Category.assoc, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, hca, hε,
          ← Category.assoc, hε]
        ext x
        simp [T]
        rfl
      · have h1 := congrArg (fun k => ((𝒯).map k).appTop) (hcb n)
        have h2 : (γ (n + 1)).inv ≫
            ((𝒯).map (BigFppfOver.liftOfIntegers (Spec.map (CommRingCat.ofHom (f n))) :
              specSite B hZ (R n) (hR n) ⟶ specSite B hZ (R (n + 1)) (hR (n + 1)))).appTop =
            CommRingCat.ofHom (f n) ≫ (γ n).inv :=
          (Scheme.ΓSpecIso_inv_naturality _).symm
        simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at h1
        ext x
        have e1 := ConcreteCategory.congr_hom h1 ((γ (n + 1)).inv x)
        have e2 := ConcreteCategory.congr_hom h2 x
        have e3 : (ε n).hom (((𝒯).map (b n)).appTop ((γ n).inv (f n x))) =
            (1 : C) ⊗ₜ[limit f] (f n x) := ConcreteCategory.congr_hom (hε' n) (f n x)
        have e4 : (ε (n + 1)).hom (((𝒯).map (b (n + 1))).appTop ((γ (n + 1)).inv x)) =
            (1 : C) ⊗ₜ[limit f] x := ConcreteCategory.congr_hom (hε' (n + 1)) x
        simp only [CommRingCat.comp_apply] at e1 e2
        change (ε n).hom (((𝒯).map (c n)).appTop (((𝒯).map (b (n + 1))).appTop
            ((γ (n + 1)).inv x))) = (CommRingCat.ofHom (T n)) ((ε (n + 1)).hom
            (((𝒯).map (b (n + 1))).appTop ((γ (n + 1)).inv x)))
        rw [e1, e4]
        refine (congrArg (fun y => (ε n).hom (((𝒯).map (b n)).appTop y)) e2).trans ?_
        refine e3.trans ?_
        simp [T, towerTransitionAlgHom]
        rfl
    have hs' : ∀ n, T n ((ε (n + 1)).hom (s (n + 1))) = (ε n).hom (s n) := fun n => by
      rw [← hs n]
      exact (ConcreteCategory.congr_hom (htrans n) (s (n + 1))).symm
    obtain ⟨g, hg, hgu⟩ := hB C (fun n => (ε n).hom (s n)) hs'
    have key : ∀ (x : C) n,
        ((𝒯).map (a n)).appTop x = s n ↔ x ⊗ₜ[limit f] (1 : R n) = (ε n).hom (s n) := by
      intro x n
      rw [← (ConcreteCategory.bijective_of_isIso (ε n).hom).1.eq_iff, ← CommRingCat.comp_apply,
        hε n]
      rfl
    refine ⟨g, fun n => (key g n).2 (hg n), fun y hy => hgu y fun n => (key y n).1 (hy n)⟩

end AlgebraicGeometry.C1590Private

end
