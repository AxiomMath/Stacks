module

public import StacksFrontier.Deformation.Artin.FormalObject.TruncationPullback
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationFullyFaithful

/-!
# Morphisms over a finite cover of a complete local base, from the thickenings

Let `p` be a category fibred in groupoids over the big fppf site of `S` whose isomorphism
presheaves are algebraic spaces (condition (2) of **Stacks 045G**), and let `M` be an object of
the site with a finite morphism `M ⟶ Spec R` to the spectrum of a Noetherian complete local base.
A morphism of `p` from an object over `M` is determined by, and can be assembled from, its
restrictions to the base changes `M ×_{Spec R} Spec (R / 𝔪 ^ (n + 1))` of the infinitesimal
thickenings of the closed point.

The target of the morphisms is arbitrary: they lie over a given morphism `M ⟶ Y` of the site.

## Main results

* `Deformation.Artin.existsUnique_hom_over_of_compatible_truncations_of_finite`: the statement for
  an object of the site identified with the spectrum of a finite `R`-algebra.
* `Deformation.Artin.existsUnique_hom_over_of_truncations`: the statement for an object of the
  site finite over the spectrum of a complete local base, with the base-changed thickenings.
* `Deformation.Artin.hom_ext_of_truncations`: the uniqueness half.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms over the spectrum of a finite algebra over a complete local ring, from the
truncations**, with an arbitrary target lying over a given morphism of the site. -/
theorem existsUnique_hom_over_of_compatible_truncations_of_finite [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hI : IsAlgebraicSpaceIsom p) (U : BigFppfOver B S hS)
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    {A : Type u} [CommRing A] [Algebra R A] [Module.Finite R A]
    (eT : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of A))
    (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅
      Spec (.of (A ⧸ (maximalIdeal R ^ (n + 1)).map (algebraMap R A))))
    (ι : ∀ n, W n ⟶ U)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((maximalIdeal R ^ (n + 1)).map (algebraMap R A)))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    {x : F} (hx : p.obj x = U) {Y : BigFppfOver B S hS} (m : U ⟶ Y) {y : F} (hy : p.obj y = Y)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x) [∀ n, p.IsHomLift (ι n) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (τ n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    (ψ : ∀ n, z n ⟶ y) [∀ n, p.IsHomLift (ι n ≫ m) (ψ n)]
    (hψ : ∀ n, t n ≫ ψ (n + 1) = ψ n) :
    ∃! φ : x ⟶ y, p.IsHomLift m φ ∧ ∀ n, r n ≫ φ = ψ n := by
  obtain ⟨y', c, hc⟩ := hp.exists_lift' m y hy
  have hy' : p.obj y' = U := IsHomLift.domain_eq p m c
  let ψ' : ∀ n, z n ⟶ y' := fun n => hp.fill (f := m) (g := ι n) rfl c (ψ n)
  have hψ'l : ∀ n, p.IsHomLift (ι n) (ψ' n) := fun n => hp.fill_isHomLift _ _ _
  have hψ'c : ∀ n, ψ' n ≫ c = ψ n := fun n => hp.fill_fac _ _ _
  have hψ' : ∀ n, t n ≫ ψ' (n + 1) = ψ' n := fun n => by
    have : p.IsHomLift (ι n) (t n ≫ ψ' (n + 1)) := by
      have := hψ'l (n + 1)
      have : p.IsHomLift (τ n ≫ ι (n + 1)) (t n ≫ ψ' (n + 1)) := inferInstance
      rwa [hτ] at this
    have := hψ'l n
    refine hp.hom_ext (f := m) (ι n) c ?_
    rw [Category.assoc, hψ'c, hψ'c, hψ]
  obtain ⟨φ₀, ⟨hφ₀, hrφ₀⟩, huniq⟩ := Stack.existsUnique_hom_of_compatible_truncations_of_finite
    p hp U ⟨x, hx⟩ ⟨y', hy'⟩ (hI U ⟨x, hx⟩ ⟨y', hy'⟩) hR eT W eW ι hι τ hτ z r t ht ψ' hψ'
  refine ⟨φ₀ ≫ c, ⟨?_, fun n => ?_⟩, fun φ ⟨hφ, hrφ⟩ => ?_⟩
  · have : p.IsHomLift (𝟙 U ≫ m) (φ₀ ≫ c) := inferInstance
    simpa using this
  · rw [← Category.assoc, hrφ₀, hψ'c]
  · let φ' := hp.fill (f := m) (g := 𝟙 U) (f' := m) (by simp) c φ
    have hφ'l : p.IsHomLift (𝟙 U) φ' := hp.fill_isHomLift _ _ _
    have hφ'c : φ' ≫ c = φ := hp.fill_fac _ _ _
    have : φ' = φ₀ := huniq φ' ⟨hφ'l, fun n => by
      have := hψ'l n
      have : p.IsHomLift (ι n ≫ 𝟙 U) (r n ≫ φ') := inferInstance
      have : p.IsHomLift (ι n) (r n ≫ φ') := by simpa using this
      refine hp.hom_ext (f := m) (ι n) c ?_
      rw [Category.assoc, hφ'c, hψ'c, hrφ]⟩
    show φ = φ₀ ≫ c
    rw [← this, hφ'c]

section Relative

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

variable (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))
  (c : ∀ n, B.Contains (A.truncation n))
  {M : BigFppfOver B S hS} (f : M ⟶ baseOver B S hS A hA)

/-- The transition maps between the base changes of consecutive thickenings. -/
abbrev truncationPullbackSucc (n : ℕ) :
    pullback f (restrictionToBase B S hS A hA c n) ⟶
      pullback f (restrictionToBase B S hS A hA c (n + 1)) :=
  pullback.map _ _ _ _ (𝟙 M) (truncationOverSucc B S hS A c n) (𝟙 _) (by simp)
    (by simp [restrictionToBase_succ])

/-- The transition map between consecutive base-changed thickenings commutes with the first
projection to `M`. -/
theorem truncationPullbackSucc_fst (n : ℕ) :
    truncationPullbackSucc A hA c f n ≫ pullback.fst _ _ = pullback.fst _ _ := by simp

/-- The transition map between consecutive base-changed thickenings lies over the transition map
`truncationOverSucc` between the thickenings. -/
theorem truncationPullbackSucc_snd (n : ℕ) :
    truncationPullbackSucc A hA c f n ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ truncationOverSucc B S hS A c n := by simp

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms over a finite cover of a complete local base, from the base-changed thickenings.**
Let `f : M ⟶ Spec R` be a morphism of the site, finite on schemes, to the spectrum of a complete
local base, and write `M_n = M ×_{Spec R} Spec (R / 𝔪 ^ (n + 1))`. A compatible family of
morphisms `ψ n : z n ⟶ y` from objects `z n` over `M_n` with compatible maps `r n` to an object
`x` over `M`, lying over the composites `M_n ⟶ M ⟶ Y`, is `r n ≫ φ` for a unique `φ : x ⟶ y`
over `M ⟶ Y`. -/
theorem existsUnique_hom_over_of_truncations [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (hI : IsAlgebraicSpaceIsom p) [IsFinite ((BigFppfOver.toScheme B S hS).map f)]
    {x : F} (hx : p.obj x = M) {Y : BigFppfOver B S hS} (m : M ⟶ Y) {y : F} (hy : p.obj y = Y)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x)
    [∀ n, p.IsHomLift (pullback.fst f (restrictionToBase B S hS A hA c n)) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (truncationPullbackSucc A hA c f n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    (ψ : ∀ n, z n ⟶ y)
    [∀ n, p.IsHomLift (pullback.fst f (restrictionToBase B S hS A hA c n) ≫ m) (ψ n)]
    (hψ : ∀ n, t n ≫ ψ (n + 1) = ψ n) :
    ∃! φ : x ⟶ y, p.IsHomLift m φ ∧ ∀ n, r n ≫ φ = ψ n := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj M) := by
    let g : (BigFppfOver.toScheme B S hS).obj M ⟶ Spec (.of A.R) :=
      (BigFppfOver.toScheme B S hS).map f
    have : IsFinite g := ‹_›
    exact isAffine_of_isAffineHom g
  let := globalSectionsAlgebra A hA f
  have := module_finite_globalSections A hA f
  have hR : IsNoetherianCompleteLocalRing A.R := ⟨A.noetherian, inferInstance, A.complete⟩
  choose eW heW using exists_iso_toScheme_pullback_restrictionToBase A hA c f
  exact existsUnique_hom_over_of_compatible_truncations_of_finite hp hI M hR
    ((BigFppfOver.toScheme B S hS).obj M).isoSpec _ eW (fun n => pullback.fst _ _) heW
    (truncationPullbackSucc A hA c f) (truncationPullbackSucc_fst A hA c f) hx m hy z r t ht ψ hψ

/-- **Uniqueness of morphisms over a finite cover of a complete local base, from the base-changed
thickenings.** -/
theorem hom_ext_of_truncations [p.IsFibered] (hp : p.IsFiberedInGroupoids)
    (hI : IsAlgebraicSpaceIsom p) [IsFinite ((BigFppfOver.toScheme B S hS).map f)]
    {x : F} (hx : p.obj x = M) {Y : BigFppfOver B S hS} (m : M ⟶ Y) {y : F} (hy : p.obj y = Y)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x)
    [∀ n, p.IsHomLift (pullback.fst f (restrictionToBase B S hS A hA c n)) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (truncationPullbackSucc A hA c f n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    {φ φ' : x ⟶ y} [p.IsHomLift m φ] [p.IsHomLift m φ'] (h : ∀ n, r n ≫ φ = r n ≫ φ') :
    φ = φ' := by
  obtain ⟨_, -, huniq⟩ := existsUnique_hom_over_of_truncations A hA c f hp hI hx m hy z r t ht
    (fun n => r n ≫ φ) (fun n => by rw [← Category.assoc, ht])
  exact (huniq φ ⟨inferInstance, fun _ => rfl⟩).trans
    (huniq φ' ⟨inferInstance, fun n => (h n).symm⟩).symm

end Relative

end Deformation.Artin

end
