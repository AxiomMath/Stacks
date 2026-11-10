module

public import Mathlib.CategoryTheory.Galois.Full
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.Tactic.Group

/-!
# A connected object with a normal stabilizer is Galois

Let `F` be a fibre functor on a Galois category and `Z` a connected object. If `Aut F` acts
transitively on `F(Z)` and the stabilizer of one point `z ∈ F(Z)` is a normal subgroup of `Aut F`,
then `Z` is Galois.

## Main results

* `CategoryTheory.PreGaloisCategory.isGalois_of_stabilizer_conj_mem`.
-/

@[expose] public noncomputable section

universe u

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category* C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u}) [FiberFunctor F]

/-- **A connected object with a normal stabilizer is Galois.** If `Aut F` acts transitively on
`F(Z)` and the stabilizer of a point `z` is stable under conjugation, then `Z` is Galois. -/
theorem isGalois_of_stabilizer_conj_mem (Z : C) [IsConnected Z] (z : F.obj Z)
    (htrans : ∀ y : F.obj Z, ∃ σ : Aut F, σ • z = y)
    (hnorm : ∀ g h : Aut F, g • z = z → (h⁻¹ * g * h) • z = z) : IsGalois Z := by
  classical
  choose s hs using htrans
  have hstab : ∀ a b : Aut F, a • z = b • z → ∀ h : Aut F, (a * h) • z = (b * h) • z := by
    intro a b hab h
    have h1 : (b⁻¹ * a) • z = z := by rw [mul_smul, hab, ← mul_smul, inv_mul_cancel, one_smul]
    calc (a * h) • z = (b * h) • ((h⁻¹ * (b⁻¹ * a) * h) • z) := by
          rw [← mul_smul]; congr 1; group
      _ = (b * h) • z := by rw [hnorm _ h h1]
  let φ : Aut F → (F.obj Z → F.obj Z) := fun h y => (s y * h) • z
  have hφeq : ∀ (h g : Aut F) (y : F.obj Z), φ h (g • y) = g • φ h y := by
    intro h g y
    change (s (g • y) * h) • z = g • ((s y * h) • z)
    rw [← mul_smul, ← mul_assoc]
    refine hstab _ _ ?_ h
    rw [hs, mul_smul, hs]
  have hφz : ∀ h : Aut F, φ h z = h • z := by
    intro h
    change (s z * h) • z = h • z
    simpa only [one_mul] using hstab (s z) 1 (by rw [hs, one_smul]) h
  have hφinj : ∀ h : Aut F, Function.Injective (φ h) := by
    intro h y y' hyy
    have h1 := hstab _ _ hyy h⁻¹
    simp only [mul_inv_cancel_right] at h1
    rw [← hs y, ← hs y', h1]
  have hlift : ∀ h : Aut F, ∃ σ : Aut Z, ∀ y : F.obj Z, F.map σ.asIso.hom y = φ h y := by
    intro h
    let m : (functorToAction F).obj Z ⟶ (functorToAction F).obj Z :=
      { hom := FintypeCat.homMk (φ h)
        comm := fun g => by
          ext y
          exact hφeq h g y }
    obtain ⟨f, hf⟩ := (functorToAction F).map_surjective m
    have hfy (y) : F.map f y = φ h y := congrArg (fun t => t.hom y) hf
    have : IsIso (F.map f) := (ConcreteCategory.isIso_iff_bijective _).2
      (Finite.injective_iff_bijective.1 fun a b hab => hφinj h (by rwa [hfy, hfy] at hab))
    have : IsIso f := isIso_of_reflects_iso f F
    exact ⟨.of (asIso f), hfy⟩
  choose σ hσ using hlift
  rw [isGalois_iff_pretransitive F Z]
  refine ⟨fun a b => ?_⟩
  set τ : Aut Z := σ ((s a)⁻¹ * s b)
  refine ⟨τ, ?_⟩
  change F.map τ.asIso.hom a = b
  calc F.map τ.asIso.hom a = F.map τ.asIso.hom (s a • z) := by rw [hs]
    _ = s a • F.map τ.asIso.hom z :=
      (congrArg (fun t => t z) ((s a).asIso.hom.naturality τ.asIso.hom)).symm
    _ = b := by rw [hσ, hφz, ← mul_smul, mul_inv_cancel_left, hs]

end CategoryTheory.PreGaloisCategory

end
