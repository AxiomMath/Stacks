module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Filtered colimits of localizations away from an element

A filtered colimit of commutative rings is computed elementwise: every element of the colimit
comes from some stage of the diagram, and two elements of one stage become equal in the colimit
exactly when some transition map already identifies them. The two lemmas
`CommRingCat.FilteredColimits.exists_eq_ι_app` and
`CommRingCat.FilteredColimits.exists_map_eq` package these two facts for an arbitrary filtered
colimit cocone, rather than for Mathlib's concrete construction of it.

The main result is that localization away from an element commutes with filtered colimits. Let
`φ : A ⟶ B` be a morphism of filtered diagrams of commutative rings and let `r` be a compatible
family of elements of `A`, i.e. one element `r j : A j` for each index with `A f (r i) = r j` for
every transition map `f : i ⟶ j`. If each `B j` is the localization of `A j` away from `r j`, then
`colim B` is the localization of `colim A` away from the image of `r`.

## Main results

* `CommRingCat.FilteredColimits.exists_eq_ι_app`: a filtered colimit of commutative rings is
  covered by its stages.
* `CommRingCat.FilteredColimits.exists_map_eq`: two elements of one stage that agree in a filtered
  colimit already agree after some transition map.
* `CommRingCat.FilteredColimits.isLocalizationAway_of_isColimit`: a filtered colimit of
  localizations away from a compatible family of elements is the localization away from the image
  of that family.

## Implementation notes

The statements are phrased for arbitrary colimit cocones witnessed by `IsColimit`, and the
`Algebra` structures are the ones induced by the given ring morphisms via `RingHom.toAlgebra`, so
that the result can be applied to the colimit cocones that occur in practice without first
identifying them with Mathlib's model.

The element whose powers are inverted is `cA.ι.app j₀ (r j₀)` for an arbitrary chosen index `j₀`;
it is independent of that choice precisely because `r` is a compatible family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat.FilteredColimits

variable {J : Type u} [Category.{u} J] [IsFiltered J] {A : J ⥤ CommRingCat.{u}}

/-- Every element of a filtered colimit of commutative rings comes from a stage of the diagram. -/
theorem exists_eq_ι_app {c : Cocone A} (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : A.obj j), (c.ι.app j y : c.pt) = x := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) hc) x
  exact ⟨j, y, hy⟩

/-- Two elements of one stage of a filtered diagram of commutative rings that have the same image
in the colimit are already identified by some transition map. -/
theorem exists_map_eq {c : Cocone A} (hc : IsColimit c) {j : J} {x y : A.obj j}
    (h : (c.ι.app j x : c.pt) = c.ι.app j y) :
    ∃ (k : J) (f : j ⟶ k), A.map f x = A.map f y :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat.{u}) hc) x y).mp h

/-- Localization away from an element commutes with filtered colimits.

Let `φ : A ⟶ B` be a morphism between filtered diagrams of commutative rings, let `r` be a
compatible family of elements of `A`, and suppose that `B j` is the localization of `A j` away
from `r j` for every `j`. Then the colimit of `B` is the localization of the colimit of `A` away
from the image of `r`. -/
theorem isLocalizationAway_of_isColimit {B : J ⥤ CommRingCat.{u}} (φ : A ⟶ B)
    {cA : Cocone A} (hA : IsColimit cA) {cB : Cocone B} (hB : IsColimit cB)
    (ψ : cA.pt ⟶ cB.pt) (hψ : ∀ j, cA.ι.app j ≫ ψ = φ.app j ≫ cB.ι.app j)
    (r : ∀ j, A.obj j) (hr : ∀ {i j : J} (f : i ⟶ j), A.map f (r i) = r j)
    (H : ∀ j, letI := (φ.app j).hom.toAlgebra; IsLocalization.Away (r j) (B.obj j))
    (j₀ : J) :
    letI := ψ.hom.toAlgebra
    IsLocalization.Away (R := cA.pt) (cA.ι.app j₀ (r j₀)) cB.pt := by
  let algB : ∀ j, Algebra (A.obj j) (B.obj j) := fun j ↦ (φ.app j).hom.toAlgebra
  let _ := ψ.hom.toAlgebra
  have hmapB (j : J) (x : A.obj j) : algebraMap (A.obj j) (B.obj j) x = φ.app j x := rfl
  have hmap (x : cA.pt) : algebraMap cA.pt cB.pt x = ψ x := rfl
  have hψ' (j : J) (x : A.obj j) : (ψ (cA.ι.app j x) : cB.pt) = cB.ι.app j (φ.app j x) := by
    simpa using congr($(hψ j) x)
  have hιA {i j : J} (f : i ⟶ j) (x : A.obj i) :
      (cA.ι.app j (A.map f x) : cA.pt) = cA.ι.app i x := by simp
  have hιB {i j : J} (f : i ⟶ j) (x : B.obj i) :
      (cB.ι.app j (B.map f x) : cB.pt) = cB.ι.app i x := by simp
  have hρ (j : J) (f : j₀ ⟶ j) :
      (cA.ι.app j (r j) : cA.pt) = cA.ι.app j₀ (r j₀) := by rw [← hr f, hιA]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨-, n, rfl⟩
    rw [hmap, map_pow]
    refine IsUnit.pow _ ?_
    rw [hψ']
    exact (IsLocalization.map_units (M := Submonoid.powers (r j₀)) (B.obj j₀)
      ⟨r j₀, 1, pow_one _⟩).map (cB.ι.app j₀).hom
  · intro z
    obtain ⟨j, z₀, hz₀⟩ := exists_eq_ι_app hB z
    obtain ⟨k, u, v, -⟩ : ∃ (k : J) (_ : j₀ ⟶ k) (_ : j ⟶ k), True :=
      ⟨IsFiltered.max j₀ j, IsFiltered.leftToMax _ _, IsFiltered.rightToMax _ _, trivial⟩
    obtain ⟨⟨a, -, n, rfl⟩, ha⟩ := IsLocalization.surj (M := Submonoid.powers (r k)) (B.map v z₀)
    have ha' : B.map v z₀ * φ.app k (r k ^ n) = φ.app k a := ha
    refine ⟨⟨cA.ι.app k a, _, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩, ?_⟩
    change z * algebraMap cA.pt cB.pt ((cA.ι.app j₀ (r j₀) : cA.pt) ^ n)
        = algebraMap cA.pt cB.pt (cA.ι.app k a)
    rw [hmap, hmap, ← hz₀, ← hιB v z₀, map_pow, ← hρ k u, hψ', hψ', ← map_pow, ← map_mul,
      ← map_pow, ha']
  · intro x y h
    obtain ⟨j₁, x₀, hx₀⟩ := exists_eq_ι_app hA x
    obtain ⟨j₂, y₀, hy₀⟩ := exists_eq_ι_app hA y
    obtain ⟨k, u, p, q, -⟩ : ∃ (k : J) (_ : j₀ ⟶ k) (_ : j₁ ⟶ k) (_ : j₂ ⟶ k), True :=
      ⟨IsFiltered.max (IsFiltered.max j₀ j₁) j₂,
        IsFiltered.leftToMax _ _ ≫ IsFiltered.leftToMax _ _,
        IsFiltered.rightToMax _ _ ≫ IsFiltered.leftToMax _ _, IsFiltered.rightToMax _ _, trivial⟩
    rw [← hx₀, ← hy₀, hmap, hmap, ← hιA p x₀, ← hιA q y₀, hψ', hψ'] at h
    obtain ⟨m, w, hw⟩ := exists_map_eq hB h
    have hw' : φ.app m (A.map w (A.map p x₀)) = φ.app m (A.map w (A.map q y₀)) := by
      simpa using hw
    obtain ⟨⟨-, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (r m))
      (S := B.obj m) (x := A.map w (A.map p x₀)) (y := A.map w (A.map q y₀))
      (by rw [hmapB, hmapB]; exact hw')
    have hn' : r m ^ n * A.map w (A.map p x₀) = r m ^ n * A.map w (A.map q y₀) := hn
    have key (c : cA.pt) (hc : c = (cA.ι.app j₀ (r j₀) : cA.pt) ^ n) : c * x = c * y := by
      subst hc
      rw [← hx₀, ← hy₀, ← hιA p x₀, ← hιA q y₀, ← hιA w (A.map p x₀), ← hιA w (A.map q y₀),
        ← hρ m (u ≫ w), ← map_pow, ← map_mul, ← map_mul, hn']
    exact ⟨⟨_, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩, key _ rfl⟩

end CommRingCat.FilteredColimits

end
