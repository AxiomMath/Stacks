module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp

/-!
# Stacks 0CQF for a tower given up to isomorphism

[Stacks, Tag 0CQF]
(`StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso`) is stated
for a derived limit of the tower `n ↦ res_{A ← Aₙ} Kₙ` in `D(A)`, with the transition maps
restricted from the `φₙ : Kₙ₊₁ ⟶ res Kₙ`. In applications the derived limit is usually that of
another tower `(Yₙ, sₙ)` of `D(A)` (for instance the image under a triangulated right adjoint of
a tower of sheaves), known to be isomorphic to that one through isomorphisms `eₙ : Yₙ ≅ res Kₙ`
compatible with the transitions. This file transports 0CQF along such an isomorphism of towers.

## Main results

* `StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso_of_iso`:
  every derived limit of `(Yₙ, sₙ)` is pseudo-coherent, and the base-change map of its projection
  to `Yₙ` followed by `eₙ` is an isomorphism for every `n`.

* `StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison_eq_adjunction_homEquiv_symm`:
  the base-change map of 0CQF is the transpose under the adjunction
  `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.adjunction` of the chosen
  derived extension of scalars.

## References

* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite CategoryTheory.Pretriangulated

namespace StacksDraft.DerivedInverseLimit

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The base-change map of 0CQF is the transpose of the given map under the adjunction of the
chosen derived extension of scalars, `TotalDerivedExtensionScalars.adjunction`. -/
theorem derivedBaseChangeComparison_eq_adjunction_homEquiv_symm
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {X : DerivedCategory (ModuleCat.{u} R)} {Y : DerivedCategory (ModuleCat.{u} S)}
    (g : X ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) :
    derivedBaseChangeComparison.{u, u, u} f g =
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).adjunction.homEquiv X Y).symm g :=
  rfl

/-- **[Stacks, Tag 0CQF] for a tower isomorphic to the restricted one.** In the situation of
`derivedLimit_isPseudoCoherent_and_baseChange_iso`, let `(Yₙ, sₙ)` be a tower of `D(A)` with
isomorphisms `eₙ : Yₙ ≅ res_{A ← Aₙ} Kₙ` carrying `sₙ` to the restricted transition of `φₙ`.
Then every derived limit `K` of `(Yₙ, sₙ)`, with structure map `p : K ⟶ ∏ Yₙ`, is pseudo-coherent,
and the base-change map `K ⊗^L_A Aₙ ⟶ Kₙ` adjoint to `p ≫ πₙ ≫ eₙ` is an isomorphism. -/
theorem derivedLimit_isPseudoCoherent_and_baseChange_iso_of_iso
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A.obj (op n))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj
        (Kₙ n))
    (hSurjective : ∀ n : ℕ,
      Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hLocallyNilpotent : ∀ n : ℕ,
      (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (hPseudoCoherent : (∀ n : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n)) ∨
      ∃ n₀ : ℕ, PseudoCoherence.IsPseudoCoherent (Kₙ n₀) ∧
        ∀ n : ℕ, n₀ ≤ n →
          IsNilpotent (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom))
    (hBaseChange : ∀ n : ℕ,
      IsIso (derivedBaseChangeComparison (A.map (homOfLE (Nat.le_succ n)).op).hom (φ n)))
    (Y : ℕ → DerivedCategory (ModuleCat.{max u v} c.pt)) (s : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (e : ∀ n : ℕ, Y n ≅
      (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategory.obj (Kₙ n))
    (he : ∀ n : ℕ, s n ≫ (e n).hom = (e (n + 1)).hom ≫
      ((ModuleCat.restrictScalars (c.π.app (op (n + 1))).hom).mapDerivedCategory.map (φ n) ≫
        (derivedRestrictScalarsComp (c.π.app (op (n + 1))).hom
          (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
          (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app
            (Kₙ n)))
    [HasProduct Y] (K : DerivedCategory (ModuleCat.{max u v} c.pt))
    (p : K ⟶ ∏ᶜ Y) (δ : ∏ᶜ Y ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ s n) δ ∈
      distTriang (DerivedCategory (ModuleCat.{max u v} c.pt))) :
    PseudoCoherence.IsPseudoCoherent K ∧ ∀ n : ℕ,
      IsIso (derivedBaseChangeComparison (c.π.app (op n)).hom (p ≫ Pi.π Y n ≫ (e n).hom)) := by
  let X : ℕ → DerivedCategory (ModuleCat.{max u v} c.pt) := fun n ↦
    (ModuleCat.restrictScalars (c.π.app (op n)).hom).mapDerivedCategory.obj (Kₙ n)
  let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    (ModuleCat.restrictScalars (c.π.app (op (n + 1))).hom).mapDerivedCategory.map (φ n) ≫
      (derivedRestrictScalarsComp (c.π.app (op (n + 1))).hom
        (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
        (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (Kₙ n)
  have : HasProduct X :=
    hasLimit_of_iso (F := Discrete.functor Y) (Discrete.natIso fun n ↦ e n.as)
  let E : (∏ᶜ Y) ≅ ∏ᶜ X := Pi.mapIso e
  have hEπ : ∀ n : ℕ, E.hom ≫ Pi.π X n = Pi.π Y n ≫ (e n).hom := fun n ↦ by
    simp [E]
  have hd : (Pi.lift fun n : ℕ ↦ Pi.π Y n - Pi.π Y (n + 1) ≫ s n) ≫ E.hom =
      E.hom ≫ Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp only [Category.assoc, hEπ, Pi.lift_comp_π_assoc, Pi.lift_comp_π, Preadditive.sub_comp,
      Preadditive.comp_sub, reassoc_of% hEπ]
    rw [he n]
  have hT' : Triangle.mk (p ≫ E.hom)
      (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) (E.inv ≫ δ) ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} c.pt)) := by
    refine isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) E.symm E.symm ?_ ?_ ?_)
    · simp
    · dsimp
      rw [← cancel_epi E.hom, E.hom_inv_id_assoc, ← reassoc_of% hd, E.hom_inv_id,
        Category.comp_id]
    · simp
  obtain ⟨h₁, h₂⟩ := derivedLimit_isPseudoCoherent_and_baseChange_iso A c hc Kₙ φ hSurjective
    hLocallyNilpotent hPseudoCoherent hBaseChange K (p ≫ E.hom) (E.inv ≫ δ) hT'
  refine ⟨h₁, fun n ↦ ?_⟩
  have h := h₂ n
  rwa [Category.assoc, hEπ] at h

end StacksDraft.DerivedInverseLimit
