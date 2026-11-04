module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel

/-!
# Stacks 0CQG for a tower identified with the restrictions of the terms

[Stacks, Tag 0CQG] (`StacksDraft.DerivedInverseLimit.derivedLimit_isPerfect_and_baseChange_iso`)
is stated for the derived-limit triangle of the system `n ↦ Kₙ` restricted to the limit ring
`A = lim Aₙ`, with transitions `Kₙ₊₁ ⟶ Kₙ` read through the composition of derived restrictions
of scalars. Here the triangle is given for an arbitrary system `(Pₙ)` of `D(A)`, together with
isomorphisms `Pₙ ≅ Kₙ` (restricted to `A`) compatible with the transitions.

## Main results

* `CategoryTheory.Pretriangulated.exists_mem_distTriang_pi_map_of_iso`: a derived-limit triangle
  can be transported along an isomorphism of inverse systems.
* `StacksDraft.DerivedInverseLimit.isPerfect_and_isIso_derivedBaseChangeComparison_of_iso`:
  Stacks 0CQG for such a system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory.Pretriangulated

universe v w

variable {C : Type w} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A derived-limit triangle transported along an isomorphism of inverse systems**: if
`K ⟶ ∏ Pₙ ⟶ ∏ Pₙ ⟶ K⟦1⟧` is distinguished with the difference map of the transitions `sₙ`, and
`ψₙ : Pₙ ≅ Xₙ` carry `sₙ` to `tₙ`, then `K ⟶ ∏ Xₙ ⟶ ∏ Xₙ ⟶ K⟦1⟧` is distinguished with the
difference map of the `tₙ`, for some connecting map. -/
theorem exists_mem_distTriang_pi_map_of_iso (P X : ℕ → C) [HasProduct P] [HasProduct X]
    (s : ∀ n : ℕ, P (n + 1) ⟶ P n) (t : ∀ n : ℕ, X (n + 1) ⟶ X n) (ψ : ∀ n : ℕ, P n ≅ X n)
    (hψ : ∀ n : ℕ, s n ≫ (ψ n).hom = (ψ (n + 1)).hom ≫ t n) {K : C} (p : K ⟶ ∏ᶜ P)
    (δ : (∏ᶜ P) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π P n - Pi.π P (n + 1) ≫ s n) δ ∈
      distTriang C) :
    ∃ δ' : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk (p ≫ Limits.Pi.map fun n : ℕ => (ψ n).hom)
        (Pi.lift fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫ t n) δ' ∈ distTriang C := by
  let e : (∏ᶜ P) ≅ ∏ᶜ X :=
    { hom := Limits.Pi.map fun n => (ψ n).hom
      inv := Limits.Pi.map fun n => (ψ n).inv
      hom_inv_id := Pi.hom_ext _ _ fun n => by simp
      inv_hom_id := Pi.hom_ext _ _ fun n => by simp }
  have ht : ∀ n : ℕ, t n ≫ (ψ n).inv = (ψ (n + 1)).inv ≫ s n := fun n => by
    rw [Iso.comp_inv_eq, Category.assoc, hψ, Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ δ, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_)⟩
  · exact Pi.hom_ext _ _ fun n => by simp [e]
  · exact Pi.hom_ext _ _ fun n => by simp [e, ht]
  · simp

end CategoryTheory.Pretriangulated

namespace StacksDraft.DerivedInverseLimit

universe u

variable (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A)
  (Kₙ : ∀ n : ℕ, StacksDraft.ringDerivedCategory (A.obj (op n)))
  (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
    (StacksDraft.ringRestrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).obj (Kₙ n))

/-- **Stacks 0CQG for a system identified with the restrictions of the terms.** For a tower of
rings with surjective transitions and locally nilpotent kernels, perfect `Kₙ` whose transitions
become isomorphisms after derived base change, a system `(Pₙ)` of `D(A)` with isomorphisms
`ψₙ : Pₙ ≅ Kₙ` (restricted to `A`) carrying its transitions to those of the `Kₙ`, and a
distinguished triangle `K ⟶ ∏ Pₙ ⟶ ∏ Pₙ ⟶ K⟦1⟧` with the difference map: `K` is perfect and
the base change map adjoint to `K ⟶ Pₙ ≅ Kₙ` is an isomorphism for every `n`. -/
theorem isPerfect_and_isIso_derivedBaseChangeComparison_of_iso (hc : IsLimit c)
    (hSurjective : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hLocallyNilpotent : ∀ n : ℕ,
      (RingHom.ker (A.map (homOfLE (Nat.le_succ n)).op).hom).IsLocallyNilpotent)
    (hPerfect : ∀ n : ℕ, StacksDraft.ringIsPerfect (Kₙ n))
    (hBaseChange : ∀ n : ℕ, IsIso (derivedBaseChangeComparison.{u, u, u}
      (A.map (homOfLE (Nat.le_succ n)).op).hom (φ n)))
    (P : ℕ → StacksDraft.ringDerivedCategory c.pt) [HasProduct P]
    (s : ∀ n : ℕ, P (n + 1) ⟶ P n)
    (ψ : ∀ n : ℕ, P n ≅ (StacksDraft.ringRestrictScalars (c.π.app (op n)).hom).obj (Kₙ n))
    (hψ : ∀ n : ℕ, s n ≫ (ψ n).hom = (ψ (n + 1)).hom ≫
      (StacksDraft.ringRestrictScalars (c.π.app (op (n + 1))).hom).map (φ n) ≫
        (derivedRestrictScalarsComp.{u, u} (c.π.app (op (n + 1))).hom
          (A.map (homOfLE (Nat.le_succ n)).op).hom (c.π.app (op n)).hom
          (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)).symm).hom.app (Kₙ n))
    (K : StacksDraft.ringDerivedCategory c.pt) (p : K ⟶ ∏ᶜ P) (δ : (∏ᶜ P) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ => Pi.π P n - Pi.π P (n + 1) ≫ s n) δ ∈
      distTriang (StacksDraft.ringDerivedCategory c.pt)) :
    StacksDraft.ringIsPerfect K ∧ ∀ n : ℕ, IsIso (derivedBaseChangeComparison.{u, u, u}
      (c.π.app (op n)).hom (p ≫ Pi.π P n ≫ (ψ n).hom)) := by
  let X : ℕ → StacksDraft.ringDerivedCategory c.pt := fun n =>
    (StacksDraft.ringRestrictScalars (c.π.app (op n)).hom).obj (Kₙ n)
  have : HasProduct X := hasLimit_of_iso (F := Discrete.functor P) (G := Discrete.functor X)
    (Discrete.natIso fun i => ψ i.as)
  obtain ⟨δ', hT'⟩ := exists_mem_distTriang_pi_map_of_iso P X s _ ψ hψ p δ hT
  have h := derivedLimit_isPerfect_and_baseChange_iso.{u, u} A c hc Kₙ φ hSurjective
    hLocallyNilpotent (Or.inl hPerfect) hBaseChange K (p ≫ Limits.Pi.map fun n => (ψ n).hom) δ' hT'
  refine ⟨h.1, fun n => ?_⟩
  have e : (p ≫ Limits.Pi.map fun n => (ψ n).hom) ≫ Pi.π X n = p ≫ Pi.π P n ≫ (ψ n).hom := by
    rw [Category.assoc, Limits.Pi.map_π]
  exact e ▸ h.2 n

end StacksDraft.DerivedInverseLimit
