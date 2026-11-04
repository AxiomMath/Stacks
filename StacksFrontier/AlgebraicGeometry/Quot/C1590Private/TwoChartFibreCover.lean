module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartGoodOfAmple
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyGoodDivisors
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite

/-!
# Two affine nonvanishing loci covering a family of curves near a fibre

Let `q : Z ⟶ T` be proper over an affine Noetherian scheme, `L` an ample invertible module on `Z`
and `u ∈ T` a point whose fibre has dimension at most one. Then there are two global sections
`σ`, `τ` of a positive tensor power of `L` with affine nonvanishing loci, and a basic open
`D(f) ∋ u` of `T`, such that `X_σ ∪ X_τ` contains `q⁻¹ D(f)`
(`AlgebraicGeometry.C1590Private.exists_sections_cover_near_fibre`).

The argument is the one of Stacks 0E6F's proof (and of
`StacksFrontier/AlgebraicGeometry/TwoAffineCech/CurveCover.lean` on a single curve), with sections of
an ample module in place of affine opens: the fibre `Z_u` is Noetherian, so its associated points
are finitely many, and Stacks 09NV gives `σ` with `X_σ` affine containing them. What `X_σ` misses
of the fibre is closed and contains no associated point, hence is finite because the fibre has
dimension at most one
(`AlgebraicGeometry.C1590Private.finite_of_isClosed_of_disjoint_schemeAssociatedPoints`), and
Stacks 09NV gives `τ` with `X_τ` affine containing it. The degrees are equalized by taking powers,
which does not move the nonvanishing loci. The complement of `X_σ ∪ X_τ` is closed with
closed image, `q` being proper, and that image misses `u`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.TensorPowerTrivialize Stacks.GradedSections

universe u

namespace AlgebraicGeometry.C1590Private

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Z : Scheme.{u}} (L : Z.Modules) [Stacks.Ample.IsInvertibleModule Z L]

/-- Transporting a section along an equality of degrees does not move its nonvanishing locus. -/
theorem nvOpen_cast {a b : ℕ} (h : a = b) (s : powSections L a) :
    Stacks.AmpleFiniteAvoidance.nvOpen L (h ▸ s) = Stacks.AmpleFiniteAvoidance.nvOpen L s := by
  subst h
  rfl

/-- **Two sections of one power of an ample module whose nonvanishing loci cover a set.** If
finite sets `E₁`, `E₂` lie in affine nonvanishing loci of sections of possibly different
positive powers, the powers can be equalized. -/
theorem exists_common_degree {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (σ₁ : powSections L d₁)
    (τ₁ : powSections L d₂) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (σ τ : powSections L n),
      Stacks.AmpleFiniteAvoidance.nvOpen L σ = Stacks.AmpleFiniteAvoidance.nvOpen L σ₁ ∧
      Stacks.AmpleFiniteAvoidance.nvOpen L τ = Stacks.AmpleFiniteAvoidance.nvOpen L τ₁ := by
  have heq : powDeg d₂ (d₁ - 1) = powDeg d₁ (d₂ - 1) := by
    rw [powDeg_eq, powDeg_eq, Nat.sub_add_cancel hd₁, Nat.sub_add_cancel hd₂, mul_comm]
  refine ⟨powDeg d₁ (d₂ - 1), ?_, sectionPow L σ₁ (d₂ - 1), heq ▸ sectionPow L τ₁ (d₁ - 1),
    nonvanishingOpen_sectionPow L σ₁ _, ?_⟩
  · rw [powDeg_eq, Nat.sub_add_cancel hd₂]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [nvOpen_cast]
    exact nonvanishingOpen_sectionPow L τ₁ _

variable {T : Scheme.{u}} (q : Z ⟶ T)

/-- **Two affine nonvanishing loci covering a neighbourhood of a fibre of dimension at most
one.** -/
theorem exists_sections_cover_near_fibre [IsAffine T] [IsLocallyNoetherian T] [IsProper q]
    (hL : Stacks.Ample.IsAmple Z L) (t : T) (hdim : topologicalKrullDim (q.fiber t) ≤ 1) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (σ τ : powSections L n),
      IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L σ) ∧
      IsAffineOpen (Stacks.AmpleFiniteAvoidance.nvOpen L τ) ∧
      ∃ f : Γ(T, ⊤), t ∈ T.basicOpen f ∧
        q ⁻¹ᵁ T.basicOpen f ≤
          Stacks.AmpleFiniteAvoidance.nvOpen L σ ⊔ Stacks.AmpleFiniteAvoidance.nvOpen L τ := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  have : LocallyOfFiniteType (q.fiberToSpecResidueField t) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd q (T.fromSpecResidueField t)))
  have : IsLocallyNoetherian (q.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (q.fiberToSpecResidueField t)
  have : IsNoetherian (q.fiber t) := {}
  set ι := q.fiberι t
  have hAss : (Stacks.Divisors.schemeAssociatedPoints (q.fiber t)).Finite := by
    have h := associatedPoints_inter_finite
      (SheafOfModules.unit (q.fiber t).ringCatSheaf) ⊤
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set (q.fiber t))))
    simpa [Stacks.Divisors.schemeAssociatedPoints] using h
  -- the first section, through the associated points of the fibre
  obtain ⟨d₁, σ₁, hd₁, hE₁, -, hσ₁⟩ :=
    Stacks.SectionExtension.exists_affine_nvOpen_containing_finite_le_of_isAmple L hL
      (hAss.image ι) ⊤ (fun _ _ => trivial)
  -- what it misses of the fibre is finite
  set C : Set (q.fiber t) := ι ⁻¹' (Stacks.AmpleFiniteAvoidance.nvOpen L σ₁ : Set Z)ᶜ
  have hCcl : IsClosed C :=
    ((Stacks.AmpleFiniteAvoidance.nvOpen L σ₁).isOpen.isClosed_compl).preimage ι.continuous
  have hCfin : C.Finite := by
    refine finite_of_isClosed_of_disjoint_schemeAssociatedPoints hdim hCcl ?_
    refine Set.disjoint_left.2 fun x hxC hxA => hxC ?_
    exact hE₁ ⟨x, hxA, rfl⟩
  -- the second section, through it
  obtain ⟨d₂, τ₁, hd₂, hE₂, -, hτ₁⟩ :=
    Stacks.SectionExtension.exists_affine_nvOpen_containing_finite_le_of_isAmple L hL
      (hCfin.image ι) ⊤ (fun _ _ => trivial)
  obtain ⟨n, hn, σ, τ, eσ, eτ⟩ := exists_common_degree L hd₁ hd₂ σ₁ τ₁
  refine ⟨n, hn, σ, τ, eσ ▸ hσ₁, eτ ▸ hτ₁, ?_⟩
  rw [eσ, eτ]
  -- the fibre is covered
  set O := Stacks.AmpleFiniteAvoidance.nvOpen L σ₁ ⊔ Stacks.AmpleFiniteAvoidance.nvOpen L τ₁
  have hfib : ∀ z : Z, q z = t → z ∈ O := by
    intro z hz
    obtain ⟨x, rfl⟩ : z ∈ Set.range ι := by rw [Scheme.Hom.range_fiberι]; exact hz
    by_cases hx : ι x ∈ Stacks.AmpleFiniteAvoidance.nvOpen L σ₁
    · exact Or.inl hx
    · exact Or.inr (hE₂ ⟨x, hx, rfl⟩)
  -- shrink the base
  have hK : IsClosed (q '' (O : Set Z)ᶜ) := q.isClosedMap _ O.isOpen.isClosed_compl
  have ht : t ∉ q '' (O : Set Z)ᶜ := by
    rintro ⟨z, hz, rfl⟩
    exact hz (hfib z rfl)
  obtain ⟨f, hf, htf⟩ := (isAffineOpen_top T).exists_basicOpen_le
    (V := ⟨(q '' (O : Set Z)ᶜ)ᶜ, hK.isOpen_compl⟩) ⟨t, ht⟩ trivial
  refine ⟨f, htf, fun z hz => ?_⟩
  by_contra hzO
  exact hf hz ⟨z, hzO, rfl⟩

end AlgebraicGeometry.C1590Private
