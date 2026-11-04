module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageOffLocus
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsComplementInjective
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.BasicOpenUnionSections
public import StacksFrontier.RingTheory.MvPolynomial.ProjectiveVariablePowerDivisibility
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (1) of Stacks 0FUR: forms on the blowup of affine space in a coordinate subspace

Fix a ring `R`, put `S = Spec R`, `X = 𝐀^{m+n}_S = Spec R[x₁, …, x_m, y₁, …, y_n]` and let
`b : L ⟶ X` be the blowup of `X` along `Z = V(y₁, …, y_n) = 𝐀^m_S`, with exceptional divisor
`E`. Clause (1) of [Stacks, Tag 0FUR] says that for `n ≥ 1` the canonical map

`Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}`

(`Stacks.DeRham.coordinateBlowupFormsDirectImage`) is an isomorphism for every `a ≥ 0`.

## The proof

It is the source's. For `n = 1` the centre is an effective Cartier divisor and `b` is an
isomorphism. For `n ≥ 2` both sides are quasi-coherent on the affine `X`, so it suffices to show
that `Γ(X, Ω^a_{X/S}) ⟶ Γ(L, Ω^a_{L/S})` is bijective. Restrict both sides to `X ∖ Z` and to
`L ∖ E = b⁻¹(X ∖ Z)`:

* `Γ(X, Ω^a_{X/S}) ⟶ Γ(X ∖ Z, Ω^a_{X/S})` is bijective, because `Ω^a_{X/S}` is free and
  `X ∖ Z = ⋃ D(y_j)` with `n ≥ 2` (`Stacks.DeRham.bijective_res_coordinateAmbientForms_compl`;
  the source's "small detail omitted");
* the map over `X ∖ Z` is bijective, since `b` is an isomorphism over `X ∖ Z`;
* `Γ(L, Ω^a_{L/S}) ⟶ Γ(L ∖ E, Ω^a_{L/S})` is injective, because a form of the smooth `L` that
  vanishes off the effective Cartier divisor `E` vanishes
  (`Stacks.DeRham.injective_res_coordinateBlowupForms_compl`).

The square commutes by naturality, so the global map is bijective.

## Main results

* `Stacks.DeRham.coordinateIdeal_support_compl`: `X ∖ Z = ⋃_j D(y_j)`.
* `Stacks.DeRham.bijective_coordinateBlowupFormsDirectImage_appTop`: the statement on global
  sections, for `n ≥ 2`.
* `Stacks.DeRham.isIso_coordinateBlowupFormsDirectImage`: **[Stacks, Tag 0FUR], clause (1)**, for
  every `n ≥ 1` and every `a`.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Stacks.MoreMorphisms

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The blowup `L` is smooth over `S` ([Stacks, Tag 0H1H]). -/
instance smooth_coordinateBlowupToBase : Smooth (coordinateBlowupToBase R m n) :=
  Stacks.MoreMorphisms.blowUp_smooth_of_pos R m n

/-- **The complement of the centre is the union of the basic opens of the last coordinates.** -/
theorem coordinateIdeal_support_compl :
    (coordinateIdeal R m n).support.compl =
      ⨆ i, (coordinateAmbient R m n).basicOpen (coordinateSection R m n i) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun i x hx => ?_)
  · by_contra hcon
    apply hx
    change x ∈ (coordinateIdeal R m n).support
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := topAffineOpen R m n) trivial]
    refine Scheme.zeroLocus_mono (X := coordinateAmbient R m n)
      (coordinateIdeal_ideal_top_le_span R m n) ?_
    rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    rintro f ⟨i, rfl⟩ hxi
    exact hcon (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hxi⟩)
  · intro hsupp
    change x ∈ (coordinateIdeal R m n).support at hsupp
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := topAffineOpen R m n) trivial,
      Scheme.mem_zeroLocus_iff] at hsupp
    exact hsupp _ (coordinateSection_mem R m n i) hx

variable {m n}

/-- **Hartogs for the forms of affine space**: for `n ≥ 2`, every `a`-form on `X ∖ Z` extends
uniquely to `X`. -/
theorem bijective_res_coordinateAmbientForms_compl (hn : 2 ≤ n) (a : ℕ) :
    Function.Bijective ((Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n)
      (a : ℤ)).presheaf.map
        (homOfLE (le_top : (coordinateIdeal R m n).support.compl ≤ ⊤)).op) := by
  have : (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n)
      (a : ℤ)).IsQuasicoherent := Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  have := Stacks.Divisors.projective_sections_relativeDifferentialForms
    (coordinateAmbientToBase R m n) ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp) a
  have h := Stacks.AlgebraicGeometry.BasicOpenUnion.bijective_res_iSup_basicOpen
    (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ))
    (coordinateSection R m n)
    (fun j => Stacks.Divisors.isSMulRegular_sections_relativeDifferentialForms
      (coordinateAmbientToBase R m n) ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp) a
      _ (isRegular_iff_mem_nonZeroDivisors.mpr (coordinateSection_mem_nonZeroDivisors R m n j)))
    (fun i j hij u v k l h => MvPolynomial.exists_eq_smul_pow_of_smul_eq_smul_of_projective
      (gammaEquiv R m n) (i := Sum.inr i) (j := Sum.inr j) (fun h' => hij (Sum.inr_injective h')) h)
    ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
  rw [← coordinateIdeal_support_compl] at h
  exact h

/-- **A form on the blowup vanishing off the exceptional divisor vanishes**: restriction
`Γ(L, Ω^a_{L/S}) ⟶ Γ(L ∖ E, Ω^a_{L/S})` is injective, `E` being an effective Cartier divisor
and `L` smooth over `S`. -/
theorem injective_res_coordinateBlowupForms_compl (a : ℕ) :
    Function.Injective ((Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
      (a : ℤ)).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (coordinateBlowupToAmbient R m n)
          (le_top : (coordinateIdeal R m n).support.compl ≤ ⊤))).op) := by
  refine (injective_iff_map_eq_zero (AddCommGrpCat.Hom.hom _)).mpr fun z hz => ?_
  refine Stacks.Divisors.eq_zero_of_res_compl_support_eq_zero (coordinateBlowupToBase R m n)
    (coordinateExceptional R m n) inferInstance a z ?_
  have hE : (coordinateExceptional R m n).support.compl =
      coordinateBlowupToAmbient R m n ⁻¹ᵁ (coordinateIdeal R m n).support.compl :=
    TopologicalSpace.Opens.ext (by rw [Scheme.IdealSheafData.support_comap]; rfl)
  have hle : coordinateBlowupToAmbient R m n ⁻¹ᵁ ⊤ ⊓ (coordinateExceptional R m n).support.compl ≤
      coordinateBlowupToAmbient R m n ⁻¹ᵁ (coordinateIdeal R m n).support.compl :=
    hE ▸ inf_le_right
  rw [← Stacks.AlgebraicGeometry.BasicOpenUnion.res_res _
    (Scheme.Hom.preimage_mono (coordinateBlowupToAmbient R m n) le_top) hle]
  exact (congrArg _ hz).trans (map_zero _)

/-- **Clause (1) of [Stacks, Tag 0FUR] on global sections, for `n ≥ 2`.** The map
`Γ(X, Ω^a_{X/S}) ⟶ Γ(L, Ω^a_{L/S})` is bijective. Restricting to `X ∖ Z` and `L ∖ E = b⁻¹(X ∖ Z)`
gives a commutative square: the restriction on `X` is bijective (Hartogs, `n ≥ 2`), the map over
`X ∖ Z` is bijective because `b` is an isomorphism there, and the restriction on `L` is injective
because a form vanishing off `E` vanishes. -/
theorem bijective_coordinateBlowupFormsDirectImage_appTop (hn : 2 ≤ n) (a : ℕ) :
    Function.Bijective ((coordinateBlowupFormsDirectImage R m n a).app ⊤) := by
  set c := coordinateBlowupFormsDirectImage R m n a
  set U := (coordinateIdeal R m n).support.compl
  have hU : IsIso (c.app U) :=
    Scheme.Hom.isIso_app_formsDirectImageComparison_of_isIso_morphismRestrict _ _ _ U
  have hcU := (ConcreteCategory.isIso_iff_bijective _).mp hU
  have hX := bijective_res_coordinateAmbientForms_compl R (m := m) hn a
  have hL := injective_res_coordinateBlowupForms_compl R (m := m) (n := n) a
  have hnat : ∀ x, (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n)
      (a : ℤ)).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (coordinateBlowupToAmbient R m n)
          (le_top : U ≤ ⊤))).op (c.app ⊤ x) =
      c.app U ((Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n)
        (a : ℤ)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x) := fun x =>
    (congrArg (fun φ => φ x) (c.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op)).symm
  refine ⟨fun x y hxy => hX.1 (hcU.1 ?_), fun z => ?_⟩
  · rw [← hnat, ← hnat, hxy]
  · obtain ⟨w, hw⟩ := hcU.2 _
    obtain ⟨x, rfl⟩ := hX.2 w
    exact ⟨x, hL ((hnat x).trans hw)⟩

/-- **[Stacks, Tag 0FUR], clause (1).** For every ring `R`, every `m`, every `n ≥ 1` and every
degree `a ≥ 0`, the canonical map `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` is an isomorphism, where
`X = 𝐀^{m+n}_S`, `S = Spec R`, and `b : L ⟶ X` is the blowup of `X` along `Z = 𝐀^m_S`. For `n = 1`
the blowup is an isomorphism (`Stacks.DeRham.isIso_coordinateBlowupFormsDirectImage_of_one`); for
`n ≥ 2` both sides are quasi-coherent on the affine `X`, so it suffices that the map be bijective
on global sections, which is `Stacks.DeRham.bijective_coordinateBlowupFormsDirectImage_appTop`. -/
@[stacks 0FUR "clause (1), in the setting of Section 0FUB, \
which fixes a ring R and sets S = Spec(R), Z = A^m_S ⊂ X = A^{m+n}_S with n ≥ 1"]
theorem isIso_coordinateBlowupFormsDirectImage (m n : ℕ) (hn : 1 ≤ n) (a : ℕ) :
    IsIso (coordinateBlowupFormsDirectImage R m n a) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases k with _ | k
  · exact isIso_coordinateBlowupFormsDirectImage_of_one R m a
  · exact isIso_coordinateBlowupFormsDirectImage_of_isIso_appTop R m (k + 2) a
      ((ConcreteCategory.isIso_iff_bijective _).mpr
        (bijective_coordinateBlowupFormsDirectImage_appTop R (by omega) a))

end Stacks.DeRham
