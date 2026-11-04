module

public import StacksFrontier.RingTheory.Ideal.BoundedColength
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.AffineOrProjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountMonotone
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree

/-!
# Finitely many closed subschemes of bounded size on a curve over a finite field

Let `Z` be a proper curve over a finite field `E`, regular at its closed points. For every `M`
there are only finitely many closed subschemes `D ⊆ Z` which are affine with a ring of global
functions of at most `M` elements. (Effective Cartier divisors of bounded degree are such, which
is how this is used: it is the finiteness step of the finiteness of `Pic⁰`.)

The support of such a `D` has at most `2 ^ M` points, the points of `Spec Γ(D, 𝒪_D)`. Among
`2 ^ M + 1` fixed closed points `P_i` of `Z` one is not in the support, and `U_i = Z ∖ {P_i}` is
affine (`AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve`). The ideal sheaf of `D` is
determined by its ideal `I` on `U_i`, through its stalks
(`AlgebraicGeometry.IdealSheafData.eq_of_stalk_eq`), and `Γ(U_i, 𝒪) ⧸ I = Γ(D, 𝒪_D)` has at
most `M` elements. A finitely generated algebra over a finite field has only finitely many ideals
of bounded finite colength (`Stacks.RingTheory.finite_setOf_ideal_natCard_quotient_le`).

## Main results

* `Stacks.Picard.finite_support_and_ncard_le`: the support bound.
* `Stacks.Picard.finite_setOf_idealSheafData_natCard_le`: the finiteness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Picard

/-- **The support of a closed subscheme with a finite ring of functions.** If `D` is affine and
`Γ(D, 𝒪_D)` is finite, then the support of `D` is finite with at most `2 ^ #Γ(D, 𝒪_D)` points. -/
theorem finite_support_and_ncard_le {Z : Scheme.{u}} (D : Z.IdealSheafData) [IsAffine D.subscheme]
    [Finite Γ(D.subscheme, ⊤)] :
    (D.support : Set Z).Finite ∧ (D.support : Set Z).ncard ≤ 2 ^ Nat.card Γ(D.subscheme, ⊤) := by
  classical
  set R := Γ(D.subscheme, ⊤)
  have hPS : Function.Injective fun x : PrimeSpectrum R => (x.asIdeal : Set R) :=
    fun x y h => PrimeSpectrum.ext (SetLike.coe_injective h)
  have : Finite (PrimeSpectrum R) := Finite.of_injective _ hPS
  have hinj : Function.Injective D.subscheme.isoSpec.hom.base :=
    D.subscheme.isoSpec.hom.homeomorph.injective
  have : Finite D.subscheme := Finite.of_injective _ hinj
  rw [← D.range_subschemeι]
  refine ⟨Set.finite_range _, ?_⟩
  calc (Set.range D.subschemeι).ncard ≤ Nat.card D.subscheme := by
        rw [← Nat.card_coe_set_eq]
        exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ ≤ Nat.card (PrimeSpectrum R) := Nat.card_le_card_of_injective _ hinj
    _ ≤ Nat.card (Set R) := Nat.card_le_card_of_injective _ hPS
    _ = 2 ^ Nat.card R := by
        have := Fintype.ofFinite R
        rw [Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]

variable {E : Type u} [Field E] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of E))

/-- The `E`-algebra structure of the ring of functions on an open of a scheme over `E`. -/
abbrev sectionsAlgebra (U : Z.Opens) : Algebra E Γ(Z, U) :=
  ((Scheme.ΓSpecIso (.of E)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra

/-- The functions on an affine open of a scheme locally of finite type over `E` form a finitely
generated `E`-algebra. -/
theorem finiteType_sectionsAlgebra [LocallyOfFiniteType f] {U : Z.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Algebra.FiniteType E Γ(Z, U) := by
  have h : ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ f.appLE ⊤ U (by simp)).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp
      (LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU (by simp))
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of E)).inv).surjective)
  exact h

/-- **The quotient by the ideal on an affine open containing the support.** If the support of `D`
lies in the affine open `U`, then `Γ(U, 𝒪_Z) ⧸ I(U) ≅ Γ(D, 𝒪_D)`. -/
def quotientIdealEquivSections (D : Z.IdealSheafData) (U : Z.affineOpens)
    (hU : (D.support : Set Z) ⊆ (U.1 : Set Z)) :
    (Γ(Z, U.1) ⧸ D.ideal U) ≃+* Γ(D.subscheme, ⊤) :=
  have h : D.subschemeι ⁻¹ᵁ U.1 = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.mem_top, iff_true]
    exact hU (D.range_subschemeι ▸ Set.mem_range_self x)
  ((D.subschemeObjIso U).symm ≪≫
    D.subscheme.presheaf.mapIso (eqToIso h.symm).op).commRingCatIsoToRingEquiv

variable [IsProper f] [IsCurve E f]

/-- **Finitely many closed subschemes of bounded size.** Let `Z` be a proper curve over a finite
field, regular at its closed points. For every `M`, only finitely many closed subschemes `D` are
affine with `Γ(D, 𝒪_D)` finite of at most `M` elements. -/
theorem finite_setOf_idealSheafData_natCard_le [Finite E]
    (hdvr : ∀ x : Z, IsClosed ({x} : Set Z) → IsDiscreteValuationRing (Z.presheaf.stalk x))
    (M : ℕ) :
    {D : Z.IdealSheafData | IsAffine D.subscheme ∧ Finite Γ(D.subscheme, ⊤) ∧
      Nat.card Γ(D.subscheme, ⊤) ≤ M}.Finite := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  set B := 2 ^ M
  let emb := (Stacks.EtaleCohomology.infinite_closedPoints_of_isCurve (f := f)).natEmbedding
  let P : Fin (B + 1) → Z := fun i => (emb i.1).1
  have hPinj : Function.Injective P := fun i j h => Fin.ext (emb.injective (Subtype.ext h))
  have hPcl : ∀ i, IsClosed ({P i} : Set Z) := fun i => (emb i.1).2
  let U : Fin (B + 1) → Z.affineOpens := fun i =>
    have := hdvr (P i) (hPcl i)
    ⟨⟨({P i} : Set Z)ᶜ, (hPcl i).isOpen_compl⟩,
      isAffineOpen_compl_singleton_of_isCurve E f inferInstance inferInstance (hPcl i)⟩
  -- every `D` of the set misses one of the `P i`
  have hmiss : ∀ D ∈ {D : Z.IdealSheafData | IsAffine D.subscheme ∧ Finite Γ(D.subscheme, ⊤) ∧
      Nat.card Γ(D.subscheme, ⊤) ≤ M}, ∃ i, P i ∉ (D.support : Set Z) := by
    rintro D ⟨haff, hfin, hcard⟩
    obtain ⟨hDfin, hDcard⟩ := finite_support_and_ncard_le D
    by_contra h
    push Not at h
    have hle : Nat.card (Fin (B + 1)) ≤ (D.support : Set Z).ncard := by
      rw [← Set.ncard_univ, ← Set.ncard_image_of_injective _ hPinj]
      exact Set.ncard_le_ncard (Set.image_subset_iff.2 fun i _ => h i) hDfin
    rw [Nat.card_fin] at hle
    have : 2 ^ Nat.card Γ(D.subscheme, ⊤) ≤ B := Nat.pow_le_pow_right (by norm_num) hcard
    omega
  -- the set is a finite union of the sets of `D` missing `P i`
  refine Set.Finite.subset (Set.finite_iUnion fun i : Fin (B + 1) =>
    (show {D : Z.IdealSheafData | (IsAffine D.subscheme ∧ Finite Γ(D.subscheme, ⊤) ∧
      Nat.card Γ(D.subscheme, ⊤) ≤ M) ∧ P i ∉ (D.support : Set Z)}.Finite from ?_))
    fun D hD => Set.mem_iUnion.2 ((hmiss D hD).imp fun _ hi => ⟨hD, hi⟩)
  let := sectionsAlgebra f (U i).1
  have := finiteType_sectionsAlgebra f (U i).2
  refine Set.Finite.of_finite_image (f := fun D : Z.IdealSheafData => D.ideal (U i))
    ((Stacks.RingTheory.finite_setOf_ideal_natCard_quotient_le E Γ(Z, (U i).1) M).subset ?_) ?_
  · rintro _ ⟨D, ⟨⟨haff, hfin, hcard⟩, hi⟩, rfl⟩
    have hsub : (D.support : Set Z) ⊆ ((U i).1 : Set Z) := fun x hx hxP => hi (hxP ▸ hx)
    let e := quotientIdealEquivSections D (U i) hsub
    exact ⟨Finite.of_equiv _ e.toEquiv.symm, (Nat.card_congr e.toEquiv).trans_le hcard⟩
  · rintro D ⟨-, hi⟩ D' ⟨-, hi'⟩ h
    refine IdealSheafData.eq_of_stalk_eq D D' fun x => ?_
    by_cases hx : x ∈ ((U i).1 : Set Z)
    · rw [IdealSheafData.stalk_eq_map_germ D x (U i) hx,
        IdealSheafData.stalk_eq_map_germ D' x (U i) hx]
      exact congrArg _ h
    · obtain rfl : x = P i := by simpa [U] using hx
      rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support D _).2 hi,
        (Stacks.Divisors.stalk_eq_top_iff_notMem_support D' _).2 hi']

end Stacks.Picard

end
