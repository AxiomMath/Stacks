module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagAffineSpace
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.IncidenceFibre

/-!
# The origin of affine space and zero schemes of functions

Auxiliary geometry for the Kummer flag class of an étale chart `ψ : U ⟶ 𝔸^d_K`.

* The origin `0 : Spec K ⟶ 𝔸^d_K` (`AlgebraicGeometry.GoodNeighbourhood.origin`) is the spectrum
  of the constant coefficient, hence a closed immersion, and its image is exactly the set of
  points where all coordinates vanish (`range_goodNeighbourhoodOrigin`).
* A morphism `g : S ⟶ U` to an affine scheme killing a function `φ` factors through the zero
  scheme `Spec(Γ(U)/φ)` (`exists_comp_zeroSchemeι_eq`), on which `φ` vanishes
  (`zeroSchemeι_appTop_self`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.range_goodNeighbourhoodOrigin`
* `Stacks.EtaleCohomology.KummerFlag.exists_comp_zeroSchemeι_eq`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.KummerFlag

section Origin

variable (K : Type u) [Field K] (n : ℕ)

/-- The origin of `𝔸^n_K` (`AlgebraicGeometry.GoodNeighbourhood.origin`) is the spectrum of the
constant coefficient `K[x_0, …, x_{n-1}] ⟶ K`. -/
theorem goodNeighbourhoodOrigin_eq :
    AlgebraicGeometry.GoodNeighbourhood.origin (k := K) n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff :
        MvPolynomial (ULift.{u} (Fin n)) K →+* K)) ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of K)).inv := by
  ext1
  · rw [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.SpecIso_inv_over,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  · rename_i j
    rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- The origin of `𝔸^n_K` is a closed immersion. -/
instance isClosedImmersion_goodNeighbourhoodOrigin :
    IsClosedImmersion (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) n) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (MvPolynomial.constantCoeff :
      MvPolynomial (ULift.{u} (Fin n)) K →+* K))) :=
    IsClosedImmersion.spec_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)
  rw [goodNeighbourhoodOrigin_eq]
  exact IsClosedImmersion.comp _ _

/-- Every coordinate function of `𝔸^n_K` pulls back to `0` along the origin. -/
theorem goodNeighbourhoodOrigin_appTop_coord (j : ULift.{u} (Fin n)) :
    (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) n).appTop
      (AffineSpace.coord (Spec (.of K)) j) = 0 := by
  rw [AffineSpace.homOfVector_appTop_coord]
  rfl

/-- A prime of `K[x_0, …, x_{n-1}]` contains the kernel of the constant coefficient exactly when
it contains every variable. -/
theorem ker_constantCoeff_le_iff_forall (𝔭 : Ideal (MvPolynomial (ULift.{u} (Fin n)) K)) :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (ULift.{u} (Fin n)) K →+* K) ≤ 𝔭 ↔
      ∀ j, MvPolynomial.X j ∈ 𝔭 := by
  refine ⟨fun h j => h (by simp), fun hX f hf => ?_⟩
  have hspan : f ∈ Ideal.span (MvPolynomial.X '' Set.univ :
      Set (MvPolynomial (ULift.{u} (Fin n)) K)) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 (show m ≠ 0 by
      rintro rfl
      rw [RingHom.mem_ker, MvPolynomial.constantCoeff_eq] at hf
      exact MvPolynomial.mem_support_iff.1 hm hf)
    exact ⟨i, Set.mem_univ _, hi⟩
  exact Ideal.span_le.2 (by rintro _ ⟨i, -, rfl⟩; exact hX i) hspan

/-- **The image of the origin is the common zero locus of the coordinates.** -/
theorem range_goodNeighbourhoodOrigin :
    Set.range (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) n).base =
      {x | ∀ j, x ∉ (𝔸(ULift.{u} (Fin n); Spec (.of K))).basicOpen
        (AffineSpace.coord (Spec (.of K)) j)} := by
  set e := AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of K)
  set c : MvPolynomial (ULift.{u} (Fin n)) K →+* K := MvPolynomial.constantCoeff
  have hrange : Set.range (PrimeSpectrum.comap c) = PrimeSpectrum.zeroLocus (RingHom.ker c) :=
    range_comap_of_surjective _ _ (fun a => ⟨MvPolynomial.C a, by simp [c]⟩)
  have hmem : ∀ (y : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin n)) K)) (j : ULift.{u} (Fin n)),
      e.inv.base y ∈ (𝔸(ULift.{u} (Fin n); Spec (.of K))).basicOpen
          (AffineSpace.coord (Spec (.of K)) j) ↔
        y ∈ PrimeSpectrum.basicOpen (MvPolynomial.X j : MvPolynomial (ULift.{u} (Fin n)) K) := by
    intro y j
    have h : e.inv ⁻¹ᵁ (𝔸(ULift.{u} (Fin n); Spec (.of K))).basicOpen
        (AffineSpace.coord (Spec (.of K)) j) =
        PrimeSpectrum.basicOpen (MvPolynomial.X j : MvPolynomial (ULift.{u} (Fin n)) K) := by
      rw [Scheme.preimage_basicOpen_top, AffineSpace.SpecIso_inv_appTop_coord,
        basicOpen_eq_of_affine]
    rw [← h]
    rfl
  have horigin : Set.range (AlgebraicGeometry.GoodNeighbourhood.origin (k := K) n).base =
      e.inv.base '' Set.range (PrimeSpectrum.comap c) := by
    rw [goodNeighbourhoodOrigin_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  ext x
  obtain ⟨y, rfl⟩ : ∃ y : PrimeSpectrum (MvPolynomial (ULift.{u} (Fin n)) K), e.inv.base y = x :=
    (Scheme.homeoOfIso e.symm).surjective x
  rw [Set.mem_setOf_eq]
  refine Iff.trans ?_ (forall_congr' fun j => (not_congr (hmem y j)).symm)
  simp only [PrimeSpectrum.mem_basicOpen, not_not]
  rw [horigin]
  have hinj : Function.Injective e.inv.base := (Scheme.homeoOfIso e.symm).injective
  refine Iff.trans (hinj.mem_set_image (s := Set.range (PrimeSpectrum.comap c))) ?_
  have h2 : y ∈ Set.range (PrimeSpectrum.comap c) ↔ RingHom.ker c ≤ y.asIdeal := by
    rw [hrange, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  exact h2.trans (ker_constantCoeff_le_iff_forall K n y.asIdeal)

end Origin

section ZeroScheme

variable {U : Scheme.{u}} [IsAffine U]

/-- A function vanishes on its zero scheme. -/
theorem zeroSchemeι_appTop_self (φ : Γ(U, ⊤)) : (zeroSchemeι φ).appTop φ = 0 := by
  have e : U.isoSpec.hom.appTop ≫ U.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  have h1 : U.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(U, ⊤)).inv φ) = φ := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_apply (C := CommRingCat) _ _
  have h2 : U.isoSpec.inv.appTop φ = (Scheme.ΓSpecIso Γ(U, ⊤)).inv φ := by
    conv_lhs => rw [← h1]
    rw [← CommRingCat.comp_apply, e, CommRingCat.id_apply]
  rw [zeroSchemeι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h2, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp

/-- **A morphism killing `φ` factors through the zero scheme of `φ`.** -/
theorem exists_comp_zeroSchemeι_eq {S : Scheme.{u}} (g : S ⟶ U) (φ : Γ(U, ⊤))
    (hg : g.appTop φ = 0) : ∃ g' : S ⟶ Spec (.of (Γ(U, ⊤) ⧸ Ideal.span {φ})),
      g' ≫ zeroSchemeι φ = g := by
  let q : Γ(U, ⊤) ⧸ Ideal.span {φ} →+* Γ(S, ⊤) :=
    Ideal.Quotient.lift (Ideal.span {φ}) g.appTop.hom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      show _ * g.appTop φ = 0
      rw [hg, mul_zero])
  refine ⟨S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q), ?_⟩
  rw [zeroSchemeι, ← Category.assoc, Category.assoc S.toSpecΓ, ← Spec.map_comp]
  have hq : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {φ})) ≫ CommRingCat.ofHom q =
      g.appTop := by
    ext a
    rfl
  rw [hq, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id,
    Category.comp_id]

end ZeroScheme

end Stacks.EtaleCohomology.KummerFlag

end
