module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz

/-!
# Finite-type morphisms from the spectrum of a field

A morphism from the spectrum of a field is of finite type if and only if it is locally of
finite type. These conditions can equivalently be detected on an affine open neighbourhood of
its image, either by finiteness of the corresponding ring map or by finiteness of the residue
field extension at the image point.

## Main results

* `AlgebraicGeometry.finiteType_specField_tfae` gives the four equivalent characterizations of
  a finite-type morphism from the spectrum of a field.

## Implementation notes

The four entries of the `List.TFAE` are the four numbered conditions in the source. In the
first entry, Mathlib expresses "of finite type" as local finite type together with
quasi-compactness. For an affine open `U`, its coordinate ring is `Γ(S, U)`; the map in the
third entry is the map on sections followed by the canonical isomorphism `Γ(Spec(k), ⊤) ≅ k`.
In the fourth entry, `Scheme.SpecToEquivOfField` supplies both the image point and the
canonical embedding of its residue field into `k`.

## References

* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A field that is of finite type over a ring `R` becomes finite over a suitable localization
`R_r` of `R`: there is an `r : R` with nonzero image such that every localization of `R` away
from `r` maps finitely to the field. -/
private lemma exists_finite_localization {R k : Type*} [CommRing R] [Field k]
    (φ : R →+* k) (hφ : φ.FiniteType) :
    ∃ r : R, φ r ≠ 0 ∧ ∀ (B : Type*) [CommRing B] [Algebra R B]
      [IsLocalization.Away r B] (ψ : B →+* k),
      ψ.comp (algebraMap R B) = φ → ψ.Finite := by
  let : Algebra R k := φ.toAlgebra
  let : Algebra R φ.range := φ.rangeRestrict.toAlgebra
  let : Algebra φ.range k := φ.range.subtype.toAlgebra
  have : IsScalarTower R φ.range k := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R k := hφ
  have : Algebra.FiniteType φ.range k := .of_restrictScalars_finiteType R _ _
  obtain ⟨a, -, alg, tower, fin⟩ :=
    exists_isField_localizationAway_and_finite_of_finiteType φ.range k Subtype.val_injective
  let := alg; have := tower; have := fin
  obtain ⟨r, hr⟩ := φ.rangeRestrict_surjective a
  subst a
  have hunit : IsUnit (φ r) := by
    change IsUnit (algebraMap φ.range k (φ.rangeRestrict r))
    rw [IsScalarTower.algebraMap_apply φ.range (Localization.Away (φ.rangeRestrict r)) k]
    exact (IsLocalization.Away.algebraMap_isUnit (φ.rangeRestrict r)).map _
  refine ⟨r, hunit.ne_zero, fun B _ _ _ ψ hψ => ?_⟩
  let q := IsLocalization.Away.map B (Localization.Away (φ.rangeRestrict r)) φ.rangeRestrict r
  have hq : Function.Surjective q :=
    (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr fun a => by
      obtain ⟨b, rfl⟩ := φ.rangeRestrict_surjective a
      exact ⟨b, 0, by simp⟩
  have heq : ψ = (algebraMap (Localization.Away (φ.rangeRestrict r)) k).comp q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r); ext x
    have hx := RingHom.congr_fun hψ x
    dsimp only [RingHom.comp_apply]
    rw [show q ((algebraMap R B) x) =
      algebraMap φ.range (Localization.Away (φ.rangeRestrict r)) (φ.rangeRestrict x) from
        by simp [q, IsLocalization.Away.map, IsLocalization.map_eq],
      ← IsScalarTower.algebraMap_apply]
    exact hx
  rw [heq]; exact (RingHom.finite_algebraMap.mpr fin).comp (.of_surjective q hq)

/-- A morphism from the spectrum of a field factors through an affine open of the target as the
spectrum of the induced map on coordinate rings. -/
private lemma specMap_appLE_fromSpec {k : Type u} [Field k] {S : Scheme.{u}}
    (f : Spec (.of k) ⟶ S) (U : S.affineOpens) (hU : ⊤ ≤ f ⁻¹ᵁ U.1) :
    Spec.map (f.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫ U.2.fromSpec = f := by
  rw [Spec.map_comp, Category.assoc, U.2.SpecMap_appLE_fromSpec f (isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
  simp

/-- A morphism from the spectrum of a field to an open subscheme is finite exactly when its
image is a closed point and the induced residue field extension is finite. -/
private lemma finite_iff_closed_and_finite_residue {k : Type u} [Field k]
    {S V : Scheme.{u}} (f : Spec (.of k) ⟶ S) (g : Spec (.of k) ⟶ V)
    (i : V ⟶ S) [IsOpenImmersion i] (hgf : g ≫ i = f) :
    IsFinite g ↔ IsClosed ({g (IsLocalRing.closedPoint k)} : Set V) ∧
      ((Scheme.SpecToEquivOfField k S f).2.hom).Finite := by
  let y := (Scheme.SpecToEquivOfField k S f).1
  let e := (Scheme.SpecToEquivOfField k S f).2
  have hy : i (g (IsLocalRing.closedPoint k)) = y := by
    change (g ≫ i) (IsLocalRing.closedPoint k) = f (IsLocalRing.closedPoint k)
    rw [hgf]
  have hr : Set.range (S.fromSpecResidueField y) ⊆ Set.range i := by
    rw [S.range_fromSpecResidueField]
    rintro _ rfl; exact ⟨_, hy⟩
  let d := IsOpenImmersion.lift i (S.fromSpecResidueField y) hr
  have hd : d ≫ i = S.fromSpecResidueField y := IsOpenImmersion.lift_fac _ _ _
  have hfac : Spec.map e ≫ d = g := by
    rw [← cancel_mono i, Category.assoc, hd, hgf]
    exact (Scheme.SpecToEquivOfField k S).symm_apply_apply f
  have : IsPreimmersion d := (IsPreimmersion.comp_iff d i).mp (hd ▸ inferInstance)
  have hrd : Set.range d = {g (IsLocalRing.closedPoint k)} := by
    rw [Set.range_unique, Set.singleton_eq_singleton_iff]
    apply i.isOpenEmbedding.injective
    change (d ≫ i) _ = _; rw [hd, Scheme.fromSpecResidueField_apply, hy]
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · have heq : Set.range g = {g (IsLocalRing.closedPoint k)} := by
        rw [Set.range_unique, Set.singleton_eq_singleton_iff]
        exact congrArg g (Subsingleton.elim _ _)
      rw [← heq]; exact g.isClosedMap.isClosed_range
    · have : IsFinite (Spec.map e ≫ d) := hfac.symm ▸ hg
      exact (IsFinite.SpecMap_iff e).mp (IsFinite.of_comp (Spec.map e) d)
  · rintro ⟨hc, he⟩
    have : IsFinite (Spec.map e) := (IsFinite.SpecMap_iff e).mpr he
    have : IsClosedImmersion d := .of_isPreimmersion d (hrd.symm ▸ hc)
    rw [← hfac]; infer_instance

/-- **Stacks Project, Tag 01TA.** For a morphism from the spectrum of a field, being of finite
type, being locally of finite type, admitting a finite affine coordinate-ring map around its
image, and having closed image with finite residue field extension are equivalent. -/
@[stacks 01TA]
theorem finiteType_specField_tfae {k : Type u} [Field k] {S : Scheme.{u}}
    (f : Spec (.of k) ⟶ S) :
    List.TFAE [
      LocallyOfFiniteType f ∧ QuasiCompact f,
      LocallyOfFiniteType f,
      ∃ (U : S.affineOpens)
          (hU : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ U.1),
        ((f.appLE U ⊤ hU) ≫ (Scheme.ΓSpecIso (.of k)).hom).hom.Finite,
      ∃ (U : S.affineOpens)
          (_hU : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ U.1)
          (x : U.1),
        (x : S) = ((Scheme.SpecToEquivOfField k S) f).1 ∧
          IsClosed ({x} : Set U.1) ∧
          letI := ((Scheme.SpecToEquivOfField k S) f).2.hom.toAlgebra
          Module.Finite (S.residueField ((Scheme.SpecToEquivOfField k S) f).1) k] := by
  tfae_have 1 ↔ 2 :=
    ⟨And.left, fun h => ⟨h, ⟨fun U _ _ => (Set.toFinite (f ⁻¹' U)).isCompact⟩⟩⟩
  tfae_have 2 → 3 := by
    intro hf
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f (IsLocalRing.closedPoint k))) isOpen_univ
    let V : S.affineOpens := ⟨U, hU⟩
    have htop : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ U := by
      intro x _; change f x ∈ U
      rwa [Subsingleton.elim x (IsLocalRing.closedPoint k)]
    let φ := f.appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (.of k)).hom
    have hφ : φ.hom.FiniteType :=
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).2).comp
        (f.finiteType_appLE hU (isAffineOpen_top _) htop)
    obtain ⟨r, hr, hfin⟩ := exists_finite_localization φ.hom hφ
    have hbasic : (⊤ : (Spec (.of k)).Opens) ≤ f ⁻¹ᵁ S.basicOpen r := by
      intro x _; change f x ∈ S.basicOpen r
      rw [← specMap_appLE_fromSpec f V htop]
      change Spec.map φ x ∈ hU.fromSpec ⁻¹ᵁ S.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]
      change φ.hom r ∉ x.asIdeal
      rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
      change φ.hom r ∉ IsLocalRing.maximalIdeal k
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_ne_zero, not_not] using hr
    refine ⟨⟨S.basicOpen r, hU.basicOpen r⟩, hbasic, ?_⟩
    have := hU.isLocalization_basicOpen r
    apply hfin Γ(S, S.basicOpen r)
    change (S.presheaf.map (homOfLE (S.basicOpen_le r)).op ≫
      (f.appLE (S.basicOpen r) ⊤ hbasic ≫ (Scheme.ΓSpecIso (.of k)).hom)).hom = φ.hom
    rw [f.map_appLE_assoc]
  tfae_have 3 → 2 := by
    rintro ⟨U, hU, hf⟩
    have hUaff : IsAffineOpen (U.1 : S.Opens) := U.2
    have : IsFinite (Spec.map (f.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom)) :=
      (IsFinite.SpecMap_iff _).mpr hf
    have : IsOpenImmersion hUaff.fromSpec := hUaff.isOpenImmersion_fromSpec
    rw [← specMap_appLE_fromSpec f U hU]; infer_instance
  tfae_have 3 ↔ 4 := by
    constructor
    · rintro ⟨U, hU, hf⟩
      have hUaff : IsAffineOpen (U.1 : S.Opens) := U.2
      let φ := f.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom
      let g := Spec.map φ ≫ hUaff.isoSpec.inv
      have hgf : g ≫ U.1.ι = f := by
        dsimp only [g]; rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
        exact specMap_appLE_fromSpec f U hU
      have : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff _).mpr hf
      obtain ⟨hc, he⟩ := (finite_iff_closed_and_finite_residue f g U.1.ι hgf).mp inferInstance
      exact ⟨U, hU, g (IsLocalRing.closedPoint k),
        congrArg (fun t : Spec (.of k) ⟶ S => t (IsLocalRing.closedPoint k)) hgf, hc, he⟩
    · rintro ⟨U, hU, x, hx, hc, he⟩
      have hUaff : IsAffineOpen (U.1 : S.Opens) := U.2
      let φ := f.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom
      let g := Spec.map φ ≫ hUaff.isoSpec.inv
      have hgf : g ≫ U.1.ι = f := by
        dsimp only [g]; rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
        exact specMap_appLE_fromSpec f U hU
      have hpoint : g (IsLocalRing.closedPoint k) = x := by
        apply Subtype.ext
        change (g ≫ U.1.ι) (IsLocalRing.closedPoint k) = x.1
        rw [hgf, hx]; rfl
      have hg : IsFinite g :=
        (finite_iff_closed_and_finite_residue f g U.1.ι hgf).mpr ⟨hpoint.symm ▸ hc, he⟩
      exact ⟨U, hU, (IsFinite.SpecMap_iff φ).mp (IsFinite.of_comp (Spec.map φ) hUaff.isoSpec.inv)⟩
  tfae_finish

end AlgebraicGeometry
