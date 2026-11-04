module

public import StacksFrontier.RingTheory.Henselian.SmoothResidueLift
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.NodalContraction.FibreReduced
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.RingTheory.Flat.HenselianFlatFiniteColimit
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyReducedCohenMacaulay

/-!
# Sections of proper nodal families over a henselian local ring

Let `R'` be a henselian local ring with separably closed residue field and `q : Y ⟶ Spec R'` a
proper flat morphism which is at-worst-nodal of relative dimension one, with `Y` nonempty. Then `q`
has a section. The closed fibre is nonempty because `q` is closed, it is geometrically reduced
because it is nodal, so it has a dense open smooth over the residue field
([Stacks, Tag 056V]) and that open has a rational point. By flatness `q` is smooth at that point,
and on an affine open around it the residue point of the smooth `R'`-algebra lifts to `R'`
(`HenselianLocalRing.exists_algHom_residue_of_smooth`).

This is the step "a curve with semistable reduction over a henselian discrete valuation ring with
separably closed residue field has a rational point" used in [Stacks, Tag 0CEH].

## Main results

* `AlgebraicGeometry.exists_section_of_smooth_of_residuePoint`: a residue point of an open on which
  `q` is smooth gives a section.
* `AlgebraicGeometry.exists_smoothLocus_point_of_nodal`: the closed fibre of a flat nodal family
  has a rational point in the smooth locus.
* `AlgebraicGeometry.exists_section_of_nodal`: **a proper flat nodal family with nonempty total
  space has a section.**

## References

* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A morphism of spectra equal to `Spec.map ε` induces `ε` on global sections, up to the
identifications `ΓSpecIso`. -/
private theorem ΓSpecIso_inv_comp_appTop_comp_hom {R K : CommRingCat.{u}} (ε : R ⟶ K)
    {p : Spec K ⟶ Spec R} (h : p = Spec.map ε) :
    (Scheme.ΓSpecIso R).inv ≫ p.appTop ≫ (Scheme.ΓSpecIso K).hom = ε := by
  subst h
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A rational point of the smooth locus of the closed fibre over a henselian local ring
gives a section.** Let `R'` be henselian local and `q : Y ⟶ Spec R'`. If `q` is smooth on an open
`U` of `Y` and `U` has a point over `Spec κ(R') ⟶ Spec R'`, then `q` has a section: on an affine
open of `U` around that point the residue point of the smooth `R'`-algebra lifts. -/
theorem exists_section_of_smooth_of_residuePoint {R' : Type u} [CommRing R']
    [HenselianLocalRing R'] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R')) (U : Y.Opens)
    (hU : Smooth (U.ι ≫ q)) {K : Type u} [Field K] (ε : R' →+* K) (hε : Function.Surjective ε)
    (σ₀ : Spec (.of K) ⟶ U.toScheme)
    (hσ₀ : σ₀ ≫ U.ι ≫ q = Spec.map (CommRingCat.ofHom ε)) :
    ∃ σ : Spec (.of R') ⟶ Y, σ ≫ q = 𝟙 _ := by
  have hker : RingHom.ker ε = maximalIdeal R' :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε hε)
  let e : K ≃+* ResidueField R' :=
    (RingHom.quotientKerEquivOfSurjective hε).symm.trans (Ideal.quotEquivOfEq hker)
  have he : e.toRingHom.comp ε = residue R' := by
    ext r
    have h1 : (RingHom.quotientKerEquivOfSurjective hε).symm (ε r) =
        Ideal.Quotient.mk (RingHom.ker ε) r :=
      (RingEquiv.symm_apply_eq _).2 (RingHom.quotientKerEquivOfSurjective_apply_mk hε r).symm
    show (Ideal.quotEquivOfEq hker) ((RingHom.quotientKerEquivOfSurjective hε).symm (ε r)) = _
    rw [h1, Ideal.quotEquivOfEq_mk]
    rfl
  obtain ⟨y⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨W₀, hW, hyW, -⟩ := Opens.isBasis_iff_nbhd.1 U.toScheme.isBasis_affineOpens
    (show σ₀ y ∈ (⊤ : U.toScheme.Opens) from trivial)
  let W : U.toScheme.Opens := W₀
  have hrange : Set.range σ₀ ⊆ (W : Set U.toScheme) := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z y]
  let σ₁ : Spec (.of K) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι σ₀ (by rwa [Scheme.Opens.range_ι])
  have hσ₁ : σ₁ ≫ W.ι = σ₀ := IsOpenImmersion.lift_fac _ _ _
  have : IsAffine W.toScheme := hW
  set g : W.toScheme ⟶ Spec (.of R') := W.ι ≫ U.ι ≫ q
  have : Smooth g := MorphismProperty.comp_mem _ _ _ inferInstance hU
  let φ : CommRingCat.of R' ⟶ Γ(W.toScheme, ⊤) := (Scheme.ΓSpecIso (.of R')).inv ≫ g.appTop
  have hg : W.toScheme.isoSpec.inv ≫ g = Spec.map φ := by
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  have hφ : φ.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), ← hg]
    infer_instance
  have h1 : σ₁ ≫ g = Spec.map (CommRingCat.ofHom ε) := by
    simp only [g]
    rw [← Category.assoc, hσ₁, hσ₀]
  have h2 : φ ≫ σ₁.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom = CommRingCat.ofHom ε := by
    simpa only [φ, Scheme.Hom.comp_appTop, Category.assoc] using
      ΓSpecIso_inv_comp_appTop_comp_hom _ h1
  let : Algebra R' Γ(W.toScheme, ⊤) := φ.hom.toAlgebra
  have : Algebra.Smooth R' Γ(W.toScheme, ⊤) := hφ
  let ψ : Γ(W.toScheme, ⊤) →ₐ[R'] ResidueField R' :=
    { toRingHom := e.toRingHom.comp (σ₁.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      commutes' := fun r => by
        have := ConcreteCategory.congr_hom h2 r
        show e ((σ₁.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom (φ r)) = residue R' r
        rw [CommRingCat.hom_comp, RingHom.comp_apply]
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        rw [this]
        exact RingHom.congr_fun he r }
  obtain ⟨s, -⟩ := HenselianLocalRing.exists_algHom_residue_of_smooth ψ
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ W.toScheme.isoSpec.inv ≫ W.ι ≫ U.ι, ?_⟩
  have hs : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext r
    exact s.commutes r
  simp only [Category.assoc]
  rw [show W.toScheme.isoSpec.inv ≫ W.ι ≫ U.ι ≫ q = Spec.map φ from hg, ← Spec.map_comp]
  exact (congrArg Spec.map hs).trans (Spec.map_id _)

/-- **A rational point in the smooth locus of the closed fibre of a nodal family.** Let `R'` be
local with separably closed residue field, and `q : Y ⟶ Spec R'` flat and at-worst-nodal of
relative dimension one with nonempty closed fibre. The closed fibre is geometrically reduced, so
it has a dense open smooth over the residue field ([Stacks, Tag 056V]), which has a rational point;
by flatness `q` is smooth there. -/
theorem exists_smoothLocus_point_of_nodal {R' : Type u} [CommRing R'] [IsLocalRing R']
    [IsSepClosed (ResidueField R')] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R'))
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) [Flat q]
    (hne : Nonempty (q.fiber (closedPoint R'))) :
    ∃ (U : Y.Opens), Smooth (U.ι ≫ q) ∧
      ∃ σ₀ : Spec ((Spec (.of R')).residueField (closedPoint R')) ⟶ U.toScheme,
        σ₀ ≫ U.ι ≫ q = (Spec (.of R')).fromSpecResidueField (closedPoint R') := by
  have : LocallyOfFinitePresentation q := locallyOfFinitePresentation hq.1.1
  set s : Spec (.of R') := closedPoint R'
  set κ := (Spec (.of R')).residueField s
  set f' := q.fiberToSpecResidueField s
  have hGR : GeometricallyReduced f' := geometricallyReduced_fiber_of_nodal q hq s hne
  have : IsReduced (q.fiber s) := isReduced_of_geometricallyReduced (k := κ) f'
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback q ((Spec (.of R')).fromSpecResidueField s)) inferInstance
  have : LocallyOfFiniteType f' := inferInstance
  obtain ⟨V, hVd, hVs⟩ := (geometricallyReduced_iff_exists_dense_open_smooth (k := κ) f').1 hGR
  have : Nonempty V := hVd.nonempty.to_subtype
  have : IsSepClosed κ := IsSepClosed.of_ringEquiv (residueFieldAtClosedPointEquiv (R := .of R'))
  have := hVs
  obtain ⟨σ₁, hσ₁⟩ := Stacks.AbelMap.exists_section_of_isSepClosed (k := κ) (V.ι ≫ f')
  set τ := σ₁ ≫ V.ι ≫ q.fiberι s
  have hτ : τ ≫ q = (Spec (.of R')).fromSpecResidueField s := by
    have hc : q.fiberι s ≫ q = f' ≫ (Spec (.of R')).fromSpecResidueField s := pullback.condition
    simp only [τ, Category.assoc, hc]
    rw [← Category.assoc, ← Category.assoc, Category.assoc σ₁, hσ₁, Category.id_comp]
  have hV : V ≤ f'.smoothLocus := by
    have h1 := (Scheme.Hom.smoothLocus_eq_top_iff (f := V.ι ≫ f')).2 hVs
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h1
    intro x hx
    exact (h1 ▸ trivial : (⟨x, hx⟩ : V.toScheme) ∈ V.ι ⁻¹ᵁ f'.smoothLocus)
  have hloc : f'.smoothLocus = q.fiberι s ⁻¹ᵁ q.smoothLocus :=
    Scheme.Hom.smoothLocus_eq_preimage_of_isPullback
      (IsPullback.of_hasPullback q ((Spec (.of R')).fromSpecResidueField s)) (Or.inl ‹Flat q›)
  have hrange : Set.range τ ⊆ (q.smoothLocus : Set Y) := by
    rintro _ ⟨z, rfl⟩
    have h1 : V.ι (σ₁ z) ∈ f'.smoothLocus := hV (σ₁ z).2
    rwa [hloc] at h1
  refine ⟨q.smoothLocus, smooth_smoothLocus_ι_comp q,
    IsOpenImmersion.lift q.smoothLocus.ι τ (by rwa [Scheme.Opens.range_ι]), ?_⟩
  rwa [← Category.assoc, IsOpenImmersion.lift_fac]

/-- A flat proper at-worst-nodal family of relative dimension one with nonempty total space over
a henselian local ring with separably closed residue field has a section. -/
theorem exists_section_of_nodal {R' : Type u} [CommRing R'] [HenselianLocalRing R']
    [IsSepClosed (ResidueField R')] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R'))
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) [Flat q] [IsProper q] [Nonempty Y] :
    ∃ σ : Spec (.of R') ⟶ Y, σ ≫ q = 𝟙 _ := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  set s : Spec (.of R') := closedPoint R'
  have hne : Nonempty (q.fiber s) := by
    have hcl : IsClosed (Set.range q) := (Scheme.Hom.isClosedMap q).isClosed_range
    have hmem : s ∈ Set.range q :=
      (IsLocalRing.specializes_closedPoint (q y)).mem_closed hcl ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hmem
    obtain ⟨z, -⟩ : y' ∈ Set.range (q.fiberι s) := by rwa [Scheme.Hom.range_fiberι q s]
    exact ⟨z⟩
  obtain ⟨U, hU, σ₀, hσ₀⟩ := exists_smoothLocus_point_of_nodal q hq hne
  let ε : CommRingCat.of R' ⟶ (Spec (.of R')).residueField s :=
    Spec.preimage ((Spec (.of R')).fromSpecResidueField s)
  have hε : Spec.map ε = (Spec (.of R')).fromSpecResidueField s := Spec.map_preimage _
  have hsurj : Function.Surjective ε.hom := by
    have h' := (ΓSpecIso_inv_comp_appTop_comp_hom ε hε.symm).symm
    rw [h']
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
      (fromSpecResidueField_closedPoint_appTop_surjective R')).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  exact exists_section_of_smooth_of_residuePoint q U hU ε.hom hsurj σ₀ (hσ₀.trans hε.symm)

end AlgebraicGeometry

end
