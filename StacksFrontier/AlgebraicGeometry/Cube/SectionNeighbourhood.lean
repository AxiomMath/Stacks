module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Cube.SeesawClosed
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# A section trivializing an invertible module on a fibre trivializes it nearby

Let `f : X ⟶ Spec R` be proper, `N` an invertible `𝒪_X`-module, `𝔭` a prime of `R` and `s` a
global section of `N` whose pullback to the fibre `X_𝔭 = X ×_R Spec κ(𝔭)` trivializes the
pullback of `N` there (it is carried to a unit by an isomorphism with `𝒪_{X_𝔭}`). Then `N` is
already trivial over `f⁻¹(D(g))` for some `g ∉ 𝔭`.

The nonvanishing locus `X_s` is open (Stacks 01CY), and its inverse image in the fibre is the
nonvanishing locus of the pulled-back section (Stacks 0H78), which is everything because that
section corresponds to a unit. So the closed set `X ∖ X_s` misses the fibre, and its image under
the closed map `f` is a closed subset of `Spec R` not containing `𝔭`; a basic open `D(g) ∋ 𝔭`
avoiding it has `f⁻¹(D(g)) ⊆ X_s`, and there `s` vanishes nowhere, so it trivializes `N` (Stacks
01CY).

This is the step of the theorem of the cube that spreads a trivialization from a fibre to a
neighbourhood of it.

## Main results

* `AlgebraicGeometry.Cube.nonvanishingLocus_hom_app_top_of_iso`: an isomorphism of modules
  preserves the nonvanishing locus of a global section.
* `AlgebraicGeometry.Cube.nonvanishingLocus_pullbackSectionHom_top`: [Stacks, Tag 0H78] for
  `AlgebraicGeometry.pullbackSectionHom`.
* `AlgebraicGeometry.Cube.exists_basicOpen_nonempty_iso_unit`: the spreading-out statement.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Cube

/-- An isomorphism of `𝒪_X`-modules carries the nonvanishing locus of a global section to that
of its image: the map on stalks is a linear isomorphism, so it preserves `𝔪_x · M_x`. -/
theorem nonvanishingLocus_hom_app_top_of_iso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M')
    (t : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus M' (e.hom.val.app (op ⊤) t) =
      Stacks.Ample.nonvanishingLocus M t := by
  ext x
  change _ ∉ Stacks.ModuleStalk.maximalSmul M' x ↔ _ ∉ Stacks.ModuleStalk.maximalSmul M x
  refine not_congr ?_
  let φ := LinearEquiv.ofBijective (stalkLinearMap M M' e.hom x)
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse e.hom e.inv e.hom_inv_id
      e.inv_hom_id x)
  have hg : (M'.presheaf.Γgerm x).hom (e.hom.val.app (op ⊤) t) =
      φ ((M.presheaf.Γgerm x).hom t) :=
    (stalkLinearMap_germ M M' e.hom ⊤ x trivial t).symm
  rw [hg]
  exact (Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv _ φ _).symm

/-- The pullback of a global section along the unit of the pullback adjunction, over `⊤`, is the
pullback of [Stacks, Tag 0H78]. -/
private theorem pullbackSectionHom_top_eq {X' X : Scheme.{u}} (i : X' ⟶ X) (M : X.Modules)
    (h : (⊤ : X'.Opens) ≤ i ⁻¹ᵁ (⊤ : X.Opens)) (s : Γ(M, ⊤)) :
    pullbackSectionHom i M ⊤ ⊤ h s = Stacks.NonvanishingPullback.pullbackGlobalSection i M s := by
  have key : ∀ (a : op (⊤ : X'.Opens) ⟶ op (⊤ : X'.Opens))
      (t : Γ((Scheme.Modules.pullback i).obj M, ⊤)),
      ((Scheme.Modules.pullback i).obj M).presheaf.map a t = t := fun a t => by
    rw [Subsingleton.elim a (𝟙 _),
      ((Scheme.Modules.pullback i).obj M).presheaf.map_id, ConcreteCategory.id_apply]
  change ((Scheme.Modules.pullback i).obj M).presheaf.map (homOfLE h).op
      (Stacks.NonvanishingPullback.pullbackGlobalSection i M s) = _
  exact key _ _

/-- **[Stacks, Tag 0H78] for `AlgebraicGeometry.pullbackSectionHom`.** -/
theorem nonvanishingLocus_pullbackSectionHom_top {X' X : Scheme.{u}} (i : X' ⟶ X) (M : X.Modules)
    (h : (⊤ : X'.Opens) ≤ i ⁻¹ᵁ (⊤ : X.Opens)) (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback i).obj M)
        (pullbackSectionHom i M ⊤ ⊤ h s) =
      i ⁻¹' Stacks.Ample.nonvanishingLocus M s := by
  rw [pullbackSectionHom_top_eq]
  exact (Stacks.NonvanishingPullback.preimage_nonvanishingLocus i M s).symm

/-- **Spreading a trivialization out from a fibre.** Let `f : X ⟶ Spec R` be proper, `N` an
invertible `𝒪_X`-module, `𝔭` a prime of `R` and `s` a global section of `N` whose pullback to the
fibre over `𝔭` is carried to a unit by an isomorphism of the pullback of `N` with the structure
sheaf.
Then `N` is trivial over `f⁻¹(D(g))` for some `g ∉ 𝔭`. -/
theorem exists_basicOpen_nonempty_iso_unit {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (N : X.Modules)
    (hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N)
    (𝔭 : PrimeSpectrum R) (s : Γ(N, ⊤))
    (e : (Scheme.Modules.pullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))))).obj N ≅
      SheafOfModules.unit _)
    (hs : IsUnit (show Γ(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap R 𝔭.asIdeal.ResidueField))), ⊤) from
      e.hom.val.app (op ⊤) (pullbackSectionHom (pullback.fst f _) N ⊤ ⊤ le_rfl s))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ Nonempty ((Scheme.Modules.pullback
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen (R := CommRingCat.of R) g).ι).obj N ≅
        SheafOfModules.unit _) := by
  have hN' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
  have : Stacks.Ample.IsInvertibleModule X N := hN'
  let φ := Spec.map (CommRingCat.ofHom (algebraMap R 𝔭.asIdeal.ResidueField))
  let j := pullback.fst f φ
  let A : Set X := Stacks.Ample.nonvanishingLocus N s
  -- the fibre over `𝔭` lies in the nonvanishing locus of `s`
  have hfib : ∀ y, j y ∈ A := fun y => by
    have h1 := nonvanishingLocus_pullbackSectionHom_top j N le_rfl s
    have h2 := nonvanishingLocus_hom_app_top_of_iso e (pullbackSectionHom j N ⊤ ⊤ le_rfl s)
    have h3 : y ∈ Stacks.Ample.nonvanishingLocus (SheafOfModules.unit _)
        (e.hom.val.app (op ⊤) (pullbackSectionHom j N ⊤ ⊤ le_rfl s)) := by
      intro hm
      have hmem := Stacks.Ample.mem_maximalIdeal_of_mem_maximalSmul _ y hm
      have hg := Stacks.Ample.unitStalkFun_Γgerm (pullback f φ) y
        (e.hom.val.app (op ⊤) (pullbackSectionHom j N ⊤ ⊤ le_rfl s))
      exact IsLocalRing.notMem_maximalIdeal.mpr (hs.map ((pullback f φ).presheaf.Γgerm y).hom)
        (hg ▸ hmem)
    have hy := h1 ▸ h2 ▸ h3
    exact hy
  -- the image of the vanishing locus is a closed set missing `𝔭`
  have hp : 𝔭 ∉ f '' Aᶜ := by
    rintro ⟨x, hx, hfx⟩
    have hx' : x ∈ Set.range j := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hfx]
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum 𝔭.asIdeal.ResidueField), ?_⟩
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap R 𝔭.asIdeal.ResidueField) ⊥ = 𝔭.asIdeal
      rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    obtain ⟨y, rfl⟩ := hx'
    exact hx (hfib y)
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := CommRingCat.of R)).exists_subset_of_mem_open
      (show 𝔭 ∈ (f '' Aᶜ)ᶜ from hp)
      (f.isClosedMap _
        (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X N s).isClosed_compl).isOpen_compl
  refine ⟨g, hpg, ?_⟩
  -- over `f⁻¹(D(g))` the section vanishes nowhere, so it trivializes `N`
  let U := f ⁻¹ᵁ PrimeSpectrum.basicOpen (R := CommRingCat.of R) g
  have hU : ∀ x ∈ U, x ∈ A := fun x hx =>
    Classical.byContradiction fun hxA => hsub hx ⟨x, hxA, rfl⟩
  let L' := (Scheme.Modules.pullback U.ι).obj N
  have : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.presheaf
      U.toScheme.ringCatSheaf.property L' := isInvertible_pullback U.ι N
  let t := pullbackSectionHom U.ι N ⊤ ⊤ le_rfl s
  have ht : Stacks.Ample.nonvanishingLocus L' t = Set.univ :=
    (nonvanishingLocus_pullbackSectionHom_top U.ι N le_rfl s).trans
      (Set.eq_univ_of_forall fun x => hU _ x.2)
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L'
    ((Stacks.NonvanishingSpelling.sectionsEquiv U.toScheme L').symm t)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq U.toScheme L' t).trans ht)
  exact ⟨(asIso (L'.unitHomEquiv.symm
    ((Stacks.NonvanishingSpelling.sectionsEquiv U.toScheme L').symm t))).symm⟩

end AlgebraicGeometry.Cube

end
