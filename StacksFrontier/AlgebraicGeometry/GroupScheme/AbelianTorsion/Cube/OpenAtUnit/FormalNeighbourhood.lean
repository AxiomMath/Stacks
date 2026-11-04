module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective
public import StacksFrontier.AlgebraicGeometry.Descent.NonvanishingSectionNearFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An invertible module trivial on every thickening of a fibre is trivial near the fibre

Let `R` be a Noetherian ring, `I ⊆ R` an ideal, `f : P ⟶ Spec R` a proper morphism and `ℒ` an
invertible `𝒪_P`-module.  Write `P_n = P ×_{Spec R} Spec(R / I^{n+1})` for the thickenings of
`P_0 = P ×_{Spec R} Spec(R / I)`.  If `ℒ` is trivial on every `P_n`, then:

* some global section `s` of `ℒ` vanishes at no point of `P_0`;
* for every point `x ∈ Spec R` with `I ⊆ 𝔭_x`, `ℒ` is trivial over `P ×_{Spec R} U` for some open
  neighbourhood `U` of `x`.

The first statement is the stabilization clause of the theorem on formal functions at `p = 0`
([Stacks, Tag 02OB], with [Stacks, Tag 02O8] proved): the images in `Γ(ℒ / Iℒ)` of
`Γ(ℒ / I^{c+1}ℒ)` and of `Γ(ℒ)` agree for some `c`, and a trivialization of `ℒ` on `P_c` gives a
generator of `ℒ / I^{c+1}ℒ`.  The second is the tube lemma for the closed map `f`,
`AlgebraicGeometry.SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus`.

This is the general form of the argument of
`Stacks.Models.RegularProperModelSituation.nonempty_iso_unit_of_forall_truncation`, where `R` is a
discrete valuation ring and `I` its maximal ideal; it is step 1(b) of the cube proof.

## Main results

* `Stacks.FormalNeighbourhood.exists_forall_mem_nonvanishingLocus_of_forall_truncation`: the
  section nonvanishing on `P_0`.
* `Stacks.FormalNeighbourhood.exists_isTrivial_of_forall_truncation`: triviality near a point of
  `V(I)`.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow
  moduleGlobalSectionsRightDerivedZeroIso)
open Stacks.Algebraization (idealPowerQuotient idealPowerMultiple idealPowerQuotientDrop
  idealQuotientPushforwardIso idealQuotientPushforwardMap_π idealPowerQuotientDrop_π
  idealPowerQuotientDrop_π_assoc pushforwardSectionComparison
  unit_comp_pushforwardSectionComparison)

universe u

namespace Stacks.FormalNeighbourhood

variable {R : Type u} [CommRing R] {P : Scheme.{u}} (f : P ⟶ Spec (.of R)) (I : Ideal R)

/-! ### The thickenings -/

/-- The closed immersion `Spec(R / I^{n+1}) ⟶ Spec R`. -/
abbrev truncationBase (n : ℕ) : Spec (.of (R ⧸ I ^ (n + 1))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

/-- The thickening `P_n = P ×_{Spec R} Spec(R / I^{n+1})`. -/
abbrev truncation (n : ℕ) : Scheme.{u} := pullback f (truncationBase I n)

/-- The closed immersion `P_n ⟶ P`. -/
abbrev truncationι (n : ℕ) : truncation f I n ⟶ P := pullback.fst f (truncationBase I n)

/-- `Spec(R / I^{n+1}) ⟶ Spec R` is a closed immersion. -/
instance isClosedImmersion_truncationBase (n : ℕ) :
    IsClosedImmersion (truncationBase I n) :=
  IsClosedImmersion.spec_of_quotient_mk (R := .of R) _

/-- `P_n ⟶ P` is a closed immersion. -/
instance isClosedImmersion_truncationι (n : ℕ) : IsClosedImmersion (truncationι f I n) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst f (truncationBase I n)))

/-- The ideal sheaf of `P_n ⊆ P` is `(I · 𝒪_P) ^ (n + 1)`. -/
theorem ker_truncationι (n : ℕ) :
    (truncationι f I n).ker = baseIdealSheaf R I f ^ (n + 1) := by
  rw [← baseIdealSheaf_pow]
  exact (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst _ _ _).symm

/-- The morphism `Spec(R / I) ⟶ Spec(R / I^{n+1})`. -/
@[ega "I 10.6.1" "special case"]
def truncationBaseTransition (n : ℕ) :
    Spec (.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.zero_le n) 1))))

/-- The composite `Spec(R / I) ⟶ Spec(R / I^{n+1}) ⟶ Spec R` is the closed immersion
`Spec(R / I) ⟶ Spec R`. -/
theorem truncationBaseTransition_comp (n : ℕ) :
    truncationBaseTransition I n ≫ truncationBase I n = truncationBase I 0 := by
  rw [truncationBaseTransition, truncationBase, truncationBase, ← Spec.map_comp]
  congr 1

/-- The closed immersion `P_0 ⟶ P_n`. -/
def truncationTransition (n : ℕ) : truncation f I 0 ⟶ truncation f I n :=
  pullback.map f (truncationBase I 0) f (truncationBase I n) (𝟙 _)
    (truncationBaseTransition I n) (𝟙 _) (by simp)
    (by rw [Category.comp_id, truncationBaseTransition_comp I n])

/-- The composite `P_0 ⟶ P_n ⟶ P` is the closed immersion `P_0 ⟶ P`. -/
@[reassoc (attr := simp)]
theorem truncationTransition_comp_truncationι (n : ℕ) :
    truncationTransition f I n ≫ truncationι f I n = truncationι f I 0 := by
  rw [truncationTransition, truncationι, truncationι, pullback.lift_fst, Category.comp_id]

variable (L : P.Modules) [L.IsQuasicoherent]

/-- **[Stacks, Tag 0EL1] at the thickenings.** `ℒ / I^{n+1}ℒ` is the direct image of the
restriction of `ℒ` to `P_n`. -/
def truncationQuotientIso (n : ℕ) :
    idealPowerQuotient (baseIdealSheaf R I f) (n + 1) L ≅
      (Scheme.Modules.pushforward (truncationι f I n)).obj
        ((Scheme.Modules.pullback (truncationι f I n)).obj L) :=
  idealQuotientPushforwardIso (baseIdealSheaf R I f) (n + 1) L (truncationι f I n)
    (ker_truncationι f I n)

/-- Composed with `truncationQuotientIso`, the quotient map `ℒ ⟶ ℒ / I^{n+1}ℒ` is the unit of the
adjunction between pullback and pushforward along `P_n ⟶ P`. -/
theorem π_comp_truncationQuotientIso_hom (n : ℕ) :
    cokernel.π (C := P.Modules)
        (idealPowerMultiple (baseIdealSheaf R I f) (n + 1) L).ι ≫
        (truncationQuotientIso f I L n).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (truncationι f I n)).unit.app L :=
  idealQuotientPushforwardMap_π _ _ _ _ (ker_truncationι f I n)

/-- Lowering the exponent is restriction along `P_0 ⟶ P_n`. -/
theorem drop_comp_truncationQuotientIso_hom (n : ℕ) :
    idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 n) L ≫
        (truncationQuotientIso f I L 0).hom =
      (truncationQuotientIso f I L n).hom ≫
        pushforwardSectionComparison (truncationTransition f I n) (truncationι f I n)
          (truncationTransition_comp_truncationι f I n) L := by
  rw [← cancel_epi (cokernel.π (C := P.Modules)
    (idealPowerMultiple (baseIdealSheaf R I f) (n + 1) L).ι),
    idealPowerQuotientDrop_π_assoc, ← Category.assoc (cokernel.π _)
      (truncationQuotientIso f I L n).hom, π_comp_truncationQuotientIso_hom f I L n,
    unit_comp_pushforwardSectionComparison]
  exact π_comp_truncationQuotientIso_hom f I L 0

/-- **The theorem on formal functions at `p = 0`.** For a coherent `ℒ` there is a `c` such that
every global section of `ℒ / I^{c+1}ℒ` agrees in `ℒ / Iℒ` with a global section of `ℒ`. -/
theorem exists_forall_exists_π_eq_drop [IsNoetherianRing R] [IsProper f] (L : P.Modules)
    (hL : Stacks.SheafOfModules.IsCoherent L) :
    ∃ c : ℕ, ∀ t : Γ(idealPowerQuotient (baseIdealSheaf R I f) (c + 1) L, ⊤),
      ∃ s : Γ(L, ⊤),
        (cokernel.π (C := P.Modules)
            (idealPowerMultiple (baseIdealSheaf R I f) (0 + 1) L).ι).app ⊤ s =
          (idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 c) L).app ⊤ t := by
  obtain ⟨c, -, -, hrange⟩ :=
    Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8
      R f inferInstance I L hL 0
      Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  refine ⟨c, fun t => ?_⟩
  have hr := hrange 1 (c + 1) (by omega)
  set E := moduleGlobalSectionsRightDerivedZeroIso P
  set t' := (E.inv.app _).hom t
  have hmem : (((AlgebraicGeometry.moduleGlobalSections P).rightDerived 0).map
      (idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 c) L)).hom t' ∈
      LinearMap.range (((AlgebraicGeometry.moduleGlobalSections P).rightDerived 0).map
        (cokernel.π (C := P.Modules)
          (idealPowerMultiple (baseIdealSheaf R I f) 1 L).ι)).hom := by
    rw [← hr]
    exact ⟨t', rfl⟩
  obtain ⟨s', hs'⟩ := hmem
  refine ⟨(E.hom.app L).hom s', ?_⟩
  have nat {A B : P.Modules} (g : A ⟶ B) (u) := LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.1 (E.hom.naturality g)) u
  have h1 := nat (cokernel.π (C := P.Modules)
    (idealPowerMultiple (baseIdealSheaf R I f) 1 L).ι) s'
  have h2 := nat (idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 c) L) t'
  have h3 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (E.inv_hom_id_app
    (idealPowerQuotient (baseIdealSheaf R I f) (c + 1) L))) t
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id,
    LinearMap.id_coe] at h1 h2 h3
  have h3' : (E.hom.app _).hom t' = t := h3
  refine h1.symm.trans ?_
  rw [hs', h2, h3']
  rfl

/-! ### Triviality on the thickenings -/

/-- **A section vanishing nowhere on `P_0`.** If the invertible module `ℒ` is trivial on every
thickening `P_n`, some global section of `ℒ` vanishes at no point of `P_0`: by the theorem on
formal functions at `p = 0`, the image of a generator of `ℒ / I^{c+1}ℒ` in `ℒ / Iℒ` lifts to a
global section, and it generates `ℒ` along `P_0`. -/
theorem exists_forall_mem_nonvanishingLocus_of_forall_truncation [IsNoetherianRing R]
    [IsProper f] (L : P.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.property L]
    (htriv : ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (truncationι f I n)).obj L ≅
      SheafOfModules.unit (truncation f I n).ringCatSheaf)) :
    ∃ s : Γ(L, ⊤), ∀ y, (truncationι f I 0).base y ∈ Stacks.Ample.nonvanishingLocus L s := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian f
  have hL' : Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L := hL
  have : L.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible L
  have hcoh : Stacks.SheafOfModules.IsCoherent L :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible P L)
  obtain ⟨c, hc⟩ := exists_forall_exists_π_eq_drop f I L hcoh
  obtain ⟨e⟩ := htriv c
  set τ := e.inv.app ⊤ (show Γ(SheafOfModules.unit (truncation f I c).ringCatSheaf, ⊤) from
    (1 : Γ(truncation f I c, ⊤)))
  obtain ⟨s, hs⟩ := hc ((truncationQuotientIso f I L c).inv.app ⊤ τ)
  have hτ : Stacks.Ample.nonvanishingLocus _ τ = Set.univ :=
    (Stacks.Ample.nonvanishingLocus_congr e.symm _).trans
      (Stacks.Models.nonvanishingLocus_unit_one _)
  refine ⟨s, fun y => ?_⟩
  have h := (Stacks.Models.nonvanishingLocus_unit_app_top (truncationι f I 0) L s).symm.trans
    ((congrArg (Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback (truncationι f I 0)).obj L))
        (Stacks.Models.app_top_eq_of_comp_eq _ _ _ _ _ _
          (π_comp_truncationQuotientIso_hom f I L 0) (drop_comp_truncationQuotientIso_hom f I L c)
          s _ hs)).trans
      ((Stacks.Models.nonvanishingLocus_pushforwardSectionComparison_app_top _ _ _ L _).trans
        (by rw [hτ, Set.preimage_univ])))
  exact (Set.ext_iff.mp h y).mpr trivial

/-- **An invertible module trivial on every thickening of the fibre over `V(I)` is trivial near
each point of `V(I)`.** Let `R` be Noetherian, `f : P ⟶ Spec R` proper and `ℒ` invertible on `P`,
trivial on every `P_n = P ×_{Spec R} Spec(R / I^{n+1})`.  Then for every `x ∈ Spec R` lying in
`V(I)` there is an open `U ∋ x` with `ℒ` trivial over `P ×_{Spec R} U`. -/
theorem exists_isTrivial_of_forall_truncation [IsNoetherianRing R] [IsProper f] (L : P.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.property L]
    (htriv : ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (truncationι f I n)).obj L ≅
      SheafOfModules.unit (truncation f I n).ringCatSheaf))
    (x : Spec (.of R)) (hx : x ∈ Set.range (truncationBase I 0).base) :
    ∃ U : (Spec (.of R)).Opens, x ∈ U ∧
      AlgebraicGeometry.SheafOfModules.IsTrivial (pullback f U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback f U.ι).IsSheaf)
        ((RingedSpaceModuleAdjunction.modulePullback
          (pullback.fst f U.ι).toLRSHom.toShHom).obj L) := by
  obtain ⟨s, hs⟩ := exists_forall_mem_nonvanishingLocus_of_forall_truncation f I L htriv
  have : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  refine
    AlgebraicGeometry.SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus
      f L f.isClosedMap ((Stacks.NonvanishingSpelling.sectionsEquiv P L).symm s) x ?_
  intro y hy
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
  have hmem : y ∈ Set.range (truncationι f I 0).base := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hy]
    exact hx
  obtain ⟨z, rfl⟩ := hmem
  exact hs z

end Stacks.FormalNeighbourhood

end
