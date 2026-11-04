module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberRedUnits
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Picard groups of models: injectivity on torsion of restriction to the reduced special fibre

In the situation of [Stacks, Tag 0C61], let `h` be an integer prime to the characteristic of the
residue field `k`. [Stacks, Tag 0CAE] says that restriction of invertible modules
`Pic(X)[h] ⟶ Pic((X_k)_red)[h]` is injective. This file proves it.

The source's proof runs through the truncations `X_n = X ×_{Spec R} Spec(R/π^{n+1})`.

* `(X_k)_red ⟶ X_n` is a thickening, and restriction is injective on `h`-torsion along it by
  [Stacks, Tag 0C6S]. In this development that tag is stated with the units condition
  `Stacks.Thickenings.GlobalUnitsPowerLift`, without which it fails; the condition holds here by
  `Stacks.Models.RegularProperModelSituation.globalUnitsPowerLift_specialFiberRedToTruncation`,
  because the global functions on `(X_k)_red` form a field purely inseparable over `k`.
* An invertible module `ℒ` trivial on every `X_n` is trivial. The source computes
  `H⁰(X, ℒ)^∧ ≅ R^∧` by the theorem on formal functions and takes a generator. Here the
  stabilization clause of the theorem on formal functions ([Stacks, Tag 02OB] at `p = 0`, with
  [Stacks, Tag 02O8] proved) produces directly a global section `s` of `ℒ` which restricts to a
  generator on the special fibre `X_0`. The nonvanishing locus of `s` is open
  ([Stacks, Tag 01CY]) and contains `X_0` ([Stacks, Tag 0H78]), and `X ⟶ Spec(R)` is proper with
  `R` local, so it is all of `X` and `s` trivializes `ℒ`.

## Main results

* `RegularProperModelSituation.exists_forall_exists_π_eq_drop`: the stabilization clause of the
  theorem on formal functions for a coherent module on the model.
* `RegularProperModelSituation.nonempty_iso_unit_of_forall_truncation`: an invertible module
  trivial on every truncation is trivial.
* `RegularProperModelSituation.eq_zero_of_forall_schemePullbackClass_truncationι_eq_zero`: the
  same in `Pic(X)`.
* `injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion`: **[Stacks, Tag 0CAE]**.

## Implementation notes

The quotient `ℒ / π^{n+1} ℒ` of the theorem on formal functions is identified with the direct
image of `ℒ|_{X_n}` by [Stacks, Tag 0EL1] (`Stacks.Algebraization.idealQuotientPushforwardIso`),
the ideal sheaf of `X_n ⊆ X` being `((π) · 𝒪_X)^{n+1}`; under these identifications lowering the
exponent is restriction along `X_0 ⟶ X_n`. The comparisons of sections are proved for arbitrary
schemes and then instantiated: stated directly for the truncations, the kernel spends its time
unfolding the fibre products when it checks the identifications `Γ(v_* ℳ, ⊤) = Γ(ℳ, ⊤)`.

## References

* [Stacks Project, Tag 0CAE](https://stacks.math.columbia.edu/tag/0CAE)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf baseIdealSheaf_pow
  moduleGlobalSectionsRightDerivedZeroIso)
open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom
  zsmulTorsion mem_zsmulTorsion schemePullbackClass_comp
  mapsTo_zsmulTorsion picardRepresentative classOf_picardRepresentative pullbackClass_classOf)
open Stacks.SheafOfModules (picardClass picardClass_eq_iff isInvertible_unit)
open Stacks.RingedSpace (structureIsSheaf modulePullback_isInvertible_of)
open Stacks.Algebraization (idealPowerQuotient idealPowerMultiple idealPowerQuotientDrop
  idealQuotientPushforwardIso idealQuotientPushforwardMap_π idealPowerQuotientDrop_π
  idealPowerQuotientDrop_π_assoc
  pushforwardSectionComparison unit_comp_pushforwardSectionComparison)

universe u

namespace Stacks.Models

/-! ### Sections along a factorization, and their nonvanishing loci -/

/-- The direct-image comparison along a factorization `a ≫ b = c`, read on global sections, is
restriction along `a` followed by the identification `a^* b^* ≅ c^*`. -/
theorem pushforwardSectionComparison_app_top {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules)
    (z : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    (pushforwardSectionComparison a b hw M).app ⊤ z =
      ((Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M)).app ⊤ z) := by
  simp only [pushforwardSectionComparison, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  have h : ∀ {U : A.Opens} (i : U ⟶ U) (x : Γ((Scheme.Modules.pullback c).obj M, U)),
      ((Scheme.Modules.pullback c).obj M).presheaf.map i.op x = x := by
    intro U i x
    rw [Subsingleton.elim i (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  exact h _ _

/-- **[Stacks, Tag 0H78] for the pullback of a global section along the adjunction unit.** The
nonvanishing locus of `v^* m` is the inverse image of the nonvanishing locus of `m`. -/
theorem nonvanishingLocus_unit_app_top {Y Z : Scheme.{u}} (v : Y ⟶ Z) (M : Z.Modules)
    (m : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback v).obj M)
        (((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app M).app ⊤ m) =
      v.base ⁻¹' Stacks.Ample.nonvanishingLocus M m :=
  (Stacks.NonvanishingPullback.preimage_nonvanishingLocus v M m).symm

/-- The unit section of the structure sheaf vanishes nowhere. -/
theorem nonvanishingLocus_unit_one (Y : Scheme.{u}) :
    Stacks.Ample.nonvanishingLocus (SheafOfModules.unit Y.ringCatSheaf)
      (show Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) from (1 : Γ(Y, ⊤))) = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one Y x _ rfl

/-- **[Stacks, Tag 0H78] along a factorization.** The nonvanishing locus of the section of
`c^* ℳ` obtained from a section `z` of `b^* ℳ` by the direct-image comparison along
`a ≫ b = c` is the inverse image of the nonvanishing locus of `z` along `a`. -/
theorem nonvanishingLocus_pushforwardSectionComparison_app_top {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules)
    (z : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback c).obj M)
        ((pushforwardSectionComparison a b hw M).app ⊤ z) =
      a.base ⁻¹' Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback b).obj M) z := by
  subst hw
  refine Eq.trans (congrArg (Stacks.Ample.nonvanishingLocus
    ((Scheme.Modules.pullback (a ≫ b)).obj M))
    (pushforwardSectionComparison_app_top a b rfl M z)) ?_
  refine (Stacks.Ample.nonvanishingLocus_congr
    ((Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr rfl).app M)
    _).trans ?_
  exact nonvanishingLocus_unit_app_top _ _ z

/-- Chasing a global section through a commutative diagram of modules: if `π ≫ i₁ = u` and
`d ≫ i₁ = iₖ ≫ C` with `i₁`, `iₖ` isomorphisms, and `π s = d (iₖ⁻¹ τ)`, then `u s = C τ`. -/
theorem app_top_eq_of_comp_eq {X : Scheme.{u}} {L Q₁ Qₖ P₁ Pₖ : X.Modules} (π : L ⟶ Q₁)
    (d : Qₖ ⟶ Q₁) (i₁ : Q₁ ≅ P₁) (iₖ : Qₖ ≅ Pₖ) (C : Pₖ ⟶ P₁) (u : L ⟶ P₁)
    (h₁ : π ≫ i₁.hom = u) (h₂ : d ≫ i₁.hom = iₖ.hom ≫ C) (s : Γ(L, ⊤)) (τ : Γ(Pₖ, ⊤))
    (hs : π.app ⊤ s = d.app ⊤ (iₖ.inv.app ⊤ τ)) : u.app ⊤ s = C.app ⊤ τ := by
  subst h₁
  have h3 := congrArg (fun φ => φ.app ⊤ τ) iₖ.inv_hom_id
  have h2 := congrArg (fun φ => φ.app ⊤ (iₖ.inv.app ⊤ τ)) h₂
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] at h2 h3 ⊢
  rw [hs, h2, h3]

end Stacks.Models

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The truncations and the theorem on formal functions -/

/-- The ideal `(π)` of the discrete valuation ring. -/
abbrev uniformizerIdeal : Ideal S.R := Ideal.span {S.π}

/-- The ideal sheaf `(π) · 𝒪_X` cutting the special fibre out of the model. -/
abbrev uniformizerIdealSheaf : S.X.IdealSheafData :=
  baseIdealSheaf S.R S.uniformizerIdeal S.X_to_R

/-- The morphism `Spec(R/π^{n+1}) ⟶ Spec(R)` is a closed immersion. -/
instance isClosedImmersion_truncationBase (n : ℕ) : IsClosedImmersion (S.truncationBase n) :=
  IsClosedImmersion.spec_of_quotient_mk (R := .of S.R) _

/-- The inclusion `X_n ⟶ X` of the `n`th truncation is a closed immersion. -/
instance isClosedImmersion_truncationι (n : ℕ) : IsClosedImmersion (S.truncationι n) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst S.X_to_R (S.truncationBase n)))

/-- The ideal sheaf of the `n`th truncation `X_n ⊆ X` is `((π) · 𝒪_X) ^ (n + 1)`. -/
theorem ker_truncationι (n : ℕ) :
    (S.truncationι n).ker = S.uniformizerIdealSheaf ^ (n + 1) := by
  rw [← baseIdealSheaf_pow]
  exact (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst _ _ _).symm

/-- The morphism `Spec(R/π) ⟶ Spec(R/π^{n+1})` between truncated bases. -/
@[ega "I 10.6.1" "special case"]
def truncationBaseTransition (n : ℕ) :
    Spec (.of (S.truncationRing 0)) ⟶ Spec (.of (S.truncationRing n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_add_left 1 n) : S.truncationIdeal n ≤ S.truncationIdeal 0)))

/-- The composite `Spec(R/π) ⟶ Spec(R/π^{n+1}) ⟶ Spec(R)` is the inclusion of `Spec(R/π)`. -/
theorem truncationBaseTransition_comp (n : ℕ) :
    S.truncationBaseTransition n ≫ S.truncationBase n = S.truncationBase 0 := by
  rw [truncationBaseTransition, truncationBase, truncationBase, ← Spec.map_comp]
  congr 1

/-- The closed immersion `X_0 ⟶ X_n` of the special fibre into the `n`th truncation. -/
def truncationTransition (n : ℕ) : S.truncation 0 ⟶ S.truncation n :=
  pullback.map S.X_to_R (S.truncationBase 0) S.X_to_R (S.truncationBase n) (𝟙 _)
    (S.truncationBaseTransition n) (𝟙 _) (by simp)
    (by rw [Category.comp_id, S.truncationBaseTransition_comp n])

/-- The composite `X_0 ⟶ X_n ⟶ X` is the inclusion of the special fibre. -/
@[reassoc (attr := simp)]
theorem truncationTransition_comp_truncationι (n : ℕ) :
    S.truncationTransition n ≫ S.truncationι n = S.truncationι 0 := by
  rw [truncationTransition, truncationι, truncationι, pullback.lift_fst, Category.comp_id]

variable (L : S.X.Modules) [L.IsQuasicoherent]

/-- **[Stacks, Tag 0EL1] at the truncations.** The quotient `ℒ / π^{n+1} ℒ` is the direct image
of the restriction of `ℒ` to the `n`th truncation. -/
def truncationQuotientIso (n : ℕ) :
    idealPowerQuotient S.uniformizerIdealSheaf (n + 1) L ≅
      (Scheme.Modules.pushforward (S.truncationι n)).obj
        ((Scheme.Modules.pullback (S.truncationι n)).obj L) :=
  idealQuotientPushforwardIso S.uniformizerIdealSheaf (n + 1) L (S.truncationι n)
    (S.ker_truncationι n)

/-- The quotient projection followed by the identification of `0EL1` is the adjunction unit. -/
theorem π_comp_truncationQuotientIso_hom (n : ℕ) :
    cokernel.π (C := S.X.Modules)
        (idealPowerMultiple S.uniformizerIdealSheaf (n + 1) L).ι ≫
        (S.truncationQuotientIso L n).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (S.truncationι n)).unit.app L :=
  idealQuotientPushforwardMap_π _ _ _ _ (S.ker_truncationι n)

/-- **Lowering the exponent is restriction along `X_0 ⟶ X_n`**, under the identifications of
`0EL1`. -/
theorem drop_comp_truncationQuotientIso_hom (n : ℕ) :
    idealPowerQuotientDrop S.uniformizerIdealSheaf (Nat.le_add_left 1 n) L ≫
        (S.truncationQuotientIso L 0).hom =
      (S.truncationQuotientIso L n).hom ≫
        pushforwardSectionComparison (S.truncationTransition n) (S.truncationι n)
          (S.truncationTransition_comp_truncationι n) L := by
  rw [← cancel_epi (cokernel.π (C := S.X.Modules)
    (idealPowerMultiple S.uniformizerIdealSheaf (n + 1) L).ι),
    idealPowerQuotientDrop_π_assoc, ← Category.assoc (cokernel.π _)
      (S.truncationQuotientIso L n).hom, S.π_comp_truncationQuotientIso_hom L n,
    unit_comp_pushforwardSectionComparison]
  exact S.π_comp_truncationQuotientIso_hom L 0

/-- **The theorem on formal functions at `p = 0`, in the form used here.** For a coherent module
`ℒ` on the model there is a `c` such that every global section of `ℒ / π^{c+1} ℒ` agrees in
`ℒ / π ℒ` with a global section of `ℒ`: the images in `Γ(ℒ / π ℒ)` of `Γ(ℒ / π^{c+1} ℒ)` and of
`Γ(ℒ)` coincide. This is the stabilization clause of [Stacks, Tag 02OB], available with
[Stacks, Tag 02O8] proved. -/
theorem exists_forall_exists_π_eq_drop (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsCoherent L) :
    ∃ c : ℕ, ∀ t : Γ(idealPowerQuotient S.uniformizerIdealSheaf (c + 1) L, ⊤),
      ∃ s : Γ(L, ⊤),
        (cokernel.π (C := S.X.Modules)
            (idealPowerMultiple S.uniformizerIdealSheaf (0 + 1) L).ι).app ⊤ s =
          (idealPowerQuotientDrop S.uniformizerIdealSheaf (Nat.le_add_left 1 c) L).app ⊤ t := by
  obtain ⟨c, -, -, hrange⟩ :=
    Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8
      S.R S.X_to_R inferInstance S.uniformizerIdeal L hL 0
      Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  refine ⟨c, fun t => ?_⟩
  have hr := hrange 1 (c + 1) (by omega)
  set E := moduleGlobalSectionsRightDerivedZeroIso S.X
  set t' := (E.inv.app _).hom t
  have hmem : (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived 0).map
      (idealPowerQuotientDrop S.uniformizerIdealSheaf (Nat.le_add_left 1 c) L)).hom t' ∈
      LinearMap.range (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived 0).map
        (cokernel.π (C := S.X.Modules)
          (idealPowerMultiple S.uniformizerIdealSheaf 1 L).ι)).hom := by
    rw [← hr]
    exact ⟨t', rfl⟩
  obtain ⟨s', hs'⟩ := hmem
  refine ⟨(E.hom.app L).hom s', ?_⟩
  have h1 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (E.hom.naturality (cokernel.π (C := S.X.Modules)
      (idealPowerMultiple S.uniformizerIdealSheaf 1 L).ι))) s'
  have h2 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    (E.hom.naturality (idealPowerQuotientDrop S.uniformizerIdealSheaf
      (Nat.le_add_left 1 c) L))) t'
  have h3 := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 (E.inv_hom_id_app
    (idealPowerQuotient S.uniformizerIdealSheaf (c + 1) L))) t
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id,
    LinearMap.id_coe] at h1 h2 h3
  have h3' : (E.hom.app _).hom t' = t := h3
  refine h1.symm.trans ?_
  rw [hs', h2, h3']
  rfl

/-! ### Triviality on the truncations -/

/-- A closed subset of the model containing no point of the special fibre is empty: its image in
`Spec(R)` is closed, since the model is proper, and a nonempty closed subset of the spectrum of a
local ring contains the closed point. -/
theorem eq_empty_of_isClosed_of_disjoint_range {Z : Set S.X} (hZ : IsClosed Z)
    (hdisj : ∀ y, (S.truncationι 0).base y ∉ Z) : Z = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z hz => ?_
  have hcl : IsClosed (S.X_to_R.base '' Z) := S.X_to_R.isClosedMap Z hZ
  have hmem : IsLocalRing.closedPoint S.R ∈ S.X_to_R.base '' Z :=
    (IsLocalRing.specializes_closedPoint (S.X_to_R.base z)).mem_closed hcl ⟨z, hz, rfl⟩
  obtain ⟨z', hz', hz'eq⟩ := hmem
  have hrange : z' ∈ Set.range (S.truncationι 0).base := by
    rw [Scheme.Pullback.range_fst]
    show S.X_to_R.base z' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk _))
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hz'eq, Ideal.mk_ker]
    intro r hr
    rw [truncationIdeal, zero_add, pow_one, SetLike.mem_coe, Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr S.uniformizer.not_isUnit)
  obtain ⟨y, rfl⟩ := hrange
  exact hdisj y hz'

/-- **An invertible module on the model which is trivial on every truncation is trivial.**

This is the formal-functions half of the proof of [Stacks, Tag 0CAE]. By the stabilization
clause of the theorem on formal functions there is a `c` such that the image of `Γ(X, ℒ)` in
`Γ(X, ℒ / π ℒ)` contains the image of `Γ(X, ℒ / π^{c+1} ℒ)`. A trivialization of `ℒ` on the
truncation `X_c` gives a generator of `ℒ / π^{c+1} ℒ`, so some global section `s` of `ℒ`
restricts to a generator on the special fibre `X_0`. The nonvanishing locus of `s` is open and
contains the special fibre, and the model is proper over the local ring `R`, so it is
everything; hence `s` trivializes `ℒ`. -/
theorem nonempty_iso_unit_of_forall_truncation (L : S.X.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (htriv : ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (S.truncationι n)).obj L ≅
      SheafOfModules.unit (S.truncation n).ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit S.X.ringCatSheaf) := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.X_to_R
  have hLag : AlgebraicGeometry.SheafOfModules.IsInvertible S.X.presheaf
      S.X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have hLag' : AlgebraicGeometry.SheafOfModules.IsInvertible S.X.sheaf.obj
      S.X.ringCatSheaf.property L := hLag
  have hL' : Stacks.SheafOfModules.IsInvertible S.X.sheaf.obj S.X.ringCatSheaf.property L := hL
  have : L.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible L
  have hcoh : Stacks.SheafOfModules.IsCoherent L :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible S.X L)
  obtain ⟨c, hc⟩ := S.exists_forall_exists_π_eq_drop L hcoh
  obtain ⟨e⟩ := htriv c
  obtain ⟨s, hs⟩ := hc ((S.truncationQuotientIso L c).inv.app ⊤
    (e.inv.app ⊤ (show Γ(SheafOfModules.unit (S.truncation c).ringCatSheaf, ⊤) from
      (1 : Γ(S.truncation c, ⊤)))))
  have hτ : Stacks.Ample.nonvanishingLocus _ (e.inv.app ⊤
      (show Γ(SheafOfModules.unit (S.truncation c).ringCatSheaf, ⊤) from
        (1 : Γ(S.truncation c, ⊤)))) = Set.univ :=
    (Stacks.Ample.nonvanishingLocus_congr e.symm _).trans (nonvanishingLocus_unit_one _)
  have hfib : ∀ y, (S.truncationι 0).base y ∈ Stacks.Ample.nonvanishingLocus L s := by
    intro y
    have h := (Stacks.Models.nonvanishingLocus_unit_app_top (S.truncationι 0) L s).symm.trans
      ((congrArg (Stacks.Ample.nonvanishingLocus
        ((Scheme.Modules.pullback (S.truncationι 0)).obj L))
          (Stacks.Models.app_top_eq_of_comp_eq _ _ _ _ _ _
            (S.π_comp_truncationQuotientIso_hom L 0) (S.drop_comp_truncationQuotientIso_hom L c)
            s _ hs)).trans
        ((Stacks.Models.nonvanishingLocus_pushforwardSectionComparison_app_top _ _ _ L _).trans
          (by rw [hτ, Set.preimage_univ])))
    exact (Set.ext_iff.mp h y).mpr trivial
  have hopen : IsOpen (Stacks.Ample.nonvanishingLocus L s) := by
    rw [← Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq S.X L s]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := S.X.toRingedSpace) L _
  have hall : Stacks.Ample.nonvanishingLocus L s = Set.univ := by
    have hempty := S.eq_empty_of_isClosed_of_disjoint_range hopen.isClosed_compl
      fun y hy => hy (hfib y)
    exact compl_eq_bot.mp hempty
  have hiso := AlgebraicGeometry.isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L
    ((Stacks.NonvanishingSpelling.sectionsEquiv S.X L).symm s)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq S.X L s).trans hall)
  exact ⟨(asIso (L.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv S.X L).symm
    s))).symm⟩

/-- **A Picard class on the model whose restriction to every truncation vanishes is zero.** This
is `nonempty_iso_unit_of_forall_truncation` read in `Pic(X)`. -/
theorem eq_zero_of_forall_schemePullbackClass_truncationι_eq_zero (x : ofScheme S.X)
    (hx : ∀ n : ℕ, schemePullbackClass (S.truncationι n) x = 0) : x = 0 := by
  set M := picardRepresentative S.X.toRingedSpace x
  have hM : picardClass S.X.presheaf (structureIsSheaf S.X.toRingedSpace) M.obj M.property = x :=
    classOf_picardRepresentative S.X.toRingedSpace x
  have hzero : ∀ Y : Scheme.{u}, (0 : ofScheme Y) =
      picardClass Y.presheaf (structureIsSheaf Y.toRingedSpace)
        (SheafOfModules.unit _) (Stacks.SheafOfModules.isInvertible_unit _ _) := fun _ => rfl
  have htriv : ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (S.truncationι n)).obj M.obj ≅
      SheafOfModules.unit (S.truncation n).ringCatSheaf) := by
    intro n
    refine (picardClass_eq_iff _ _ _ _
      (modulePullback_isInvertible_of (S.truncationι n).toLRSHom.toShHom M.obj M.property)
      (Stacks.SheafOfModules.isInvertible_unit _ _)).1 ?_
    rw [← pullbackClass_classOf (S.truncationι n).toLRSHom.toShHom M.obj M.property, hM,
      ← hzero]
    exact hx n
  obtain ⟨e⟩ := S.nonempty_iso_unit_of_forall_truncation M.obj (hL := M.property) htriv
  rw [← hM, hzero S.X]
  exact (picardClass_eq_iff _ _ _ _ M.property (Stacks.SheafOfModules.isInvertible_unit _ _)).2 ⟨e⟩

end RegularProperModelSituation

/-- **Stacks Project, Tag 0CAE.** In Situation 0C61, let `h` be an integer prime to the
characteristic of the residue field `k`. Then restriction of invertible modules
`Pic(X)[h] ⟶ Pic((X_k)_red)[h]` is injective.

The proof is the source's. For every truncation `X_n = X ×_{Spec R} Spec(R/π^{n+1})` the reduced
special fibre `(X_k)_red ⟶ X_n` is a thickening, and restriction is injective on `h`-torsion along
it by [Stacks, Tag 0C6S]: the units condition of that tag holds because the global functions on
`(X_k)_red` form a field purely inseparable over `k`, the special fibre being geometrically
connected. So an `h`-torsion class trivial on `(X_k)_red` is trivial on every `X_n`, and then
trivial on `X` by the theorem on formal functions and the properness of `X ⟶ Spec(R)`. -/
@[stacks 0CAE "restriction Pic(X)[h] → Pic((X_k)_red)[h] is injective for h prime to the \
characteristic of k"]
theorem injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion
    (S : RegularProperModelSituation.{u}) {h : ℤ} (hh : IsUnit ((h : ℤ) : S.k)) :
    Set.InjOn (schemePullbackClass S.specialFiberRedι) (zsmulTorsion (ofScheme S.X) h) := by
  intro x hx y hy hxy
  rw [← sub_eq_zero]
  have hz : x - y ∈ zsmulTorsion (ofScheme S.X) h := by
    rw [mem_zsmulTorsion, smul_sub, mem_zsmulTorsion.1 hx, mem_zsmulTorsion.1 hy, sub_zero]
  have hred : schemePullbackClass S.specialFiberRedι (x - y) = 0 := by
    have := map_sub (schemePullbackClassHom S.specialFiberRedι) x y
    change schemePullbackClass S.specialFiberRedι (x - y) =
      schemePullbackClass S.specialFiberRedι x - schemePullbackClass S.specialFiberRedι y at this
    rw [this, hxy, sub_self]
  refine S.eq_zero_of_forall_schemePullbackClass_truncationι_eq_zero (x - y) fun n => ?_
  have hbij := Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_globalUnitsPowerLift
    (S.specialFiberRedToTruncation n) (S.isThickening_specialFiberRedToTruncation n)
    (S.isUnit_intCast_specialFiberRed hh) (S.globalUnitsPowerLift_specialFiberRedToTruncation hh n)
  have hmz : schemePullbackClass (S.truncationι n) (x - y)
      ∈ zsmulTorsion (ofScheme (S.truncation n)) h :=
    mapsTo_zsmulTorsion (A := ofScheme S.X) (B := ofScheme (S.truncation n))
      (schemePullbackClassHom (S.truncationι n)) h hz
  have h0 : (0 : ofScheme (S.truncation n)) ∈ zsmulTorsion (ofScheme (S.truncation n)) h := by
    rw [mem_zsmulTorsion, smul_zero]
  refine hbij.injOn hmz h0 ?_
  rw [schemePullbackClass_comp, S.specialFiberRedToTruncation_comp_truncationι n, hred]
  exact (map_zero (schemePullbackClassHom (S.specialFiberRedToTruncation n))).symm

end Stacks.Models

end
