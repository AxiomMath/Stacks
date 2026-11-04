module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A blowup is an isomorphism away from its center

Let `I` be a quasi-coherent ideal sheaf on a scheme `X`. The blowup morphism
`AlgebraicGeometry.blowUpToBase I` restricts to an isomorphism over the open complement of the
closed subscheme cut out by `I`.

## Main results

* `AlgebraicGeometry.isIso_projInclusionToOpen_of_ideal_eq_top`: over an affine open where `I` is
  the unit ideal, the blowup chart is the open itself.
* `AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support`: the blowup morphism is
  an isomorphism over any open disjoint from the support of `I`.
* `AlgebraicGeometry.isIso_blowUp_restrict_compl_support`: the blowup morphism is an isomorphism
  over the complement of the support of `I`.

## Implementation notes

Over an affine open `U` where `I.ideal U = ⊤` the local Rees algebra is
`⨁_{n ≥ 0} Γ(X, U)`, whose projective spectrum is `Spec Γ(X, U)`. Rather than build that graded
comparison by hand, the proof uses the affine charts of the blowup that
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/AffineCharts.lean` already provides: the chart
attached to a section `a` of `I` has coordinate ring the affine blowup algebra `Γ(X, U)[I/a]`,
and `AlgebraicGeometry.affineBlowupStandardOpenIso_over` identifies its structure morphism with
`Spec` of `Γ(X, U) → Γ(X, U)[I/a]`. Taking `a = 1`, which is available exactly because
`I.ideal U = ⊤`, both factors become isomorphisms: the blowup algebra `Γ(X, U)[I/1]` is
`Γ(X, U)` itself, and the chart is the whole projective spectrum because every homogeneous
element of positive degree is a multiple of the degree-one section attached to `1`.

Passing from the affine opens to the complement of the support uses that
`CategoryTheory.MorphismProperty.isomorphisms` is Zariski-local at the target, in the form
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` applied to the restricted morphism and
transported along `AlgebraicGeometry.morphismRestrictRestrict`. An affine open of `X` is disjoint
from the support of `I` exactly when `I` is the unit ideal there, since the support meets an
affine open in the zero locus of the ideal of sections there.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace Opposite Stacks.RelativeProj

universe u

variable {X : Scheme.{u}}

/-! ### The graded ring of local sections of the Rees algebra

The three lemmas here recover, for the map `AlgebraicGeometry.reesToBase` from the local Rees
algebra to the structure sheaf, the facts that it is computed on homogeneous elements by the
affine identification of the degree-`n` piece with `Iⁿ`, that it is injective on each homogeneous
piece, and that it is a retraction of the structure-sheaf map. -/

/-- The map to the base is injective on each homogeneous piece. -/
private alias reesToBase_injective_on_grade' := reesToBase_injective_on_grade

/-- The map to the base is a retraction of the structure-sheaf map. -/
private lemma reesToBase_baseMap (I : X.IdealSheafData) (U : X.affineOpens)
    (r : X.presheaf.obj (op U.1)) :
    reesToBase I U ((reesSituation I).sectionRingBaseMap U.1 r) = r := by
  let r' : X.ringCatSheaf.obj.obj (op U.1) := r
  change reesToBase I U ((reesSituation I).sectionRingBaseMap U.1 r') = r
  rw [relativeProj_sectionRingBaseMap_apply (reesSituation I) U.1 r', reesToBase_of]
  change (((reesAlgebraData I).pieceEquiv (0 : ℤ) (by omega) U
    (r' • (reesAlgebraData I).algebra.one.eval (op U.1))) : X.presheaf.obj (op U.1)) = r
  rw [(reesAlgebraData I).pieceEquiv_smul, (reesAlgebraData I).pieceEquiv_one]
  simp [r']

/-! ### The chart at the unit section -/

/-- When the section `a` of `I` is the unit, every homogeneous element of positive degree in the
local Rees algebra is a multiple of the degree-one section attached to `a`: it is the product of
that section's `n`-th power with the function it maps to in the structure sheaf. -/
private lemma mem_span_degreeOne (I : X.IdealSheafData) (U : X.affineOpens)
    (a : ↥(I.ideal U)) (ha : (a : X.presheaf.obj (op U.1)) = 1)
    (n : ℕ) (hn : 0 < n) (y : (reesSituation I).sectionRing U.1)
    (hy : y ∈ (reesSituation I).sectionRingGrading U.1 n) :
    y ∈ Ideal.span {((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1)} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr hn
  have hbt : reesToBase I U ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) = 1 := by
    rw [reesToBase_degreeOne, ha]
  have hgr : (reesSituation I).sectionRingBaseMap U.1 (reesToBase I U y) *
      ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) ^ (m + 1) ∈
      (reesSituation I).sectionRingGrading U.1 (m + 1) := by
    have h0 := Situation.sectionRingBaseMap_mem_zero (reesSituation I) U.1 (reesToBase I U y)
    have h1 := SetLike.pow_mem_graded (A := (reesSituation I).sectionRingGrading U.1)
      (m + 1) (reesDegreeOne I U a).2
    simpa using SetLike.mul_mem_graded h0 h1
  have hval : reesToBase I U ((reesSituation I).sectionRingBaseMap U.1 (reesToBase I U y) *
      ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) ^ (m + 1)) =
      reesToBase I U y := by
    rw [map_mul, map_pow, hbt, one_pow, mul_one, reesToBase_baseMap]
  have hsub : y - (reesSituation I).sectionRingBaseMap U.1 (reesToBase I U y) *
      ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) ^ (m + 1) = 0 :=
    reesToBase_injective_on_grade' I U (m + 1) _
      (((reesSituation I).sectionRingGrading U.1 (m + 1)).sub_mem hy hgr)
      (by rw [map_sub, hval, sub_self])
  rw [sub_eq_zero] at hsub
  rw [hsub]
  refine Ideal.mem_span_singleton'.mpr ⟨(reesSituation I).sectionRingBaseMap U.1
    (reesToBase I U y) * ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) ^ m, ?_⟩
  rw [mul_assoc, ← pow_succ]

/-- The standard chart at the unit section of `I` is the whole projective spectrum of the local
Rees algebra: a homogeneous prime avoiding the irrelevant ideal cannot contain the degree-one
section attached to the unit, since every homogeneous element of positive degree is a multiple of
it. -/
private lemma basicOpen_degreeOne_eq_top (I : X.IdealSheafData) (U : X.affineOpens)
    (a : ↥(I.ideal U)) (ha : (a : X.presheaf.obj (op U.1)) = 1) :
    Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1) = ⊤ := by
  ext x
  refine iff_of_true ?_ (by simp)
  rw [SetLike.mem_coe, Proj.mem_basicOpen]
  intro ht
  refine x.not_irrelevant_le ?_
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi y hy
  have hspan : Ideal.span {((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1)} ≤
      x.asHomogeneousIdeal.toIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)
  exact hspan (mem_span_degreeOne I U a ha i hi y hy)

/-- The affine blowup algebra `R[I/1]` at the unit is `R`: its generators `y/1` are the images of
the elements of `R`, and a localization away from `1` is the ring itself. -/
private lemma bijective_algebraMap_affineBlowupAlgebra {R : Type*} [CommRing R] (J : Ideal R)
    (a : R) (ha : a = 1) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away a S] :
    Function.Bijective (algebraMap R ↥(affineBlowupAlgebra J a S)) := by
  subst ha
  have hM : Submonoid.powers (1 : R) ≤ nonZeroDivisors R := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have hval : ∀ x : R, ((algebraMap R ↥(affineBlowupAlgebra J (1 : R) S)) x : S) =
      algebraMap R S x := fun _ => rfl
  have hle : affineBlowupAlgebra J (1 : R) S ≤ (⊥ : Subalgebra R S) := by
    refine Algebra.adjoin_le ?_
    rintro z ⟨y, -, rfl⟩
    exact Algebra.mem_bot.mpr ⟨y, (IsLocalization.mk'_one S y).symm⟩
  refine ⟨fun p q hpq => hinj ?_, fun z => ?_⟩
  · rw [← hval p, ← hval q, hpq]
  · obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (hle z.2)
    exact ⟨r, Subtype.ext ((hval r).trans hr)⟩

/-- **The blowup in the unit ideal is trivial.** Over an affine open `U` of the base on which the
quasi-coherent ideal `I` is the unit ideal, the chart structure morphism of the blowup of `X` in
`I` is an isomorphism onto `U`. -/
public theorem isIso_projInclusionToOpen_of_ideal_eq_top (I : X.IdealSheafData)
    (U : X.affineOpens) (hI : I.ideal U = ⊤) :
    IsIso ((reesSituation I).projInclusionToOpen U.1 U.2) := by
  let a : ↥(I.ideal U) := ⟨1, by rw [hI]; trivial⟩
  have ha : (a : X.presheaf.obj (op U.1)) = 1 := rfl
  have hunit : IsIso (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U.1))
      ↥(affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (op U.1))
        (Localization.Away (a : X.presheaf.obj (op U.1)))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_algebraMap_affineBlowupAlgebra _ _ ha _)
  have hchart : IsIso ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      ((reesDegreeOne I U a) : (reesSituation I).sectionRing U.1)).ι ≫
      (reesSituation I).projInclusionToOpen U.1 U.2) := by
    refine (isIso_comp_left_iff (affineBlowupStandardOpenIso I U a).hom _).mp ?_
    rw [affineBlowupStandardOpenIso_over I U a]
    exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)
  rw [basicOpen_degreeOne_eq_top I U a ha] at hchart
  have htop : IsIso ((⊤ : (AlgebraicGeometry.Proj
      ((reesSituation I).sectionRingGrading U.1)).Opens).ι) := by
    change IsIso (Scheme.topIso _).hom
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hchart

/-! ### From the affine charts to the complement of the center -/

/-- The blowup morphism is an isomorphism over an affine open on which the center is the unit
ideal. -/
private lemma isIso_blowUpToBase_restrict_affine (I : X.IdealSheafData) (U : X.affineOpens)
    (hI : I.ideal U = ⊤) : IsIso (blowUpToBase I ∣_ U.1) := by
  have hp : IsIso ((reesSituation I).projInclusionToOpen U.1 U.2) :=
    isIso_projInclusionToOpen_of_ideal_eq_top I U hI
  have hC := Situation.relativeProjChart_isPullback (reesSituation I) U
  have hR := isPullback_morphismRestrict (blowUpToBase I) U.1
  rw [← hC.flip.isoIsPullback_inv_fst _ _ hR]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) hp

/-- An affine open disjoint from the support of a quasi-coherent ideal sheaf is one where the
ideal is the unit ideal: the support meets the affine open in the zero locus of the ideal of
sections there, so that zero locus is empty. -/
private lemma ideal_eq_top_of_subset_compl_support (I : X.IdealSheafData) (U : X.affineOpens)
    (h : (U.1 : Set X) ⊆ (I.support : Set X)ᶜ) : I.ideal U = ⊤ := by
  have hzl : X.zeroLocus (U := U.1) (I.ideal U : Set _) ∩ (U.1 : Set X) = ∅ := by
    rw [← Scheme.IdealSheafData.coe_support_inter I U, Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    exact h hz2 hz1
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp
    ((U.2.fromSpec_image_zeroLocus (I.ideal U : Set _)).trans hzl))

/-- Being an isomorphism over an open of the target is local on that open: if a family of opens of
`W` covers it and the morphism is an isomorphism over the image in the target of each member, then
it is an isomorphism over `W`. -/
public lemma isIso_morphismRestrict_of_iSup {Y Z : Scheme.{u}} (f : Y ⟶ Z) (W : Z.Opens)
    {ι : Type u} (V : ι → W.toScheme.Opens) (hV : iSup V = ⊤)
    (h : ∀ i, IsIso (f ∣_ (W.ι ''ᵁ V i))) : IsIso (f ∣_ W) := by
  have hiso : MorphismProperty.isomorphisms Scheme (f ∣_ W) := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top V hV fun i => ?_
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f W (V i))).mpr (h i)
  exact hiso

/-- **The blowup morphism is an isomorphism over any open disjoint from the center.** The affine
opens of such an open cover it, and on each of them the center is the unit ideal. -/
public theorem isIso_blowUpToBase_restrict_of_subset_compl_support (I : X.IdealSheafData)
    (W : X.Opens) (hW : (W : Set X) ⊆ (I.support : Set X)ᶜ) :
    IsIso (blowUpToBase I ∣_ W) := by
  refine isIso_morphismRestrict_of_iSup _ W (fun V : W.toScheme.affineOpens => V.1)
    (iSup_affineOpens_eq_top _) fun V => ?_
  have haff : IsAffineOpen (W.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion _
  exact isIso_blowUpToBase_restrict_affine I ⟨_, haff⟩
    (ideal_eq_top_of_subset_compl_support I ⟨_, haff⟩
      fun z hz => hW (Scheme.Opens.ι_image_le W V.1 hz))

/-- **Stacks Project, Tag 02OS.** The blowup of a scheme in a quasi-coherent ideal sheaf is an
isomorphism over the open complement of the closed subscheme the ideal cuts out. -/
@[stacks 02OS "isomorphism_off_center", sga "7 XVIII 2.1" "more general"]
public theorem isIso_blowUp_restrict_compl_support (I : X.IdealSheafData) :
    IsIso (blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)) :=
  isIso_blowUpToBase_restrict_of_subset_compl_support I _ fun _ hz => hz

end AlgebraicGeometry

end
