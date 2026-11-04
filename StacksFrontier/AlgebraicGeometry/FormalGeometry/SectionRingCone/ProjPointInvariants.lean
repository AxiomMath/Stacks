module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.Proper
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem

/-!
# Points of a proper scheme and the homogeneous primes of its section ring

Let `k` be a field, `X` a scheme proper over `k`, `L` an ample invertible `𝒪_X`-module and
`A = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` its section ring, graded by
`Stacks.AmpleFiniteAvoidance.grading L`. By [Stacks, Tag 0EKI] the canonical morphism
`r : X ⟶ Proj A` of [Stacks, Tag 01PZ] is an isomorphism, so every point `x` of `X` is a relevant
homogeneous prime `r(x)` of `A`. This file records how the invariants of `x` that enter the
depth–dimension hypothesis of [Stacks, Tag 0EL1] are read off `r(x)`:

* a homogeneous section `a` of positive degree does not vanish at `x` exactly when `a ∉ r(x)`;
* every relevant homogeneous prime is `r(x)` for some `x`, in particular the homogeneous core of
  any prime not containing the irrelevant ideal;
* the local ring `𝒪_{X,x}` is the homogeneous localization `A_{(r(x))}`, compatibly with the
  global functions, which act on both sides through the degree-zero part of `A`; hence the two
  have the same depth;
* the dimension of the closure of `x` is the transcendence degree over `k` of the residue field of
  `A_{(r(x))}`;
* `A` is a Noetherian `k`-algebra of finite type, and every prime of `A` containing the irrelevant
  ideal is maximal.

These are the inputs that turn the algebraic depth and dimension bounds on the cone `Spec A` into
the hypothesis on `X`.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.sectionRingAlgebra` — the `k`-algebra structure on `A`.
* `Stacks.Algebraization.SectionRingCone.baseFieldToDegreeZero` — `k` in degree zero of `A`.
* `Stacks.Algebraization.SectionRingCone.stalkRingEquivAtPrime` — `𝒪_{X,x} ≃+* A_{(r(x))}`.

## Main results

* `Stacks.Algebraization.SectionRingCone.mem_nvOpen_iff_notMem_asHomogeneousIdeal`
* `Stacks.Algebraization.SectionRingCone.exists_asHomogeneousIdeal_eq_homogeneousCore`
* `Stacks.Algebraization.SectionRingCone.notMem_support_zeroScheme_of_notMem_asHomogeneousIdeal`
* `Stacks.Algebraization.SectionRingCone.stalkRingEquivAtPrime_germ`
* `Stacks.Algebraization.SectionRingCone.depth_stalk_eq_depth_atPrime`
* `Stacks.Algebraization.SectionRingCone.dimClosureAt_eq_trdeg_residueField_atPrime`
* `Stacks.Algebraization.SectionRingCone.finiteType_sectionRing`,
  `Stacks.Algebraization.SectionRingCone.isNoetherianRing_sectionRing`,
  `Stacks.Algebraization.SectionRingCone.isMaximal_sectionRing_of_irrelevant_le`

## Implementation notes

The degree-zero part of `A` is identified with `Γ(X, 𝒪_X)` in two ways in this library: by the
inclusion `Stacks.SectionRingZero.sectionRingZeroHom`, through which the finite-type statement of
[Stacks, Tag 0B5T] is made, and by the ratio
`Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom`,
through which `r` is compared with `Proj A ⟶ Spec A₀`.
`Stacks.Algebraization.SectionRingCone.degZeroRingHom_sectionRingZeroHom` shows that one undoes
the other, which is what makes the `k`-algebra structures on `𝒪_{X,x}` and on `A_{(r(x))}` agree.

## References

* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (grading nvOpen)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjMorphism.ToSpecZero (degZeroRingHom unitSec)
open Stacks.AlgebraicGeometry.GradedProperCohomology (specAlgebraRingHom)

universe u

namespace Stacks.Algebraization.SectionRingCone

section Graded

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- **The germ of a pulled-back degree-zero function is its degree-zero fraction.** For `z ∈ 𝒜₀`,
the global function of `Proj 𝒜` pulled back from `z` along `Proj 𝒜 ⟶ Spec 𝒜₀` has, at every
point `x`, the germ `z / 1` of the homogeneous localization at `x`. -/
theorem stalkIso_germ_toSpecZero_appTop (x : AlgebraicGeometry.Proj 𝒜) (z : 𝒜 0) :
    Proj.stalkIso' 𝒜 x ((AlgebraicGeometry.Proj 𝒜).presheaf.germ ⊤ x trivial
      ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (.of (𝒜 0))).inv z))) =
      fromZeroRingHom 𝒜 _ z := by
  apply HomogeneousLocalization.val_injective
  refine (congrArg HomogeneousLocalization.val
    (Proj.stalkIso'_germ 𝒜 ⊤ x trivial _)).trans ?_
  refine (Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val 𝒜 z x).trans ?_
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

end Graded

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The degree-zero part -/

/-- **The degree-zero comparison undoes the degree-zero inclusion.** A global function `c`, put
in degree zero of the section ring by `Stacks.SectionRingZero.sectionRingZeroHom` and divided by
the unit section, is `c` again. -/
theorem degZeroRingHom_sectionRingZeroHom (c : Γ(X, ⊤)) :
    degZeroRingHom L ⟨Stacks.SectionRingZero.sectionRingZeroHom X L c,
      Stacks.ExternalGrading.of_mem_summand 0 _⟩ = c := by
  show Stacks.SectionRingChartMap.ratioR L (unitSec L) _
    (DirectSum.of (powSections L) 0 ((Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm c))
    = c
  rw [Stacks.SectionRingChartMap.ratioR_of]
  refine Stacks.SectionRingChartMap.ratio_unique L (unitSec L) _ _ c ?_
  rw [Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top,
    Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top]
  have h := Stacks.SectionRingGeometric.globalSection_unitComp X
    ((Stacks.SectionRingGeometric.unitScalarAddEquiv X).symm c) (unitSec L)
  rw [Stacks.SectionRingZero.unitScalar_unitScalarAddEquiv_symm] at h
  exact (congrArg (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _)
    (Category.comp_id _).symm).trans h

/-- **Every degree-zero element is a global function put in degree zero.** -/
theorem sectionRingZeroHom_degZeroRingHom (w : grading L 0) :
    Stacks.SectionRingZero.sectionRingZeroHom X L (degZeroRingHom L w) = (w : sectionRing L) := by
  have h := (Stacks.SectionRingProjMorphism.ToSpecZero.bijective_degZeroRingHom L).1
    (degZeroRingHom_sectionRingZeroHom L (degZeroRingHom L w))
  exact congrArg Subtype.val h

/-! ### The base field acting on the section ring -/

variable (k : Type u) [Field k] (g : X ⟶ Spec (.of k))

/-- The `k`-algebra structure on the section ring of `L`: the base field acts through the global
functions of `X`, put in degree zero. -/
abbrev sectionRingAlgebra : Algebra k (sectionRing L) :=
  ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp (specAlgebraRingHom k g)).toAlgebra

omit [Ample.IsInvertibleModule X L] in
/-- The image of the base field in the section ring lies in degree zero. -/
theorem sectionRingAlgebra_mem_grading_zero (c : k) :
    Stacks.SectionRingZero.sectionRingZeroHom X L (specAlgebraRingHom k g c) ∈ grading L 0 :=
  Stacks.ExternalGrading.of_mem_summand 0 _


/-- **The base field in degree zero of the section ring**: `k` acts on the global functions of
`X` through `g`, and the degree-zero part of the section ring is the ring of global functions. -/
def baseFieldToDegreeZero : k →+* grading L 0 :=
  (RingEquiv.ofBijective (degZeroRingHom L)
    (Stacks.SectionRingProjMorphism.ToSpecZero.bijective_degZeroRingHom L)).symm.toRingHom.comp
    (specAlgebraRingHom k g)

/-- The base field in degree zero is the base field in the section ring. -/
theorem coe_baseFieldToDegreeZero (c : k) :
    ((baseFieldToDegreeZero L k g c : grading L 0) : sectionRing L) =
      Stacks.SectionRingZero.sectionRingZeroHom X L (specAlgebraRingHom k g c) := by
  have h : degZeroRingHom L (baseFieldToDegreeZero L k g c) = specAlgebraRingHom k g c :=
    (RingEquiv.ofBijective (degZeroRingHom L)
      (Stacks.SectionRingProjMorphism.ToSpecZero.bijective_degZeroRingHom L)).apply_symm_apply _
  rw [← h, sectionRingZeroHom_degZeroRingHom]

/-- The base field acts on the section ring through its degree-zero part. -/
theorem algebraMap_sectionRingAlgebra (c : k) :
    letI := sectionRingAlgebra L k g
    algebraMap k (sectionRing L) c = (baseFieldToDegreeZero L k g c : sectionRing L) :=
  (coe_baseFieldToDegreeZero L k g c).symm

/-- **The section ring is a finitely generated `k`-algebra** ([Stacks, Tag 0B5T], clause (1)). -/
theorem finiteType_sectionRing [IsProper g] (hL : Stacks.Ample.IsAmple X L) :
    letI := sectionRingAlgebra L k g
    Algebra.FiniteType k (sectionRing L) := by
  let := sectionRingAlgebra L k g
  exact RingHom.finiteType_algebraMap.mp
    (Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing g L hL)

/-- **The section ring is Noetherian**, being of finite type over a field. -/
theorem isNoetherianRing_sectionRing [IsProper g] (hL : Stacks.Ample.IsAmple X L) :
    IsNoetherianRing (sectionRing L) := by
  let := sectionRingAlgebra L k g
  have := finiteType_sectionRing L k g hL
  exact Algebra.FiniteType.isNoetherianRing k (sectionRing L)

/-- **A prime of the section ring containing the irrelevant ideal is maximal.** Modulo the
irrelevant ideal every element is a degree-zero element, that is a global function of `X`, and
those are integral over `k` because `X` is proper; a domain integral over a field is a field. -/
theorem isMaximal_sectionRing_of_irrelevant_le [IsProper g] (q : Ideal (sectionRing L))
    [q.IsPrime]
    (hq : (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ q) : q.IsMaximal := by
  let := sectionRingAlgebra L k g
  have hint : (specAlgebraRingHom k g).IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
      (isIntegral_appTop_of_universallyClosed g)
  have halg : Algebra.IsIntegral k (sectionRing L ⧸ q) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    set w : grading L 0 := ⟨DirectSum.of (powSections L) 0 (x 0),
      Stacks.ExternalGrading.of_mem_summand 0 _⟩
    have hx : Ideal.Quotient.mk q x = Ideal.Quotient.mk q
        (Stacks.SectionRingZero.sectionRingZeroHom X L (degZeroRingHom L w)) := by
      rw [sectionRingZeroHom_degZeroRingHom, Ideal.Quotient.eq]
      refine hq ((Stacks.ExternalGrading.mem_irrelevant_iff_degree_zero_eq_zero _).2 ?_)
      simp [w]
    rw [hx]
    obtain ⟨p, hp, hpe⟩ := hint (degZeroRingHom L w)
    refine ⟨p, hp, ?_⟩
    have := congrArg ((Ideal.Quotient.mk q).comp (Stacks.SectionRingZero.sectionRingZeroHom X L))
      hpe
    rw [map_zero, Polynomial.hom_eval₂] at this
    exact this
  exact Ideal.Quotient.maximal_of_isField q (isField_of_isIntegral_of_isField' (Field.toIsField k))


/-! ### Points of `X` as homogeneous primes -/

variable [IsProper g] (hL : Stacks.Ample.IsAmple X L)

/-- **A point lies in the nonvanishing open of a homogeneous section exactly when that section is
outside the homogeneous prime of the point.** -/
theorem mem_nvOpen_iff_notMem_asHomogeneousIdeal {d : ℕ} (hd : 0 < d) (a : powSections L d)
    (x : X) :
    x ∈ nvOpen L a ↔
      DirectSum.of (powSections L) d a ∉ ((projHomOfIsAmple L hL) x).asHomogeneousIdeal := by
  rw [← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd]
  exact Iff.rfl

include g in
/-- **Every point of `Proj Γ_*(X, L)` comes from a point of `X`.** -/
theorem exists_projHomOfIsAmple_eq (y : AlgebraicGeometry.Proj (grading L)) :
    ∃ x : X, projHomOfIsAmple L hL x = y := by
  have := Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL g
  exact ⟨(inv (projHomOfIsAmple L hL)) y, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩

include g in
/-- **The homogeneous core of a relevant prime of the section ring is the homogeneous prime of a
point of `X`.** -/
theorem exists_asHomogeneousIdeal_eq_homogeneousCore (p : Ideal (sectionRing L)) [p.IsPrime]
    (hp : ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ p) :
    ∃ x : X, ((projHomOfIsAmple L hL) x).asHomogeneousIdeal = p.homogeneousCore (grading L) := by
  have hprime : (p.homogeneousCore (grading L)).toIdeal.IsPrime :=
    Ideal.IsPrime.homogeneousCore (𝒜 := grading L) ‹_›
  have hrel : ¬ HomogeneousIdeal.irrelevant (grading L) ≤ p.homogeneousCore (grading L) := by
    intro h
    exact hp (le_trans h (Ideal.toIdeal_homogeneousCore_le (grading L) p))
  obtain ⟨x, hx⟩ :=
    exists_projHomOfIsAmple_eq L k g hL ⟨p.homogeneousCore (grading L), hprime, hrel⟩
  exact ⟨x, congrArg ProjectiveSpectrum.asHomogeneousIdeal hx⟩


/-! ### The zero scheme of a section -/

/-- **A point whose homogeneous prime does not contain a degree-one section lies off the zero
scheme of that section.** Here `s₁` is a degree-one element of the section ring with the same
nonvanishing locus as the global section `s` of `L`; the point lies in `X_{s₁} = X_s`, where `s`
does not vanish, so it is outside `Z(s)`. -/
theorem notMem_support_zeroScheme_of_notMem_asHomogeneousIdeal (s : Γ(L, ⊤))
    (s₁ : powSections L 1) (hs : (nvOpen L s₁ : Set X) = Stacks.Ample.nonvanishingLocus L s)
    (x : X)
    (hx : DirectSum.of (powSections L) 1 s₁ ∉ ((projHomOfIsAmple L hL) x).asHomogeneousIdeal) :
    x ∉ (AlgebraicGeometry.zeroScheme X L s).support := by
  have hmem : x ∈ nvOpen L s₁ :=
    (mem_nvOpen_iff_notMem_asHomogeneousIdeal L hL one_pos s₁ x).2 hx
  have hnv : x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L s := by
    rw [← SetLike.mem_coe, Stacks.NonvanishingOpen.coe_nonvanishingOpen, ← hs]
    exact hmem
  exact AlgebraicGeometry.notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L s hnv

/-! ### The local rings -/

/-- The homogeneous ideal of a point of `Proj` is prime, read on a point of the scheme. -/
theorem isPrime_asHomogeneousIdeal_toIdeal (y : AlgebraicGeometry.Proj (grading L)) :
    y.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime y

attribute [local instance] isPrime_asHomogeneousIdeal_toIdeal

/-- **The local ring of `X` at `x` is the homogeneous localization of the section ring at the
homogeneous prime of `x`**: the stalk map of the isomorphism `X ≅ Proj Γ_*(X, L)` followed by
Mathlib's identification of the stalks of `Proj`. -/
def stalkRingEquivAtPrime (x : X) :
    X.presheaf.stalk x ≃+*
      AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal :=
  haveI := Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL g
  (asIso ((projHomOfIsAmple L hL).stalkMap x)).symm.commRingCatIsoToRingEquiv.trans
    (Proj.stalkIso' (grading L) ((projHomOfIsAmple L hL) x))

include g in
/-- **The depth of `𝒪_{X,x}` is the depth of the homogeneous localization at the point.** -/
theorem depth_stalk_eq_depth_atPrime (x : X) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) =
      Module.depth (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal)
        (IsLocalRing.maximalIdeal
          (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal))
        (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal) :=
  Module.depth_self_eq_of_ringEquiv (stalkRingEquivAtPrime L k g hL x)

/-- **On germs of global functions the comparison is the degree-zero fraction.** The germ at `x`
of the function `c` goes to `w / 1`, where `w ∈ A₀` is `c` read in degree zero. -/
theorem stalkRingEquivAtPrime_germ (x : X) (c : Γ(X, ⊤)) :
    stalkRingEquivAtPrime L k g hL x (X.presheaf.germ ⊤ x trivial c) =
      fromZeroRingHom (grading L) _ ⟨Stacks.SectionRingZero.sectionRingZeroHom X L c,
        Stacks.ExternalGrading.of_mem_summand 0 _⟩ := by
  have := Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL g
  set w : grading L 0 := ⟨Stacks.SectionRingZero.sectionRingZeroHom X L c,
    Stacks.ExternalGrading.of_mem_summand 0 _⟩
  set t := (Proj.toSpecZero (grading L)).appTop ((Scheme.ΓSpecIso (.of (grading L 0))).inv w)
  have htri := Stacks.SectionRingProjMorphism.ToSpecZero.projHomOfIsAmple_toSpecZero L hL
  have key : (Scheme.ΓSpecIso (.of (grading L 0))).inv ≫ (Proj.toSpecZero (grading L)).appTop ≫
      (projHomOfIsAmple L hL).appTop = CommRingCat.ofHom (degZeroRingHom L) := by
    rw [← Scheme.Hom.comp_appTop, htri, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
      Category.comp_id]
  have hc : (projHomOfIsAmple L hL).appTop t = c := by
    have h := ConcreteCategory.congr_hom key w
    simp only at h
    exact h.trans (degZeroRingHom_sectionRingZeroHom L c)
  have hgerm := Scheme.Hom.germ_stalkMap_apply (projHomOfIsAmple L hL) ⊤ x trivial t
  rw [← hc]
  show Proj.stalkIso' (grading L) _ ((inv ((projHomOfIsAmple L hL).stalkMap x)) _) = _
  rw [show X.presheaf.germ ⊤ x trivial ((projHomOfIsAmple L hL).appTop t) =
      (projHomOfIsAmple L hL).stalkMap x
        ((AlgebraicGeometry.Proj (grading L)).presheaf.germ ⊤ _ trivial t) from hgerm.symm,
    ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  exact stalkIso_germ_toSpecZero_appTop (grading L) _ w


/-! ### The dimension of the closure of a point -/

/-- **The dimension of the closure of a point is the transcendence degree over `k` of the residue
field of the homogeneous localization at that point**, for any `k`-algebra structure on that
residue field which is the one induced by the section ring: `k` acts through the global functions
of `X`, put in degree zero, then as degree-zero fractions. -/
theorem dimClosureAt_eq_trdeg_residueField_atPrime (x : X)
    [Algebra k (IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal))]
    (hk : ∀ c : k, algebraMap k (IsLocalRing.ResidueField
        (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal)) c =
      IsLocalRing.residue _ (fromZeroRingHom (grading L) _
        ⟨Stacks.SectionRingZero.sectionRingZeroHom X L (specAlgebraRingHom k g c),
          sectionRingAlgebra_mem_grading_zero L k g c⟩)) :
    dimClosureAt X x = (Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal))) :
        WithBot ℕ∞) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hdim : dimClosureAt X x =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) :=
    topologicalKrullDim_closure_singleton_eq_trdeg k X g x
  rw [hdim]
  let e : X.residueField x ≃+* IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal) :=
    IsLocalRing.ResidueField.mapEquiv (stalkRingEquivAtPrime L k g hL x)
  let eₐ : X.residueField x ≃ₐ[k] IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal) :=
    AlgEquiv.ofRingEquiv (f := e) fun c => by
      rw [hk c]
      show IsLocalRing.ResidueField.map _
          (IsLocalRing.residue _ (X.presheaf.germ ⊤ x trivial (specAlgebraRingHom k g c))) = _
      rw [IsLocalRing.ResidueField.map_residue]
      exact congrArg (IsLocalRing.residue _) (stalkRingEquivAtPrime_germ L k g hL x _)
  rw [eₐ.trdeg_eq]


/-- **The dimension of the closure of a point**, with the `k`-algebra structure on the residue
field of the homogeneous localization given by
`Stacks.Algebraization.SectionRingCone.baseFieldToDegreeZero`
followed by the degree-zero fractions. -/
theorem dimClosureAt_eq_trdeg_residueField_atPrime_baseField (x : X) :
    letI : Algebra k (IsLocalRing.ResidueField
        (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal)) :=
      ((IsLocalRing.residue _).comp
        ((fromZeroRingHom (grading L) _).comp (baseFieldToDegreeZero L k g))).toAlgebra
    dimClosureAt X x = (Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal))) :
        WithBot ℕ∞) := by
  let : Algebra k (IsLocalRing.ResidueField
      (AtPrime (grading L) ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal)) :=
    ((IsLocalRing.residue _).comp
      ((fromZeroRingHom (grading L) _).comp (baseFieldToDegreeZero L k g))).toAlgebra
  refine dimClosureAt_eq_trdeg_residueField_atPrime L k g hL x fun c => ?_
  show IsLocalRing.residue _ (fromZeroRingHom (grading L) _ (baseFieldToDegreeZero L k g c)) = _
  congr 2
  exact Subtype.ext (coe_baseFieldToDegreeZero L k g c)

end Monoidal

end Stacks.Algebraization.SectionRingCone
