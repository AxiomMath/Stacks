module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityI.VanishingConditions
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityI.FactorThroughFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of Tor and Ext above a fixed degree

For a map of modules and chosen projective resolutions, vanishing of sufficiently high
components of a lift is characterized by vanishing of the induced maps on Ext. These
conditions imply the corresponding vanishing for Tor, and the two versions of Tor vanishing
are equivalent. If the source is suitably pseudo-coherent, all seven conditions are
equivalent.

## Main results

* `tfae_lift_ext_conditions` proves the equivalence of conditions (1)--(5).
* `canonicalExtClassPullbackVanishes_imp_torMapVanishesAbove` proves (5) implies (6).
* `tfae_tor_conditions` proves the equivalence of conditions (6) and (7).
* `tfae_of_isPseudoCoherentFrom` proves that all seven conditions are equivalent under the
  pseudo-coherence hypothesis.
* `tfae_of_isNoetherianRing_of_finite` gives the stated Noetherian finite-module special case.

## Implementation notes

The conditions themselves are stated in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityI.VanishingConditions`. The
implication from Tor vanishing back to Ext vanishing is an induction on the degree which
replaces `M` by the kernel of a finite free presentation; pseudo-coherence is what keeps that
kernel in the inductive hypothesis, and the base case is the factorization through a free
module of Tag 0G9T.

## References

* [Stacks Project, Tag 0G9V](https://stacks.math.columbia.edu/tag/0G9V)
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {R : Type u} [CommRing R]

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The canonical symmetry of `Tor'` in its two variables. -/
private noncomputable def torPrimeSymmetry (i : ℕ) :
    Tor' (ModuleCat.{u} R) i ≅ (Tor' (ModuleCat.{u} R) i).flip := by
  let h₁ := Tor_iso_Tor' R i
  let h₂ := Classical.choice (tor_symm_canonically_iso R i)
  exact h₁.symm ≪≫ h₂ ≪≫ (flipFunctor _ _ _).mapIso h₁

/-- Dimension shift of `Tor'` in the second variable, transported across the canonical
symmetry. -/
private noncomputable def torPrimeShiftSecond (j : ℕ) (N M : ModuleCat.{u} R) :
    (((Tor' (ModuleCat.{u} R) (j + 2)).obj M).obj N) ≅
      (((Tor' (ModuleCat.{u} R) (j + 1)).obj M).obj (Tor_iso_Tor'.syzygy R N)) := by
  let s₂ := torPrimeSymmetry (R := R) (j + 2)
  let s₁ := torPrimeSymmetry (R := R) (j + 1)
  let sh := Tor_iso_Tor'.tor'Shift R j N
  exact (s₂.app M).app N ≪≫ (sh.app M) ≪≫
    ((s₁.app (Tor_iso_Tor'.syzygy R N)).app M)

/-- The dimension shift of `Tor'` is natural in the first variable. -/
private lemma torPrimeShiftSecond_naturality (j : ℕ) (N : ModuleCat.{u} R)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    ((Tor' (ModuleCat.{u} R) (j + 2)).map f).app N ≫
        (torPrimeShiftSecond (R := R) j N M').hom =
      (torPrimeShiftSecond (R := R) j N M).hom ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).map f).app
          (Tor_iso_Tor'.syzygy R N) := by
  dsimp [torPrimeShiftSecond]
  simp only [Category.assoc]
  have h₁ : ((Tor' (ModuleCat.{u} R) (j + 2)).map f).app N ≫
        ((torPrimeSymmetry (R := R) (j + 2)).hom.app M').app N =
      ((torPrimeSymmetry (R := R) (j + 2)).hom.app M).app N ≫
        ((Tor' (ModuleCat.{u} R) (j + 2)).flip.map f).app N :=
    congrArg (fun g ↦ g.app N)
      ((torPrimeSymmetry (R := R) (j + 2)).hom.naturality f)
  have h₂ := (Tor_iso_Tor'.tor'Shift R j N).hom.naturality f
  have h₃ := ((torPrimeSymmetry (R := R) (j + 1)).app
    (Tor_iso_Tor'.syzygy R N)).hom.naturality f
  change _ = _ ≫ ((Tor' (ModuleCat.{u} R) (j + 1)).map f).app
      (Tor_iso_Tor'.syzygy R N) at h₃
  change ((Tor' (ModuleCat.{u} R) (j + 2)).flip.map f).app N ≫
      (Tor_iso_Tor'.tor'Shift R j N).hom.app M' = _ at h₂
  change ((Tor' (ModuleCat.{u} R) (j + 1)).obj
      (Tor_iso_Tor'.syzygy R N)).map f ≫
      ((torPrimeSymmetry (R := R) (j + 1)).hom.app
        (Tor_iso_Tor'.syzygy R N)).app M' = _ at h₃
  calc
    _ = ((torPrimeSymmetry (R := R) (j + 2)).hom.app M).app N ≫
        ((Tor' (ModuleCat.{u} R) (j + 2)).flip.map f).app N ≫
        (Tor_iso_Tor'.tor'Shift R j N).hom.app M' ≫
        ((torPrimeSymmetry (R := R) (j + 1)).hom.app
          (Tor_iso_Tor'.syzygy R N)).app M' := by
      simpa only [Category.assoc] using congrArg (fun g ↦ g ≫
        (Tor_iso_Tor'.tor'Shift R j N).hom.app M' ≫
        ((torPrimeSymmetry (R := R) (j + 1)).hom.app
          (Tor_iso_Tor'.syzygy R N)).app M') h₁
    _ = ((torPrimeSymmetry (R := R) (j + 2)).hom.app M).app N ≫
        (Tor_iso_Tor'.tor'Shift R j N).hom.app M ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).obj
          (Tor_iso_Tor'.syzygy R N)).map f ≫
        ((torPrimeSymmetry (R := R) (j + 1)).hom.app
          (Tor_iso_Tor'.syzygy R N)).app M' := by
      simpa only [Category.assoc] using congrArg (fun g ↦
        ((torPrimeSymmetry (R := R) (j + 2)).hom.app M).app N ≫ g ≫
        ((torPrimeSymmetry (R := R) (j + 1)).hom.app
          (Tor_iso_Tor'.syzygy R N)).app M') h₂
    _ = _ := by
      rw [← Category.assoc, h₃, Category.assoc]
      rfl

variable {M M' : ModuleCat.{u} R} {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
  (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M')
  [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p']
  (alpha : M ⟶ M') (e : ℕ)

/-- Truncate a lift of resolutions below a degree in which it already vanishes. -/
private noncomputable def cutResolutionLift
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ P') (e : ℕ)
    (ha : a.f (-((e + 1 : ℕ) : ℤ)) = 0) : P ⟶ P' where
  f i := if i ≤ -((e + 1 : ℕ) : ℤ) then 0 else a.f i
  comm' i j hij := by
    have hrel : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
    by_cases hi : i ≤ -((e + 1 : ℕ) : ℤ)
    · by_cases hj : j ≤ -((e + 1 : ℕ) : ℤ)
      · rw [ite_eq_left hi, ite_eq_left hj]
        simp
      · have heq : i = -((e + 1 : ℕ) : ℤ) := by omega
        subst i
        have hcomm := a.comm' (-((e + 1 : ℕ) : ℤ)) j hij
        rw [ha] at hcomm
        rw [ite_eq_left hi, ite_eq_right hj]
        simpa using hcomm
    · by_cases hj : j ≤ -((e + 1 : ℕ) : ℤ)
      · omega
      · rw [ite_eq_right hi, ite_eq_right hj]
        exact a.comm' i j hij

omit [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p'] in
/-- Condition (2) implies condition (1). -/
private theorem liftVanishingAtSucc_imp_above :
    HasLiftVanishingAtSucc p p' alpha e → HasLiftVanishingAbove p p' alpha e := by
  rintro ⟨a, ha, hzero⟩
  let b := cutResolutionLift a e hzero
  refine ⟨b, ?_, ?_⟩
  · apply HomologicalComplex.to_single_hom_ext
    have hc : ¬ (0 : ℤ) ≤ -((e + 1 : ℕ) : ℤ) := by omega
    have hb : b.f 0 = a.f 0 := by simp only [b, cutResolutionLift, hc, ite_false]
    simpa [hb] using congrArg (fun g ↦ g.f 0) ha
  · intro i hi
    have hc : -((i : ℤ)) ≤ -((e + 1 : ℕ) : ℤ) := by omega
    show (if -((i : ℤ)) ≤ -((e + 1 : ℕ) : ℤ) then 0 else a.f (-((i : ℤ)))) = 0
    rw [ite_eq_left hc]

omit [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p'] in
/-- Conditions (1) and (2) are equivalent. -/
private theorem liftVanishingAbove_iff_atSucc :
    HasLiftVanishingAbove p p' alpha e ↔ HasLiftVanishingAtSucc p p' alpha e :=
  ⟨fun ⟨a, ha, hv⟩ ↦ ⟨a, ha, hv (e + 1) (by omega)⟩, liftVanishingAtSucc_imp_above p p' alpha e⟩

/-- Correct a lift of resolutions by the coboundary `phi` in degree `t = s + 1`, and kill all
components in degrees `≤ s`. -/
private noncomputable def correctedResolutionLift
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ P') {s t : ℤ} (hst : s + 1 = t)
    (phi : P.X t ⟶ image (P'.d s t))
    (hphi : a.f s ≫ factorThruImage (P'.d s t) = P.d s t ≫ phi) : P ⟶ P' where
  f i := if i ≤ s then 0 else if h : i = t then
      a.f i - (eqToHom (congrArg P.X h) ≫ phi ≫ image.ι (P'.d s t) ≫
        eqToHom (congrArg P'.X h.symm)) else a.f i
  comm' i j hij := by
    have hrel : i + 1 = j := hij
    by_cases hi : i ≤ s
    · by_cases hj : j ≤ s
      · simp [hi, hj]
      · have hi' : s = i := by omega
        subst hi'
        have hj' : t = j := by omega
        subst hj'
        have hcancel : P.d s t ≫ (a.f t - phi ≫ image.ι (P'.d s t)) = 0 := by
          rw [Preadditive.comp_sub, ← a.comm' s t hij, sub_eq_zero, ← reassoc_of% hphi,
            image.fac]
        rw [if_pos le_rfl, if_neg hj, dif_pos rfl, zero_comp, eqToHom_refl, eqToHom_refl,
          Category.id_comp, Category.comp_id, hcancel]
    · by_cases hit : i = t
      · subst i
        have hj : ¬ j ≤ s := by omega
        have hjt : j ≠ t := by omega
        simp [hi, hj, hjt, a.comm' t j hij, image_ι_comp_eq_zero (P'.d_comp_d s t j)]
      · have hj : ¬ j ≤ s := by omega
        have hjt : j ≠ t := by omega
        simp [hi, hit, hj, hjt, a.comm' i j hij]

/-- Above `s`, the corrected lift agrees with the original lift after composing with any map
`q` with `P'.d s t ≫ q.f t = 0`. -/
private lemma correctedResolutionLift_comp_f
    {P P' Q : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ P') {s t : ℤ} (hst : s + 1 = t)
    (phi : P.X t ⟶ image (P'.d s t))
    (hphi : a.f s ≫ factorThruImage (P'.d s t) = P.d s t ≫ phi) (q : P' ⟶ Q)
    (hq : P'.d s t ≫ q.f t = 0) (i : ℤ) (hi : s < i) :
    (correctedResolutionLift a hst phi hphi ≫ q).f i = (a ≫ q).f i := by
  by_cases hit : i = t
  · subst i
    simp [correctedResolutionLift, not_le.2 hi, Preadditive.sub_comp, image_ι_comp_eq_zero hq]
  · simp [correctedResolutionLift, not_le.2 hi, hit]

omit [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p'] in
/-- Condition (5) implies condition (2): subtract the coboundary from the lift. -/
private theorem canonicalExtClassPullbackVanishes_imp_liftVanishingAtSucc :
    CanonicalExtClassPullbackVanishes p p' alpha e →
      HasLiftVanishingAtSucc p p' alpha e := by
  rintro ⟨a, phi, ha, hphi⟩
  have hst : -((e + 1 : ℕ) : ℤ) + 1 = -(e : ℤ) := by omega
  have hq : P'.d (-((e + 1 : ℕ) : ℤ)) (-(e : ℤ)) ≫ p'.f (-(e : ℤ)) = 0 := by
    rw [← p'.comm' _ _ (show (ComplexShape.up ℤ).Rel _ _ from hst),
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M' (-((e + 1 : ℕ) : ℤ))
        (by omega)).eq_of_tgt (p'.f (-((e + 1 : ℕ) : ℤ))) 0, zero_comp]
  refine ⟨correctedResolutionLift a hst phi hphi, ?_, by simp [correctedResolutionLift]⟩
  apply HomologicalComplex.to_single_hom_ext
  rw [correctedResolutionLift_comp_f a hst phi hphi p' hq 0 (by omega)]
  exact congrArg (fun g ↦ g.f 0) (show a ≫ p' = _ from ha)

omit [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p'] in
/-- Condition (2) implies condition (5), with the zero coboundary. -/
private theorem liftVanishingAtSucc_imp_canonicalExtClassPullbackVanishes :
    HasLiftVanishingAtSucc p p' alpha e →
      CanonicalExtClassPullbackVanishes p p' alpha e := by
  rintro ⟨a, ha, hzero⟩
  refine ⟨a, 0, ha, ?_⟩
  rw [hzero]
  simp

omit [CochainComplex.IsProjectiveResolution p] [CochainComplex.IsProjectiveResolution p'] in
/-- Conditions (2) and (5) are equivalent. -/
private theorem canonicalExtClassPullbackVanishes_iff_liftVanishingAtSucc :
    CanonicalExtClassPullbackVanishes p p' alpha e ↔
      HasLiftVanishingAtSucc p p' alpha e :=
  ⟨canonicalExtClassPullbackVanishes_imp_liftVanishingAtSucc p p' alpha e,
    liftVanishingAtSucc_imp_canonicalExtClassPullbackVanishes p p' alpha e⟩

/-- The source of a projective resolution is K-projective. -/
lemma resolution_isKProjective
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (q : K ⟶ L)
    [CochainComplex.IsProjectiveResolution q] : K.IsKProjective := by
  obtain ⟨n, _⟩ := CochainComplex.IsProjectiveResolution.exists_isStrictlyLE q
  have := CochainComplex.IsProjectiveResolution.projective q
  exact CochainComplex.isKProjective_of_projective K n

/-- Out of a K-projective complex every map in the derived category comes from a chain map. -/
private lemma derived_map_surjective
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKProjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro g
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso _).hom.app K ≫ g ≫
      (DerivedCategory.quotientCompQhIso _).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  refine ⟨φ, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality φ
  rw [hβ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact ((cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app K)).1 h).symm

/-- A chain map out of a K-projective complex is zero in the derived category exactly when it is
null-homotopic. -/
lemma derived_map_eq_zero_iff
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKProjective] (f : K ⟶ L) :
    DerivedCategory.Q.map f = 0 ↔ Nonempty (Homotopy f 0) := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff]
  constructor
  · intro h
    apply (CochainComplex.IsKProjective.Qh_map_bijective K _).injective
    have hn := DerivedCategory.quotientCompQhIso_hom_naturality f
    rw [h, comp_zero] at hn
    simpa only [Functor.map_zero] using
      (cancel_mono ((DerivedCategory.quotientCompQhIso _).hom.app L)).1 (by simpa using hn)
  · intro h
    have hn := DerivedCategory.quotientCompQhIso_hom_naturality f
    rw [h, Functor.map_zero, zero_comp] at hn
    exact (cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app K)).1 (by simpa using hn.symm)

/-- A shifted single complex in the derived category. -/
noncomputable def derivedSingleShiftIso (N : ModuleCat.{u} R) (i : ℤ) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (-i)).obj N) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)⟦i⟧ :=
  ((DerivedCategory.singleFunctorIsoCompQ _ (-i)).app N).symm ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso i (-i) 0 (by omega)).symm.app N

/-- Vanishing of the Ext maps in degree `i` is null-homotopy of the composites of a lift with
the chain maps to shifted single complexes. -/
private lemma ext_map_vanishes_iff_nullHomotopic
    (a : P ⟶ P') (ha : IsResolutionLift p p' alpha a) (i : ℕ) :
    (∀ (N : ModuleCat.{u} R) (x : Abelian.zExt M' N (i : ℤ)),
      (DerivedCategory.singleFunctor _ 0).map alpha ≫ x = 0) ↔
    (∀ (N : ModuleCat.{u} R) (b : P' ⟶ (CochainComplex.singleFunctor _ (-(i : ℤ))).obj N),
      Nonempty (Homotopy (a ≫ b) 0)) := by
  have := resolution_isKProjective p
  have := resolution_isKProjective p'
  have hmap : DerivedCategory.Q.map p ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map alpha) =
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p' := by
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map ha.symm
  constructor
  · intro h N b
    apply (derived_map_eq_zero_iff _).1
    have hx := h N (inv (DerivedCategory.Q.map p') ≫
      DerivedCategory.Q.map b ≫ (derivedSingleShiftIso N i).hom)
    change DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map alpha) ≫ _ = 0 at hx
    have hx' := congrArg (fun f ↦ DerivedCategory.Q.map p ≫ f) hx
    simp only [← Category.assoc] at hx'
    rw [hmap] at hx'
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, comp_zero] at hx'
    apply (cancel_mono (derivedSingleShiftIso N i).hom).1
    simpa only [Functor.map_comp, zero_comp, Category.assoc] using hx'
  · intro h N x
    obtain ⟨b, hb⟩ := derived_map_surjective P'
      ((CochainComplex.singleFunctor _ (-(i : ℤ))).obj N)
      (DerivedCategory.Q.map p' ≫ x ≫ (derivedSingleShiftIso N i).inv)
    have hz := (derived_map_eq_zero_iff _).2 (h N b)
    rw [Functor.map_comp, hb] at hz
    show DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map alpha) ≫ x = 0
    apply (cancel_epi (DerivedCategory.Q.map p)).1
    apply (cancel_mono (derivedSingleShiftIso N i).inv).1
    simp only [← Category.assoc] at hz ⊢
    rw [← hmap] at hz
    simpa using hz

/-- Condition (1) implies condition (3). -/
private theorem liftVanishingAbove_imp_extMapVanishesAbove :
    HasLiftVanishingAbove p p' alpha e → ExtMapVanishesAbove alpha e := by
  rintro ⟨a, ha, hvan⟩ N i hi
  apply (ext_map_vanishes_iff_nullHomotopic p p' alpha a ha i).2
    (fun N b ↦ ?_) N
  have hab : a ≫ b = 0 :=
    HomologicalComplex.to_single_hom_ext (by simp [hvan i hi])
  rw [hab]
  exact ⟨Homotopy.refl 0⟩

/-- Every component of a quasi-isomorphism onto a single complex is epi. -/
private lemma epi_resolution_component
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {N : ModuleCat.{u} R}
    (q : K ⟶ singleComplex N) [QuasiIso q] (i : ℤ) : Epi (q.f i) := by
  let L := singleComplex N
  have hπ : IsIso (L.homologyπ i) :=
    L.isIso_homologyπ (i - 1) i (by simp) (by simp [L])
  have hι : IsIso (L.iCycles i) := by
    let e := L.iCyclesIso i (i + 1) (by simp) (by simp [L])
    exact (show IsIso e.hom from inferInstance)
  have hc : Epi (HomologicalComplex.cyclesMap q i ≫ L.homologyπ i) := by
    rw [← HomologicalComplex.homologyπ_naturality]
    infer_instance
  have hc' : Epi (HomologicalComplex.cyclesMap q i) :=
    (epi_comp_iff_of_isIso _ (L.homologyπ i)).1 hc
  have hh : Epi (K.iCycles i ≫ q.f i) := by
    rw [← HomologicalComplex.cyclesMap_i]
    infer_instance
  exact epi_of_epi (K.iCycles i) (q.f i)

/-- A map of modules lifts to the chosen projective resolutions. -/
private lemma exists_resolution_lift : ∃ a, IsResolutionLift p p' alpha a := by
  have := resolution_isKProjective p
  exact (CochainComplex.IsKProjective.exists_lift_of_quasiIso p'
    (p ≫ (CochainComplex.singleFunctor _ 0).map alpha)).2
      (CochainComplex.IsProjectiveResolution.projective p)
      (epi_resolution_component p')

/-- Condition (4) implies condition (5). -/
private theorem extMapVanishesAtSucc_imp_canonical :
    ExtMapVanishesAtSucc alpha e → CanonicalExtClassPullbackVanishes p p' alpha e := by
  intro h
  obtain ⟨a, ha⟩ := exists_resolution_lift p p' alpha
  let s : ℤ := -((e + 1 : ℕ) : ℤ)
  let t : ℤ := -(e : ℤ)
  let d := P'.d s t
  let N := image d
  let b : P' ⟶ (CochainComplex.singleFunctor _ s).obj N :=
    HomologicalComplex.mkHomToSingle (factorThruImage d) (by
      intro j hj
      apply (cancel_mono (image.ι d)).1
      simp only [Category.assoc, image.fac, zero_comp]
      exact P'.d_comp_d j s t)
  obtain ⟨H⟩ := (ext_map_vanishes_iff_nullHomotopic p p' alpha a ha (e + 1)).1 h N b
  refine ⟨a, H.hom t s ≫ (HomologicalComplex.singleObjXSelf _ s N).hom, ha, ?_⟩
  have hc := H.comm s
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel s t by dsimp [s, t]; simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (s - 1) s by simp)] at hc
  change a.f s ≫ b.f s = P.d s t ≫ H.hom t s + H.hom s (s - 1) ≫ 0 + 0 at hc
  simp only [comp_zero, add_zero] at hc
  have hb : b.f s = factorThruImage d ≫
      (HomologicalComplex.singleObjXSelf _ s N).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  rw [hb] at hc
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun f ↦ f ≫ (HomologicalComplex.singleObjXSelf _ s N).hom) hc

/-- Conditions (1)--(5) are equivalent. -/
@[stacks 0G9V "equivalence of conditions (1)--(5)"]
lemma tfae_lift_ext_conditions :
    List.TFAE [
      HasLiftVanishingAbove p p' alpha e,
      HasLiftVanishingAtSucc p p' alpha e,
      ExtMapVanishesAbove alpha e,
      ExtMapVanishesAtSucc alpha e,
      CanonicalExtClassPullbackVanishes p p' alpha e] := by
  tfae_have 1 ↔ 2 := liftVanishingAbove_iff_atSucc p p' alpha e
  tfae_have 1 → 3 := liftVanishingAbove_imp_extMapVanishesAbove p p' alpha e
  tfae_have 3 → 4 := fun h N x ↦ h N (e + 1) (by omega) x
  tfae_have 4 → 5 := extMapVanishesAtSucc_imp_canonical p p' alpha e
  tfae_have 5 ↔ 2 := canonicalExtClassPullbackVanishes_iff_liftVanishingAtSucc p p' alpha e
  tfae_finish

/-- The cochain augmentation of a chain projective resolution is a projective resolution. -/
lemma isProjectiveResolution_π' {X : ModuleCat.{u} R}
    (Q : ProjectiveResolution X) : CochainComplex.IsProjectiveResolution Q.π' :=
  ⟨⟨0, inferInstance⟩, fun _ ↦ inferInstance⟩

/-- Transport a map of cochain projective resolutions to the underlying chain complexes. -/
private noncomputable def chainMapOfCochainHom
    {X Y : ModuleCat.{u} R} (Q : ProjectiveResolution X) (Q' : ProjectiveResolution Y)
    (a : Q.cochainComplex ⟶ Q'.cochainComplex) : Q.complex ⟶ Q'.complex where
  f n := (Q.cochainComplexXIso (-n) n).inv ≫ a.f (-n) ≫
    (Q'.cochainComplexXIso (-n) n).hom
  comm' i j hij := by
    have h := a.comm (-(i : ℤ)) (-(j : ℤ))
    rw [Q.cochainComplex_d _ _ i j, Q'.cochainComplex_d _ _ i j] at h
    apply (cancel_epi (Q.cochainComplexXIso (-i) i).hom).1
    apply (cancel_mono (Q'.cochainComplexXIso (-j) j).inv).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The transported chain map still lifts the map of resolved modules. -/
private lemma chainMapOfCochainHom_comm
    {X Y : ModuleCat.{u} R} (Q : ProjectiveResolution X) (Q' : ProjectiveResolution Y)
    (f : X ⟶ Y) (a : Q.cochainComplex ⟶ Q'.cochainComplex)
    (ha : IsResolutionLift Q.π' Q'.π' f a) :
    (chainMapOfCochainHom Q Q' a).f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ f := by
  have h := congrArg (fun g ↦ g.f 0) ha
  have hf : ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv :=
    HomologicalComplex.single_map_f_self _ _ f
  simp only [HomologicalComplex.comp_f, ProjectiveResolution.π'_f_zero, hf] at h
  change a.f 0 ≫ (Q'.cochainComplexXIso 0 0).hom ≫ Q'.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv =
    ((Q.cochainComplexXIso 0 0).hom ≫ Q.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ f ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv at h
  have hh := congrArg (fun g ↦ (Q.cochainComplexXIso 0 0).inv ≫ g ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom) h
  show ((Q.cochainComplexXIso 0 0).inv ≫ a.f 0 ≫
    (Q'.cochainComplexXIso 0 0).hom) ≫ Q'.π.f 0 = Q.π.f 0 ≫ f
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at hh
  exact hh

/-- A chain map with a vanishing component induces the zero map on homology there. -/
private lemma homologyMap_eq_zero_of_component_eq_zero
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (i : ℕ) (hf : f.f i = 0) :
    HomologicalComplex.homologyMap f i = 0 := by
  apply (cancel_epi (K.homologyπ i)).1
  rw [HomologicalComplex.homologyπ_naturality, comp_zero]
  have hc : HomologicalComplex.cyclesMap f i = 0 := by
    apply (cancel_mono (L.iCycles i)).1
    simp [HomologicalComplex.cyclesMap_i, hf]
  rw [hc, zero_comp]

/-- Condition (3) implies condition (6). -/
private theorem extMapVanishesAbove_imp_torMapVanishesAbove :
    ExtMapVanishesAbove alpha e → TorMapVanishesAbove alpha e := by
  intro h N i hi
  let Q := projectiveResolution M
  let Q' := projectiveResolution M'
  have := isProjectiveResolution_π' Q
  have := isProjectiveResolution_π' Q'
  obtain ⟨a, ha, hz⟩ := ((tfae_lift_ext_conditions Q.π' Q'.π' alpha e).out 3 1).1 h
  let b := chainMapOfCochainHom Q Q' a
  have hbi : b.f i = 0 := by simp [b, chainMapOfCochainHom, hz i hi]
  show ((MonoidalCategory.tensorRight N).leftDerived i).map alpha = 0
  apply (cancel_mono (Q'.isoLeftDerivedObj (MonoidalCategory.tensorRight N) i).hom).1
  rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality alpha Q Q' b
    (chainMapOfCochainHom_comm Q Q' alpha a ha)]
  have hfunctor : (HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
        (ComplexShape.down ℕ) i).map
        (((MonoidalCategory.tensorRight N).mapHomologicalComplex _).map b) = 0 := by
    rw [HomologicalComplex.homologyFunctor_map]
    exact homologyMap_eq_zero_of_component_eq_zero _ i (by simp [hbi])
  simp only [Functor.comp_map, hfunctor, comp_zero, zero_comp]

/-- Condition (5) implies condition (6). -/
@[stacks 0G9V "condition (5) implies condition (6)"]
lemma canonicalExtClassPullbackVanishes_imp_torMapVanishesAbove :
    CanonicalExtClassPullbackVanishes p p' alpha e → TorMapVanishesAbove alpha e := fun h ↦
  extMapVanishesAbove_imp_torMapVanishesAbove alpha e
    (((tfae_lift_ext_conditions p p' alpha e).out 5 3).1 h)

/-- Conditions (6) and (7) are equivalent. -/
@[stacks 0G9V "equivalence of conditions (6) and (7)"]
lemma tfae_tor_conditions :
    List.TFAE [TorMapVanishesAbove alpha e, TorMapVanishesAtSucc alpha e] := by
  rw [List.tfae_cons_cons]
  refine ⟨⟨fun h N ↦ h N (e + 1) (by omega), fun h N i hi ↦ ?_⟩, List.tfae_singleton _⟩
  have hz : ∀ k : ℕ, ∀ N : ModuleCat.{u} R,
      ((Tor' (ModuleCat.{u} R) (e + 1 + k)).map alpha).app N = 0 := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      intro N
      let j := e + k
      have hnat := torPrimeShiftSecond_naturality (R := R) j N alpha
      have hsy :
          ((Tor' (ModuleCat.{u} R) (j + 1)).map alpha).app
            (Tor_iso_Tor'.syzygy R N) = 0 := by
        have hidx : j + 1 = e + 1 + k := by simp only [j]; omega
        rw [hidx]
        exact ih (Tor_iso_Tor'.syzygy R N)
      have hcomp :
          ((Tor' (ModuleCat.{u} R) (j + 2)).map alpha).app N ≫
              (torPrimeShiftSecond (R := R) j N M').hom = 0 := by
        rw [hnat, hsy]
        simp
      have hzero : ((Tor' (ModuleCat.{u} R) (j + 2)).map alpha).app N = 0 :=
        (cancel_mono (torPrimeShiftSecond (R := R) j N M').hom).1 (by simpa using hcomp)
      have hidx : j + 2 = e + 1 + (k + 1) := by simp only [j]; omega
      rw [← hidx]
      exact hzero
  have hid : e + 1 + (i - (e + 1)) = i := by omega
  rw [← hid]
  exact hz (i - (e + 1)) N

/-- Condition (4) restated with Mathlib's `Abelian.Ext`. -/
private lemma extMapVanishesAtSucc_iff :
    ExtMapVanishesAtSucc alpha e ↔
      ∀ (N : ModuleCat.{u} R) (x : Abelian.Ext M' N (e + 1)),
        (Abelian.Ext.mk₀ alpha).comp x (zero_add _) = 0 := by
  constructor
  · intro h N x
    apply Abelian.Ext.ext
    simpa only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
      ShiftedHom.mk₀_comp, Abelian.Ext.zero_hom] using h N x.hom
  · intro h N x
    obtain ⟨y, rfl⟩ := Abelian.Ext.homEquiv.surjective x
    simpa only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
      ShiftedHom.mk₀_comp, Abelian.Ext.zero_hom] using congrArg Abelian.Ext.hom (h N y)

/-- Ext vanishing passes from the kernels of a map of short exact sequences with projective
middle term to the cokernels, one degree up. -/
private lemma ext_vanishes_of_kernel_map
    {S S' : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hS' : S'.ShortExact)
    [Projective S'.X₂] (f : S ⟶ S') (e : ℕ)
    (h : ExtMapVanishesAtSucc f.τ₁ e) : ExtMapVanishesAtSucc f.τ₃ (e + 1) := by
  rw [extMapVanishesAtSucc_iff] at h ⊢
  intro N x
  obtain ⟨y, rfl⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS' N x
    (Abelian.Ext.eq_zero_of_projective _) (show 1 + (e + 1) = e + 1 + 1 by omega)
  rw [← Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ f.τ₃) hS'.extClass y
    (zero_add 1) (by omega) (by omega)]
  rw [← hS.extClass_naturality hS' f,
    Abelian.Ext.comp_assoc_of_second_deg_zero, h N y, Abelian.Ext.comp_zero]

/-- The two models of Tor vanish together. -/
private lemma tor_map_eq_zero_iff (f : M ⟶ M') (N : ModuleCat.{u} R) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).map f).app N = 0 ↔
      ((Tor' (ModuleCat.{u} R) i).map f).app N = 0 := by
  let E : Tor (ModuleCat.{u} R) i ≅ Tor' (ModuleCat.{u} R) i := Tor_iso_Tor' R i
  let a := (E.app M).app N
  let b := (E.app M').app N
  have hn := congrArg (fun t ↦ t.app N) (E.hom.naturality f)
  change ((Tor (ModuleCat.{u} R) i).map f).app N ≫ b.hom =
    a.hom ≫ ((Tor' (ModuleCat.{u} R) i).map f).app N at hn
  constructor
  · intro h
    have hh := congrArg (fun g ↦ a.inv ≫ g) hn
    rw [h, zero_comp, comp_zero] at hh
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh.symm
  · intro h
    have hh := congrArg (fun g ↦ g ≫ b.inv) hn
    rw [h, comp_zero, zero_comp] at hh
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

/-- Tor vanishing passes from the cokernels of a map of short exact sequences with flat middle
terms to the kernels, one degree down. -/
private lemma tor_vanishes_kernel_map
    {S S' : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hS' : S'.ShortExact)
    [Module.Flat R S.X₂] [Module.Flat R S'.X₂] (f : S ⟶ S') (e : ℕ)
    (h : TorMapVanishesAtSucc f.τ₃ (e + 1)) : TorMapVanishesAtSucc f.τ₁ e := by
  intro N
  apply (tor_map_eq_zero_iff f.τ₁ N (e + 1)).1
  have hz := (tor_map_eq_zero_iff f.τ₃ N (e + 2)).2 (h N)
  have hn := lesShift.comp_naturality_S R hS hS' e f N
  apply (cancel_epi (lesShift.comp R S hS e N).hom).1
  rw [hz, zero_comp] at hn
  simpa only [comp_zero] using hn.symm

/-- The kernel of an epimorphism sits in a short exact sequence. -/
private lemma shortExact_kernel_ι {X Y : ModuleCat.{u} R} (q : X ⟶ Y) [Epi q] :
    (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
  ⟨ShortComplex.exact_kernel q⟩

/-- A finite free module is pseudo-coherent from every degree. -/
private lemma finiteFree_pseudoCoherent (F : ModuleCat.{u} R)
    [Module.Finite R F] [Module.Free R F] (m : ℤ) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := R) F m := by
  refine ⟨singleComplex F, StacksDraft.PseudoCoherence.isBoundedFiniteFree_single F 0,
    𝟙 _, ?_, ?_⟩
  · intro i hi
    show IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map (𝟙 _))
    infer_instance
  · show Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) m).map (𝟙 _))
    infer_instance

/-- The kernel of a finite free presentation of a pseudo-coherent module is pseudo-coherent one
degree up. -/
private lemma kernel_pseudoCoherent (F X : ModuleCat.{u} R) (q : F ⟶ X)
    [Epi q] [Module.Finite R F] [Module.Free R F] (m : ℤ)
    (hX : StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := R) X m) :
    StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom
      (R := R) (kernel q : ModuleCat.{u} R) (m + 1) := by
  have hS := shortExact_kernel_ι q
  exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_three m hS.singleTriangle
    hS.singleTriangle_distinguished (finiteFree_pseudoCoherent F (m + 1)) hX

/-- Condition (7) implies condition (4) when the source is suitably pseudo-coherent. -/
private theorem extMapVanishesAtSucc_of_tor_of_pseudoCoherent (e : ℕ)
    {M M' : ModuleCat.{u} R} (alpha : M ⟶ M')
    (hM : StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom
      (R := R) M (-(e : ℤ) - 1)) (hT : TorMapVanishesAtSucc alpha e) :
    ExtMapVanishesAtSucc alpha e := by
  induction e generalizing M M' with
  | zero =>
    have hfp : Module.FinitePresentation R M :=
      (StacksDraft.PseudoCoherence.modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := R) M).2.1.mp (by simpa using hM)
    obtain ⟨J, σ, τ, hfac⟩ := factor_through_free_of_tor_one_map_eq_zero alpha hT
    have hf : alpha = ModuleCat.ofHom σ ≫ ModuleCat.ofHom τ := ModuleCat.hom_ext hfac
    rw [extMapVanishesAtSucc_iff]
    intro N x
    rw [hf, ← Abelian.Ext.mk₀_comp_mk₀_assoc]
    have hz : (Abelian.Ext.mk₀ (ModuleCat.ofHom τ)).comp x (zero_add _) = 0 :=
      Abelian.Ext.eq_zero_of_projective _
    rw [hz, Abelian.Ext.comp_zero]
  | succ e ih =>
    have hfin : Module.Finite R M :=
      (StacksDraft.PseudoCoherence.modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := R) M).1.mp (hM.mono (by omega))
    obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
    let F : ModuleCat.{u} R := ModuleCat.of R (Fin n → R)
    let π : F ⟶ M := ModuleCat.ofHom q
    have hπ : Epi π := (ModuleCat.epi_iff_surjective π).2 hq
    let π' := Projective.π M'
    let b : F ⟶ Projective.over M' := Projective.factorThru (π ≫ alpha) π'
    have hb : b ≫ π' = π ≫ alpha := Projective.factorThru_comp _ _
    let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    let S' := ShortComplex.mk (kernel.ι π') π' (kernel.condition π')
    have hS : S.ShortExact := shortExact_kernel_ι π
    have hS' : S'.ShortExact := shortExact_kernel_ι π'
    let f : S ⟶ S' :=
      ⟨kernel.map π π' b alpha hb.symm, b, alpha, kernel.lift_ι _ _ _, hb⟩
    have hK : StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom
        (R := R) S.X₁ (-(e : ℤ) - 1) := by
      convert kernel_pseudoCoherent F M π (-((e + 1 : ℕ) : ℤ) - 1) hM using 1
      push_cast
      ring
    exact ext_vanishes_of_kernel_map hS hS' f e (ih f.τ₁ hK (tor_vanishes_kernel_map hS hS' f e hT))

/-- If `M` is `(-e-1)`-pseudo-coherent, all seven conditions are equivalent. -/
@[stacks 0G9V "all conditions under pseudo-coherence"]
lemma tfae_of_isPseudoCoherentFrom
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (-(e : ℤ) - 1)) :
    List.TFAE [
      HasLiftVanishingAbove p p' alpha e,
      HasLiftVanishingAtSucc p p' alpha e,
      ExtMapVanishesAbove alpha e,
      ExtMapVanishesAtSucc alpha e,
      CanonicalExtClassPullbackVanishes p p' alpha e,
      TorMapVanishesAbove alpha e,
      TorMapVanishesAtSucc alpha e] := by
  have hE := tfae_lift_ext_conditions p p' alpha e
  have hT := tfae_tor_conditions alpha e
  tfae_have 1 ↔ 2 := hE.out 1 2
  tfae_have 2 ↔ 3 := hE.out 2 3
  tfae_have 3 ↔ 4 := hE.out 3 4
  tfae_have 4 ↔ 5 := hE.out 4 5
  tfae_have 5 → 6 := canonicalExtClassPullbackVanishes_imp_torMapVanishesAbove p p' alpha e
  tfae_have 6 ↔ 7 := hT.out 1 2
  tfae_have 7 → 4 := extMapVanishesAtSucc_of_tor_of_pseudoCoherent e alpha hM
  tfae_finish

/-- Over a Noetherian ring, all seven conditions are equivalent when `M` is finite. -/
@[stacks 0G9V "Noetherian finite-module case"]
lemma tfae_of_isNoetherianRing_of_finite [IsNoetherianRing R] [Module.Finite R M] :
    List.TFAE [
      HasLiftVanishingAbove p p' alpha e,
      HasLiftVanishingAtSucc p p' alpha e,
      ExtMapVanishesAbove alpha e,
      ExtMapVanishesAtSucc alpha e,
      CanonicalExtClassPullbackVanishes p p' alpha e,
      TorMapVanishesAbove alpha e,
      TorMapVanishesAtSucc alpha e] := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
    show StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := R) M
    exact ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      K 0 M).2.2).mpr inferInstance
  exact tfae_of_isPseudoCoherentFrom p p' alpha e
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all K).mp hpc (-(e : ℤ) - 1))

end
