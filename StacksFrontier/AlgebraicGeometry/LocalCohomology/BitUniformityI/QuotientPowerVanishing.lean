module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityI.VanishingEquivalences
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.UniverseChange
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.TorsionColimit
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniform Ext-vanishing for the quotients by the powers of an ideal

Let `I` be an ideal of a Noetherian ring `A` and let `e` be the cohomological dimension of `I`
in `A`. For every `n` there is an `m > n` such that the quotient map `A/I^m → A/I^n` induces the
zero map on `Ext^i(-, N)` for every module `N` and every `i > e`.

## Main results

* `Stacks.LocalCohomology.exists_quotientPower_extMapVanishesAbove` produces the deeper power.

## Implementation notes

The vanishing of `colim_m Ext^{e+1}(A/I^m, N)` is read off from the two identifications already
in the library: `Stacks.LocalCohomology.localCohomologyHomologyIsoColimitExt` presents that
colimit as a local cohomology module, and `Stacks.LocalCohomology.localCohomology_vanishing_tfae`
propagates the vanishing bound for `A` itself, which is the defining property of the
cohomological dimension, to every module. Passing between the two models of local cohomology uses
`Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app`, which is Noetherian
input.

A single element of that colimit then suffices: the canonical class of condition (5) of Tag 0G9V,
built from the image of the differential `P_{e+1} → P_e` of a projective resolution of `A/I^n`,
controls all of `Ext` at once through `tfae_lift_ext_conditions`.

The cohomological dimension is an integer, while the conditions of Tag 0G9V are indexed by a
natural number; the statement uses `Int.toNat`. That loses nothing for a proper ideal, whose
cohomological dimension is nonnegative, and the only ideal with cohomological dimension `-1` is
the unit ideal, for which every `A/I^n` with `n ≥ 1` vanishes. The source's hypothesis `n ≥ 1` is
not needed: for `n = 0` the target `A/I^0` is zero and every condition holds.

## References

* [Stacks Project, Tag 0EH1](https://stacks.math.columbia.edu/tag/0EH1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Dualizing (localCohomology quotientPowerSucc extPowers)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

noncomputable section

/-! ### Elements of a vanishing sequential colimit of modules -/

/-- Forgetting the module structure preserves `ℕ`-indexed colimits of modules one universe above
the ring, where `Ext` modules live. -/
private lemma forget_preservesSequentialColimits (A : Type u) [CommRing A] :
    PreservesColimitsOfShape.{0, 0} ℕ (forget (ModuleCat.{u + 1} A)) := by
  let V := CategoryTheory.forget (ModuleCat.{u + 1} A)
  let A' : Type (u + 1) := ULift.{u + 1, u} A
  let e : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} A' :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv : A' ≃+* A)
  let V' := CategoryTheory.forget (ModuleCat.{u + 1} A')
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits V'
  have : PreservesColimitsOfShape.{0, 0} ℕ V' := inferInstance
  have hV : e.functor ⋙ V' ≅ V := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  have : PreservesColimitsOfShape.{0, 0} ℕ (e.functor ⋙ V') := inferInstance
  exact preservesColimitsOfShape_of_natIso hV

/-- If a sequential colimit of modules vanishes, every element of every stage is killed by one of
the transition maps. -/
private lemma exists_map_eq_zero_of_isZero_colimit {A : Type u} [CommRing A]
    (F : ℕ ⥤ ModuleCat.{u + 1} A) [HasColimit F] (hF : IsZero (colimit F))
    (n : ℕ) (x : F.obj n) : ∃ m : ℕ, ∃ h : n ≤ m, F.map (homOfLE h) x = 0 := by
  have := forget_preservesSequentialColimits A
  have hx : colimit.ι F n x = 0 := by
    rw [show colimit.ι F n = 0 from hF.eq_of_tgt _ _]
    simp
  obtain ⟨m, f, hm⟩ := Concrete.colimit_rep_eq_zero.{u + 1} A F n x hx
  exact ⟨m, leOfHom f, by rw [Subsingleton.elim (homOfLE (leOfHom f)) f]; exact hm⟩

/-! ### Vanishing of the colimit of Ext modules above the cohomological dimension -/

/-- Over a Noetherian ring the two models of local cohomology agree in every degree: the derived
`I`-power-torsion model of Tag 0A6Q and the termwise torsion subcomplex of a K-injective
representative. -/
private def localCohomologyModelHomologyIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj K)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (localCohomology A I K) := by
  have := isIso_compareSectionsWithSupportLocalCohomology_app.{u, 0} A I hI K
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).mapIso
      (asIso ((compareSectionsWithSupportLocalCohomology.{u, 0} A I hI).app K))).symm ≪≫
    localCohomologyWithSupportInHomologyIso A I K q

/-- Above the cohomological dimension of `I` in `A`, the colimit over `m` of
`Ext^q(A/I^m, N)` vanishes for every module `N`. -/
private lemma isZero_colimit_extPowers (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (N : ModuleCat.{u} A) (q : ℤ)
    (hq : cohomologicalDimension A I hI < q) :
    IsZero (colimit (extPowers A I
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) q)) := by
  have hd := isLocalCohomologyBound_cohomologicalDimension A I hI
  have h2 := ((localCohomology_vanishing_tfae.{u} A I hI _ hd.1).out 1 2).mp hd.2
  have hzero := (h2 N q hq).of_iso (localCohomologyModelHomologyIso A I hI _ q).symm
  exact (Functor.map_isZero (ModuleCat.uliftFunctor.{u + 1} A) hzero).of_iso
    (localCohomologyHomologyIsoColimitExt A I _ q).symm

/-- The transition maps of the system `m ↦ Ext^q(A/I^m, K)` are precomposition with the quotient
maps between the powers of `I`. -/
private lemma extPowers_map_apply {A : Type u} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ) {i j : ℕ} (h : i ≤ j)
    (x : DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ I ^ i))) K q) :
    (extPowers A I K q).map (homOfLE h) x =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom
          (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) h)).toLinearMap) ≫ x := by
  let F := extPowers A I K q
  change F.map (homOfLE h) x = _
  induction j, h using Nat.le_induction with
  | base =>
    simp [F, extPowers, Ideal.Quotient.factorₐ_refl]
    rfl
  | succ j hij ih =>
    have hcomp : homOfLE (show i ≤ j + 1 from hij.trans (Nat.le_succ j)) =
        homOfLE hij ≫ homOfLE (Nat.le_succ j) := Subsingleton.elim _ _
    rw [hcomp, Functor.map_comp]
    change (F.map (homOfLE (Nat.le_succ j))) ((F.map (homOfLE hij)) x) = _
    rw [ih]
    dsimp only [F, extPowers]
    rw [Functor.ofSequence_map_homOfLE_succ]
    change (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (quotientPowerSucc A I j) ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (I := I) hij)).toLinearMap) ≫ x) = _
    have hstep : quotientPowerSucc A I j ≫
        ModuleCat.ofHom
          (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) hij)).toLinearMap =
      ModuleCat.ofHom (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (I := I) (hij.trans (Nat.le_succ j)))).toLinearMap := by
      refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp [quotientPowerSucc]
    rw [← Category.assoc, ← Functor.map_comp, hstep]

/-! ### The canonical class from a null-homotopy -/

/-- A null-homotopy of `a ≫ b`, where `b` is the corestriction of the differential `P'^s → P'^t`
to its image, factors `a^s` followed by that corestriction through the differential of `P`. -/
private lemma comp_factorThruImage_eq_of_homotopy {A : Type u} [CommRing A]
    {P P' : CochainComplex (ModuleCat.{u} A) ℤ} {s t : ℤ} (hst : s + 1 = t) (a : P ⟶ P')
    (b : P' ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) s).obj (image (P'.d s t)))
    (hb : b.f s = factorThruImage (P'.d s t) ≫ (HomologicalComplex.singleObjXSelf _ s _).inv)
    (H : Homotopy (a ≫ b) 0) :
    a.f s ≫ factorThruImage (P'.d s t) =
      P.d s t ≫ H.hom t s ≫ (HomologicalComplex.singleObjXSelf _ s _).hom := by
  have hc := H.comm s
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel s t from hst),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (s - 1) s by simp)] at hc
  change a.f s ≫ b.f s = P.d s t ≫ H.hom t s + H.hom s (s - 1) ≫ 0 + 0 at hc
  simp only [comp_zero, add_zero, hb] at hc
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    hc =≫ (HomologicalComplex.singleObjXSelf _ s _).hom

/-- If the pullback along `alpha` of the class `inv p' ≫ b ≫ ε` vanishes, where `p'` is a
quasi-isomorphism, then `a ≫ b` vanishes in the derived category for every lift `a` of `alpha`. -/
private lemma derived_map_comp_eq_zero_of_isResolutionLift {A : Type u} [CommRing A]
    {M M' : ModuleCat.{u} A} {P P' L : CochainComplex (ModuleCat.{u} A) ℤ}
    {Y : DerivedCategory (ModuleCat.{u} A)} (p : P ⟶ singleComplex M) (p' : P' ⟶ singleComplex M')
    [IsIso (DerivedCategory.Q.map p')] (alpha : M ⟶ M') (a : P ⟶ P')
    (ha : IsResolutionLift p p' alpha a) (b : P' ⟶ L) (ε : DerivedCategory.Q.obj L ≅ Y)
    (h : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map alpha ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M').hom ≫
        inv (DerivedCategory.Q.map p') ≫ DerivedCategory.Q.map b ≫ ε.hom = 0) :
    DerivedCategory.Q.map (a ≫ b) = 0 := by
  have hS : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map alpha ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M').hom =
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).hom ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map alpha) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.naturality alpha
  rw [← Category.assoc, hS, Category.assoc] at h
  replace h := (cancel_epi _).1 (h.trans comp_zero.symm)
  have hRel : DerivedCategory.Q.map a ≫ DerivedCategory.Q.map p' =
      DerivedCategory.Q.map p ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map alpha) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map ha
  have hpre := DerivedCategory.Q.map p ≫= h
  rw [← Category.assoc, ← hRel] at hpre
  apply (cancel_mono ε.hom).1
  simpa only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, comp_zero, zero_comp]
    using hpre

/-! ### Tag 0EH1 -/

/-- **[Stacks, Tag 0EH1].** Let `I` be an ideal of a Noetherian ring `A` and let `e` be the
cohomological dimension of `I` in `A`. For every `n` there is an `m > n` for which the quotient
map `A/I^m → A/I^n` satisfies the equivalent conditions of [Stacks, Tag 0G9V] in degree `e`:
`Ext^i(A/I^n, N) → Ext^i(A/I^m, N)` is zero for every `A`-module `N` and every `i > e`. -/
@[stacks 0EH1]
theorem exists_quotientPower_extMapVanishesAbove
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n < m,
      ExtMapVanishesAbove
        (ModuleCat.ofHom (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (I := I) (Nat.le_of_lt hnm))).toLinearMap)
        (cohomologicalDimension A I (IsNoetherian.noetherian I)).toNat := by
  have hI : I.FG := IsNoetherian.noetherian I
  set e := (cohomologicalDimension A I hI).toNat with he
  set q : ℤ := ((e + 1 : ℕ) : ℤ) with hq
  have hdq : cohomologicalDimension A I hI < q := by
    rw [hq, he]
    omega
  -- The resolution of `A/I^n` and the canonical cocycle of condition (5) of Tag 0G9V.
  let Mn : ModuleCat.{u} A := ModuleCat.of A (A ⧸ I ^ n)
  let Qn : ProjectiveResolution Mn := ProjectiveResolution.of Mn
  let Pn := Qn.cochainComplex
  let pn := Qn.π'
  let _ : CochainComplex.IsProjectiveResolution pn := isProjectiveResolution_π' Qn
  let s : ℤ := -q
  let t : ℤ := -(e : ℤ)
  let N : ModuleCat.{u} A := image (Pn.d s t)
  let b : Pn ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) s).obj N :=
    HomologicalComplex.mkHomToSingle (factorThruImage (Pn.d s t)) fun j _ ↦
      (cancel_mono (image.ι (Pn.d s t))).1 <| by
        simpa only [Category.assoc, image.fac, zero_comp] using Pn.d_comp_d j s t
  let Kcoeff : DerivedCategory (ModuleCat.{u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  let z₀ : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj Mn) ⟶ Kcoeff⟦q⟧ :=
    inv (DerivedCategory.Q.map pn) ≫ DerivedCategory.Q.map b ≫ (derivedSingleShiftIso N q).hom
  let z : DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Mn)
      Kcoeff q := ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app Mn).hom ≫ z₀
  -- The class `z` dies at some finite stage of the system of Ext modules.
  let F := extPowers A I Kcoeff q
  let x : F.obj n := z
  obtain ⟨m₀, hnm₀, hkill₀⟩ :=
    exists_map_eq_zero_of_isZero_colimit F (isZero_colimit_extPowers A I hI N q hdq) n x
  have hnm : n < m₀ + 1 := Nat.lt_succ_of_le hnm₀
  have hkill : F.map (homOfLE hnm.le) x = 0 := by
    rw [show homOfLE hnm.le = homOfLE hnm₀ ≫ homOfLE (Nat.le_succ m₀) from Subsingleton.elim _ _,
      Functor.map_comp]
    change F.map _ (F.map (homOfLE hnm₀) x) = 0
    rw [hkill₀]
    simp
  refine ⟨m₀ + 1, hnm, ?_⟩
  -- The resolution of `A/I^m` and a lift of the quotient map.
  let Mm : ModuleCat.{u} A := ModuleCat.of A (A ⧸ I ^ (m₀ + 1))
  let alpha : Mm ⟶ Mn := ModuleCat.ofHom
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) hnm.le)).toLinearMap
  let Qm : ProjectiveResolution Mm := ProjectiveResolution.of Mm
  let pm := Qm.π'
  let _ : CochainComplex.IsProjectiveResolution pm := isProjectiveResolution_π' Qm
  let rlift : Qm.Hom Qn alpha :=
    ⟨ProjectiveResolution.lift alpha Qm Qn,
      ProjectiveResolution.lift_commutes_zero alpha Qm Qn⟩
  let a := rlift.hom'
  have ha : IsResolutionLift pm pn alpha a := rlift.hom'_comp_π'
  rw [extPowers_map_apply I Kcoeff q hnm.le x] at hkill
  have : Qm.cochainComplex.IsKProjective := resolution_isKProjective pm
  obtain ⟨H⟩ := (derived_map_eq_zero_iff (a ≫ b)).mp
    (derived_map_comp_eq_zero_of_isResolutionLift pm pn alpha a ha b (derivedSingleShiftIso N q)
      hkill)
  -- Condition (5) of Tag 0G9V, hence all of conditions (1)--(5).
  have hcanonical : CanonicalExtClassPullbackVanishes pm pn alpha e :=
    ⟨a, _, ha, comp_factorThruImage_eq_of_homotopy (by dsimp only [s, t, q]; omega) a b
      (HomologicalComplex.mkHomToSingle_f _ _) H⟩
  exact ((tfae_lift_ext_conditions pm pn alpha e).out 5 3).mp hcanonical

end

end Stacks.LocalCohomology

end
