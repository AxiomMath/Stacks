module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LefschetzTraceFormula
public import StacksFrontier.Homology.Perfect.Filtration
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The trace of `π_X^*` on `RΓ_c(X_k̄, K)` for a bounded complex, termwise

Step 3 of the proof of [Stacks, Tag 03UG]. Let `K` be a complex of sheaves of `Λ`-modules on
`X_étale` concentrated in degrees `[a, b]`, such that `RΓ_c(X_k̄, Kⁿ)` is perfect for each term
`Kⁿ`, placed in degree zero. Then `RΓ_c(X_k̄, K)` is perfect and

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{n = a}^{b} (-1)ⁿ Tr(π_X^* | RΓ_c(X_k̄, Kⁿ))`

in `Λ^♮`, for the canonical action `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`.

The proof uses the additivity of the trace along short exact sequences
(`Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_X₂_eq_add`) twice.

* The stupid truncations give `0 → σ^{≥ a+1} K → K → Kᵃ[-a] → 0`, which drives an induction on
  `b - a`.
* The sign comes from the short exact sequence `0 → F[-n] → cone(𝟙_{F[-n]}) → F[-n+1] → 0`,
  whose middle term is contractible. Its cohomology with compact support is zero, so
  `Tr(F[-n]) = -Tr(F[-n+1])`.

No shift of the canonical Frobenius is needed.

## Main results

* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_X₁`,
  `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_X₃`: two out of three for
  perfectness, in the outer positions.
* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomology_of_homotopy`: a contractible
  complex has zero cohomology with compact support.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_single`: the trace for a sheaf
  placed in degree `n` is `(-1)ⁿ` times the trace in degree zero.
* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_eq_sum_single`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

section TwoOutOfThree

variable {S : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
  (h₃ : CochainComplex.plus _ S.X₃)

include hS hcard in
/-- **Perfectness of `RΓ_c(X_k̄, -)` is two out of three, first term.** -/
theorem isPerfect_compactSupportFrobeniusCohomology_X₁
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₂, h₂⟩)))
    (hp₃ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₃, h₃⟩))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₁, h₁⟩)) := by
  obtain ⟨Rs⟩ := Functor.TwistResolution.nonempty
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (compactSupportShortComplex_shortExact.{u, 0} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₃, h₃⟩)).property)
    (compactSupportShortComplexTwist.{u, 0} Λ f j kbar p q hcard S)
  exact (StacksDraft.Perfect.isPerfect_of_distinguished _
    (Functor.twistTriangle_distinguished
      (etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))) _ _ _ Rs)).2.2 hp₂ hp₃

include hS hcard in
/-- **Perfectness of `RΓ_c(X_k̄, -)` is two out of three, last term.** -/
theorem isPerfect_compactSupportFrobeniusCohomology_X₃
    (hp₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₁, h₁⟩)))
    (hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₂, h₂⟩))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₃, h₃⟩)) := by
  obtain ⟨Rs⟩ := Functor.TwistResolution.nonempty
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
    (compactSupportShortComplex_shortExact.{u, 0} Λ f j kbar hS)
    (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₁, h₁⟩)).property)
    (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ⟨S.X₃, h₃⟩)).property)
    (compactSupportShortComplexTwist.{u, 0} Λ f j kbar p q hcard S)
  exact (StacksDraft.Perfect.isPerfect_of_distinguished _
    (Functor.twistTriangle_distinguished
      (etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))) _ _ _ Rs)).1 hp₁ hp₂

end TwoOutOfThree

section Contractible

/-- **A contractible complex has zero cohomology with compact support.** -/
theorem isZero_compactSupportFrobeniusCohomology_of_homotopy
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (h : Homotopy (𝟙 K.obj) 0) :
    IsZero (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)) := by
  let G₁ := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let G₂ := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let K' := G₂.mapCochainComplexPlus.obj (G₁.mapCochainComplexPlus.obj K)
  have h₁ : Homotopy (𝟙 ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj)) 0 :=
    (Homotopy.ofEq (by simp)).trans ((G₁.mapHomotopy h).trans (Homotopy.ofEq (by simp)))
  have h₂ : Homotopy (𝟙 K'.obj) 0 :=
    (Homotopy.ofEq ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map_id _).symm).trans
      ((G₂.mapHomotopy h₁).trans
        (Homotopy.ofEq ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map_zero _ _)))
  have hQ : IsZero (DerivedCategory.Plus.Q.obj K') := by
    rw [IsZero.iff_id_eq_zero]
    refine ObjectProperty.hom_ext _ ?_
    exact (DerivedCategory.Q.map_id K'.obj).symm.trans
      ((DerivedCategory.Q_map_eq_of_homotopy _ h₂).trans (DerivedCategory.Q.map_zero _ _))
  let F₁ := etaleModuleDirectImage.{u, 0} Λ
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
  let F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))
  let : F₁.rightDerivedFunctorPlus.CommShift ℤ := Functor.commShiftRightDerivedFunctorPlus F₁
  have : F₁.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_rightDerivedFunctorPlus F₁
  let : F₂.rightDerivedFunctorPlus.CommShift ℤ := Functor.commShiftRightDerivedFunctorPlus F₂
  have : F₂.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_rightDerivedFunctorPlus F₂
  exact DerivedCategory.Plus.ι.map_isZero
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map_isZero
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map_isZero hQ))

end Contractible

section Iso

/-- The trace of `π_X^*` on `RΓ_c(X_k̄, -)` is invariant under isomorphism. -/
theorem canonicalCompactSupportLefschetzNumber_congr [Finite Λ]
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (e : K ≅ K')
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)))
    (hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K'))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hK =
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K' hK' :=
  perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk j.toBase) kbar p q
    hcard ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.mapIso e) hK hK'

/-- The trace of `π_X^*` vanishes when `RΓ_c(X_k̄, -)` is zero. -/
theorem canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero [Finite Λ]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)))
    (hZ : IsZero (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K))) :
    canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hK = 0 :=
  perfectDerivedTrace_eq_zero_of_isZero Λ _ hZ _

/-- A complex all of whose terms are zero has zero cohomology with compact support. -/
theorem isZero_compactSupportFrobeniusCohomology_of_isZero_X
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hK : ∀ n, IsZero (K.obj.X n)) :
    IsZero (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)) :=
  isZero_compactSupportFrobeniusCohomology_of_homotopy Λ j kbar K
    (Homotopy.ofEq (by ext n : 1; exact (hK n).eq_of_src _ _))

end Iso

section Single

variable [Finite Λ] (F : EtaleModules.{u, 0} Λ X)

/-- The sheaf `F` placed in degree `m`. -/
abbrev singleIn (m : ℤ) : CochainComplex.Plus (EtaleModules.{u, 0} Λ X) :=
  (Stacks.DerivedIndexing.singlePlusFunctor _ m).obj F

/-- `(F[-m])[1] ≅ F[-(m - 1)]`. -/
def singleInShiftIso (m : ℤ) :
    (singleIn Λ F m).obj⟦(1 : ℤ)⟧ ≅ (singleIn Λ F (m - 1)).obj :=
  ((CochainComplex.singleFunctors (EtaleModules.{u, 0} Λ X)).shiftIso 1 (m - 1) m
    (add_sub_cancel 1 m)).app F

/-- The short exact sequence `0 → F[-m] → cone(𝟙) → F[-m][1] → 0`. -/
abbrev singleConeShortComplex (m : ℤ) : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) :=
  CochainComplex.mappingCone.triangleRotateShortComplex (𝟙 (singleIn Λ F m).obj)

/-- The short complex `singleConeShortComplex Λ F m` is short exact. -/
lemma singleConeShortComplex_shortExact (m : ℤ) : (singleConeShortComplex Λ F m).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting
      (𝟙 (singleIn Λ F m).obj) n).shortExact

/-- The third term of `singleConeShortComplex Λ F m` is bounded below. -/
lemma singleConeShortComplex_plus₃ (m : ℤ) :
    CochainComplex.plus _ (singleConeShortComplex Λ F m).X₃ :=
  (CochainComplex.plus _).prop_of_iso (singleInShiftIso Λ F m).symm (singleIn Λ F (m - 1)).property

/-- The middle term of `singleConeShortComplex Λ F m` is bounded below. -/
lemma singleConeShortComplex_plus₂ (m : ℤ) :
    CochainComplex.plus _ (singleConeShortComplex Λ F m).X₂ :=
  CochainComplex.plus_X₂_of_shortExact (singleConeShortComplex_shortExact Λ F m)
    (singleIn Λ F m).property (singleConeShortComplex_plus₃ Λ F m)

include hcard in
/-- **`Tr(F[-m]) = -Tr(F[-(m-1)])`**, with perfectness passing both ways: the cone of the
identity of `F[-m]` is contractible. -/
theorem canonicalCompactSupportLefschetzNumber_singleIn_step (m : ℤ) :
    (StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ F m))) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ F (m - 1))))) ∧
    ∀ hm hm', canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        (singleIn Λ F m) hm =
      -canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard (singleIn Λ F (m - 1))
        hm' := by
  set S := singleConeShortComplex Λ F m
  have hS := singleConeShortComplex_shortExact Λ F m
  have h₁ : CochainComplex.plus _ S.X₁ := (singleIn Λ F m).property
  have h₂ := singleConeShortComplex_plus₂ Λ F m
  have h₃ := singleConeShortComplex_plus₃ Λ F m
  have e₃ : (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ≅ singleIn Λ F (m - 1) :=
    ObjectProperty.isoMk _ (singleInShiftIso Λ F m)
  have hZ : IsZero (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar ⟨S.X₂, h₂⟩)) :=
    isZero_compactSupportFrobeniusCohomology_of_homotopy Λ j kbar ⟨S.X₂, h₂⟩
      (CochainComplex.mappingCone.homotopyToZeroOfId _)
  have hp₂ := StacksDraft.Perfect.isPerfect_of_isZero _ hZ
  refine ⟨⟨fun hm => ?_, fun hm' => ?_⟩, fun hm hm' => ?_⟩
  · exact isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ j kbar e₃
      (isPerfect_compactSupportFrobeniusCohomology_X₃ Λ j kbar p q hcard hS h₁ h₂ h₃ hm hp₂)
  · exact isPerfect_compactSupportFrobeniusCohomology_X₁ Λ j kbar p q hcard hS h₁ h₂ h₃ hp₂
      (isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ j kbar e₃.symm hm')
  · have hp₃ := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ j kbar e₃.symm hm'
    have hadd := canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ f j kbar p q hcard hS h₁ h₂ h₃
      hm hp₂ hp₃
    rw [canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero Λ j kbar p q hcard _ hp₂ hZ,
      canonicalCompactSupportLefschetzNumber_congr Λ j kbar p q hcard e₃ hp₃ hm'] at hadd
    exact eq_neg_of_add_eq_zero_left hadd.symm

include hcard in
/-- **The trace for a sheaf placed in degree `m` is `(-1)ᵐ` times the trace in degree zero.** -/
theorem canonicalCompactSupportLefschetzNumber_singleIn (m : ℤ)
    (h₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ F 0)))) :
    ∃ hm, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard (singleIn Λ F m) hm =
      m.negOnePow • canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        (singleIn Λ F 0) h₀ := by
  induction m using Int.induction_on with
  | zero => exact ⟨h₀, by simp⟩
  | succ m ih =>
    obtain ⟨hm, hm_eq⟩ := ih
    have hstep := canonicalCompactSupportLefschetzNumber_singleIn_step Λ j kbar p q hcard F (m + 1)
    simp only [add_sub_cancel_right] at hstep
    have hm1 := hstep.1.2 hm
    refine ⟨hm1, ?_⟩
    rw [hstep.2 hm1 hm, hm_eq, Int.negOnePow_succ, Units.neg_smul]
  | pred m ih =>
    obtain ⟨hm, hm_eq⟩ := ih
    have hstep :=
      canonicalCompactSupportLefschetzNumber_singleIn_step Λ j kbar p q hcard F (-(m : ℤ))
    have hm1 := hstep.1.1 hm
    refine ⟨hm1, ?_⟩
    have h2 := hstep.2 hm hm1
    rw [hm_eq] at h2
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one, Units.neg_smul, h2, neg_neg]

end Single

section Bounded

open ComplexShape

variable [Finite Λ]

/-- The terms of `σ^{≤ a} K` vanish away from degree `a`, for `K` concentrated in degrees `≥ a`. -/
lemma isZero_stupidTruncLE_X (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (i : ℤ) (hi : i ≠ a) :
    IsZero ((K.stupidTrunc (embeddingUpIntLE a)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact Functor.isZero_stupidTrunc_X_of_isZero K _ i (K.isZero_of_isStrictlyGE a i h)
  · exact K.isZero_stupidTrunc_X (embeddingUpIntLE a) i
      ((notMem_range_embeddingUpIntLE_iff a i).2 h)

/-- `σ^{≤ a} K ≅ Kᵃ[-a]` for `K` concentrated in degrees `≥ a`. -/
def stupidTruncLEIsoSingle (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] :
    K.stupidTrunc (embeddingUpIntLE a) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if hi : i = a then
        eqToIso (by rw [hi]) ≪≫ K.stupidTruncXIso (embeddingUpIntLE a) (i := 0)
          (show a - ((0 : ℕ) : ℤ) = a by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (K.X a)).symm ≪≫
          eqToIso (by rw [hi])
      else (isZero_stupidTruncLE_X Λ K a i hi).iso
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi))
    (fun i j hij => by
      by_cases hi : i = a
      · have hj : j ≠ a := by
          rw [← (ComplexShape.up ℤ).next_eq' hij, hi, CochainComplex.next]
          exact (lt_add_one a).ne'
        exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj).eq_of_tgt _ _
      · exact (isZero_stupidTruncLE_X Λ K a i hi).eq_of_src _ _)

include hcard in
/-- The zero case: a complex concentrated in an empty range of degrees. -/
lemma canonicalCompactSupportLefschetzNumber_eq_sum_single_of_lt
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a b : ℤ) (hab : b < a)
    [CochainComplex.IsStrictlyGE K.obj a] [CochainComplex.IsStrictlyLE K.obj b]
    (h : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ (K.obj.X n) 0)))) :
    ∃ hK, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hK =
      ∑ n ∈ Finset.Icc a b, n.negOnePow • canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar
        p q hcard (singleIn Λ (K.obj.X n) 0) (h n) := by
  have hz : ∀ n, IsZero (K.obj.X n) := fun n => by
    by_cases hn : n < a
    · exact CochainComplex.isZero_of_isStrictlyGE K.obj a n hn
    · exact CochainComplex.isZero_of_isStrictlyLE K.obj b n (lt_of_lt_of_le hab (not_lt.mp hn))
  have hZ := isZero_compactSupportFrobeniusCohomology_of_isZero_X Λ j kbar K hz
  refine ⟨StacksDraft.Perfect.isPerfect_of_isZero _ hZ, ?_⟩
  rw [canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero Λ j kbar p q hcard _ _ hZ,
    Finset.Icc_eq_empty (not_le.mpr hab), Finset.sum_empty]

include hcard in
/-- For `K` concentrated in degrees `[a, b]` with `b < a + N`, whose terms placed in degree zero
have perfect cohomology with compact support, `RΓ_c` of `K` is perfect and its Lefschetz number
is `∑ n ∈ [a, b], (-1)ⁿ Tr(Kⁿ[0])`. -/
lemma canonicalCompactSupportLefschetzNumber_eq_sum_single_aux (N : ℕ) :
    ∀ (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a b : ℤ), b < a + N →
      CochainComplex.IsStrictlyGE K.obj a → CochainComplex.IsStrictlyLE K.obj b →
      ∀ (h : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ (K.obj.X n) 0)))),
      ∃ hK, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hK =
        ∑ n ∈ Finset.Icc a b, n.negOnePow • canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j
          kbar p q hcard (singleIn Λ (K.obj.X n) 0) (h n) := by
  induction N with
  | zero =>
    intro K a b hab _ _ h
    exact canonicalCompactSupportLefschetzNumber_eq_sum_single_of_lt Λ j kbar p q hcard K a b
      (by simpa using hab) h
  | succ N ih =>
    intro K a b hab hga hlb h
    by_cases hba : b < a
    · exact canonicalCompactSupportLefschetzNumber_eq_sum_single_of_lt Λ j kbar p q hcard K a b
        hba h
    have hab' : a ≤ b := not_lt.mp hba
    -- the stupid truncation sequence `0 → σ^{≥ a+1} K → K → σ^{≤ a} K → 0`
    let S := Functor.stupidTruncShortComplex K.obj a
    have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
      (Functor.stupidTruncSplitting K.obj a i).shortExact
    let G := K.obj.stupidTrunc (embeddingUpIntGE (a + 1))
    have hGge : CochainComplex.IsStrictlyGE G (a + 1) :=
      Functor.isStrictlyGE_stupidTruncGE K.obj (a + 1)
    have hGle : CochainComplex.IsStrictlyLE G b := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => Functor.isZero_stupidTrunc_X_of_isZero K.obj _ i
        (CochainComplex.isZero_of_isStrictlyLE K.obj b i hi)
    have h₁ : CochainComplex.plus _ S.X₁ := ⟨a + 1, hGge⟩
    have h₂ : CochainComplex.plus _ S.X₂ := K.property
    have h₃ : CochainComplex.plus _ S.X₃ := Functor.plus_stupidTruncLE K.obj K.property a
    -- the terms of `σ^{≥ a+1} K`
    have eG : ∀ n, a + 1 ≤ n → (G.X n ≅ K.obj.X n) := fun n hn =>
      K.obj.stupidTruncXIso (embeddingUpIntGE (a + 1)) (i := (n - (a + 1)).toNat)
        (show a + 1 + (((n - (a + 1)).toNat : ℕ) : ℤ) = n by
          rw [Int.toNat_of_nonneg (sub_nonneg.mpr hn)]; ring)
    have hG : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar (singleIn Λ (G.X n) 0))) := by
      intro n
      by_cases hn : a + 1 ≤ n
      · exact isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso (eG n hn).symm) (h n)
      · refine StacksDraft.Perfect.isPerfect_of_isZero _
          (isZero_compactSupportFrobeniusCohomology_of_isZero_X Λ j kbar _ fun i => ?_)
        exact Functor.map_isZero (HomologicalComplex.eval _ _ i)
          (Functor.map_isZero (CochainComplex.singleFunctor _ 0)
            (CochainComplex.isZero_of_isStrictlyGE G (a + 1) n (not_le.mp hn)))
    obtain ⟨hp₁, hG_eq⟩ := ih ⟨G, h₁⟩ (a + 1) b (by push_cast at hab; linarith) hGge hGle hG
    -- the last piece is `Kᵃ[-a]`
    have e₃ : (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ≅ singleIn Λ (K.obj.X a) a :=
      ObjectProperty.isoMk _ (stupidTruncLEIsoSingle Λ K.obj a)
    obtain ⟨ha, ha_eq⟩ := canonicalCompactSupportLefschetzNumber_singleIn Λ j kbar p q hcard
      (K.obj.X a) a (h a)
    have hp₃ := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ j kbar e₃.symm ha
    have hp₂ := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ f j kbar hS h₁ h₂ h₃ hp₁ hp₃
    refine ⟨hp₂, ?_⟩
    have hadd := canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ f j kbar p q hcard hS h₁ h₂ h₃
      hp₁ hp₂ hp₃
    have hG_eq' : canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard
        ⟨S.X₁, h₁⟩ hp₁ = _ := hG_eq
    refine hadd.trans ?_
    rw [hG_eq', canonicalCompactSupportLefschetzNumber_congr Λ j kbar p q hcard e₃ hp₃ ha, ha_eq,
      ← Finset.insert_Icc_add_one_left_eq_Icc hab',
      Finset.sum_insert (fun hmem => by simp at hmem), add_comm]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [canonicalCompactSupportLefschetzNumber_congr Λ j kbar p q hcard
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso (eG n (Finset.mem_Icc.mp hn).1))
      (hG n) (h n)]

include hcard in
/-- **Step 3 of [Stacks, Tag 03UG]: the trace on a bounded complex, termwise.** For `K`
concentrated in degrees `[a, b]` with `RΓ_c(X_k̄, Kⁿ)` perfect for every term, `RΓ_c(X_k̄, K)` is
perfect and

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{n = a}^{b} (-1)ⁿ Tr(π_X^* | RΓ_c(X_k̄, Kⁿ))`,

where `Kⁿ` is placed in degree zero. -/
theorem canonicalCompactSupportLefschetzNumber_eq_sum_single
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a b : ℤ)
    [CochainComplex.IsStrictlyGE K.obj a] [CochainComplex.IsStrictlyLE K.obj b]
    (h : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (K.obj.X n))))) :
    ∃ hK, canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j kbar p q hcard K hK =
      ∑ n ∈ Finset.Icc a b, n.negOnePow • canonicalCompactSupportLefschetzNumber.{u, 0} Λ f j
        kbar p q hcard ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (K.obj.X n)) (h n) :=
  canonicalCompactSupportLefschetzNumber_eq_sum_single_aux Λ j kbar p q hcard
    (b - a + 1).toNat K a b (by omega) inferInstance inferInstance h

end Bounded

end Stacks.EtaleCohomology

end
