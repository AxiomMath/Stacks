module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompRightDerivedBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.TorsionExhaustion
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# The composition comparison `R(H ∘ F) ⟶ RH ∘ F` for an exact `F`, on bounded below complexes

Let `F : A ⥤ B` be an exact functor and `H : B ⥤ C` an additive left exact functor between
abelian categories with enough injectives, and write
`c : R⁺(F ⋙ H) ⟶ R⁺F ⋙ R⁺H` for the composition comparison on bounded below derived categories
(`CategoryTheory.Functor.rightDerivedFunctorPlusComp`). This file gives three criteria for `c`,
in the form needed by case (a) of [Stacks, Tag 0F7B]:

* `c` is invertible at `M[0]` when `M` has a bounded below resolution by objects `T` which are
  acyclic for `F ⋙ H` and whose images `F(T)` are acyclic for `H`;
* `c` is invertible at `M[0]` when `M` is a filtered colimit of objects at which it is, provided
  the higher derived functors `R^q(F ⋙ H)` and `F ⋙ R^q H` preserve that colimit;
* if `K` is a bounded below complex of injective objects such that `c` is invertible at every
  `H^q(K)[0]`, then `H` carries every quasi-isomorphism from `F(K)` to a bounded below complex of
  injective objects to a quasi-isomorphism: `F(K)` computes `RH`.

The last is the dévissage of `Stacks.ExactCompDerived.quasiIso_map_of_isStrictlyGE` with the
exactness of `F ⋙ H` replaced by the injectivity of the terms of `K` (which makes the unit of
`R⁺(F ⋙ H)` invertible at `K`) and by the hypothesis at the cohomology objects.

## Main results

* `Stacks.ExactCompDerived.isIso_rightDerivedFunctorPlusComp_app_single_of_resolution`.
* `Stacks.ExactCompDerived.isIso_rightDerivedFunctorPlusComp_app_single_of_isColimit`.
* `Stacks.ExactCompDerived.quasiIso_map_of_injective_of_isStrictlyGE`.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.ExactCompDerived

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (H : B ⥤ C) [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits H]

attribute [local instance] HasDerivedCategory.standard commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The unit of `R⁺F` is invertible for an exact functor `F`. -/
private theorem isIso_rightDerivedFunctorPlusUnit_app_of_exact {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B] (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : HomotopyCategory.Plus A) : IsIso (F.rightDerivedFunctorPlusUnit.app T) :=
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have := isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  NatIso.isIso_app_of_isIso _ _

/-- A quasi-isomorphism of complexes becomes a quasi-isomorphism in the homotopy category. -/
private theorem quasiIso_quotient_map {D : Type*} [Category* D] [Abelian D]
    {K L : CochainComplex D ℤ} (g : K ⟶ L) [QuasiIso g] :
    HomotopyCategory.quasiIso D (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map g) := by
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  infer_instance

omit [PreservesFiniteLimits H] in
/-- **The composition comparison is invertible at a bounded below complex of objects acyclic for
`F ⋙ H` whose images under `F` are acyclic for `H`.** The units of `R⁺(F ⋙ H)`, `R⁺F` and `R⁺H`
are invertible there (Leray's acyclicity lemma, [Stacks, Tag 015E]). -/
lemma isIso_rightDerivedFunctorPlusComp_app_Qh_of_rightAcyclic (T : HomotopyCategory.Plus A)
    (hT₁ : ∀ n : ℤ, (F ⋙ H).rightAcyclic (T.obj.as.X n))
    (hT₂ : ∀ n : ℤ, H.rightAcyclic (F.obj (T.obj.as.X n))) :
    IsIso ((rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj T)) := by
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnit.app T) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic (F ⋙ H) T hT₁
  have hF := isIso_rightDerivedFunctorPlusUnit_app_of_exact F T
  have hH : IsIso (H.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj T)) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic H _ hT₂
  have : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnit.app T ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj T)) := by
    rw [unit_comp_rightDerivedFunctorPlusComp_app F H T]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH (Functor.map_isIso _ _)
  exact IsIso.of_isIso_comp_left ((F ⋙ H).rightDerivedFunctorPlusUnit.app T) _

/-- **The composition comparison at `M[0]`, from an acyclic resolution of `M`.** If `M` has a
resolution `M[0] ⟶ T` by a bounded below complex whose terms are acyclic for `F ⋙ H` and have
images under `F` acyclic for `H`, then the composition comparison is invertible at `M[0]`. -/
theorem isIso_rightDerivedFunctorPlusComp_app_single_of_resolution (M : A)
    (T : CochainComplex A ℤ) (n : ℤ) [CochainComplex.IsStrictlyGE T n]
    (ι : (CochainComplex.singleFunctor A 0).obj M ⟶ T) [QuasiIso ι]
    (hT₁ : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero (((F ⋙ H).rightDerived p).obj (T.X i)))
    (hT₂ : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero ((H.rightDerived p).obj (F.obj (T.X i)))) :
    IsIso ((rightDerivedFunctorPlusComp F H).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)) := by
  have : PreservesFiniteLimits (F ⋙ H) := comp_preservesFiniteLimits F H
  let Tp : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj T,
      (HomotopyCategory.plus_quotient_obj_iff T).2 ⟨n, inferInstance⟩⟩
  have hT := isIso_rightDerivedFunctorPlusComp_app_Qh_of_rightAcyclic F H Tp
    (fun i => (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
      (hT₁ i))
    (fun i => (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
      (hT₂ i))
  let ιp : (HomotopyCategory.Plus.singleFunctor A 0).obj M ⟶ Tp :=
    ObjectProperty.homMk ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ι)
  have hιp : HomotopyCategory.Plus.quasiIso A ιp := by
    exact quasiIso_quotient_map ι
  have : IsIso (DerivedCategory.Plus.Qh.map ιp) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) ιp hιp
  let e := (DerivedCategory.Plus.singleFunctorIsoCompQh A 0).app M ≪≫
    asIso (DerivedCategory.Plus.Qh.map ιp)
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 hT

omit [PreservesFiniteLimits H] in
/-- **The composition comparison at `M[0]`, for a filtered colimit `M`.** If `M` is the point of a
colimit cocone, the comparison is invertible at the single complex on every object of the
diagram, and the higher derived functors `R^q(F ⋙ H)` and `F ⋙ R^q H` preserve the colimit, then
the comparison is invertible at `M[0]`: on cohomology objects it is a natural transformation
between functors preserving the colimit. -/
theorem isIso_rightDerivedFunctorPlusComp_app_single_of_isColimit {J : Type*} [Category* J]
    {D : J ⥤ A} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsIso ((rightDerivedFunctorPlusComp F H).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj (D.obj j))))
    (h₁ : ∀ q : ℕ, PreservesColimit D ((F ⋙ H).rightDerived q))
    (h₂ : ∀ q : ℕ, PreservesColimit D (F ⋙ H.rightDerived q)) :
    IsIso ((rightDerivedFunctorPlusComp F H).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt)) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  let Φ := DerivedCategory.Plus.singleFunctor A 0 ⋙ (F ⋙ H).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor C n
  let Ψ := DerivedCategory.Plus.singleFunctor A 0 ⋙ (F.rightDerivedFunctorPlus ⋙
    H.rightDerivedFunctorPlus) ⋙ DerivedCategory.Plus.homologyFunctor C n
  let α : Φ ⟶ Ψ := Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
    (Functor.whiskerRight (rightDerivedFunctorPlusComp F H)
      (DerivedCategory.Plus.homologyFunctor C n))
  show IsIso (α.app c.pt)
  rcases lt_or_ge n 0 with hn | hn
  · have hΦ : IsZero (Φ.obj c.pt) := by
      have : ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt).IsGE 0 := inferInstance
      have := isGE_rightDerivedFunctorPlus_obj (F ⋙ H)
        ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt) 0
      exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn
    have hΨ : IsZero (Ψ.obj c.pt) := by
      have : ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt).IsGE 0 := inferInstance
      have := isGE_rightDerivedFunctorPlus_obj F
        ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt) 0
      have : ((F.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt)).IsGE 0 :=
        isGE_rightDerivedFunctorPlus_obj H
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj c.pt)) 0
      exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn
    exact ⟨0, hΦ.eq_of_src _ _, hΨ.eq_of_src _ _⟩
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let eΦ : Φ ≅ (F ⋙ H).rightDerived q :=
      Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard (F ⋙ H) q
    let eΨ : Ψ ≅ F ⋙ H.rightDerived q :=
      Functor.isoWhiskerRight (Stacks.Cohomology.AcyclicCollapse.singleFunctorIso F)
          (H.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ)) ≪≫
        Functor.isoWhiskerLeft F
          (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard H q)
    have := h₁ q
    have := h₂ q
    have : PreservesColimit D Φ := preservesColimit_of_natIso D eΦ.symm
    have : PreservesColimit D Ψ := preservesColimit_of_natIso D eΨ.symm
    exact Stacks.EtaleCohomology.SmoothBaseChange.isIso_app_of_isColimit hc α fun j => by
      show IsIso ((DerivedCategory.Plus.homologyFunctor C (q : ℤ)).map
        ((rightDerivedFunctorPlusComp F H).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj (D.obj j))))
      have := hD j
      infer_instance

omit [PreservesFiniteLimits H] in
/-- **`H` computes `RH` on `F(K)` for a bounded below complex `K` of injective objects at whose
cohomology objects the composition comparison is invertible**: for every quasi-isomorphism
`s : F(K) ⟶ J` to a bounded below complex of injective objects, `H(s)` is a quasi-isomorphism.
The composition comparison `R(H ∘ F) ⟶ RH ∘ RF` is invertible at `K` by dévissage
(`DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE`), the units of `R(H ∘ F)` (the terms
of `K` being injective) and of `RF` (`F` being exact) are invertible at `K`, so the unit of `RH`
is invertible at `F(K)`. This is `Stacks.ExactCompDerived.quasiIso_map_of_isStrictlyGE` with the
exactness of `H ∘ F` replaced by the injectivity of the terms of `K`. -/
theorem quasiIso_map_of_injective_of_isStrictlyGE (K : CochainComplex A ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE K n] [∀ i, Injective (K.X i)]
    (hK : ∀ q : ℤ, IsIso ((rightDerivedFunctorPlusComp F H).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj (K.homology q))))
    {J : CochainComplex B ℤ} (s : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ J)
    [QuasiIso s] (m : ℤ) [CochainComplex.IsStrictlyGE J m] [∀ i, Injective (J.X i)] :
    QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have := isTriangulated_rightDerivedFunctorPlus (F ⋙ H)
  have := isTriangulated_rightDerivedFunctorPlus F
  have := isTriangulated_rightDerivedFunctorPlus H
  have := natTransCommShift_rightDerivedFunctorPlusComp F H
  let Kp : HomotopyCategory.Plus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K,
      (HomotopyCategory.plus_quotient_obj_iff K).2 ⟨n, inferInstance⟩⟩
  let Jp : HomotopyCategory.Plus B :=
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj J,
      (HomotopyCategory.plus_quotient_obj_iff J).2 ⟨m, inferInstance⟩⟩
  let η := rightDerivedFunctorPlusComp F H
  have hGE : (DerivedCategory.Plus.Qh.obj Kp).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    show (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).IsGE n
    have := (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso A).app K).symm n
  have hη : IsIso (η.app (DerivedCategory.Plus.Qh.obj Kp)) := by
    refine DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE η
      (fun L m hL => ?_) (fun L m hL => ?_) _ n hGE (fun q => ?_)
    · exact isGE_rightDerivedFunctorPlus_obj (F ⋙ H) L m
    · have := isGE_rightDerivedFunctorPlus_obj F L m
      exact isGE_rightDerivedFunctorPlus_obj H _ m
    · let e : (DerivedCategory.Plus.homologyFunctor A q).obj (DerivedCategory.Plus.Qh.obj Kp) ≅
          K.homology q :=
        (DerivedCategory.homologyFunctor A q).mapIso
            ((DerivedCategory.quotientCompQhIso A).app K) ≪≫
          (DerivedCategory.homologyFunctorFactors A q).app K
      exact (NatTrans.isIso_app_iff_of_iso η
        ((DerivedCategory.Plus.singleFunctor A 0).mapIso e)).2 (hK q)
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnit.app Kp) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic (F ⋙ H) Kp
      fun i => Functor.rightAcyclic_of_injective (F ⋙ H) (K.X i)
  have hF := isIso_rightDerivedFunctorPlusUnit_app_of_exact F Kp
  have hH : IsIso (H.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj Kp)) := by
    have : IsIso (H.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj Kp) ≫
        H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app Kp)) := by
      rw [← unit_comp_rightDerivedFunctorPlusComp_app F H Kp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hFH hη
    exact IsIso.of_isIso_comp_right _ (H.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusUnit.app Kp))
  let sp : F.mapHomotopyCategoryPlus.obj Kp ⟶ Jp :=
    ObjectProperty.homMk ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)
  have hJ : IsIso (H.rightDerivedFunctorPlusUnit.app Jp) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic H Jp
      fun i => Functor.rightAcyclic_of_injective H (J.X i)
  have hsp : HomotopyCategory.Plus.quasiIso B sp := by
    exact quasiIso_quotient_map s
  have hQs : IsIso (H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map sp)) := by
    have : IsIso (DerivedCategory.Plus.Qh.map sp) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) sp hsp
    infer_instance
  have hn := H.rightDerivedFunctorPlusUnit.naturality sp
  dsimp only [Functor.comp_map] at hn
  have h₁ : IsIso (DerivedCategory.Plus.Qh.map (H.mapHomotopyCategoryPlus.map sp)) := by
    have : IsIso (DerivedCategory.Plus.Qh.map (H.mapHomotopyCategoryPlus.map sp) ≫
        H.rightDerivedFunctorPlusUnit.app Jp) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (H.rightDerivedFunctorPlusUnit.app Jp)
  have h₂ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s))) :=
    (DerivedCategory.Plus.ι (C := C)).map_isIso (DerivedCategory.Plus.Qh.map
      (H.mapHomotopyCategoryPlus.map sp))
  rwa [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff] at h₂

end Stacks.ExactCompDerived

end
