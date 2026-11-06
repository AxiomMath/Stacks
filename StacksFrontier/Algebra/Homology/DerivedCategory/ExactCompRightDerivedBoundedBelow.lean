module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTransformationDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H` computes `RH` on `F(K)` for `K` bounded below, when `H ∘ F` is exact

Let `F : A ⥤ B` and `G : A ⥤ C` be exact functors between abelian categories with enough
injectives, `H : B ⥤ C` an additive functor and `Θ : G ≅ F ⋙ H`. Let `K` be a bounded below
complex of objects of `A` each of whose cohomology objects `M` has `F(M)` acyclic for `H`. Then
`F(K)` computes the right derived functor of `H`: for every quasi-isomorphism `s : F(K) ⟶ J` to a
bounded below complex of injective objects, `H(s)` is a quasi-isomorphism.

This is the dévissage of case (a) of [Stacks, Tag 0F7G], where `F = f_!`, `G = g_!` and
`H = h_*`. The composition comparison `R(H ∘ F) ⟶ RH ∘ RF` on `D⁺(A)` is shift-compatible and
triangulated, and it is invertible on a single object `M[0]` exactly when `F(M)` is `H`-acyclic,
`F` and `H ∘ F ≅ G` being exact; so it is invertible at `K` by dévissage along the canonical
truncations. Since the units of `RF` and of `R(H ∘ F)` are invertible, so is the unit of `RH` at
`F(K)`.

## Main results

* `Stacks.ExactCompDerived.isIso_rightDerivedFunctorPlusComp_app_single`: the composition
  comparison is invertible at `M[0]` when `F(M)` is `H`-acyclic.
* `Stacks.ExactCompDerived.quasiIso_map_of_isStrictlyGE`: `H(s)` is a quasi-isomorphism.
* `Stacks.ExactCompDerived.exists_quasiIso_isKInjective_quasiIso_map_of_isStrictlyGE`: such an `s`
  exists, with `J` K-injective.
* `Stacks.ExactCompDerived.quasiIso_map_of_rightAcyclic_of_bounded`: for `H` of finite
  cohomological dimension, a complex of `H`-acyclic objects computes `RH` on the unbounded derived
  category ([Stacks, Tag 07K7]).

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.ExactCompDerived

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : A ⥤ C) (H : B ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits H]
  (Θ : G ≅ F ⋙ H)

section Plus

attribute [local instance] HasDerivedCategory.standard commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- A morphism whose image under a natural transformation's target is invertible is sent to an
isomorphism by the source, when the components of the transformation are invertible. -/
private theorem isIso_map_of_isIso_app {D E : Type*} [Category* D] [Category* E] {Φ Ψ : D ⥤ E}
    (α : Φ ⟶ Ψ) {X Y : D} (f : X ⟶ Y) [IsIso (α.app X)] [IsIso (α.app Y)]
    [IsIso (Ψ.map f)] : IsIso (Φ.map f) :=
  IsIso.of_isIso_fac_right (α.naturality f)

/-- An object is right acyclic for `G` exactly when the unit of `RG` (Mathlib's
`rightDerivedFunctorPlusUnith`, whose definition is not exposed) is invertible at the single
complex on it in degree zero: both are units of right derived functors of the same functor. -/
private lemma rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app {D E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [EnoughInjectives D] (G : D ⥤ E)
    [G.Additive] (X : D) :
    G.rightAcyclic X ↔ IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj X)) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  change IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app _) ↔ _
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))]
  exact isIso_comp_right_iff _ _

omit [EnoughInjectives B] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] in
include Θ in
/-- The unit of `R(H ∘ F)` is invertible, `H ∘ F ≅ G` being exact. -/
lemma isIso_rightDerivedFunctorPlusUnit_comp :
    IsIso (F ⋙ H).rightDerivedFunctorPlusUnith := by
  have : PreservesFiniteLimits (F ⋙ H) := preservesFiniteLimits_of_natIso Θ
  have : PreservesFiniteColimits (F ⋙ H) := preservesFiniteColimits_of_natIso Θ
  have : (F ⋙ H).PreservesHomology := Functor.preservesHomologyOfExact _
  exact isIso_rightDerivedFunctorPlusUnit_of_preservesHomology (F ⋙ H)

omit [G.Additive] in
include Θ in
/-- **The composition comparison is invertible at a single object `M[0]` whose image `F(M)` is
`H`-acyclic.** -/
lemma isIso_rightDerivedFunctorPlusComp_app_single (M : A)
    (hM : ∀ p : ℕ, 0 < p → IsZero ((H.rightDerived p).obj (F.obj M))) :
    IsIso ((rightDerivedFunctorPlusComp F H).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)) := by
  let Xs := (HomotopyCategory.Plus.singleFunctor A 0).obj M
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app Xs) :=
    (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app F M).1 (rightAcyclic_of_exact F M)
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) :=
    have := isIso_rightDerivedFunctorPlusUnit_comp F G H Θ
    NatIso.isIso_app_of_isIso _ _
  have hH : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Xs)) := by
    let e := Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso F 0 M
    have : IsIso (H.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj (F.obj M))) :=
      (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app H (F.obj M)).1
        ((Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived H (F.obj M)).2 hM)
    exact IsIso.of_isIso_fac_right (H.rightDerivedFunctorPlusUnith.naturality e.hom).symm
  have key : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) := by
    rw [unit_comp_rightDerivedFunctorPlusComp_app F H Xs]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH (Functor.map_isIso _ _)
  have ht : IsIso ((rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) _ hFH key
  let e := (DerivedCategory.Plus.singleFunctorIsoCompQh A 0).app M
  have ht' : IsIso ((rightDerivedFunctorPlusComp F H).app
      ((HomotopyCategory.Plus.singleFunctor _ 0 ⋙ DerivedCategory.Plus.Qh).obj M)) := ht
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 ht'

omit [G.Additive] in
include Θ in
/-- **`H` computes `RH` on `F(K)` for `K` bounded below whose cohomology objects `M` have `F(M)`
acyclic for `H`**: for every quasi-isomorphism `s : F(K) ⟶ J` to a bounded below complex of
injective objects, `H(s)` is a quasi-isomorphism. The composition comparison
`R(H ∘ F) ⟶ RH ∘ RF` is invertible at `K` by dévissage
(`DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE` and
`isIso_rightDerivedFunctorPlusComp_app_single`), so the unit of `RH` is invertible at `F(K)`. -/
theorem quasiIso_map_of_isStrictlyGE (K : CochainComplex A ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE K n]
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p → IsZero ((H.rightDerived p).obj (F.obj (K.homology q))))
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
      have hM := isIso_rightDerivedFunctorPlusComp_app_single F G H Θ (K.homology q) (hK q)
      exact (NatTrans.isIso_app_iff_of_iso η
        ((DerivedCategory.Plus.singleFunctor A 0).mapIso e)).2 hM
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Kp) :=
    have := isIso_rightDerivedFunctorPlusUnit_comp F G H Θ
    NatIso.isIso_app_of_isIso _ _
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app Kp) :=
    have : F.PreservesHomology := Functor.preservesHomologyOfExact F
    have := isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
    NatIso.isIso_app_of_isIso _ _
  have hH : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Kp)) := by
    have : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Kp) ≫
        H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app Kp)) := by
      rw [← unit_comp_rightDerivedFunctorPlusComp_app F H Kp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hFH hη
    exact IsIso.of_isIso_comp_right _ (H.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusUnith.app Kp))
  let sp : F.mapHomotopyCategoryPlus.obj Kp ⟶ Jp :=
    ObjectProperty.homMk ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)
  have hJ : IsIso (H.rightDerivedFunctorPlusUnith.app Jp) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic H Jp
      (fun i => by
        show H.rightAcyclic (J.X i)
        exact Functor.rightAcyclic_of_injective _ _)
  have hsp : HomotopyCategory.Plus.quasiIso B sp := by
    show HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hQs : IsIso ((DerivedCategory.Plus.Qh ⋙ H.rightDerivedFunctorPlus).map sp) := by
    have : IsIso (DerivedCategory.Plus.Qh.map sp) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) sp hsp
    exact Functor.map_isIso H.rightDerivedFunctorPlus (DerivedCategory.Plus.Qh.map sp)
  have h₁ : IsIso (DerivedCategory.Plus.Qh.map (H.mapHomotopyCategoryPlus.map sp)) :=
    isIso_map_of_isIso_app H.rightDerivedFunctorPlusUnith sp
  have h₂ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s))) :=
    (DerivedCategory.Plus.ι (C := C)).map_isIso (DerivedCategory.Plus.Qh.map
      (H.mapHomotopyCategoryPlus.map sp))
  rwa [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff] at h₂

omit [G.Additive] in
include Θ in
/-- **A K-injective resolution of `F(K)` which `H` carries to a quasi-isomorphism**, for `K`
bounded below whose cohomology objects `M` have `F(M)` acyclic for `H`: a resolution by a bounded
below complex of injective objects (`quasiIso_map_of_isStrictlyGE`). -/
theorem exists_quasiIso_isKInjective_quasiIso_map_of_isStrictlyGE (K : CochainComplex A ℤ)
    (n : ℤ) [CochainComplex.IsStrictlyGE K n]
    (hK : ∀ (q : ℤ) (p : ℕ), 0 < p → IsZero ((H.rightDerived p).obj (F.obj (K.homology q)))) :
    ∃ (J : CochainComplex B ℤ) (s : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ J),
      QuasiIso s ∧ J.IsKInjective ∧
        QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  obtain ⟨J, s, hs, hJ, hJn⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
  exact ⟨J, s, hs, CochainComplex.isKInjective_of_injective J n,
    quasiIso_map_of_isStrictlyGE F G H Θ K n hK s n⟩

universe w in
/-- **[Stacks, Tag 07K7] for a K-injective resolution.** Let `H : B ⥤ C` be left exact of finite
cohomological dimension `d` on a Grothendieck abelian category `B`, and let `L` be a complex of
`H`-acyclic objects. Then `H` carries every quasi-isomorphism `s : L ⟶ J` to a K-injective
complex to a quasi-isomorphism: both `L` and `J` compute any right derived functor of `H` on the
unbounded derived category. -/
@[ega "0 11.5.4" "special case", sga "4½ Etat_0 4.2.3.2" "(1)"]
theorem quasiIso_map_of_rightAcyclic_of_bounded [IsGrothendieckAbelian.{w} B] (d : ℕ)
    (hd : ∀ (M : B) (p : ℕ), d < p → IsZero ((H.rightDerived p).obj M))
    {L J : CochainComplex B ℤ}
    (hL : ∀ (i : ℤ) (p : ℕ), 0 < p → IsZero ((H.rightDerived p).obj (L.X i)))
    (s : L ⟶ J) [QuasiIso s] (hJ : J.IsKInjective) :
    QuasiIso ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have hcomp : ∀ Z : B, H.rightAcyclic Z →
      (H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso B) ((HomotopyCategory.Plus.singleFunctor B 0).obj Z) := by
    intro Z hZ
    have : (HomotopyCategory.Plus.quasiIso B).HasLeftCalculusOfFractions := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
      infer_instance
    rw [Functor.computesRightDerived_iff_isIso_app _ DerivedCategory.Plus.Qh
      H.rightDerivedFunctorPlus (HomotopyCategory.Plus.quasiIso _) H.rightDerivedFunctorPlusUnith _
      (fun K => ?_)]
    · exact (rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnith_app H Z).1 hZ
    · let r : (HomotopyCategory.Plus.localizerMorphism _).RightResolution K :=
        Classical.arbitrary _
      exact ⟨_, r.w, r.hw, inferInstance⟩
  obtain ⟨hRF, -, h3⟩ := Functor.hasRightDerivedFunctor_of_isZero_rightDerived H
    H.rightDerivedFunctorPlus H.rightDerivedFunctorPlusUnith
    (fun Z => (H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso _) ((HomotopyCategory.Plus.singleFunctor _ 0).obj Z))
    (fun _ => Iff.rfl)
    (fun Z => ⟨Injective.under Z, Injective.ι Z, inferInstance,
      hcomp _ (Functor.rightAcyclic_of_injective _ _)⟩)
    (d + 1) (fun Z => by
      have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single H Z
        d 0 (fun p hp => hd Z p (by exact_mod_cast hp))
      exact DerivedCategory.isZero_of_isLE _ (0 + d) _ (by push_cast; omega))
  let RF := (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
  let α := (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
  obtain ⟨hα, -⟩ := h3 RF α
  have hαL := hα L fun i => hcomp _
    ((Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived H _).2 (hL i))
  have hαJ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective.{w}
    (H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh RF α J hJ
  have hQs : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have : IsIso ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)) :=
    Functor.map_isIso RF _
  have h₁ : IsIso (DerivedCategory.Qh.map ((H.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s))) :=
    isIso_map_of_isIso_app α ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s)
  have : (H.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map s) =
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := rfl
  rw [this] at h₁
  exact (HomologicalComplex.mem_quasiIso_iff _).1
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
      ((DerivedCategory.isIso_Qh_map_iff _).1 h₁))

end Plus

end Stacks.ExactCompDerived

end
