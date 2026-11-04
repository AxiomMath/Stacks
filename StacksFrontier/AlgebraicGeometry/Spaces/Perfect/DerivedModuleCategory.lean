module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULiftSelfIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CompactHomVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedEquivalence
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# `D_QCoh` of a quasi-compact quasi-separated algebraic space as a module category

Let `X` be a quasi-compact and quasi-separated algebraic space. There is a differential graded
algebra `(E, d)` with only finitely many nonzero cohomology groups such that `D_QCoh(𝒪_X)` is
equivalent to `D(E, d)`. This is Stacks 09MC.

The equivalence is constructed on the equi-universe model `Y` of the small étale ringed site of
`X`, through the equivalence `D(𝒪_X) ≌ D(𝒪_Y)` of
`AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`: on `Y` the endomorphism differential
graded algebra of a complex has its carrier in the universe of the sections, so that `D(E, d)` is
a category of the right size. The image `𝒬` of `D_QCoh(𝒪_X)` in `D(𝒪_Y)` is a triangulated
subcategory closed under direct sums; a K-injective complex `K` representing the image of a
perfect generator `P` of `D_QCoh(𝒪_X)` (Stacks 09IY) is compact relative to `𝒬` (Stacks 09M8) and
generates `𝒬`, so `- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒬` is an equivalence for `E = Hom^•(K, K)`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalence`). Since `K` is K-injective,
`H^i(E) = Hom(K, K[i]) = Hom(P, P[i])` (09MD), which vanishes for `i` large because `P` is bounded
above and compact (half of Stacks 09MB), and for `i` small by the t-structure, `P` being bounded.

## Main results

* `AlgebraicGeometry.Space.exists_differentialGradedAlgebra_equivalence`: **Stacks 09MC**.

## References

* [Stacks Project, Tag 09MC](https://stacks.math.columbia.edu/tag/09MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The equi-universe model of the small étale ringed site of `X`. -/
abbrev modelSite (X : AlgebraicSpaces B S hS) : RingedSite.{u, u, u} :=
  smallEtaleModelRingedSite B S hS X.1 X.2

/-- The inverse of the equivalence of module categories with the model is additive. -/
instance (X : AlgebraicSpaces B S hS) :
    (smallEtaleModelModulesEquivalence B S hS X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The equivalence `D(𝒪_X) ≌ D(𝒪_Y)` with the model, with its source written as the derived
category of `𝒪_X`-modules in which `D_QCoh(𝒪_X)` is stated. -/
def modelEquivalence (X : AlgebraicSpaces B S hS) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ≌
      DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)) :=
  smallEtaleModelDerivedEquivalence B S hS X

/-- The inverse of `modelEquivalence X` commutes with the shifts. -/
instance (X : AlgebraicSpaces B S hS) : (modelEquivalence X).inverse.CommShift ℤ :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory.CommShift ℤ)

/-- The inverse of `modelEquivalence X` is a triangulated functor. -/
instance (X : AlgebraicSpaces B S hS) : (modelEquivalence X).inverse.IsTriangulated :=
  (inferInstance :
    (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory.IsTriangulated)

/-- The image of `D_QCoh(𝒪_X)` in `D(𝒪_Y)`: the objects whose image in `D(𝒪_X)` has
quasi-coherent cohomology sheaves. -/
abbrev modelQcohDerived (X : AlgebraicSpaces B S hS) :
    ObjectProperty (DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))) :=
  (QcohDerived B S hS X).inverseImage (modelEquivalence X).inverse

section

variable (X : AlgebraicSpaces B S hS)

/-- The image of `D_QCoh(𝒪_X)` in `D(𝒪_Y)` is a triangulated subcategory. -/
instance : (modelQcohDerived X).IsTriangulated := by
  have : (QcohDerived B S hS X).IsTriangulated :=
    isTriangulated_quasicoherentDerivedCategory B S hS X.1 X.2
  exact inferInstanceAs
    (((QcohDerived B S hS X).inverseImage (modelEquivalence X).inverse).IsTriangulated)

/-- The image of `D_QCoh(𝒪_X)` in `D(𝒪_Y)` is closed under isomorphisms. -/
instance : (modelQcohDerived X).IsClosedUnderIsomorphisms :=
  ⟨fun e h => (QcohDerived B S hS X).prop_of_iso ((modelEquivalence X).inverse.mapIso e) h⟩

/-- `D_QCoh(𝒪_X)`, read in the model, is closed under direct sums. -/
theorem modelQcohDerived_prop_of_isColimit {ι : Type u}
    (Z : ι → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)))
    (c : Cofan Z)
    (hc : IsColimit c) (hZ : ∀ i, modelQcohDerived X (Z i)) : modelQcohDerived X c.pt := by
  have := isClosedUnderColimitsOfShape_qcohDerived B S hS X ι
  exact (QcohDerived B S hS X).prop_of_isColimit
    (isColimitOfPreserves (modelEquivalence X).inverse hc) (fun j => hZ j.as)

/-- `D_QCoh(𝒪_X)` is equivalent to its image in `D(𝒪_Y)`. -/
def quasicoherentDerivedCategoryEquivModel :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ≌ (modelQcohDerived X).FullSubcategory := by
  let e := modelEquivalence X
  have hF : ∀ M : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      modelQcohDerived X (((QcohDerived B S hS X).ι ⋙ e.functor).obj M) :=
    fun M => (QcohDerived B S hS X).prop_of_iso (e.unitIso.app M.obj) M.property
  haveI : ((QcohDerived B S hS X).ι ⋙ e.functor).Faithful := inferInstance
  haveI : ((QcohDerived B S hS X).ι ⋙ e.functor).Full := inferInstance
  haveI : ((modelQcohDerived X).lift ((QcohDerived B S hS X).ι ⋙ e.functor) hF).EssSurj :=
    ⟨fun L => ⟨⟨e.inverse.obj L.obj, L.property⟩,
      ⟨ObjectProperty.isoMk _ (e.counitIso.app L.obj)⟩⟩⟩
  haveI : ((modelQcohDerived X).lift ((QcohDerived B S hS X).ι ⋙ e.functor) hF).IsEquivalence :=
    { }
  exact ((modelQcohDerived X).lift ((QcohDerived B S hS X).ι ⋙ e.functor) hF).asEquivalence

/-- On the equi-universe model, lifting a complex of modules to the ambient universe of the
tensor construction changes it only up to isomorphism. -/
def modelLiftComplexIso (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ) :
    RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K ≅ K :=
  (NatIso.mapHomologicalComplex (NatIso.ofComponents
      (Stacks.SheafOfModules.moduleULiftSelfIso
        (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))
      (fun f => (SheafOfModules.fullyFaithfulForget _).map_injective (by
        ext U x; rfl))) (ComplexShape.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

/-- **A K-injective perfect generator on the model.** There is a complex `K` on the
equi-universe model whose lift is K-injective and which represents the image of a perfect object
`P` generating `D_QCoh(𝒪_X)` (Stacks 09IY). -/
theorem exists_kInjective_perfect_generator (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ,
      (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K).IsKInjective ∧
      ∃ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧
        (∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
          IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj)) ∧
        Nonempty ((modelEquivalence X).inverse.obj
          (DerivedCategory.Q.obj
            (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) ≅ P) := by
  obtain ⟨P, hP, hgen⟩ := exists_isPerfect_generator X hqc hqs
  let : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, u, u, u} (modelSite X).J
      (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)
  let P' := (modelEquivalence X).functor.obj P
  let M := DerivedCategory.Q.objPreimage P'
  let K := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))).obj M
  have hK : K.IsKInjective := inferInstance
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O))).app M
  have hι : IsIso (DerivedCategory.Q.map ι) := inferInstance
  refine ⟨K, CochainComplex.isKInjective_of_iso (modelLiftComplexIso X K).symm, P, hP, hgen,
    ⟨(modelEquivalence X).inverse.mapIso
      (DerivedCategory.Q.mapIso (modelLiftComplexIso X K) ≪≫
        (asIso (DerivedCategory.Q.map ι)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso P') ≪≫
      ((modelEquivalence X).unitIso.app P).symm⟩⟩

/-- **Morphisms from a perfect object to its far shifts vanish**: for a perfect object `P` of
`D_QCoh(𝒪_X)`, `Hom(P, P[i]) = 0` for `i ≪ 0` and for `i ≫ 0` (the latter is half of
Stacks 09MB). -/
theorem exists_hom_shift_eq_zero_of_isPerfect (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P) :
    ∃ lo hi : ℤ, ∀ i : ℤ, (i < lo ∨ hi < i) → ∀ f : P ⟶ P⟦i⟧, f = 0 := by
  have hPq : QcohDerived B S hS X P := qcohDerived_of_isPerfect_derivedCategoryB X P hP
  obtain ⟨a, b, ha, hb⟩ := exists_isGE_isLE_of_isPerfect hqc P hP
  obtain ⟨N, hN⟩ := exists_hom_eq_zero_of_isCompactObject X hqc hqs ⟨P, hPq⟩
    (isCompactObject_of_isPerfect X hqc hqs ⟨P, hPq⟩ hP)
  refine ⟨a - b, N + b, fun i hi f => ?_⟩
  rcases hi with hi | hi
  · have hge : (P⟦i⟧).IsGE (a - i) :=
      DerivedCategory.TStructure.t.isGE_shift P a i (a - i) (by omega)
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f b (a - i) (by omega) hb hge
  · have hle : (P⟦i⟧).IsLE (b - i) :=
      DerivedCategory.TStructure.t.isLE_shift P b i (b - i) (by omega)
    have hle' : (P⟦i⟧).IsLE (-N) :=
      DerivedCategory.TStructure.t.isLE_of_le (P⟦i⟧) (b - i) (-N) (by omega)
    exact hN (P⟦i⟧) (qcohDerived_shift P i hPq) hle' f


/-- A functor commuting with shifts sends the shift of `A` to the shift of any `P` that `A` is
sent to. -/
private def shiftObjIsoOfCommShift {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] {A : C} {P : D} (eP : F.obj A ≅ P) (n : ℤ) :
    F.obj (A⟦n⟧) ≅ P⟦n⟧ :=
  (F.commShiftIso n).app A ≪≫ (shiftFunctor D n).mapIso eP

variable {X} in
/-- The image in the model of a perfect object, and its shifts, are compact relative to the image
of `D_QCoh(𝒪_X)` (Stacks 09M8). -/
theorem isRelativelyCompactShifts_model (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (eP : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) ≅ P) :
    RingedSite.IsRelativelyCompactShifts.{u, u, u, u, u} (modelSite X) K (modelQcohDerived X) := by
  let e := modelEquivalence X
  intro A' hA' ι _ Z hZ T j hj
  obtain ⟨A₀, n, e', hA₀⟩ := hA'
  rw [ObjectProperty.singleton_iff] at hA₀
  subst hA₀
  have hperf : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (e.inverse.obj A') := by
    obtain ⟨E, hE, ⟨i⟩⟩ := RingedSite.isPerfect_shift_general _ hP n
    exact ⟨E, hE, ⟨i ≪≫ (e.inverse.mapIso e' ≪≫ shiftObjIsoOfCommShift e.inverse eP n).symm⟩⟩
  have hc := isQcohCompact_of_isPerfect X hqc hqs (e.inverse.obj A') hperf
    (fun i => e.inverse.obj (Z i)) hZ (fun i => e.inverse.map (j i))
    ((isColimitMapCoconeCofanMkEquiv e.inverse Z j) (isColimitOfPreserves e.inverse hj))
  exact (bijective_cofanMap_map_iff_of_fullyFaithful e.inverse A' j).1 hc

variable {X} in
/-- The image in the model of a generator of `D_QCoh(𝒪_X)` generates the image of
`D_QCoh(𝒪_X)`. -/
theorem isZero_of_modelQcohDerived
    (K : CochainComplex (RingedSite.ModO.{u, u, u, u} (modelSite X)) ℤ)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P⟦n⟧ ⟶ E.obj))
    (eP : (modelEquivalence X).inverse.obj
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) ≅ P)
    (L : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite X).O)))
    (hL : modelQcohDerived X L)
    (h : ∀ (n : ℤ) (f : (DerivedCategory.Q.obj
      (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K))⟦n⟧ ⟶ L), f = 0) : IsZero L := by
  let e := modelEquivalence X
  have hz : IsZero (e.inverse.obj L) := (hgen ⟨e.inverse.obj L, hL⟩).2 fun n =>
    ⟨fun g₁ g₂ => by
      let eS := shiftObjIsoOfCommShift e.inverse eP n
      have hg : ∀ g : P⟦n⟧ ⟶ e.inverse.obj L, g = 0 := fun g => by
        have h0 := h n (e.inverse.preimage (eS.hom ≫ g))
        rw [← cancel_epi eS.hom, comp_zero, ← e.inverse.map_preimage (eS.hom ≫ g), h0,
          Functor.map_zero]
      rw [hg g₁, hg g₂]⟩
  exact (e.functor.map_isZero hz).of_iso (e.counitIso.app L).symm

/-- **Stacks 09MC.** *Let `X` be a quasi-compact and quasi-separated algebraic space over `S`.
Then there exists a differential graded algebra `(E, d)` with only a finite number of nonzero
cohomology groups `H^i(E)` such that `D_QCoh(𝒪_X)` is equivalent to `D(E, d)`.* -/
@[stacks 09MC]
theorem exists_differentialGradedAlgebra_equivalence (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ E : DifferentialGradedAlgebra.{0, u} ℤ, {i : ℤ | Nontrivial (E.Cohomology i)}.Finite ∧
      Nonempty (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ≌
        DifferentialGradedModule.derivedCategory.{0, u, u} E) := by
  obtain ⟨K, hKinj, P, hP, hgen, ⟨eP⟩⟩ := exists_kInjective_perfect_generator X hqc hqs
  have hK : modelQcohDerived X
      (DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)) :=
    (QcohDerived B S hS X).prop_of_iso eP.symm (qcohDerived_of_isPerfect_derivedCategoryB X P hP)
  refine ⟨(RingedSite.Rep.{u, u, u, u, u, 0} (modelSite X) ℤ K).algebra, ?_,
    ⟨(quasicoherentDerivedCategoryEquivModel X).trans
      (RingedSite.tensorWithComplexDerivedEquivalence.{u, u, u, u, u} (modelSite X) K
        (modelQcohDerived X) (fun Z c hc hZ => modelQcohDerived_prop_of_isColimit X Z c hc hZ) hK
        (isRelativelyCompactShifts_model hqc hqs K P hP eP)
        (isZero_of_modelQcohDerived K P hgen eP)).symm⟩⟩
  obtain ⟨lo, hi, hvan⟩ := exists_hom_shift_eq_zero_of_isPerfect X hqc hqs P hP
  refine (Set.finite_Icc lo hi).subset fun i (hne : Nontrivial _) => ?_
  by_contra hout
  have hi' : i < lo ∨ hi < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hout
  let e := modelEquivalence X
  let A := DerivedCategory.Q.obj (RingedSite.liftComplex.{u, u, u, u, u} (modelSite X) K)
  have h0 : ∀ f : A ⟶ A⟦i⟧, f = 0 := fun f => by
    apply e.inverse.map_injective
    rw [Functor.map_zero, ← cancel_epi eP.inv, comp_zero,
      ← cancel_mono (shiftObjIsoOfCommShift e.inverse eP i).hom, zero_comp]
    exact hvan i hi' _
  exact not_subsingleton _ ((RingedSite.repCohomologyEquivDerivedHom.{u, u, u, u, u} (modelSite X)
    K i).subsingleton_congr.2 ⟨fun f₁ f₂ => by rw [h0 f₁, h0 f₂]⟩)

end

end AlgebraicGeometry.Space

end
