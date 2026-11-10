module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.AdjunctionBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.RightAdjointBoundedCohomologicalDimension

/-!
# The unbounded equivalence for an abstract adjunction of derived categories

For an adjunction `L ⊣ R` between derived categories of modules on sites in the Olsson--Laszlo
situation, with `L` identified with the functor induced by an exact functor which restricts to an
equivalence between weak Serre subcategories compatibly with the unit, the adjunction restricts
to an equivalence `D_{𝒜'} ≌ D_𝒜` of unbounded subcategories, as in Stacks 0D7V.

## References

* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

/- `isIso_homologyMap_truncGEπ_app` stood here: the same statement, with the same proof, as
`DerivedCategory.isIso_homologyMap_truncGEπ_app` in
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean:98`, which this module
imports. Uses here and in `UnboundedEquivalenceRelativeSituation` name that one. -/

/-! ### The argument for an abstract adjunction

As for Tag 0D7U, the argument only uses an adjunction `L ⊣ R` of derived categories of modules
whose left adjoint is identified with the functor induced by an exact functor `F`; here the two
sites carry the Olsson--Laszlo hypothesis, through which Tag 0D6U enters. The statements are
read off below for a morphism presented by sites, and in `UnboundedEquivalenceOfToposHom.lean`
for an arbitrary morphism of ringed topoi. -/

section Core

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} O)]
  {C' : Type w} [Category.{w} C'] {J' : GrothendieckTopology C'} {O' : Sheaf J' RingCat.{w}}
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} O')]
  (F : SheafOfModules.{w} O' ⥤ SheafOfModules.{w} O) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]
  {L : DerivedCategory (SheafOfModules.{w} O') ⥤ DerivedCategory (SheafOfModules.{w} O)}
  {R : DerivedCategory (SheafOfModules.{w} O) ⥤ DerivedCategory (SheafOfModules.{w} O')}
  (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated] (eL : L ≅ F.mapDerivedCategory)
  (A : ObjectProperty (SheafOfModules.{w} O)) (A' : ObjectProperty (SheafOfModules.{w} O'))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  (hA : ∀ M, A' M → A (F.obj M))

include hA eL in
omit [L.CommShift ℤ] [L.IsTriangulated] [EnoughInjectives (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O')] [A'.IsWeakSerreClass] in
/-- `L` carries `D_{𝒜'}` into `D_𝒜`: its cohomology objects are `F` of those of the source. -/
theorem derivedCategoryB_obj_of_iso_adjunctionUnboundedEquivalence
    (K : DerivedCategory (SheafOfModules.{w} O'))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    DerivedCategoryB.derivedCategoryB A (L.obj K) :=
  fun q ↦ A.prop_of_iso (homologyObjIsoOfIsoAdjunctionBoundedBelowDescent F eL K q).symm
    (hA _ (hK q))

variable (hEquiv : (A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso (adj.unit.app
    ((DerivedCategory.singleFunctor (SheafOfModules.{w} O') 0).obj M)))

include hA hEquiv hUnit eL in
omit [L.CommShift ℤ] [L.IsTriangulated] [EnoughInjectives (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O')] [A.IsWeakSerreClass] [A'.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the object `R ℱ` lives in degrees `≤ 0`**: it is the object `ℱ'` of `𝒜'`
with `F ℱ' ≅ ℱ`, placed in degree zero. -/
theorem isLE_rightAdjoint_singleFunctor_obj_of_iso_adjunctionUnboundedEquivalence
    (M : SheafOfModules.{w} O) (hM : A M) :
    (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj M)).IsLE 0 := by
  have := hEquiv
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)) ⟨M, hM⟩
  have hN := hUnit N.obj N.property
  have eL' := singleFunctorObjIsoOfIsoAdjunctionBoundedBelowDescent F eL N.obj ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).mapIso (A.ι.mapIso e)
  have eR : (DerivedCategory.singleFunctor (SheafOfModules.{w} O') 0).obj N.obj ≅
      R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj M) :=
    (@asIso _ _ _ _ _ hN).trans (R.mapIso eL')
  exact DerivedCategory.TStructure.t.isLE_of_iso eR 0

variable (B : Set C)
  (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : C, B V → ℤ)
  (coverings : ∀ V : C, B V → Stacks.Cohomology.CofinalCoveringSystem J V)
  (vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} O, A F →
        IsZero (Stacks.Cohomology.moduleCohomology O (𝒰.X i) p F))
  (B' : Set C')
  (basisCover' : ∀ U : C', ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ J' U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : C', B' V → ℤ)
  (coverings' : ∀ V : C', B' V → Stacks.Cohomology.CofinalCoveringSystem J' V)
  (vanishing' : ∀ (V : C') (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} O', A' F →
        IsZero (Stacks.Cohomology.moduleCohomology O' (𝒰.X i) p F))

include hA hEquiv hUnit eL basisCover vanishing basisCover' vanishing' in
/-- `R` carries `D_𝒜` into `D_{𝒜'}`. This is Tag 0D6U, part (a), with `N = 0`, for the exact right
adjoint `R`. -/
theorem derivedCategoryB_rightAdjoint_obj_of_iso_adjunctionUnboundedEquivalence :
    ∀ K : DerivedCategory (SheafOfModules.{w} O), DerivedCategoryB.derivedCategoryB A K →
      DerivedCategoryB.derivedCategoryB A' (R.obj K) := by
  intro K hK
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  let : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  have := adj.isRightAdjoint
  open Stacks.Cohomology.OlssonLaszlo in
  exact derivedCategoryB_map_obj_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension A A'
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing' R
    (DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom adj
      (isLE_obj_of_iso_adjunctionBoundedBelowDescent F eL)) 0
    (fun p M hM ↦
      (derivedCategoryBPlus_obj_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence F adj eL
        A A' hA hEquiv hUnit M hM).2 p)
    (fun p hp M hM ↦
      have := isLE_rightAdjoint_singleFunctor_obj_of_iso_adjunctionUnboundedEquivalence F adj eL
        A A' hA hEquiv hUnit M hM
      DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)
    K hK

include hA hEquiv hUnit eL basisCover vanishing basisCover' vanishing' in
/-- **The counit `L R K ⟶ K` is invertible for every `K` of `D_𝒜`**, granted that it is on
`D⁺_𝒜`: truncate, and compare through Tag 0D6U, part (b). -/
theorem isIso_counit_app_of_derivedCategoryB_of_iso_adjunctionUnboundedEquivalence
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤ adj.counitIsIso)
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    IsIso (adj.counit.app K) := by
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  let : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  have := adj.isRightAdjoint
  rw [DerivedCategory.isIso_iff]
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(n : ℤ)) j hn K
  have hε : IsIso (adj.counit.app ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) :=
    hCounitPlus _ (Stacks.Cohomology.OlssonLaszlo.truncGETower_obj_mem_plus A K hK n)
  have hRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) :=
    open Stacks.Cohomology.OlssonLaszlo in
    isIso_homology_map_truncGEπ_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension A A'
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' R
      (DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom adj
        (isLE_obj_of_iso_adjunctionBoundedBelowDescent F eL)) 0
      (fun p M hM ↦
        (derivedCategoryBPlus_obj_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence F adj
          eL A A' hA hEquiv hUnit M hM).2 p)
      (fun p hp M hM ↦
        have := isLE_rightAdjoint_singleFunctor_obj_of_iso_adjunctionUnboundedEquivalence F adj eL
          A A' hA hEquiv hUnit M hM
        DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)
      K hK n j (by omega)
  have hLRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O) j).map
      (L.map (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) :=
    (NatIso.isIso_map_iff (compHomologyFunctorIsoOfIsoAdjunctionBoundedBelowDescent F eL j)
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))).2
      (inferInstanceAs (IsIso (F.map
        ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
          (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))))))
  have : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O) j).map
      (adj.counit.app K) ≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{w} O) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) := by
    rw [← Functor.map_comp, show adj.counit.app K ≫
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K =
        L.map (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) ≫
          adj.counit.app _ from (adj.counit.naturality _).symm, Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))

include hA hEquiv in
omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [L.CommShift ℤ]
  [L.IsTriangulated] [EnoughInjectives (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O')] [A.IsWeakSerreClass] [A'.IsWeakSerreClass] in
/-- **`F` reflects isomorphisms between objects of `𝒜'`**, because it induces an equivalence
`𝒜' ⟶ 𝒜`. -/
theorem isIso_of_isIso_map_of_isEquivalence_adjunctionUnboundedEquivalence
    {M N : SheafOfModules.{w} O'} (g : M ⟶ N) (hM : A' M) (hN : A' N)
    [IsIso (F.map g)] : IsIso g := by
  have := hEquiv
  let G := A.lift (A'.ι ⋙ F) (fun N ↦ hA N.obj N.property)
  let g' : (⟨M, hM⟩ : A'.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk g
  have h₂ : IsIso (G.map g') :=
    (ObjectProperty.isIso_hom_iff (G.map g')).1 (inferInstanceAs (IsIso (F.map g)))
  exact (ObjectProperty.isIso_hom_iff g').2 (isIso_of_reflects_iso g' G)

include hA hEquiv hUnit eL basisCover vanishing basisCover' vanishing' in
/-- **The unit `K ⟶ R L K` is invertible for every `K` of `D_{𝒜'}`**: by the triangle identity
`L` of it is invertible, and `F = H^j ∘ L` reflects isomorphisms between objects of `𝒜'`. -/
theorem isIso_unit_app_of_derivedCategoryB_of_iso_adjunctionUnboundedEquivalence
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤ adj.counitIsIso)
    (K : DerivedCategory (SheafOfModules.{w} O'))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    IsIso (adj.unit.app K) := by
  have hFK : DerivedCategoryB.derivedCategoryB A (L.obj K) :=
    derivedCategoryB_obj_of_iso_adjunctionUnboundedEquivalence F eL A A' hA K hK
  have hGFK : DerivedCategoryB.derivedCategoryB A' (R.obj (L.obj K)) :=
    derivedCategoryB_rightAdjoint_obj_of_iso_adjunctionUnboundedEquivalence F adj eL A A' hA
      hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' _ hFK
  have hε : IsIso (adj.counit.app (L.obj K)) :=
    isIso_counit_app_of_derivedCategoryB_of_iso_adjunctionUnboundedEquivalence F adj eL A A' hA
      hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus _ hFK
  have hLη : IsIso (L.map (adj.unit.app K)) := by
    have htri : IsIso (L.map (adj.unit.app K) ≫ adj.counit.app (L.obj K)) := by
      rw [adj.left_triangle_components K]
      exact (Iso.refl (L.obj K)).isIso_hom
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj K))
  rw [DerivedCategory.isIso_iff]
  intro j
  have hpb : IsIso (F.map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map (adj.unit.app K))) :=
    (NatIso.isIso_map_iff (compHomologyFunctorIsoOfIsoAdjunctionBoundedBelowDescent F eL j)
      (adj.unit.app K)).1
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O) j).map
        (L.map (adj.unit.app K)))))
  exact isIso_of_isIso_map_of_isEquivalence_adjunctionUnboundedEquivalence F A A' hA hEquiv _
    (hK j) (hGFK j)

/-- **The restriction of `L ⊣ R` to the subcategories `D_{𝒜'}` and `D_𝒜`.** -/
noncomputable def adjunctionUnboundedOfIsoAdjunctionUnboundedEquivalence :
    (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙ L)
        (fun K ↦ derivedCategoryB_obj_of_iso_adjunctionUnboundedEquivalence F eL A A' hA
          K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙ R)
        (fun K ↦ derivedCategoryB_rightAdjoint_obj_of_iso_adjunctionUnboundedEquivalence F adj eL
          A A' hA hEquiv hUnit
          B basisCover degreeBound coverings vanishing
          B' basisCover' degreeBound' coverings' vanishing' K.obj K.property) :=
  adj.restrictFullyFaithful
    (DerivedCategoryB.derivedCategoryB A').fullyFaithfulι
    (DerivedCategoryB.derivedCategoryB A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- **The equivalence `D_{𝒜'} ≌ D_𝒜` for an abstract adjunction**, granted that the counit is
invertible on `D⁺_𝒜`: both restricted adjoints are then fully faithful. -/
noncomputable def equivalenceUnboundedOfIsoAdjunctionUnboundedEquivalence
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤ adj.counitIsIso) :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  have hUnitB : DerivedCategoryB.derivedCategoryB A' ≤ adj.unitIsIso := fun K hK ↦
    isIso_unit_app_of_derivedCategoryB_of_iso_adjunctionUnboundedEquivalence F adj eL A A' hA
      hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus K hK
  have hCounitB : DerivedCategoryB.derivedCategoryB A ≤ adj.counitIsIso := fun K hK ↦
    isIso_counit_app_of_derivedCategoryB_of_iso_adjunctionUnboundedEquivalence F adj eL A A' hA
      hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus K hK
  letI hL := adj.fullyFaithfulιCompLeftAdjointOfLE hUnitB
  letI hR := adj.fullyFaithfulιCompRightAdjointOfLE hCounitB
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (adjunctionUnboundedOfIsoAdjunctionUnboundedEquivalence F adj eL A A' hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing').toEquivalence

/-- **Stacks 0D7V for an abstract adjunction.** For an adjunction `L ⊣ R` of derived categories
of modules with `L` identified with the functor induced by an exact functor `F`, weak Serre
subcategories `𝒜`, `𝒜'` such that `F` induces an equivalence `𝒜' ⟶ 𝒜` and the unit is invertible
on `𝒜'`, and both sites satisfying the Olsson--Laszlo hypothesis, `L` restricts to an equivalence
`D_{𝒜'} ≌ D_𝒜`. The counit propagates to `D⁺_𝒜` by the abstract form of Tag 0D7S. -/
noncomputable def equivalenceUnboundedAdjunctionUnboundedEquivalence :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  equivalenceUnboundedOfIsoAdjunctionUnboundedEquivalence F adj eL A A' hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing'
    (fun K hK ↦ isIso_counit_app_of_isIso_homology_adjunctionBoundedBelowDescent adj
      (isGE_obj_of_iso_adjunctionBoundedBelowDescent F eL)
      (DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom adj
        (isLE_obj_of_iso_adjunctionBoundedBelowDescent F eL)) K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦
        isIso_counit_app_singleFunctor_obj_of_iso_adjunctionBoundedBelowEquivalence F adj eL A A' hA
          hEquiv hUnit _ (hK.2 q))

end Core

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedToposSiteHom X Y)
  (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]

section Exact

variable [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-! ### Derived pullback is degreewise pullback, naturally -/

/-! ### The two derived functors restrict -/

variable (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))

variable (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))

variable (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝒰.X i) p F))

include hA basisCover vanishing basisCover' vanishing' in
/-- `Rf_*` carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`. This is Tag 0D6U, part (a), with `N = 0`: the
higher direct images of an object of `𝒜` lie in `𝒜'` because its pushforward is bounded below
with cohomology in `𝒜'`, and they vanish above degree `0` because that pushforward lives in
degrees `≤ 0`. -/
theorem derivedCategoryB_derivedPushforward_obj_of_exact_adjunctionUnboundedEquivalence
    (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
    (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A' ((derivedPushforward f).obj K) :=
  have : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact f)
  derivedCategoryB_rightAdjoint_obj_of_iso_adjunctionUnboundedEquivalence
    f.pullbackTopos (derivedPullbackPushforwardAdjunctionOfExact f) (derivedPullbackNatIso f)
    A A' hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing B' basisCover' degreeBound' coverings' vanishing'
    K hK

/-! ### The unit and the counit are invertible -/

/-! ### The equivalence -/

end Exact

end Stacks.Cohomology.CohomologicalDescent

end
