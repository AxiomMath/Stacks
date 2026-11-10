module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalence

/-!
# The unbounded equivalence for an abstract adjunction of derived categories of modules

Stacks 0D6U and 0D7V are stated in this library for a morphism of ringed topoi presented by a
continuous functor between the underlying sites (`AlgebraicGeometry.RingedToposSiteHom`). Their
proofs use nothing of that presentation beyond four properties of the derived direct image `R`:
it is a right adjoint, it commutes with the shift, it is triangulated, and it preserves
boundedness below. This file isolates that argument for an arbitrary adjunction `L ⊣ R` between
derived categories of sheaves of modules on the sites of two Olsson--Laszlo situations, so that
it applies to morphisms of ringed topoi with no site presentation, such as the augmentation of
the total site of a hypercovering.

## Main results

* `Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_obj_of_rightAdjoint`: Stacks 0D6U, part (a),
  for an abstract `R`.
* `Stacks.Cohomology.OlssonLaszlo.isIso_homology_map_truncGEπ_of_rightAdjoint`: Stacks 0D6U,
  part (b), for an abstract `R`.
* `Stacks.Cohomology.CohomologicalDescent.equivalenceOfAdjunctionUnbounded`: the argument of
  Stacks 0D7V for an adjunction `L ⊣ R` whose left adjoint is computed degreewise by an
  additive functor `F`, with its two functors identified as the restrictions of `L` and `R`.

## Implementation notes

The derived categories are those of the `HasDerivedCategory.standard` model, because the input
Stacks 0D6S (`Stacks.Cohomology.OlssonLaszlo.truncGETower_presentation`) is stated there.

## References

* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.OlssonLaszlo

universe v u wRing wModule v' u' wRing' wModule'

attribute [local instance] HasDerivedCategory.standard

open Stacks.InverseSystem

section Abstract

variable (S : OlssonLaszloSituation.{v, u, wRing, wModule})
  (S' : OlssonLaszloSituation.{v', u', wRing', wModule'})
  (R : DerivedCategory (SheafOfModules.{wModule} S.O) ⥤
    DerivedCategory (SheafOfModules.{wModule'} S'.O))
  [R.IsRightAdjoint] [R.CommShift ℤ] [R.IsTriangulated]
  (hRGE : ∀ (L : DerivedCategory (SheafOfModules.{wModule} S.O)) (m : ℤ), L.IsGE m →
    (R.obj L).IsGE m)
  (N : ℤ)
  (himage : ∀ (p : ℕ) (F : SheafOfModules.{wModule} S.O), S.A F →
    S'.A ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) (p : ℤ)).obj
      (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj F))))
  (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) → ∀ F : SheafOfModules.{wModule} S.O, S.A F →
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) (p : ℤ)).obj
      (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj F))))

omit [R.IsRightAdjoint] [R.IsTriangulated] in
include hRGE hvanishImage in
/-- An abstract right adjoint which preserves boundedness below and whose higher images of the
objects of `A` vanish above `N` carries an object of `A` placed in degree `n` into degrees
`≤ n + N`. -/
theorem isLE_map_singleFunctor_obj_of_rightAdjoint
    (M : SheafOfModules.{wModule} S.O) (hM : S.A M) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) n).obj M)).IsLE
      (n + N) := by
  refine isLE_map_singleFunctor_obj_of_isLE_zero R M N ?_ n
  have hGE := hRGE ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj M) 0
    inferInstance
  rw [DerivedCategory.isLE_iff]
  intro p hp
  by_cases hp0 : 0 ≤ p
  · obtain ⟨pn, rfl⟩ : ∃ pn : ℕ, (pn : ℤ) = p := ⟨p.toNat, Int.toNat_of_nonneg hp0⟩
    exact hvanishImage pn (by exact_mod_cast hp) M hM
  · exact DerivedCategory.isZero_of_isGE _ 0 p (by omega)

omit [R.IsRightAdjoint] in
include hRGE hvanishImage in
/-- The transition maps of the image under `R` of the truncation tower of an object of `D_A`
are cohomology isomorphisms in degrees `j ≥ N - k`. -/
theorem isIso_homology_map_truncGETower_succ_of_rightAdjoint
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) (k : ℕ) (j : ℤ)
    (hj : N - (k : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j).map
      (R.map ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).map
        (homOfLE (Nat.le_succ k)).op))) :=
  isIso_homologyMap_map_truncGETower_succ R S.A N
    (fun M n hM ↦ isLE_map_singleFunctor_obj_of_rightAdjoint S S' R hRGE N hvanishImage M hM n)
    K hK k j hj

/-- The cohomology in degree `i` of the image under `R` of the truncation tower of an object of
`D_A` is eventually constant, with value its stage `N - i`. -/
private def eventuallyConstantValue_homology_map_truncGETower
    (hRGE : ∀ (L : DerivedCategory (SheafOfModules.{wModule} S.O)) (m : ℤ), L.IsGE m →
      (R.obj L).IsGE m)
    (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) → ∀ F : SheafOfModules.{wModule} S.O, S.A F →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) (p : ℤ)).obj
        (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) (i : ℤ) :
    EventuallyConstantValue
      ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K ⋙ R) ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) i)
      ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) i).obj
        (R.obj ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj
          ⟨(N - i).toNat⟩))) := by
  refine ⟨(N - i).toNat, ?_, Iso.refl _⟩
  apply isEventuallyConstantTo_of_isIso_succ
  intro k hk
  exact isIso_homology_map_truncGETower_succ_of_rightAdjoint S S' R hRGE N hvanishImage
    K hK k i (by omega)

omit [R.IsRightAdjoint] in
include hRGE himage in
/-- Every stage of the image under `R` of the truncation tower of an object of `D_A` lies in
`D⁺_{A'}`. -/
theorem derivedCategoryBPlus_map_truncGETower_obj_of_rightAdjoint
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) (k : ℕ) :
    DerivedCategoryB.derivedCategoryBPlus S'.A
      (R.obj ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨k⟩)) := by
  have sourceProperty := truncGETower_obj_mem_plus S.A K hK k
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1 sourceProperty.1
  refine DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE R S'.A
    (WeakSerre.isWeakSerre_of_isWeakSerreClass S'.A) hRGE _ a ha fun q ↦ ?_
  have hGE := hRGE ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj
    ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) q).obj
      ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K).obj ⟨k⟩))) 0
    inferInstance
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨0, hGE⟩, fun pp ↦ ?_⟩
  by_cases hp0 : 0 ≤ pp
  · obtain ⟨pn, rfl⟩ : ∃ pn : ℕ, (pn : ℤ) = pp := ⟨pp.toNat, Int.toNat_of_nonneg hp0⟩
    exact himage pn _ (sourceProperty.2 q)
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre S'.A
      (WeakSerre.isWeakSerre_of_isWeakSerreClass S'.A) _
      (DerivedCategory.isZero_of_isGE _ 0 pp (by omega))

include hRGE himage hvanishImage in
/-- **Stacks 0D6U, part (a), for an abstract right adjoint.** Let `R` be a triangulated right
adjoint between the derived categories of modules of two Olsson--Laszlo situations, commuting
with the shift and preserving boundedness below, such that `Hᵖ(R(F[0]))` lies in `A'` for every
`p ≥ 0` and vanishes for `p > N`, for every `F` in `A`. Then `R` carries `D_A` into `D_{A'}`. -/
theorem derivedCategoryB_obj_of_rightAdjoint
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) :
    DerivedCategoryB.derivedCategoryB S'.A (R.obj K) := by
  obtain ⟨hprod, L, c, p, δ, htriangle, hc, hcIso⟩ := truncGETower_presentation S K hK
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K
  let towerR := tower ⋙ R
  have hT : ∀ k : ℕ, DerivedCategoryB.derivedCategoryBPlus S'.A (towerR.obj ⟨k⟩) :=
    derivedCategoryBPlus_map_truncGETower_obj_of_rightAdjoint S S' R hRGE himage K hK
  let : HasProduct fun k : ℕ ↦ tower.obj ⟨k⟩ := hprod
  obtain ⟨hprod', p', δ', htriangle', -⟩ :=
    exists_presented_derivedLimit_map R tower L p δ htriangle c
      (fun k ↦ (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K) hc
  let : HasProduct fun k : ℕ ↦ towerR.obj ⟨k⟩ := hprod'
  let ℋ : ℤ → SheafOfModules.{wModule'} S'.O := fun i ↦
    (DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) i).obj
      (towerR.obj ⟨(N - i).toNat⟩)
  have heventual := fun i ↦
    eventuallyConstantValue_homology_map_truncGETower S S' R N hRGE hvanishImage K hK i
  have hlimit : DerivedCategoryB.derivedCategoryB S'.A (R.obj L) :=
    derivedCategoryB_of_presented_derivedLimit S' towerR hT _ p' ⟨δ', htriangle'⟩ ℋ heventual
      fun i ↦ (hT (N - i).toNat).2 i
  intro j
  exact S'.A.prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j).mapIso
      (R.mapIso (asIso c)).symm) (hlimit j)

include hRGE himage hvanishImage in
/-- **Stacks 0D6U, part (b), for an abstract right adjoint.** In the situation of
`derivedCategoryB_obj_of_rightAdjoint`, the map `Hʲ(R K) ⟶ Hʲ(R(τ_{≥ -n}K))` induced by the
truncation is an isomorphism for every `j ≥ N - n`. -/
theorem isIso_homology_map_truncGEπ_of_rightAdjoint
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  obtain ⟨hprod, L, c, p, δ, htriangle, hc, hcIso⟩ := truncGETower_presentation S K hK
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) K
  let towerR := tower ⋙ R
  have hT : ∀ k : ℕ, DerivedCategoryB.derivedCategoryBPlus S'.A (towerR.obj ⟨k⟩) :=
    derivedCategoryBPlus_map_truncGETower_obj_of_rightAdjoint S S' R hRGE himage K hK
  let : HasProduct fun k : ℕ ↦ tower.obj ⟨k⟩ := hprod
  obtain ⟨hprod', p', δ', htriangle', hcompat⟩ :=
    exists_presented_derivedLimit_map R tower L p δ htriangle c
      (fun k ↦ (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K) hc
  let : HasProduct fun k : ℕ ↦ towerR.obj ⟨k⟩ := hprod'
  let ℋ : ℤ → SheafOfModules.{wModule'} S'.O := fun i ↦
    (DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) i).obj
      (towerR.obj ⟨(N - i).toNat⟩)
  let heventual := fun i ↦
    eventuallyConstantValue_homology_map_truncGETower S S' R N hRGE hvanishImage K hK i
  have hidxle : (N - j).toNat ≤ n := Int.toNat_le.2 (by omega)
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j
  let κ : ∀ k : ℕ, K ⟶ tower.obj ⟨k⟩ := fun k ↦
    (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K
  let d := Stacks.Cohomology.cohomologyToEventuallyConstantValue S' towerR (R.obj L) p' j
    (ℋ j) (heventual j)
  have hd : IsIso d := Stacks.Cohomology.isIso_cohomologyToEventuallyConstantValue
    S' towerR hT (R.obj L) p' ⟨δ', htriangle'⟩ ℋ heventual j
  have hidxComp : H.map (R.map c) ≫ d =
      H.map (R.map (κ (N - j).toNat)) ≫ (heventual j).iso.hom := by
    change H.map (R.map c) ≫
      (H.map (p' ≫ Pi.π (fun k : ℕ ↦ R.obj (tower.obj ⟨k⟩)) (N - j).toNat) ≫
        (heventual j).iso.hom) = _
    erw [← CategoryTheory.Functor.map_comp_assoc]
    exact congrArg (fun g ↦ H.map g ≫ (heventual j).iso.hom) (hcompat (N - j).toNat)
  have hidxMap : IsIso (H.map (R.map (κ (N - j).toNat))) := by
    have hcomp : IsIso (H.map (R.map c) ≫ d) := by infer_instance
    rw [hidxComp] at hcomp
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (heventual j).iso.isIso_hom hcomp
  have hπfactor : κ n ≫ tower.map (homOfLE hidxle).op = κ (N - j).toNat := by
    let π : (Functor.const ℕᵒᵖ).obj K ⟶ tower := NatTrans.ofOpSequence κ (by
      intro k
      change 𝟙 K ≫ κ k = κ (k + 1) ≫ tower.map (homOfLE (Nat.le_succ k)).op
      rw [Category.id_comp]
      dsimp only [κ, tower]
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) K).symm)
    exact (π.naturality (homOfLE hidxle).op).symm.trans (Category.id_comp _)
  have htrans : IsIso (H.map (R.map (tower.map (homOfLE hidxle).op))) :=
    (heventual j).isEventuallyConstant.isIso_map (homOfLE hidxle).op (𝟙 _)
  rw [← hπfactor, R.map_comp, H.map_comp] at hidxMap
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ htrans hidxMap

end Abstract

end Stacks.Cohomology.OlssonLaszlo

namespace Stacks.Cohomology.CohomologicalDescent

universe v u wRing wModule v' u' wRing' wModule'

attribute [local instance] HasDerivedCategory.standard

section Abstract

variable (S : OlssonLaszloSituation.{v, u, wRing, wModule})
  (S' : OlssonLaszloSituation.{v', u', wRing', wModule'})
  {L : DerivedCategory (SheafOfModules.{wModule'} S'.O) ⥤
    DerivedCategory (SheafOfModules.{wModule} S.O)}
  {R : DerivedCategory (SheafOfModules.{wModule} S.O) ⥤
    DerivedCategory (SheafOfModules.{wModule'} S'.O)}
  (adj : L ⊣ R) [hRC : R.CommShift ℤ] [hRT : R.IsTriangulated]
  (F : SheafOfModules.{wModule'} S'.O ⥤ SheafOfModules.{wModule} S.O)
  (eH : ∀ q : ℤ, L ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) q ≅
    DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) q ⋙ F)
  (hRGE : ∀ (K : DerivedCategory (SheafOfModules.{wModule} S.O)) (m : ℤ), K.IsGE m →
    (R.obj K).IsGE m)
  (hA : ∀ M, S'.A M → S.A (F.obj M))
  (hRsingleLE : ∀ M, S.A M →
    (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj M)).IsLE 0)
  (hRsingleA : ∀ M, S.A M → ∀ p : ℕ,
    S'.A ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) (p : ℤ)).obj
      (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{wModule} S.O) 0).obj M))))
  (hUnit : DerivedCategoryB.derivedCategoryB S'.A ≤ adj.unitIsIso)
  (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus S.A ≤ adj.counitIsIso)

include eH hA in
/-- The left adjoint carries `D_{A'}` into `D_A`: its cohomology is `F` of the cohomology of its
argument, and `F` carries `A'` into `A`. -/
theorem derivedCategoryB_leftAdjoint_obj
    (K : DerivedCategory (SheafOfModules.{wModule'} S'.O))
    (hK : DerivedCategoryB.derivedCategoryB S'.A K) :
    DerivedCategoryB.derivedCategoryB S.A (L.obj K) :=
  fun q ↦ S.A.prop_of_iso ((eH q).app K).symm (hA _ (hK q))

include adj hRGE hRsingleLE hRsingleA in
/-- The right adjoint carries `D_A` into `D_{A'}`, by Stacks 0D6U (a) with `N = 0`. -/
theorem derivedCategoryB_rightAdjoint_obj
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) :
    DerivedCategoryB.derivedCategoryB S'.A (R.obj K) :=
  have : R.IsRightAdjoint := ⟨L, ⟨adj⟩⟩
  Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_obj_of_rightAdjoint S S' R hRGE 0
    (fun p M hM ↦ hRsingleA M hM p) (fun p hp M hM ↦
      have := hRsingleLE M hM
      DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp) K hK

include eH hRGE hRsingleLE hRsingleA hCounitPlus in
/-- **The counit `L R K ⟶ K` is invertible for every `K` of `D_A`.** Fix a degree `j` and
truncate at `-n ≤ j`: the truncation is an isomorphism on `Hʲ`, the counit at the truncation is
invertible because the truncation lies in `D⁺_A`, and `R` of the truncation is an isomorphism on
`Hʲ` by Stacks 0D6U (b); `Hʲ ∘ L` is `F ∘ Hʲ`, so the naturality square of the counit gives the
claim in degree `j`. -/
theorem isIso_counit_app_of_derivedCategoryB
    (K : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hK : DerivedCategoryB.derivedCategoryB S.A K) :
    IsIso (adj.counit.app K) := by
  have : R.IsRightAdjoint := ⟨L, ⟨adj⟩⟩
  rw [DerivedCategory.isIso_iff]
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{wModule} S.O) j
  let H' := DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j
  let π := (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K
  have hπ : IsIso (H.map π) := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(n : ℤ)) j hn K
  have hε : IsIso (adj.counit.app ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) :=
    hCounitPlus _ (Stacks.Cohomology.OlssonLaszlo.truncGETower_obj_mem_plus S.A K hK n)
  have hRπ : IsIso (H'.map (R.map π)) :=
    Stacks.Cohomology.OlssonLaszlo.isIso_homology_map_truncGEπ_of_rightAdjoint S S' R hRGE 0
      (fun p M hM ↦ hRsingleA M hM p) (fun p hp M hM ↦
        have := hRsingleLE M hM
        DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp) K hK n j (by omega)
  have hLRπ : IsIso (H.map (L.map (R.map π))) := by
    have h : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule'} S'.O) j ⋙ F).map
        (R.map π)) := by
      change IsIso (F.map (H'.map (R.map π)))
      infer_instance
    exact (NatIso.isIso_map_iff (eH j) (R.map π)).2 h
  have hnat : H.map (L.map (R.map π)) ≫
        H.map (adj.counit.app ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) =
      H.map (adj.counit.app K) ≫ H.map π := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg H.map (adj.counit.naturality π)
  have hcomp : IsIso (H.map (adj.counit.app K) ≫ H.map π) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map π)

include adj F eH hRGE hA hRsingleLE hRsingleA in
/-- **The restriction of `L ⊣ R` to `D_{A'}` and `D_A`.** -/
def adjunctionDerivedCategoryB :
    (DerivedCategoryB.derivedCategoryB S.A).lift
        ((DerivedCategoryB.derivedCategoryB S'.A).ι ⋙ L)
        (fun K ↦ derivedCategoryB_leftAdjoint_obj S S' F eH hA K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryB S'.A).lift
        ((DerivedCategoryB.derivedCategoryB S.A).ι ⋙ R)
        (fun K ↦ derivedCategoryB_rightAdjoint_obj S S' adj hRGE hRsingleLE hRsingleA
          K.obj K.property) :=
  adj.restrictFullyFaithful (DerivedCategoryB.derivedCategoryB S'.A).fullyFaithfulι
    (DerivedCategoryB.derivedCategoryB S.A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

include adj F eH hRGE hA hRsingleLE hRsingleA hUnit hCounitPlus in
/-- **The argument of Stacks 0D7V for an abstract adjunction.** Let `L ⊣ R` be an adjunction
between the derived categories of modules of two Olsson--Laszlo situations, with `R`
triangulated, commuting with the shift and preserving boundedness below, and `L` computed
degreewise by a functor `F` carrying `A'` into `A`. If `R` of every object of `A` placed in
degree zero lies in degrees `≤ 0` with cohomology in `A'`, the unit is invertible on `D_{A'}` and
the counit on `D⁺_A`, then the restriction of the adjunction is an equivalence
`D_{A'} ≌ D_A`. -/
def equivalenceOfAdjunctionUnbounded :
    (DerivedCategoryB.derivedCategoryB S'.A).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB S.A).FullSubcategory :=
  have hCounitB : DerivedCategoryB.derivedCategoryB S.A ≤ adj.counitIsIso := fun K hK ↦
    isIso_counit_app_of_derivedCategoryB S S' adj F eH hRGE hRsingleLE hRsingleA hCounitPlus K hK
  letI hL := adj.fullyFaithfulιCompLeftAdjointOfLE hUnit
  letI hR := adj.fullyFaithfulιCompRightAdjointOfLE hCounitB
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (adjunctionDerivedCategoryB S S' adj F eH hRGE hA hRsingleLE hRsingleA).toEquivalence

/-- The forward functor of `equivalenceOfAdjunctionUnbounded` is the restriction of `L`. -/
theorem equivalenceOfAdjunctionUnbounded_functor :
    (equivalenceOfAdjunctionUnbounded S S' adj F eH hRGE hA hRsingleLE hRsingleA hUnit
        hCounitPlus).functor =
      (DerivedCategoryB.derivedCategoryB S.A).lift
        ((DerivedCategoryB.derivedCategoryB S'.A).ι ⋙ L)
        (fun K ↦ derivedCategoryB_leftAdjoint_obj S S' F eH hA K.obj K.property) :=
  rfl

/-- The inverse of `equivalenceOfAdjunctionUnbounded` is the restriction of `R`. -/
theorem equivalenceOfAdjunctionUnbounded_inverse :
    (equivalenceOfAdjunctionUnbounded S S' adj F eH hRGE hA hRsingleLE hRsingleA hUnit
        hCounitPlus).inverse =
      (DerivedCategoryB.derivedCategoryB S'.A).lift
        ((DerivedCategoryB.derivedCategoryB S.A).ι ⋙ R)
        (fun K ↦ derivedCategoryB_rightAdjoint_obj S S' adj hRGE hRsingleLE hRsingleA
          K.obj K.property) :=
  rfl

end Abstract

end Stacks.Cohomology.CohomologicalDescent

end
