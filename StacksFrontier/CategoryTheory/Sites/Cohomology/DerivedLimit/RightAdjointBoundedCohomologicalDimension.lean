module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.EventuallyConstantDerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedLimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite

/-!
# An exact right adjoint in the Olsson--Laszlo situation

For a triangulated right adjoint `R : D(O) ⥤ D(O')` between derived categories of modules on two
sites in the Olsson--Laszlo situation, preserving boundedness below, carrying the weak Serre class
`𝒜` into `𝒜'` on cohomology and with bounded cohomological dimension on `𝒜`, the functor `R`
carries `D_𝒜(O)` into `D_{𝒜'}(O')`, as in Stacks 0D6U for the derived direct image.

## References

* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.OlssonLaszlo

universe v u wRing wModule w

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] Stacks.DerivedLimit.truncGETower

/-! ### The Olsson--Laszlo situations on two sites

The two sides of the argument only ever meet through an exact functor `R` of derived
categories which is a right adjoint and preserves boundedness below. The statements are proved
in that generality, for two arbitrary sites with sheaves of rings, and then read off for the
derived direct image of a morphism of ringed topoi presented by a continuous functor of sites
(`AlgebraicGeometry.RingedToposSiteHom`). -/

/-! ### Comparing the truncations of a single object -/

section Transition

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {C' : Type w} [Category.{w} C'] {J' : GrothendieckTopology C'} {O' : Sheaf J' RingCat.{w}}
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The truncations of `K` factor through one another.** For `m ≤ n` the truncation
`K ⟶ τ_{≥ -n}K` followed by the transition map `τ_{≥ -n}K ⟶ τ_{≥ -m}K` of the truncation tower
is the truncation `K ⟶ τ_{≥ -m}K`. Hence a functor `R` whose composite with `Hʲ` inverts both
the transition map and the truncation to the stage `m` inverts the truncation to the stage
`n`. -/
private theorem isIso_homology_map_truncGEπ_of_le
    (R : DerivedCategory (SheafOfModules.{w} O) ⥤ DerivedCategory (SheafOfModules.{w} O'))
    (K : DerivedCategory (SheafOfModules.{w} O)) {m n : ℕ} (hmn : m ≤ n) (j : ℤ)
    (htrans : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{w} O) K).map
        (homOfLE hmn).op))))
    (hm : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K)))) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{w} O) K
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j
  let κ : ∀ k : ℕ, K ⟶ tower.obj ⟨k⟩ := fun k ↦
    (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K
  have hπfactor : κ n ≫ tower.map (homOfLE hmn).op = κ m := by
    let π : (Functor.const ℕᵒᵖ).obj K ⟶ tower := NatTrans.ofOpSequence κ (by
      intro k
      change 𝟙 K ≫ κ k = κ (k + 1) ≫ tower.map (homOfLE (Nat.le_succ k)).op
      rw [Category.id_comp]
      dsimp only [κ, tower]
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) K).symm)
    exact (π.naturality (homOfLE hmn).op).symm.trans (Category.id_comp _)
  have hcomp : IsIso (H.map (R.map (κ n)) ≫ H.map (R.map (tower.map (homOfLE hmn).op))) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hπfactor]
    exact hm
  exact IsIso.of_isIso_comp_right (H.map (R.map (κ n)))
    (H.map (R.map (tower.map (homOfLE hmn).op)))

end Transition

section Core

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} O)]
  {C' : Type w} [Category.{w} C'] {J' : GrothendieckTopology C'} {O' : Sheaf J' RingCat.{w}}
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} O')]
  (A : ObjectProperty (SheafOfModules.{w} O))
  (A' : ObjectProperty (SheafOfModules.{w} O'))
  [hA : A.IsWeakSerreClass] [hA' : A'.IsWeakSerreClass]
  (B : Set C)
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

/-- The Olsson--Laszlo situation on the source site. -/
private noncomputable def sourceSituation_general :
    Stacks.Cohomology.OlssonLaszloSituation.{w, w, w, w} where
  C := C
  J := J
  O := O
  A := A
  B := B
  basis_cover := basisCover
  degreeBound := degreeBound
  coverings := coverings
  vanishing := vanishing

/-- The Olsson--Laszlo situation on the target site. -/
private noncomputable def targetSituation_general :
    Stacks.Cohomology.OlssonLaszloSituation.{w, w, w, w} where
  C := C'
  J := J'
  O := O'
  A := A'
  B := B'
  basis_cover := basisCover'
  degreeBound := degreeBound'
  coverings := coverings'
  vanishing := vanishing'

attribute [local implicit_reducible] sourceSituation_general targetSituation_general

open Stacks.InverseSystem

/-! ### An exact right adjoint in the Olsson--Laszlo situation -/

variable (R : DerivedCategory (SheafOfModules.{w} O) ⥤ DerivedCategory (SheafOfModules.{w} O'))
  [R.CommShift ℤ] [R.IsTriangulated]
  (hGE : ∀ (K : DerivedCategory (SheafOfModules.{w} O)) (n : ℤ), K.IsGE n → (R.obj K).IsGE n)
  (N : ℤ)
  (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} O), A F →
    A' ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') (p : ℤ)).obj
      (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj F))))
  (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
    ∀ F : SheafOfModules.{w} O, A F →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') (p : ℤ)).obj
        (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj F))))

omit [EnoughInjectives (SheafOfModules O)] [EnoughInjectives (SheafOfModules O')] hA
  [R.CommShift ℤ] [R.IsTriangulated] in
include hGE hvanishImage in
/-- **An exact functor preserving boundedness below sends a module of `A` placed in degree zero
into degrees `≤ N`** as soon as its cohomology vanishes there above `N`. -/
private theorem isLE_map_singleFunctor_zero_of_vanishing
    (M : SheafOfModules.{w} O) (hM : A M) :
    (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj M)).IsLE N := by
  have : (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj M)).IsGE 0 :=
    hGE _ 0 inferInstance
  rw [DerivedCategory.isLE_iff]
  intro p hp
  by_cases hp0 : 0 ≤ p
  · lift p to ℕ using hp0
    exact hvanishImage p hp M hM
  · exact DerivedCategory.isZero_of_isGE _ 0 p (by omega)

omit [EnoughInjectives (SheafOfModules O)] [EnoughInjectives (SheafOfModules O')] hA
  [R.IsTriangulated] in
include hGE hvanishImage in
/-- **An exact functor preserving boundedness below, whose cohomology on modules of `A` vanishes
above `N`, has cohomological dimension `N` over `A`**: it sends a module of `A` placed in any
degree `n` into cohomological degrees `≤ n + N`. -/
theorem isLE_map_singleFunctor_obj_of_vanishing_rightAdjointBoundedCohomologicalDimension
    (M : SheafOfModules.{w} O) (hM : A M) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) n).obj M)).IsLE (n + N) :=
  isLE_map_singleFunctor_obj_of_isLE_zero R M N
    (isLE_map_singleFunctor_zero_of_vanishing A R hGE N hvanishImage M hM) n

omit [EnoughInjectives (SheafOfModules O)] [EnoughInjectives (SheafOfModules O')] hA in
include hGE himage hA' in
/-- **Stacks 0D6U, the bounded below case, for an exact functor.** An exact functor preserving
boundedness below which carries the modules of `A` into `D⁺_{A'}` carries `D⁺_A(O)` into
`D⁺_{A'}(O')`. -/
theorem derivedCategoryBPlus_map_obj_of_image_rightAdjointBoundedCohomologicalDimension
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryBPlus A K) :
    DerivedCategoryB.derivedCategoryBPlus A' (R.obj K) := by
  obtain ⟨a, ha⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1
  refine DerivedCategoryB.derivedCategoryBPlus_map_obj_of_isGE R A'
    (WeakSerre.isWeakSerre_of_isWeakSerreClass A') hGE K a ha fun q ↦ ?_
  have hGE0 : (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O) q).obj K))).IsGE 0 :=
    hGE _ 0 inferInstance
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2 ⟨0, hGE0⟩, fun pp ↦ ?_⟩
  by_cases hp0 : 0 ≤ pp
  · lift pp to ℕ using hp0
    exact himage pp _ (hK.2 q)
  · exact DerivedCategoryB.zero_mem_of_isWeakSerre A'
      (WeakSerre.isWeakSerre_of_isWeakSerreClass A') _
      (DerivedCategory.isZero_of_isGE _ 0 pp (by omega))

omit [EnoughInjectives (SheafOfModules O)] [EnoughInjectives (SheafOfModules O')] in
include hGE hvanishImage hA in
/-- **Stacks 0D6U, the stabilisation of the image of the truncation tower, for an exact
functor.** The map `R(τ_{≥ -(k+1)}K) ⟶ R(τ_{≥ -k}K)` is an isomorphism on `H^j` for
`j ≥ N - k`. -/
theorem isIso_homology_map_truncGETower_succ_of_vanishing_rightAdjointBoundedCohomologicalDimension
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K) (k : ℕ) (j : ℤ)
    (hj : N - (k : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{w} O) K).map
          (homOfLE (Nat.le_succ k)).op))) :=
  isIso_homologyMap_map_truncGETower_succ R A N
    (fun M n hM ↦
      isLE_map_singleFunctor_obj_of_vanishing_rightAdjointBoundedCohomologicalDimension A R hGE N
        hvanishImage M hM n)
    K hK k j hj

section Eventual

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {C' : Type w} [Category.{w} C'] {J' : GrothendieckTopology C'} {O' : Sheaf J' RingCat.{w}}
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The tower of images is eventually constant on `H^i`.** From a stage `k₀` with `N - i ≤ k₀`
on, every transition map of the tower `(R(τ_{≥ -k}K))ₖ` is an isomorphism on `H^i`. -/
private theorem isEventuallyConstantTo_homology_truncGETower_comp
    (A : ObjectProperty (SheafOfModules.{w} O)) [A.IsWeakSerreClass]
    (R : DerivedCategory (SheafOfModules.{w} O) ⥤ DerivedCategory (SheafOfModules.{w} O'))
    [R.CommShift ℤ] [R.IsTriangulated]
    (hGE : ∀ (K : DerivedCategory (SheafOfModules.{w} O)) (n : ℤ), K.IsGE n → (R.obj K).IsGE n)
    (N : ℤ)
    (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
      ∀ F : SheafOfModules.{w} O, A F →
        IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') (p : ℤ)).obj
          (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K) (i : ℤ) (k₀ : ℕ) (hk₀ : N - i ≤ (k₀ : ℤ)) :
    ((Stacks.DerivedLimit.truncGETower (SheafOfModules.{w} O) K ⋙ R) ⋙
      DerivedCategory.homologyFunctor (SheafOfModules.{w} O') i).IsEventuallyConstantTo
        (.op k₀) := by
  apply isEventuallyConstantTo_of_isIso_succ
  intro k hk
  exact isIso_homology_map_truncGETower_succ_of_vanishing_rightAdjointBoundedCohomologicalDimension
    A R hGE N hvanishImage K hK k i (by omega)

end Eventual

variable [R.IsRightAdjoint]

/-- Both conclusions of Stacks 0D6U for an exact right adjoint, proved from one presentation of
the truncation tower. -/
private theorem derivedCategoryB_map_obj_and_isIso_homology_map_truncGEπ_of_isRightAdjoint
    (basisCover : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{w} U,
      𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i))
    (vanishing : ∀ (V : C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
      (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
        ∀ F : SheafOfModules.{w} O, A F →
          IsZero (Stacks.Cohomology.moduleCohomology O (𝒰.X i) p F))
    (basisCover' : ∀ U : C', ∃ 𝒰 : PreZeroHypercover.{w} U,
      𝒰.sieve₀ ∈ J' U ∧ ∀ i, B' (𝒰.X i))
    (vanishing' : ∀ (V : C') (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
      (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
        ∀ F : SheafOfModules.{w} O', A' F →
          IsZero (Stacks.Cohomology.moduleCohomology O' (𝒰.X i) p F))
    (hGE : ∀ (K : DerivedCategory (SheafOfModules.{w} O)) (n : ℤ), K.IsGE n → (R.obj K).IsGE n)
    (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} O), A F →
      A' ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') (p : ℤ)).obj
        (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj F))))
    (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
      ∀ F : SheafOfModules.{w} O, A F →
        IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') (p : ℤ)).obj
          (R.obj ((DerivedCategory.singleFunctor (SheafOfModules.{w} O) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A' (R.obj K) ∧ ∀ (n : ℕ) (j : ℤ), N - (n : ℤ) ≤ j →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
        (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  let S := sourceSituation_general A B basisCover degreeBound coverings vanishing
  let S' := targetSituation_general A' B' basisCover' degreeBound' coverings' vanishing'
  obtain ⟨hprod, L, c, p, δ, htriangle, hc, hcIso⟩ :=
    truncGETower_presentation S K hK
  let tower := Stacks.DerivedLimit.truncGETower (SheafOfModules.{w} O) K
  let towerR := tower ⋙ R
  have hT : ∀ k : ℕ, DerivedCategoryB.derivedCategoryBPlus A' (towerR.obj ⟨k⟩) := fun k ↦
    derivedCategoryBPlus_map_obj_of_image_rightAdjointBoundedCohomologicalDimension A A' R
      hGE himage _ (truncGETower_obj_mem_plus A K hK k)
  let : HasProduct fun k : ℕ ↦ tower.obj ⟨k⟩ := hprod
  obtain ⟨hprod', p', δ', htriangle', hcompat⟩ :=
    exists_presented_derivedLimit_map R tower L p δ htriangle c
      (fun k ↦ (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K) hc
  let : HasProduct fun k : ℕ ↦ towerR.obj ⟨k⟩ := hprod'
  let idx : ℤ → ℕ := fun i ↦ (N - i).toNat
  let ℋ : ℤ → SheafOfModules.{w} O' := fun i ↦
    (DerivedCategory.homologyFunctor (SheafOfModules.{w} O') i).obj
      (towerR.obj ⟨idx i⟩)
  let heventual : ∀ i : ℤ, EventuallyConstantValue
      (towerR ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{w} O') i) (ℋ i) := fun i ↦
    ⟨idx i, isEventuallyConstantTo_homology_truncGETower_comp A R hGE N hvanishImage K hK i
      (idx i) (Int.self_le_toNat _), Iso.refl _⟩
  have hℋ : ∀ i : ℤ, A' (ℋ i) := fun i ↦ (hT (idx i)).2 i
  refine ⟨?_, fun n j hj ↦ ?_⟩
  · have hlimit : DerivedCategoryB.derivedCategoryB A' (R.obj L) :=
      derivedCategoryB_of_presented_derivedLimit S' towerR hT _ p' ⟨δ', htriangle'⟩ ℋ heventual hℋ
    intro j
    exact A'.prop_of_iso
      ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).mapIso
        (R.mapIso (asIso c)).symm) (hlimit j)
  · have hidxle : idx j ≤ n := Int.toNat_le.2 (by omega)
    let H := DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j
    let κ : ∀ k : ℕ, K ⟶ tower.obj ⟨k⟩ := fun k ↦
      (DerivedCategory.TStructure.t.truncGEπ (-(k : ℤ))).app K
    let d := Stacks.Cohomology.cohomologyToEventuallyConstantValue S' towerR (R.obj L) p' j
      (ℋ j) (heventual j)
    have hd : IsIso d := Stacks.Cohomology.isIso_cohomologyToEventuallyConstantValue
      S' towerR hT (R.obj L) p' ⟨δ', htriangle'⟩ ℋ heventual j
    have hidxComp : H.map (R.map c) ≫ d =
        H.map (R.map (κ (idx j))) ≫ (heventual j).iso.hom := by
      change H.map (R.map c) ≫
        (H.map (p' ≫ Pi.π (fun k : ℕ ↦ R.obj (tower.obj ⟨k⟩)) (idx j)) ≫
          (heventual j).iso.hom) = _
      rw [← CategoryTheory.Functor.map_comp_assoc]
      exact congrArg (fun g ↦ H.map g ≫ (heventual j).iso.hom) (hcompat (idx j))
    have hidxMap : IsIso (H.map (R.map (κ (idx j)))) := by
      have hcomp : IsIso (H.map (R.map c) ≫ d) := by infer_instance
      rw [hidxComp] at hcomp
      exact IsIso.of_isIso_comp_right _ (heventual j).iso.hom
    have htransition : IsIso ((towerR ⋙ H).map (homOfLE hidxle).op) :=
      (heventual j).isEventuallyConstant.isIso_map (homOfLE hidxle).op (𝟙 _)
    exact isIso_homology_map_truncGEπ_of_le R K hidxle j htransition hidxMap

include hA hA' basisCover vanishing basisCover' vanishing' hGE himage hvanishImage in
/-- **Stacks 0D6U, part (a), for an exact right adjoint.** Let `R : D(O) ⥤ D(O')` be an exact
functor which is a right adjoint and preserves boundedness below, between the derived
categories of two sites satisfying the Olsson--Laszlo hypothesis for `A` and `A'`. If
`Hᵖ(R(F[0]))` lies in `A'` for every `p ≥ 0` and vanishes for `p > N`, for every `F` of `A`,
then `R` carries `D_A(O)` into `D_{A'}(O')`. -/
theorem derivedCategoryB_map_obj_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A' (R.obj K) :=
  (derivedCategoryB_map_obj_and_isIso_homology_map_truncGEπ_of_isRightAdjoint A A' B degreeBound
    coverings B' degreeBound' coverings' R N basisCover vanishing basisCover' vanishing' hGE
    himage hvanishImage K hK).1

include hA hA' basisCover vanishing basisCover' vanishing' hGE himage hvanishImage in
/-- **Stacks 0D6U, part (b), for an exact right adjoint.** In the situation of
`derivedCategoryB_map_obj_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension`, the map
`Hʲ(R K) ⟶ Hʲ(R(τ_{≥ -n}K))` induced by
the truncation `K ⟶ τ_{≥ -n}K` is an isomorphism for every `j ≥ N - n`. -/
theorem isIso_homology_map_truncGEπ_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension
    (K : DerivedCategory (SheafOfModules.{w} O))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w} O') j).map
      (R.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) :=
  (derivedCategoryB_map_obj_and_isIso_homology_map_truncGEπ_of_isRightAdjoint A A' B degreeBound
    coverings B' degreeBound' coverings' R N basisCover vanishing basisCover' vanishing' hGE
    himage hvanishImage K hK).2 n j hj

end Core

/-! ### The derived direct image of a morphism of ringed topoi presented by sites -/

section Topoi

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [hA : A.IsWeakSerreClass] [hA' : A'.IsWeakSerreClass]
  (B : Set X.C)
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
  (N : ℤ)
  (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), A F →
    A' ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
  (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
    ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
        ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))

omit [EnoughInjectives (SheafOfModules (SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules (SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The derived direct image preserves boundedness below.** This is
`Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction` at the
adjunction supplied by `f` being a morphism of sites. -/
theorem isGE_derivedPushforward_obj_rightAdjointBoundedCohomologicalDimension
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (hK : K.IsGE n) : ((derivedPushforward f).obj K).IsGE n :=
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  let : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (pullbackInvertsQuasiIso_isKFlat f hmos)
  Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction f
    (derivedPullbackPushforwardAdjunctionOfKFlat f hmos fun _ ↦
      pullbackInvertsQuasiIso_isKFlat f hmos)
    (isLE_derivedPullback_obj_of_isMorphismOfSites f hmos) K n hK

omit hA [EnoughInjectives (SheafOfModules (SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules (SheafOfModules.Tensor.ringSheaf Y.O))] in
include hA' in
/-- **Stacks 0D6U, the bounded below case.** The derived direct image carries `D⁺_A(O)` into
`D⁺_{A'}(O')`. -/
theorem derivedCategoryBPlus_derivedPushforward_obj_rightAdjointBoundedCohomologicalDimension
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (himage : ∀ (p : ℕ) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), A F →
      A' ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
        ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryBPlus A K) :
    DerivedCategoryB.derivedCategoryBPlus A' ((derivedPushforward f).obj K) := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  let := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have : (derivedPushforward f).IsTriangulated := isTriangulated_derivedPushforward f
  exact derivedCategoryBPlus_map_obj_of_image_rightAdjointBoundedCohomologicalDimension A A'
    (derivedPushforward f)
    (isGE_derivedPushforward_obj_rightAdjointBoundedCohomologicalDimension f hmos) himage K hK

end Topoi

end Stacks.Cohomology.OlssonLaszlo

end
