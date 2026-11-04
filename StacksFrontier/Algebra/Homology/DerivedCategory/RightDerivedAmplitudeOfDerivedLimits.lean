module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorAmplitude
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGESuccTriangle
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness

/-!
# A right derived functor keeps the upper bound of objects that are derived limits

Let `𝒜` be an abelian category with countable products and enough injectives, let `P` be a
property of objects of `𝒜`, let `F : 𝒜 ⥤ Ab` be an additive functor commuting with countable
products and let `(RF, α)` be a right derived functor of `F` on the unbounded derived category.
Suppose

* `RF` carries `M[-n]` into `D^{≤ n}` for every `M` satisfying `P` (that is, `R^pF(M) = 0` for
  `p > 0`), and
* every object `E` all of whose cohomology objects satisfy `P` is the derived limit of the tower
  `n ↦ τ_{≥ -n} E` of its truncations from below.

Then `RF` carries every object of `D^{≤ c}` whose cohomology objects satisfy `P` into `D^{≤ c}`,
with no lower bound on the object. This is assertion (3) of Stacks 08F7 in the case `N = 1`,
with the vanishing on `P` and the convergence of the truncation tower (Stacks 08F6) as hypotheses
on an abstract category.

## Main results

* `Stacks.DerivedLimit.isLE_rightDerived_obj_of_isGE_of_isLE`: `RF` carries an object of
  `D^{[a, b]}` whose cohomology objects satisfy `P` into `D^{≤ b}`.
* `Stacks.DerivedLimit.isMittagLeffler_homology_rightDerived_truncGETower`: the cohomology systems
  of the image under `RF` of the truncation tower are Mittag-Leffler.
* `Stacks.DerivedLimit.isLE_rightDerived_obj_of_isLE_of_isDerivedLimit`: `RF` carries every object
  of `D^{≤ c}` whose cohomology objects satisfy `P` into `D^{≤ c}`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SmallDerivedCategory

namespace Stacks.DerivedLimit

universe w

attribute [local instance] HasDerivedCategory.standard

universe w'

/-- A right derived functor on the unbounded derived category is triangulated. -/
private theorem exists_commShift_isTriangulated {𝒜 : Type*} {B : Type*} [Category* 𝒜] [Category* B]
    [Abelian 𝒜] [Abelian B] [HasDerivedCategory 𝒜] [HasDerivedCategory B]
    [IsGrothendieckAbelian.{w'} 𝒜] (F : 𝒜 ⥤ B) [F.Additive]
    (RF : DerivedCategory 𝒜 ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))] :
    ∃ _ : RF.CommShift ℤ, RF.IsTriangulated :=
  ⟨Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) ℤ,
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α⟩

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  [HasProductsOfShape ℕ 𝒜] [EnoughInjectives 𝒜] [IsGrothendieckAbelian.{w'} 𝒜]

omit [IsGrothendieckAbelian.{w'} 𝒜] in
/-- The truncation tower `n ↦ τ_{≥ -n} E` of an object `E` of `D(𝒜)` has a product. -/
theorem hasProduct_truncGETower (E : DerivedCategory 𝒜) :
    HasProduct fun n : ℕ ↦ (truncGETower 𝒜 E).obj ⟨n⟩ :=
  (DerivedCategory.exists_isDerivedLimit_of_forall_isGE (truncGETower 𝒜 E)
    (fun n ↦ ⟨-(n : ℤ), by rw [truncGETower_obj]; infer_instance⟩)).fst

attribute [local instance] hasProduct_truncGETower

variable (P : ObjectProperty 𝒜) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (F : 𝒜 ⥤ AddCommGrpCat.{w}) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory 𝒜 ⥤ DerivedCategory AddCommGrpCat.{w})
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))]
  (hRF : ∀ M : 𝒜, P M → ∀ n : ℤ,
    (RF.obj ((DerivedCategory.singleFunctor 𝒜 n).obj M)).IsLE n)

omit [HasProductsOfShape ℕ 𝒜] [EnoughInjectives 𝒜] [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α hRF in
/-- `RF` carries an object of `D^{[a, b]}` whose cohomology objects satisfy `P` into `D^{≤ b}`. -/
theorem isLE_rightDerived_obj_of_isGE_of_isLE (E : DerivedCategory 𝒜)
    (hqc : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor 𝒜 q).obj E))
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) : (RF.obj E).IsLE b := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated F RF α
  have := hGE
  have := hLE
  simpa using isLE_obj_of_isGE_of_isLE P RF 0 (fun M hM n ↦ by simpa using hRF M hM n) E hqc a b

omit [HasProductsOfShape ℕ 𝒜] [EnoughInjectives 𝒜] [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α hRF in
/-- For an object `E` whose cohomology objects satisfy `P` and every `i`, the inverse system
`n ↦ H^i(RF(τ_{≥ -n} E))` is Mittag-Leffler. -/
theorem isMittagLeffler_homology_rightDerived_truncGETower (E : DerivedCategory 𝒜)
    (hqc : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor 𝒜 q).obj E)) (i : ℤ) :
    (((truncGETower 𝒜 E ⋙ RF) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{w} i) ⋙
        forget AddCommGrpCat.{w}).IsMittagLeffler := by
  obtain ⟨_, _⟩ := exists_commShift_isTriangulated F RF α
  refine isMittagLeffler_of_eventually_surjective (-i).toNat fun n hn ↦ ?_
  have hnn : -i ≤ (n : ℤ) := Int.toNat_le.1 hn
  obtain ⟨f, δ, hT⟩ : ∃ (f : (DerivedCategory.singleFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj
        ((DerivedCategory.homologyFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj E) ⟶
        (DerivedCategory.TStructure.t.truncGE (-((n + 1 : ℕ) : ℤ))).obj E)
      (δ : (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E ⟶
        ((DerivedCategory.singleFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj
          ((DerivedCategory.homologyFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj E))⟦(1 : ℤ)⟧),
      Triangle.mk f ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) δ ∈ distTriang _ := by
    have key : ∀ (a b : ℤ) (hb : a + 1 = b), ∃ (f : (DerivedCategory.singleFunctor 𝒜 a).obj
          ((DerivedCategory.homologyFunctor 𝒜 a).obj E) ⟶
          (DerivedCategory.TStructure.t.truncGE a).obj E)
        (δ : (DerivedCategory.TStructure.t.truncGE b).obj E ⟶
          ((DerivedCategory.singleFunctor 𝒜 a).obj
            ((DerivedCategory.homologyFunctor 𝒜 a).obj E))⟦(1 : ℤ)⟧),
        Triangle.mk f ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app E)
          δ ∈ distTriang _ := by
      rintro a b rfl
      exact DerivedCategory.exists_truncGESucc_triangle E a
    exact key _ _ (by push_cast; ring)
  have hsingle := hRF _ (hqc (-((n + 1 : ℕ) : ℤ))) (-((n + 1 : ℕ) : ℤ))
  have hTd := RF.map_distinguished _ hT
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{w} (i + 1)).obj
      (RF.obj ((DerivedCategory.singleFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj
        ((DerivedCategory.homologyFunctor 𝒜 (-((n + 1 : ℕ) : ℤ))).obj E)))) := by
    exact DerivedCategory.isZero_of_isLE _ (-((n + 1 : ℕ) : ℤ)) (i + 1)
      (by push_cast at hnn ⊢; omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{w} i).map
      (RF.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{w}
      0).homologySequence_epi_shift_map_mor₂_iff _ hTd i (i + 1) rfl).2 (hz.eq_of_tgt _ _)
  show Function.Surjective ⇑((DerivedCategory.homologyFunctor AddCommGrpCat.{w} i).map
    (RF.map ((truncGETower 𝒜 E).map (homOfLE (Nat.le_succ n)).op)))
  rw [truncGETower_map_homOfLE_succ]
  exact (AddCommGrpCat.epi_iff_surjective _).1 hepi

include F α hRF in
/-- If every object whose cohomology objects satisfy `P` is the derived limit of its truncation
tower, then `RF` carries every object of `D^{≤ c}` whose cohomology objects satisfy `P` into
`D^{≤ c}`. -/
theorem isLE_rightDerived_obj_of_isLE_of_isDerivedLimit
    (hlim : ∀ E : DerivedCategory 𝒜, (∀ q : ℤ, P ((DerivedCategory.homologyFunctor 𝒜 q).obj E)) →
      IsDerivedLimit (truncGETower 𝒜 E) E)
    (E : DerivedCategory 𝒜) (hqc : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor 𝒜 q).obj E))
    (c : ℤ) (hLE : E.IsLE c) : (RF.obj E).IsLE c := by
  have := hLE
  obtain ⟨p, δ₀, hT₀⟩ := hlim E hqc
  obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α
    (truncGETower 𝒜 E) E p ⟨δ₀, hT₀⟩
  let := hp'
  have hlim' : IsDerivedLimit (truncGETower 𝒜 E ⋙ RF) (RF.obj E) := ⟨_, δ, hδ⟩
  have hbound : ∀ n : ℕ, ((truncGETower 𝒜 E ⋙ RF).obj ⟨n⟩).IsLE c := by
    intro n
    have hGE : ((truncGETower 𝒜 E).obj ⟨n⟩).IsGE (-(n : ℤ)) := by
      rw [truncGETower_obj]; infer_instance
    have hLE' : ((truncGETower 𝒜 E).obj ⟨n⟩).IsLE c := by
      rw [truncGETower_obj]; infer_instance
    exact isLE_rightDerived_obj_of_isGE_of_isLE P F RF α hRF _
      (fun q ↦ prop_homologyFunctor_truncGE_obj P E hqc (-(n : ℤ)) q) (-(n : ℤ)) c hGE hLE'
  exact isLE_of_isDerivedLimit_of_isMittagLeffler _ (RF.obj E) hlim' c hbound
    (isMittagLeffler_homology_rightDerived_truncGETower P F RF α hRF E hqc)

end Stacks.DerivedLimit

end
