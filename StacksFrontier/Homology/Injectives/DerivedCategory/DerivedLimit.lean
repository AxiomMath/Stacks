module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Homology.Injectives.DerivedCategory.KInjectiveProducts
import StacksCore.Tactic.StacksAttribute

/-!
# Right derived functors and derived limits

Let `F : A ⥤ B` be an additive functor from a Grothendieck abelian category to an abelian
category with exact countable products, and suppose `F` preserves countable products. This
file shows that a right derived functor `RF` of `F` carries derived limits of inverse systems
indexed by `ℕ` to derived limits: if a distinguished triangle exhibits `K` as the derived
limit of `X : ℕᵒᵖ ⥤ DerivedCategory A`, then the corresponding triangle built from `RF.obj K`
and the countable product of the `RF.obj (X.obj ⟨n⟩)` is again distinguished.

The argument has two halves. First, a triangulated functor which preserves the countable
product occurring in a derived limit automatically transports the derived-limit triangle, the
only work being to transport the Milnor differential along the product comparison map. Second,
`RF` has both properties. It is triangulated because every object of `DerivedCategory A` is
represented by a K-injective complex and the unit of the derived functor is an isomorphism
there, so the triangulated criterion for left extensions applies; and it preserves countable
products because a countable product of K-injective complexes is K-injective and is computed
termwise, where `F` preserves it by hypothesis. Both halves use the chosen functorial
K-injective resolution and the identification of derived-category products with termwise
products of K-injective representatives.

## Main results

* `Stacks.Injectives.isDerivedLimit_map_of_preservesProduct`: a triangulated functor which
  preserves the countable product occurring in a derived limit carries the derived-limit
  triangle to a derived-limit triangle.
* `Stacks.Injectives.rightDerivedFunctor_isTriangulated`: a right derived functor of an
  additive functor out of a Grothendieck abelian category is triangulated.
* `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`: applying a right derived functor
  to a derived-limit triangle again gives a derived-limit triangle, with the image of its
  supplied structural map.

## Implementation notes

A right derived functor is allowed to be any functor equipped with its
`IsRightDerivedFunctor` universal property. This makes the result independent of the choice of
K-injective resolutions. The conclusion includes existence of the required product in the
target derived category, rather than assuming it. The structural map is specified as
`RF.map p ≫ piComparison RF _`, so its composite with each product projection is the image of
the corresponding structural map of the original derived limit.

Only products indexed by `ℕ` occur in a derived limit, so exact countable products and
preservation of countable products are stated for that shape. The countable product of
K-injective representatives is produced at the universe where the Grothendieck abelian
category is well behaved, so the family is reindexed by `ULift ℕ` and the resulting fan
transported back to one indexed by `ℕ`.

## References

* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
-/

@[expose] public section

universe w w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.Injectives

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- A triangulated functor which preserves the countable product occurring in a derived limit
carries the derived-limit triangle of an inverse system to a derived-limit triangle. The new
structural map is the image of the old one followed by the product comparison. -/
lemma isDerivedLimit_map_of_preservesProduct
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    (X : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ X.obj ⟨n⟩]
    [PreservesLimit (Discrete.functor (fun n : ℕ ↦ X.obj ⟨n⟩)) G]
    [HasProduct fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)]
    (K : C) (p : K ⟶ ∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩)
    (hK : ∃ δ : (∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) (n + 1) ≫
          X.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang C) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)) ⟶ (G.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk (G.map p ≫ piComparison G (fun n : ℕ ↦ X.obj ⟨n⟩))
        (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)) n -
          Pi.π (fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)) (n + 1) ≫
            G.map (X.map (homOfLE (Nat.le_succ n)).op)) δ ∈ distTriang D := by
  obtain ⟨δ, hT⟩ := hK
  let P : ℕ → C := fun n ↦ X.obj ⟨n⟩
  let d : (∏ᶜ P) ⟶ ∏ᶜ P := Pi.lift (fun n ↦ Pi.π P n -
    Pi.π P (n + 1) ≫ X.map (homOfLE (Nat.le_succ n)).op)
  let d' : (∏ᶜ fun n ↦ G.obj (P n)) ⟶ ∏ᶜ fun n ↦ G.obj (P n) := Pi.lift (fun n ↦
    Pi.π (fun n ↦ G.obj (P n)) n - Pi.π (fun n ↦ G.obj (P n)) (n + 1) ≫
      G.map (X.map (homOfLE (Nat.le_succ n)).op))
  let e := asIso (piComparison G P)
  have hd : G.map d ≫ e.hom = e.hom ≫ d' := by
    apply Pi.hom_ext
    intro n
    dsimp [e, d, d']
    simp only [Category.assoc, piComparison_comp_π, Pi.lift_π, Preadditive.comp_sub]
    rw [← G.map_comp, Pi.lift_π, G.map_sub, G.map_comp, ← Category.assoc,
      piComparison_comp_π]
  refine ⟨e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  apply isomorphic_distinguished _ (G.map_distinguished _ hT)
  refine Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · show (G.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ G.map p
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show d' ≫ e.inv = e.inv ≫ G.map d
    rw [← cancel_epi e.hom, e.hom_inv_id_assoc, ← Category.assoc, ← hd, Category.assoc,
      e.hom_inv_id, Category.comp_id]
  · dsimp [Functor.mapTriangle]
    rw [(shiftFunctor D (1 : ℤ)).map_id]
    simp only [Category.comp_id]

/-- An exact right adjoint between pretriangulated categories carries a derived limit of a
countable inverse system to a derived limit of the image system.

A right adjoint preserves the countable product occurring in a derived limit, so this is
`isDerivedLimit_map_of_preservesProduct` with the preservation hypothesis discharged. Unlike
`isDerivedLimit_map_rightDerivedFunctor`, nothing is assumed about the exactness of countable
products in the target: that assumption is what the adjunction replaces, and it is exactly the
assumption that fails for sheaves of modules, where products are computed objectwise but
epimorphisms are only local surjections. -/
theorem isDerivedLimit_map_rightAdjoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (G : C ⥤ D) [G.IsRightAdjoint] [G.CommShift ℤ] [G.IsTriangulated]
    (X : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ X.obj ⟨n⟩]
    (K : C) (hK : IsDerivedLimit X K) :
    ∃ h : HasProduct (fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)),
      @IsDerivedLimit D _ _ _ _ _ _ (X ⋙ G) h (G.obj K) := by
  obtain ⟨p, δ, hT⟩ := hK
  have : PreservesLimitsOfSize.{0, 0} G :=
    (Adjunction.ofIsRightAdjoint G).rightAdjoint_preservesLimits
  let h : HasProduct (fun n : ℕ ↦ G.obj (X.obj ⟨n⟩)) :=
    ⟨⟨_, isLimitOfHasProductOfPreservesLimit G (fun n : ℕ ↦ X.obj ⟨n⟩)⟩⟩
  exact ⟨h, G.map p ≫ piComparison G (fun n : ℕ ↦ X.obj ⟨n⟩),
    isDerivedLimit_map_of_preservesProduct G X K p ⟨δ, hT⟩⟩

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [IsGrothendieckAbelian.{w} A]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- A K-injective cochain complex representing a given object of the derived category,
obtained by applying the chosen functorial K-injective resolution to a chosen preimage. -/
private noncomputable def resolution (Y : DerivedCategory A) : CochainComplex A ℤ :=
  (kInjectiveResolutionFunctor A).obj (DerivedCategory.Q.objPreimage Y)

/-- The identification of `resolution Y` with `Y` in the derived category. -/
private noncomputable def resolutionIso (Y : DerivedCategory A) :
    DerivedCategory.Q.obj (resolution Y) ≅ Y :=
  (asIso (DerivedCategory.Q.map ((kInjectiveResolutionInclusion A).app
    (DerivedCategory.Q.objPreimage Y)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Y

/-- The complex `resolution Y` is K-injective. -/
private lemma resolution_isKInjective (Y : DerivedCategory A) :
    (resolution Y).IsKInjective := by
  dsimp [resolution]
  infer_instance

/-- A limit fan indexed by `ULift ℕ` restricts to a limit fan indexed by `ℕ`. -/
def isLimitFanMkULiftDown {C : Type u₁} [Category.{v₁} C] {f : ULift.{w} ℕ → C}
    {c : Fan f} (hc : IsLimit c) : IsLimit (Fan.mk c.pt fun n : ℕ ↦ c.proj ⟨n⟩) :=
  Fan.IsLimit.mk _ (fun s ↦ hc.lift (Fan.mk s.pt fun n ↦ s.proj n.down))
    (fun s n ↦ hc.fac (Fan.mk s.pt fun n ↦ s.proj n.down) ⟨⟨n⟩⟩)
    (fun s m hm ↦ hc.hom_ext fun ⟨⟨n⟩⟩ ↦ by
      rw [hc.fac]
      exact hm n)

/-- The image in the derived category of the termwise product of a countable family of
K-injective complexes is a product. -/
noncomputable def isLimitQMapFanPiOfIsKInjective (I : ℕ → CochainComplex A ℤ)
    (hI : ∀ n, (I n).IsKInjective) :
    IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ I))
      fun n ↦ DerivedCategory.Q.map (Pi.π I n)) := by
  let IT : ULift.{w} ℕ → CochainComplex A ℤ := fun n ↦ I n.down
  let cT := productFanInDerivedCategory IT
  let hcT : IsLimit cT :=
    Classical.choice (isLimit_productFanInDerivedCategory (A := A) IT fun n ↦ hI n.down)
  let pT : Fan I := Fan.mk (∏ᶜ IT) fun n ↦ Pi.π IT ⟨n⟩
  let hpT : IsLimit pT := isLimitFanMkULiftDown (productIsProduct IT)
  refine IsLimit.ofIsoLimit (isLimitFanMkULiftDown hcT) (Cone.ext
    (DerivedCategory.Q.mapIso (hpT.conePointUniqueUpToIso (productIsProduct I))) ?_)
  rintro ⟨n⟩
  dsimp [cT, productFanInDerivedCategory]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  exact (hpT.conePointUniqueUpToIso_hom_comp (productIsProduct I) ⟨n⟩).symm

include F α in
/-- A right derived functor of `F` preserves the product of the images in the derived category
of a countable family of K-injective complexes. -/
lemma preservesLimit_discrete_Q_of_isKInjective (I : ℕ → CochainComplex A ℤ)
    (hI : ∀ n, (I n).IsKInjective) :
    PreservesLimit (Discrete.functor fun n ↦ DerivedCategory.Q.obj (I n)) RF := by
  apply preservesLimit_of_preserves_limit_cone (isLimitQMapFanPiOfIsKInjective I hI)
  let FB := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let J : ℕ → CochainComplex B ℤ := fun n ↦ FB.obj (I n)
  have : PreservesLimitsOfShape (Discrete ℕ) FB := inferInstance
  have : (∏ᶜ I).IsKInjective := KInjectiveProduct.product_mathlib_isKInjective I hI
  have : IsIso ((complexUnit F RF α).app (∏ᶜ I)) := isIso_complexUnit_app F RF α _
  have (n : ℕ) : IsIso ((complexUnit F RF α).app (I n)) := by
    have := hI n
    exact isIso_complexUnit_app F RF α _
  let β : DerivedCategory.Q.obj (∏ᶜ J) ≅ RF.obj (DerivedCategory.Q.obj (∏ᶜ I)) :=
    (DerivedCategory.Q.mapIso (asIso (piComparison FB I))).symm ≪≫
      asIso ((complexUnit F RF α).app (∏ᶜ I))
  let d := Stacks.DerivedProducts.productFanInDerivedCategory J
  let hd := Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory J)
  let eJ : Discrete.functor (fun n ↦ DerivedCategory.Q.obj (J n)) ≅
      Discrete.functor (fun n ↦ DerivedCategory.Q.obj (I n)) ⋙ RF :=
    Discrete.natIso (fun n ↦ asIso ((complexUnit F RF α).app (I n.as)))
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv eJ d).symm hd) (Cone.ext β ?_)
  rintro ⟨n⟩
  dsimp [d, Stacks.DerivedProducts.productFanInDerivedCategory, β, eJ]
  show DerivedCategory.Q.map (Pi.π J n) ≫ (complexUnit F RF α).app (I n) =
    (DerivedCategory.Q.map (inv (piComparison FB I)) ≫
      (complexUnit F RF α).app (∏ᶜ I)) ≫ RF.map (DerivedCategory.Q.map (Pi.π I n))
  rw [Category.assoc, ← dsimp% (complexUnit F RF α).naturality (Pi.π I n),
    ← Category.assoc, ← DerivedCategory.Q.map_comp,
    show inv (piComparison FB I) ≫ FB.map (Pi.π I n) = Pi.π J n by
      rw [← piComparison_comp_π FB I n, IsIso.inv_hom_id_assoc]]

include F α in
/-- A right derived functor of `F` preserves countable products. Both the product in
`DerivedCategory A` and the product in `DerivedCategory B` are computed as termwise products of
K-injective representatives, where `F` preserves the product by hypothesis. -/
lemma preservesLimit_discrete_of_isRightDerivedFunctor
    (G : Functor (Discrete ℕ) (DerivedCategory A)) :
    PreservesLimit G RF := by
  let I : ℕ → CochainComplex A ℤ := fun n ↦ resolution (G.obj ⟨n⟩)
  let e : Discrete.functor (fun n : ℕ ↦ DerivedCategory.Q.obj (I n)) ≅ G :=
    Discrete.natIso (fun n ↦ resolutionIso (G.obj n))
  have := preservesLimit_discrete_Q_of_isKInjective F RF α I fun n ↦ resolution_isKInjective _
  exact preservesLimit_of_iso_diagram RF e

omit [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α in
/-- A right derived functor of an additive functor out of a Grothendieck abelian category is
triangulated. Every object of the derived category is represented by a K-injective complex, and
a distinguished triangle may be completed inside the K-injective complexes, where the unit of
the derived functor is an isomorphism. -/
public lemma rightDerivedFunctor_isTriangulated :
    let := Functor.IsRightDerivedFunctor.commShift RF α
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
    RF.IsTriangulated := by
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  apply Functor.isTriangulated_of_leftExtension RF α
  intro X Y f
  let I := resolution X
  let J := resolution Y
  have : I.IsKInjective := resolution_isKInjective X
  have : J.IsKInjective := resolution_isKInjective Y
  let eI : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≅ X :=
    (DerivedCategory.quotientCompQhIso A).app I ≪≫ resolutionIso X
  let eJ : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj J) ≅ Y :=
    (DerivedCategory.quotientCompQhIso A).app J ≪≫ resolutionIso Y
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj I) J).surjective (eI.hom ≫ f ≫ eJ.inv)
  obtain ⟨Z, g₂, g₃, hT⟩ := distinguished_cocone_triangle g
  have hZ := (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal.ext_of_isTriangulatedClosed₃
    _ hT (CochainComplex.IsKInjective.rightOrthogonal I)
    (CochainComplex.IsKInjective.rightOrthogonal J)
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  have : CochainComplex.IsKInjective L := (CochainComplex.isKInjective_iff_rightOrthogonal L).2 hZ
  exact ⟨Triangle.mk g g₂ g₃, hT, rightDerivedUnit_isIso_at_kInjective _ RF α I,
    rightDerivedUnit_isIso_at_kInjective _ RF α J, rightDerivedUnit_isIso_at_kInjective _ RF α L,
    ⟨Arrow.isoMk eI eJ (by simp [hg])⟩⟩

include F α in
/-- **Stacks 08U1.** The right derived functor of an additive functor from a Grothendieck
abelian category to an abelian category with exact countable products carries every
derived-limit triangle to a derived-limit triangle, if the functor preserves countable
products. Its structural map is the image of the supplied `p`, followed by the canonical
product comparison; hence its projections are `RF.map (p ≫ Pi.π _ n)`. -/
@[stacks 08U1]
theorem isDerivedLimit_map_rightDerivedFunctor (X : ℕᵒᵖ ⥤ DerivedCategory A)
    [HasProduct fun n : ℕ ↦ X.obj ⟨n⟩] (K : DerivedCategory A)
    (p : K ⟶ ∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩)
    (hK : ∃ δ : (∏ᶜ fun n : ℕ ↦ X.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ X.obj ⟨n⟩) (n + 1) ≫
          X.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory A)) :
    ∃ h : HasProduct (fun n : ℕ ↦ RF.obj (X.obj ⟨n⟩)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ RF.obj (X.obj ⟨n⟩)) ⟶ (RF.obj K)⟦(1 : ℤ)⟧,
        Triangle.mk (RF.map p ≫ piComparison RF (fun n : ℕ ↦ X.obj ⟨n⟩))
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ RF.obj (X.obj ⟨n⟩)) n -
            Pi.π (fun n : ℕ ↦ RF.obj (X.obj ⟨n⟩)) (n + 1) ≫
              RF.map (X.map (homOfLE (Nat.le_succ n)).op)) δ ∈
          distTriang (DerivedCategory B) := by
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have := rightDerivedFunctor_isTriangulated F RF α
  have := preservesLimit_discrete_of_isRightDerivedFunctor F RF α
    (Discrete.functor (fun n : ℕ ↦ X.obj ⟨n⟩))
  let h : HasProduct (fun n : ℕ ↦ RF.obj (X.obj ⟨n⟩)) :=
    ⟨⟨_, isLimitOfHasProductOfPreservesLimit RF (fun n : ℕ ↦ X.obj ⟨n⟩)⟩⟩
  exact ⟨h, isDerivedLimit_map_of_preservesProduct RF X K p hK⟩

end Stacks.Injectives

end
