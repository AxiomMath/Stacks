module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.CoverSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.InjectiveDegreewiseSurjectivity
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearDerivedSections

/-!
# The unbounded Mayer--Vietoris triangle over the ring of global functions

Let `(X, 𝒪_X)` be a ringed space, let `A = Γ(X, 𝒪_X)`, and let `X = U ∪ V` be a union of two
open subsets. Every object `E` of `D(𝒪_X)` sits in a distinguished triangle

`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ∩ V, E) ⟶ RΓ(X, E)⟦1⟧`

functorially in `E`. This file produces that triangle in the derived category `D(A)` of
`A`-modules, for the `A`-linear derived sections functors `RΓ(W, -) : D(𝒪_X) ⥤ D(A)`.

## Main definitions

* `Stacks.Cohomology.LinearMayerVietoris.coverSections`: the direct sum
  `ℱ(U) ⊕ ℱ(V)` of `A`-linear sections, the middle term of the Mayer--Vietoris sequence.
* `Stacks.Cohomology.LinearMayerVietoris.coverFirst` and
  `Stacks.Cohomology.LinearMayerVietoris.coverSecond`: the two maps
  `ℱ(X) ⟶ ℱ(U) ⊕ ℱ(V) ⟶ ℱ(U ∩ V)` of the Mayer--Vietoris sequence, the second with the usual
  sign on the summand over `V`, built from the two projections
  `Stacks.Cohomology.LinearMayerVietoris.coverFst`,
  `Stacks.Cohomology.LinearMayerVietoris.coverSnd` and the two inclusions
  `Stacks.Cohomology.LinearMayerVietoris.coverInl`,
  `Stacks.Cohomology.LinearMayerVietoris.coverInr` of the direct sum.

## Main results

* `Stacks.Cohomology.LinearMayerVietoris.shortExact_coverSections`: the Mayer--Vietoris
  sequence of `A`-linear sections is short exact at every injective sheaf of modules.
* `Stacks.Cohomology.LinearMayerVietoris.linearUnboundedMayerVietoris`: the functorial
  distinguished Mayer--Vietoris triangle in `D(A)` of the `A`-linear derived sections functors
  for a cover by two opens.

The long exact cohomology sequence obtained from this triangle is
`Stacks.Cohomology.LinearMayerVietoris.linearUnboundedMayerVietoris_longExact`, in
`StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearUnboundedLongExact`.

## References

* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.LinearDerivedSections

universe w w₁ w₂ v₁ v₂ u₁ u₂ u

namespace Stacks.Cohomology.LinearMayerVietoris

/-! ### Biproduct bookkeeping -/

section Biprod

variable {C : Type u₁} [Category.{v₁} C]

/-- Cancelling an inverse pair at the head of a composite. -/
private lemma inv_hom_comp_cancel {P Q R : C} (u : P ⟶ Q) (v : Q ⟶ P) (huv : u ≫ v = 𝟙 P)
    (f : P ⟶ R) : u ≫ v ≫ f = f := by
  rw [← Category.assoc, huv, Category.id_comp]

section HasZero

variable [HasZeroMorphisms C]

/-- A map followed by a lift is the lift of the two composites. -/
private lemma comp_lift_eq {P P' Y Z : C} [HasBinaryBiproduct Y Z] (f : P' ⟶ P) (x : P ⟶ Y)
    (y : P ⟶ Z) (x' : P' ⟶ Y) (y' : P' ⟶ Z) (hx : f ≫ x = x') (hy : f ≫ y = y') :
    f ≫ biprod.lift x y = biprod.lift x' y' := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst, hx, biprod.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, hy, biprod.lift_snd]

/-- A descent followed by a map is the descent of the two composites. -/
private lemma desc_comp_eq {Y Z S S' : C} [HasBinaryBiproduct Y Z] (x : Y ⟶ S) (y : Z ⟶ S)
    (f : S ⟶ S') (x' : Y ⟶ S') (y' : Z ⟶ S') (hx : x ≫ f = x') (hy : y ≫ f = y') :
    biprod.desc x y ≫ f = biprod.desc x' y' := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, biprod.inl_desc, hx, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_desc, hy, biprod.inr_desc]

/-- A lift followed by an isomorphism of biproducts is again a lift. -/
private lemma lift_mapIso_eq {P Y Z Y' Z' : C} [HasBinaryBiproduct Y Z]
    [HasBinaryBiproduct Y' Z'] (x : P ⟶ Y) (y : P ⟶ Z) (a : Y ≅ Y') (b : Z ≅ Z')
    (x' : P ⟶ Y') (y' : P ⟶ Z') (hx : x ≫ a.hom = x') (hy : y ≫ b.hom = y') :
    biprod.lift x y ≫ (biprod.mapIso a b).hom = biprod.lift x' y' := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.mapIso_hom, biprod.map_fst, biprod.lift_fst_assoc, hx,
      biprod.lift_fst]
  · rw [Category.assoc, biprod.mapIso_hom, biprod.map_snd, biprod.lift_snd_assoc, hy,
      biprod.lift_snd]

/-- An isomorphism of biproducts followed by a descent is again a descent. -/
private lemma mapIso_desc_eq {Y Z Y' Z' S : C} [HasBinaryBiproduct Y Z]
    [HasBinaryBiproduct Y' Z'] (a : Y ≅ Y') (b : Z ≅ Z') (p : Y' ⟶ S) (q : Z' ⟶ S)
    (p' : Y ⟶ S) (q' : Z ⟶ S) (hp : a.hom ≫ p = p') (hq : b.hom ≫ q = q') :
    (biprod.mapIso a b).hom ≫ biprod.desc p q = biprod.desc p' q' := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inl_desc, hp, biprod.inl_desc]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc, hq, biprod.inr_desc]

end HasZero

section Pre

variable [Preadditive C]

/-- A map into a biproduct built from a splitting of its source is an isomorphism: the five
equations of a bicone make the two descriptions mutually inverse. -/
private def biprodIsoOfTotal {P Y Z : C} [HasBinaryBiproduct Y Z] (p : P ⟶ Y) (q : P ⟶ Z)
    (i : Y ⟶ P) (j : Z ⟶ P) (hip : i ≫ p = 𝟙 Y) (hjq : j ≫ q = 𝟙 Z) (hiq : i ≫ q = 0)
    (hjp : j ≫ p = 0) (htot : p ≫ i + q ≫ j = 𝟙 P) : P ≅ Y ⊞ Z where
  hom := biprod.lift p q
  inv := biprod.desc i j
  hom_inv_id := by rw [biprod.lift_desc, htot]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_desc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, hip, biprod.inl_fst]
      · rw [Category.assoc, biprod.lift_snd, hiq, biprod.inl_snd]
    · rw [← Category.assoc, biprod.inr_desc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, hjp, biprod.inr_fst]
      · rw [Category.assoc, biprod.lift_snd, hjq, biprod.inr_snd]

/-- Transporting a splitting of an object along isomorphisms of the two summands: the apex of a
bicone is the biproduct of any two objects isomorphic to its legs. -/
private def biprodIsoOfTotal' {P Y Z Y' Z' : C} [HasBinaryBiproduct Y' Z'] (p : P ⟶ Y)
    (q : P ⟶ Z) (i : Y ⟶ P) (j : Z ⟶ P) (a : Y ≅ Y') (b : Z ≅ Z') (hip : i ≫ p = 𝟙 Y)
    (hjq : j ≫ q = 𝟙 Z) (hiq : i ≫ q = 0) (hjp : j ≫ p = 0)
    (htot : p ≫ i + q ≫ j = 𝟙 P) : P ≅ Y' ⊞ Z' :=
  biprodIsoOfTotal (p ≫ a.hom) (q ≫ b.hom) (a.inv ≫ i) (b.inv ≫ j)
    (by rw [Category.assoc, ← Category.assoc i, hip, Category.id_comp, a.inv_hom_id])
    (by rw [Category.assoc, ← Category.assoc j, hjq, Category.id_comp, b.inv_hom_id])
    (by rw [Category.assoc, ← Category.assoc i, hiq, zero_comp, comp_zero])
    (by rw [Category.assoc, ← Category.assoc j, hjp, zero_comp, comp_zero])
    (by rw [Category.assoc, Category.assoc, ← Category.assoc a.hom, a.hom_inv_id,
      Category.id_comp, ← Category.assoc b.hom, b.hom_inv_id, Category.id_comp, htot])

/-- The map of biproducts attached to a pair of sums is the sum of the maps. -/
private lemma biprod_map_add {Y Z Y' Z' : C} [HasBinaryBiproduct Y Z]
    [HasBinaryBiproduct Y' Z'] (a a' : Y ⟶ Y') (b b' : Z ⟶ Z') :
    biprod.map (a + a') (b + b') = biprod.map a b + biprod.map a' b' := by
  apply biprod.hom_ext <;> simp [Preadditive.add_comp]

/-- Moving a sign out of the middle of a composite. -/
private lemma comp_neg_comp {P Q R S : C} (u : P ⟶ Q) (v : Q ⟶ R) (f : R ⟶ S) :
    u ≫ (-v) ≫ f = -(u ≫ v ≫ f) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg]

/-- A commuting square of morphisms stays commuting after negating one pair of parallel
sides. -/
private lemma neg_comp_eq {P Q R S : C} (x : P ⟶ Q) (f : Q ⟶ R) (b : P ⟶ S) (y : S ⟶ R)
    (h : x ≫ f = b ≫ y) : (-x) ≫ f = b ≫ (-y) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

end Pre

end Biprod

/-! ### Right derived functors computed on a K-injective resolution -/

section Derived

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [IsGrothendieckAbelian.{w} C]

variable (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- A chosen right derived functor is computed by the functorial K-injective resolution:
applying `F` degreewise to the resolution and localizing agrees with `RF`. -/
private def resolutionIso :
    Stacks.Injectives.kInjectiveResolutionFunctor C ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF := by
  have ha : ∀ K, IsIso ((Functor.whiskerLeft (Stacks.Injectives.kInjectiveResolutionFunctor C)
      (Stacks.Injectives.complexUnit F RF α)).app K) := fun _ =>
    Stacks.Injectives.isIso_complexUnit_app F RF α _
  have hb : ∀ K, IsIso ((Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion C)
      (DerivedCategory.Q ⋙ RF)).app K) := fun K =>
    RF.map_isIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K))
  have : IsIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor C) (Stacks.Injectives.complexUnit F RF α)) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion C) (DerivedCategory.Q ⋙ RF)) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor C) (Stacks.Injectives.complexUnit F RF α)) ≪≫
    (asIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion C) (DerivedCategory.Q ⋙ RF))).symm

/-- The two legs of `resolutionIso`, spelled out. -/
private lemma resolutionIso_hom_app (K : CochainComplex C ℤ) :
    (resolutionIso F RF α).hom.app K =
      (Stacks.Injectives.complexUnit F RF α).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj K) ≫
        inv (RF.map (DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K))) := by
  simp [resolutionIso, NatIso.isIso_inv_app]

/-- A formal diagram chase: if `f ≫ g = g' ≫ f'`, `a ≫ g' = m ≫ b` and `n ≫ p' = p ≫ m`, then
`(p ≫ a ≫ f) ≫ g = n ≫ p' ≫ b ≫ f'`. -/
private lemma squareChase {D' : Type*} [Category D'] {P P' Q₁ Q₂ R₁ R₂ S T : D'}
    (p : P ⟶ Q₁) (a : Q₁ ⟶ R₁) (f : R₁ ⟶ S) (g : S ⟶ T) (g' : R₁ ⟶ R₂) (f' : R₂ ⟶ T)
    (m : Q₁ ⟶ Q₂) (b : Q₂ ⟶ R₂) (n : P ⟶ P') (p' : P' ⟶ Q₂)
    (hn : f ≫ g = g' ≫ f') (hh : a ≫ g' = m ≫ b) (hi : n ≫ p' = p ≫ m) :
    (p ≫ a ≫ f) ≫ g = n ≫ p' ≫ b ≫ f' := by
  rw [Category.assoc, Category.assoc, hn, reassoc_of% hh, ← reassoc_of% hi]

/-- Cancelling two isomorphisms across a commuting square: if `b ≫ y = x ≫ z` with `b` and `z`
isomorphisms, then `inv b ≫ x = y ≫ inv z`. -/
private lemma invCompComm {D' : Type*} [Category D'] {P Q R S : D'} (b : P ⟶ Q) [IsIso b]
    (y : Q ⟶ S) (x : P ⟶ R) (z : R ⟶ S) [IsIso z] (h : b ≫ y = x ≫ z) :
    inv b ≫ x = y ≫ inv z := by
  rw [IsIso.inv_comp_eq, reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]

/-- The second formal chase: transporting a square across one inverted leg. -/
private lemma compInvChase {D' : Type*} [Category D'] {P P' Q Q' R R' : D'} (a : P ⟶ Q)
    (ib : Q ⟶ R) (rR : R ⟶ R') (rQ : Q ⟶ Q') (ib' : Q' ⟶ R') (n : P ⟶ P') (a' : P' ⟶ Q')
    (h1 : ib ≫ rR = rQ ≫ ib') (h2 : a ≫ rQ = n ≫ a') :
    (a ≫ ib) ≫ rR = n ≫ a' ≫ ib' := by
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

variable {F}

omit [IsGrothendieckAbelian.{w} C]
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] in
/-- The complex-level comparison maps are compatible with a map of the underlying functors. -/
private lemma complexUnit_fac {G : C ⥤ D} [G.Additive]
    {RG : DerivedCategory C ⥤ DerivedCategory D}
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG) (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β) :
    Stacks.Injectives.complexUnit F RF α ≫ Functor.whiskerLeft DerivedCategory.Q r =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
        DerivedCategory.Q ≫ Stacks.Injectives.complexUnit G RG β := by
  refine NatTrans.ext (funext fun K => ?_)
  have hn : RF.map ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
        r.app (DerivedCategory.Q.obj K) =
      r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        RG.map ((DerivedCategory.quotientCompQhIso C).hom.app K) :=
    r.naturality ((DerivedCategory.quotientCompQhIso C).hom.app K)
  have hh : α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        r.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
        β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    congr_app h ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hi : DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso D).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) :=
    (DerivedCategory.quotientCompQhIso D).inv.naturality
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)
  exact squareChase _ _ _ _ _ _ _ _ _ _ hn hh hi

/-- The comparisons with the K-injective resolution are compatible with a map of the underlying
functors. -/
private lemma resolutionIso_fac {G : C ⥤ D} [G.Additive]
    {RG : DerivedCategory C ⥤ DerivedCategory D}
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β)
    (K : CochainComplex C ℤ) :
    (resolutionIso F RF α).hom.app K ≫ r.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj K)) ≫
        (resolutionIso G RG β).hom.app K := by
  have hF : IsIso (RF.map (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K))) := RF.map_isIso _
  have hG : IsIso (RG.map (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K))) := RG.map_isIso _
  rw [resolutionIso_hom_app, resolutionIso_hom_app]
  exact compInvChase _ _ _ _ _ _ _
    (invCompComm _ _ _ _ (r.naturality (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion C).app K))))
    (congr_app (complexUnit_fac RF α β τ r h)
      ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj K))

end Derived

/-! ### The Mayer--Vietoris sequence of `A`-linear sections -/

section Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.isGrothendieckAbelianU

variable (X : RingedSpace.{u, u}) (U V : Opens X.carrier)

/-- The middle term of the Mayer--Vietoris sequence: the direct sum `ℱ(U) ⊕ ℱ(V)` of the
`A`-linear sections of a sheaf of `𝒪_X`-modules over `U` and over `V`, for
`A = Γ(X, 𝒪_X)`. -/
def coverSections : SheafOfModules.{u} (structureSheafRing X) ⥤ ModuleCat.{u} (baseRing X) where
  obj M := (linearSections X U).obj M ⊞ (linearSections X V).obj M
  map f := biprod.map ((linearSections X U).map f) ((linearSections X V).map f)
  map_id _ := by apply biprod.hom_ext <;> simp
  map_comp _ _ := by apply biprod.hom_ext <;> simp

/-- The middle term of the Mayer--Vietoris sequence is an additive functor. -/
instance coverSections_additive : (coverSections X U V).Additive where
  map_add {_ _ f g} := by
    change biprod.map ((linearSections X U).map (f + g))
      ((linearSections X V).map (f + g)) = _
    rw [(linearSections X U).map_add, (linearSections X V).map_add, biprod_map_add]
    rfl

/-- The projection of the middle term of the Mayer--Vietoris sequence to the sections over
`U`. -/
def coverFst : coverSections X U V ⟶ linearSections X U where
  app _ := biprod.fst
  naturality _ _ _ := by simp [coverSections]

/-- The projection of the middle term of the Mayer--Vietoris sequence to the sections over
`V`. -/
def coverSnd : coverSections X U V ⟶ linearSections X V where
  app _ := biprod.snd
  naturality _ _ _ := by simp [coverSections]

/-- The inclusion of the sections over `U` into the middle term of the Mayer--Vietoris
sequence. -/
def coverInl : linearSections X U ⟶ coverSections X U V where
  app _ := biprod.inl
  naturality _ _ _ := by simp [coverSections]

/-- The inclusion of the sections over `V` into the middle term of the Mayer--Vietoris
sequence. -/
def coverInr : linearSections X V ⟶ coverSections X U V where
  app _ := biprod.inr
  naturality _ _ _ := by simp [coverSections]

/-- **The first map of the Mayer--Vietoris sequence**, the pair of the two restrictions
`ℱ(X) ⟶ ℱ(U) ⊕ ℱ(V)`. -/
def coverFirst : linearSections X ⊤ ⟶ coverSections X U V where
  app M := biprod.lift ((linearRestriction X (le_top : U ≤ ⊤)).app M)
    ((linearRestriction X (le_top : V ≤ ⊤)).app M)
  naturality _ _ f := by
    apply biprod.hom_ext
    · simpa [coverSections] using (linearRestriction X (le_top : U ≤ ⊤)).naturality f
    · simpa [coverSections] using (linearRestriction X (le_top : V ≤ ⊤)).naturality f

/-- **The second map of the Mayer--Vietoris sequence**, the difference of the two restrictions
`ℱ(U) ⊕ ℱ(V) ⟶ ℱ(U ∩ V)`. -/
def coverSecond : coverSections X U V ⟶ linearSections X (U ⊓ V) where
  app M := biprod.desc ((linearRestriction X (inf_le_left : U ⊓ V ≤ U)).app M)
    (-((linearRestriction X (inf_le_right : U ⊓ V ≤ V)).app M))
  naturality _ _ f := by
    apply biprod.hom_ext'
    · simpa [coverSections] using
        (linearRestriction X (inf_le_left : U ⊓ V ≤ U)).naturality f
    · simpa [coverSections, Preadditive.comp_neg, Preadditive.neg_comp] using
        (linearRestriction X (inf_le_right : U ⊓ V ≤ V)).naturality f

/-- The first projection of the first map of the Mayer--Vietoris sequence is the restriction
to `U`. -/
lemma coverFirst_comp_coverFst :
    coverFirst X U V ≫ coverFst X U V = linearRestriction X (le_top : U ≤ ⊤) :=
  NatTrans.ext (funext fun _ => biprod.lift_fst _ _)

/-- The second projection of the first map of the Mayer--Vietoris sequence is the restriction
to `V`. -/
lemma coverFirst_comp_coverSnd :
    coverFirst X U V ≫ coverSnd X U V = linearRestriction X (le_top : V ≤ ⊤) :=
  NatTrans.ext (funext fun _ => biprod.lift_snd _ _)

/-- On the summand of sections over `U`, the second map of the Mayer--Vietoris sequence is the
restriction to `U ∩ V`. -/
lemma coverInl_comp_coverSecond :
    coverInl X U V ≫ coverSecond X U V =
      linearRestriction X (inf_le_left : U ⊓ V ≤ U) :=
  NatTrans.ext (funext fun _ => biprod.inl_desc _ _)

/-- On the summand of sections over `V`, the second map of the Mayer--Vietoris sequence is minus
the restriction to `U ∩ V`. -/
lemma coverInr_comp_coverSecond :
    coverInr X U V ≫ coverSecond X U V =
      -linearRestriction X (inf_le_right : U ⊓ V ≤ V) :=
  NatTrans.ext (funext fun _ => biprod.inr_desc _ _)

/-- The two maps of the Mayer--Vietoris sequence compose to zero. -/
lemma coverFirst_comp_coverSecond : coverFirst X U V ≫ coverSecond X U V = 0 := by
  refine NatTrans.ext (funext fun M => ?_)
  change biprod.lift _ _ ≫ biprod.desc _ _ = 0
  rw [biprod.lift_desc, Preadditive.comp_neg, ← NatTrans.comp_app, ← NatTrans.comp_app,
    linearRestriction_comp, linearRestriction_comp]
  simp

/-! ### Short exactness at an injective sheaf of modules -/

/-- The square of two open subsets covering the space is a Mayer--Vietoris square. -/
private def coverMayerVietorisSquare (hUV : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology X.carrier).MayerVietorisSquare :=
  Opens.mayerVietorisSquare' (coverSquare U V hUV) (hUV.symm.trans (sup_comm U V)) (inf_comm U V)

/-- The `A`-linear sections of a sheaf of modules over a cover `X = U ∪ V` by two opens form a
pullback square of `A`-modules. -/
lemma isPullback_linearSections (hUV : U ⊔ V = ⊤) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsPullback ((linearRestriction X (le_top : U ≤ ⊤)).app M)
      ((linearRestriction X (le_top : V ≤ ⊤)).app M)
      ((linearRestriction X (inf_le_left : U ⊓ V ≤ U)).app M)
      ((linearRestriction X (inf_le_right : U ⊓ V ≤ V)).app M) := by
  refine IsPullback.of_map (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}) ?_ ?_
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, linearRestriction_comp,
      linearRestriction_comp]
  · exact ((coverMayerVietorisSquare X U V hUV).sheafCondition_of_sheaf
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj M) : IsPullback _ _ _ _).flip

/-- Restriction of the `A`-linear sections of an injective sheaf of modules is an
epimorphism. -/
lemma epi_linearRestriction (M : SheafOfModules.{u} (structureSheafRing X)) [Injective M]
    {Z W : Opens X.carrier} (h : Z ≤ W) : Epi ((linearRestriction X h).app M) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
    (structureSheafRing X) M h

/-- The Mayer--Vietoris sequence `0 → ℱ(X) → ℱ(U) ⊕ ℱ(V) → ℱ(U ∩ V) → 0` of `A`-linear
sections is short exact at an injective sheaf of modules `ℱ`, for a cover `X = U ∪ V`. -/
lemma shortExact_coverSections (hUV : U ⊔ V = ⊤) (M : SheafOfModules.{u} (structureSheafRing X))
    [Injective M] :
    (ShortComplex.mk ((coverFirst X U V).app M) ((coverSecond X U V).app M)
      (NatTrans.congr_app (coverFirst_comp_coverSecond X U V) M)).ShortExact := by
  have := epi_linearRestriction X M (inf_le_right : U ⊓ V ≤ V)
  exact Stacks.Cohomology.MayerVietoris.shortExact_of_isPullback
    (isPullback_linearSections X U V hUV M) _

/-! ### The Mayer--Vietoris sequence applied degreewise to a complex -/

/-- The chosen functorial K-injective resolution of complexes of `𝒪_X`-modules, the resolution
on which the derived sections functors are computed. -/
private abbrev resolution :=
  Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} (structureSheafRing X))

section Complexes

variable (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- The inclusion of the summand over `U` followed by the projection to it is the identity,
degreewise on a complex. -/
private lemma complexInl_comp_Fst :
    (NatTrans.mapHomologicalComplex (coverInl X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverFst X U V) (ComplexShape.up ℤ)).app I = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_fst

/-- The inclusion of the summand over `V` followed by the projection to it is the identity,
degreewise on a complex. -/
private lemma complexInr_comp_Snd :
    (NatTrans.mapHomologicalComplex (coverInr X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverSnd X U V) (ComplexShape.up ℤ)).app I = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_snd

/-- The inclusion of the summand over `U` followed by the projection to the one over `V`
vanishes, degreewise on a complex. -/
private lemma complexInl_comp_Snd :
    (NatTrans.mapHomologicalComplex (coverInl X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverSnd X U V) (ComplexShape.up ℤ)).app I = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inl_snd

/-- The inclusion of the summand over `V` followed by the projection to the one over `U`
vanishes, degreewise on a complex. -/
private lemma complexInr_comp_Fst :
    (NatTrans.mapHomologicalComplex (coverInr X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverFst X U V) (ComplexShape.up ℤ)).app I = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.inr_fst

/-- The two projections and the two inclusions exhibit the middle term as a direct sum,
degreewise on a complex. -/
private lemma complex_total :
    (NatTrans.mapHomologicalComplex (coverFst X U V) (ComplexShape.up ℤ)).app I ≫
          (NatTrans.mapHomologicalComplex (coverInl X U V) (ComplexShape.up ℤ)).app I +
        (NatTrans.mapHomologicalComplex (coverSnd X U V) (ComplexShape.up ℤ)).app I ≫
          (NatTrans.mapHomologicalComplex (coverInr X U V) (ComplexShape.up ℤ)).app I = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => biprod.total

/-- The two maps of the Mayer--Vietoris sequence compose to zero degreewise on a complex. -/
private lemma complexFirst_comp_Second :
    (NatTrans.mapHomologicalComplex (coverFirst X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app I = 0 :=
  HomologicalComplex.hom_ext _ _ fun n =>
    NatTrans.congr_app (coverFirst_comp_coverSecond X U V) (I.X n)

/-- The inclusion of the summand over `U` followed by the second map of the Mayer--Vietoris
sequence, degreewise on a complex. -/
private lemma complexInl_comp_Second :
    (NatTrans.mapHomologicalComplex (coverInl X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app I =
      (NatTrans.mapHomologicalComplex (linearRestriction X (inf_le_left : U ⊓ V ≤ U))
        (ComplexShape.up ℤ)).app I := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, coverInl_comp_coverSecond]

/-- The inclusion of the summand over `V` followed by the second map of the Mayer--Vietoris
sequence, degreewise on a complex. -/
private lemma complexInr_comp_Second :
    (NatTrans.mapHomologicalComplex (coverInr X U V) (ComplexShape.up ℤ)).app I ≫
        (NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app I =
      -(NatTrans.mapHomologicalComplex (linearRestriction X (inf_le_right : U ⊓ V ≤ V))
        (ComplexShape.up ℤ)).app I := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, coverInr_comp_coverSecond]
  refine HomologicalComplex.hom_ext _ _ (fun _ => ?_)
  rfl

/-- The Mayer--Vietoris sequence of complexes of `A`-modules attached to a complex of
`𝒪_X`-modules with injective terms is short exact. -/
private lemma shortExact_complexCover (hUV : U ⊔ V = ⊤)
    (hI : ∀ n, Injective (I.X n)) :
    (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex (coverFirst X U V) (ComplexShape.up ℤ)).app I)
      ((NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app I)
      (complexFirst_comp_Second X U V I)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => have := hI n; shortExact_coverSections X U V hUV _

end Complexes

/-! ### Comparison with the chosen resolution -/

/-- The comparison of the `A`-linear derived sections over `W` with their value on the chosen
K-injective resolution. -/
private def sectionsResolutionIso (W : Opens X.carrier) :
    resolution X ⋙ (linearSections X W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ derivedLinearSections X W :=
  resolutionIso (linearSections X W) (derivedLinearSections X W)
    (derivedLinearSectionsUnit X W)

/-- The defining compatibility of the right-derived restriction map with the comparison maps of
the `A`-linear derived sections functors. -/
private lemma derivedLinearRestriction_fac {Z W : Opens X.carrier} (h : Z ≤ W) :
    derivedLinearSectionsUnit X W ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedLinearRestriction X h) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (linearRestriction X h) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫
        derivedLinearSectionsUnit X Z :=
  Functor.rightDerivedNatTrans_fac (derivedLinearSections X W) (derivedLinearSections X Z)
    (derivedLinearSectionsUnit X W) (derivedLinearSectionsUnit X Z) (quasiIsos X)
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (linearRestriction X h) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The comparisons with the chosen resolution carry the restriction of sections onto the
right-derived restriction. -/
private lemma sectionsResolutionIso_fac {Z W : Opens X.carrier} (h : Z ≤ W)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (sectionsResolutionIso X W).hom.app K ≫
        (derivedLinearRestriction X h).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (linearRestriction X h)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
        (sectionsResolutionIso X Z).hom.app K :=
  resolutionIso_fac _ _ _ _ _ (derivedLinearRestriction_fac X h) K

variable (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- The Mayer--Vietoris sequence of the chosen K-injective resolution is short exact. -/
private lemma shortExact_resolutionCover (hUV : U ⊔ V = ⊤) :
    (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex (coverFirst X U V) (ComplexShape.up ℤ)).app
        ((resolution X).obj K))
      ((NatTrans.mapHomologicalComplex (coverSecond X U V) (ComplexShape.up ℤ)).app
        ((resolution X).obj K))
      (complexFirst_comp_Second X U V ((resolution X).obj K))).ShortExact :=
  shortExact_complexCover X U V ((resolution X).obj K) hUV (fun _ => inferInstance)

/-- The middle term of the Mayer--Vietoris triangle: the sections of the chosen resolution
over `U` and over `V`, localized, form the biproduct of the two derived sections. -/
private def middleComparison :
    DerivedCategory.Q.obj (((coverSections X U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((resolution X).obj K)) ≅
      (derivedLinearSections X U).obj (DerivedCategory.Q.obj K) ⊞
        (derivedLinearSections X V).obj (DerivedCategory.Q.obj K) :=
  biprodIsoOfTotal'
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverFst X U V)
      (ComplexShape.up ℤ)).app ((resolution X).obj K)))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverSnd X U V)
      (ComplexShape.up ℤ)).app ((resolution X).obj K)))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInl X U V)
      (ComplexShape.up ℤ)).app ((resolution X).obj K)))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInr X U V)
      (ComplexShape.up ℤ)).app ((resolution X).obj K)))
    ((sectionsResolutionIso X U).app K) ((sectionsResolutionIso X V).app K)
    (by rw [← DerivedCategory.Q.map_comp, complexInl_comp_Fst, DerivedCategory.Q.map_id])
    (by rw [← DerivedCategory.Q.map_comp, complexInr_comp_Snd, DerivedCategory.Q.map_id])
    (by rw [← DerivedCategory.Q.map_comp, complexInl_comp_Snd, DerivedCategory.Q.map_zero])
    (by rw [← DerivedCategory.Q.map_comp, complexInr_comp_Fst, DerivedCategory.Q.map_zero])
    (by rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_add, complex_total, DerivedCategory.Q.map_id])

/-- The forward map of the comparison of the middle term. -/
private lemma middleComparison_hom :
    (middleComparison X U V K).hom =
      biprod.lift
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverFst X U V)
            (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
          (sectionsResolutionIso X U).hom.app K)
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverSnd X U V)
            (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
          (sectionsResolutionIso X V).hom.app K) :=
  rfl

/-- The inverse map of the comparison of the middle term. -/
private lemma middleComparison_inv :
    (middleComparison X U V K).inv =
      biprod.desc
        ((sectionsResolutionIso X U).inv.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInl X U V)
            (ComplexShape.up ℤ)).app ((resolution X).obj K)))
        ((sectionsResolutionIso X V).inv.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInr X U V)
            (ComplexShape.up ℤ)).app ((resolution X).obj K))) :=
  rfl

/-- The first map of the Mayer--Vietoris sequence of the chosen resolution, followed by the
localized projection to the sections over `W`, is the right-derived restriction to `W`. -/
private lemma map_coverFirst_comp_map_proj {W : Opens X.carrier} (h : W ≤ ⊤)
    (π : coverSections X U V ⟶ linearSections X W)
    (hπ : coverFirst X U V ≫ π = linearRestriction X h) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverFirst X U V)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
          (sectionsResolutionIso X W).hom.app K) =
      (sectionsResolutionIso X ⊤).hom.app K ≫
        (derivedLinearRestriction X h).app (DerivedCategory.Q.obj K) := by
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, hπ]
  exact (sectionsResolutionIso_fac X h K).symm

/-- The first map of the Mayer--Vietoris sequence of the chosen resolution is the pair of the
right-derived restrictions to `U` and to `V`. -/
private lemma map_coverFirst_comp_middleComparison :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverFirst X U V)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
      (middleComparison X U V K).hom =
    (sectionsResolutionIso X ⊤).hom.app K ≫
      biprod.lift
        ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app (DerivedCategory.Q.obj K))
        ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app (DerivedCategory.Q.obj K)) := by
  rw [middleComparison_hom]
  exact (comp_lift_eq _ _ _ _ _
    (map_coverFirst_comp_map_proj X U V K _ _ (coverFirst_comp_coverFst X U V))
    (map_coverFirst_comp_map_proj X U V K _ _ (coverFirst_comp_coverSnd X U V))).trans
    (comp_lift_eq ((sectionsResolutionIso X ⊤).hom.app K) _ _ _ _ rfl rfl).symm

/-- The localized restriction of sections of the chosen resolution, between the comparison
isomorphisms, is the right-derived restriction. -/
private lemma inv_comp_map_restriction_comp {Z W : Opens X.carrier} (h : Z ≤ W) :
    (sectionsResolutionIso X W).inv.app K ≫
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (linearRestriction X h)
          (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
        (sectionsResolutionIso X Z).hom.app K) =
      (derivedLinearRestriction X h).app (DerivedCategory.Q.obj K) := by
  rw [← sectionsResolutionIso_fac X h K]
  exact inv_hom_comp_cancel _ _ (congr_app (sectionsResolutionIso X W).inv_hom_id K) _

/-- On the summand of sections over `U`, the second map of the Mayer--Vietoris sequence of the
chosen resolution is the right-derived restriction to `U ∩ V`. -/
private lemma coverInl_comp_map_coverSecond :
    ((sectionsResolutionIso X U).inv.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInl X U V)
          (ComplexShape.up ℤ)).app ((resolution X).obj K))) ≫
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverSecond X U V)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
          (sectionsResolutionIso X (U ⊓ V)).hom.app K) =
      (derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app
        (DerivedCategory.Q.obj K) := by
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map _),
    ← DerivedCategory.Q.map_comp, complexInl_comp_Second]
  exact inv_comp_map_restriction_comp X K _

/-- On the summand of sections over `V`, the second map of the Mayer--Vietoris sequence of the
chosen resolution is minus the right-derived restriction to `U ∩ V`. -/
private lemma coverInr_comp_map_coverSecond :
    ((sectionsResolutionIso X V).inv.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverInr X U V)
          (ComplexShape.up ℤ)).app ((resolution X).obj K))) ≫
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverSecond X U V)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
          (sectionsResolutionIso X (U ⊓ V)).hom.app K) =
      -((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app
        (DerivedCategory.Q.obj K)) := by
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map _),
    ← DerivedCategory.Q.map_comp, complexInr_comp_Second, DerivedCategory.Q.map_neg]
  exact (comp_neg_comp _ _ _).trans (congrArg Neg.neg (inv_comp_map_restriction_comp X K _))

/-- The second map of the Mayer--Vietoris sequence of the chosen resolution is the difference of
the right-derived restrictions to `U ∩ V`. -/
private lemma middleComparison_inv_comp_map_coverSecond :
    (middleComparison X U V K).inv ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (coverSecond X U V)
        (ComplexShape.up ℤ)).app ((resolution X).obj K)) ≫
        (sectionsResolutionIso X (U ⊓ V)).hom.app K =
    biprod.desc
      ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app (DerivedCategory.Q.obj K))
      (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app
        (DerivedCategory.Q.obj K))) := by
  rw [middleComparison_inv]
  exact desc_comp_eq _ _ _ _ _ (coverInl_comp_map_coverSecond X U V K)
    (coverInr_comp_map_coverSecond X U V K)

/-! ### The distinguished triangle -/

/-- The connecting map of the Mayer--Vietoris sequence of the chosen resolution, natural in the
complex. -/
private def coverBoundary (hUV : U ⊔ V = ⊤) :
    resolution X ⋙ (linearSections X (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      (resolution X ⋙ (linearSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (shortExact_resolutionCover X U V K hUV)
  naturality K L k :=
    (DerivedCategory.triangleOfSESδ_naturality (shortExact_resolutionCover X U V K hUV)
      (shortExact_resolutionCover X U V L hUV)
      { τ₁ := ((linearSections X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolution X).map k)
        τ₂ := ((coverSections X U V).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolution X).map k)
        τ₃ := ((linearSections X (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((resolution X).map k)
        comm₁₂ := (NatTrans.mapHomologicalComplex (coverFirst X U V)
          (ComplexShape.up ℤ)).naturality ((resolution X).map k)
        comm₂₃ := (NatTrans.mapHomologicalComplex (coverSecond X U V)
          (ComplexShape.up ℤ)).naturality ((resolution X).map k) }).symm

/-- The Mayer--Vietoris triangle of the chosen resolution is distinguished, and agrees with the
triangle of the right-derived restriction maps at the localization of a complex. -/
private lemma distTriang_of_Q_obj (hUV : U ⊔ V = ⊤)
    (δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ))
    (hδ : δ.app (DerivedCategory.Q.obj K) =
      (sectionsResolutionIso X (U ⊓ V)).inv.app K ≫ (coverBoundary X U V hUV).app K ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)).map
          ((sectionsResolutionIso X ⊤).hom.app K)) :
    Triangle.mk
        (biprod.lift
          ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app (DerivedCategory.Q.obj K))
          ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app (DerivedCategory.Q.obj K)))
        (biprod.desc
          ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app
            (DerivedCategory.Q.obj K))
          (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app
            (DerivedCategory.Q.obj K))))
        (δ.app (DerivedCategory.Q.obj K)) ∈
      distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) := by
  refine isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (shortExact_resolutionCover X U V K hUV)) _
    (Iso.symm ?_)
  refine Triangle.isoMk _ _ ((sectionsResolutionIso X ⊤).app K) (middleComparison X U V K)
    ((sectionsResolutionIso X (U ⊓ V)).app K) ?_ ?_ ?_
  · exact map_coverFirst_comp_middleComparison X U V K
  · exact (Iso.inv_comp_eq _).1 (middleComparison_inv_comp_map_coverSecond X U V K)
  · have hUV' : (sectionsResolutionIso X (U ⊓ V)).hom.app K ≫
        (sectionsResolutionIso X (U ⊓ V)).inv.app K = 𝟙 _ :=
      congr_app (sectionsResolutionIso X (U ⊓ V)).hom_inv_id K
    change DerivedCategory.triangleOfSESδ (shortExact_resolutionCover X U V K hUV) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)).map
        ((sectionsResolutionIso X ⊤).hom.app K) =
      (sectionsResolutionIso X (U ⊓ V)).hom.app K ≫ δ.app (DerivedCategory.Q.obj K)
    rw [hδ]
    exact (inv_hom_comp_cancel _ _ hUV' _).symm

/-- A Mayer--Vietoris triangle of natural transformations which is distinguished at the
localization of every complex is distinguished at every object of `D(𝒪_X)`. -/
private lemma distTriang_of_distTriang_Q_obj
    (δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ))
    (hdist : ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ,
      Triangle.mk
        (biprod.lift
          ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app (DerivedCategory.Q.obj K))
          ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app (DerivedCategory.Q.obj K)))
        (biprod.desc
          ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app
            (DerivedCategory.Q.obj K))
          (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app
            (DerivedCategory.Q.obj K))))
        (δ.app (DerivedCategory.Q.obj K)) ∈
          distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Triangle.mk
        (biprod.lift ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app E)
          ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app E))
        (biprod.desc ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app E)
          (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app E)))
        (δ.app E) ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) := by
  refine isomorphic_distinguished _ (hdist (DerivedCategory.Q.objPreimage E)) _ (Iso.symm ?_)
  refine Triangle.isoMk _ _
    ((derivedLinearSections X ⊤).mapIso (DerivedCategory.Q.objObjPreimageIso E))
    (biprod.mapIso
      ((derivedLinearSections X U).mapIso (DerivedCategory.Q.objObjPreimageIso E))
      ((derivedLinearSections X V).mapIso (DerivedCategory.Q.objObjPreimageIso E)))
    ((derivedLinearSections X (U ⊓ V)).mapIso (DerivedCategory.Q.objObjPreimageIso E))
    ?_ ?_ ?_
  · exact (lift_mapIso_eq _ _ _ _ _ _
      ((derivedLinearRestriction X (le_top : U ≤ ⊤)).naturality _).symm
      ((derivedLinearRestriction X (le_top : V ≤ ⊤)).naturality _).symm).trans
      (comp_lift_eq _ _ _ _ _ rfl rfl).symm
  · exact (desc_comp_eq _ _ _ _ _
      ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).naturality _).symm
      (neg_comp_eq _ _ _ _
        ((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).naturality _).symm)).trans
      (mapIso_desc_eq
        ((derivedLinearSections X U).mapIso (DerivedCategory.Q.objObjPreimageIso E))
        ((derivedLinearSections X V).mapIso (DerivedCategory.Q.objObjPreimageIso E))
        ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app E)
        (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app E)) _ _ rfl rfl).symm
  · exact (δ.naturality (DerivedCategory.Q.objObjPreimageIso E).hom).symm

/-- Let `X` be a ringed space covered by two open subsets `U` and `V`, and let `A = Γ(X, 𝒪_X)`.
The restriction maps of the `A`-linear derived sections functors, with the usual sign on the
overlap, fit into a distinguished triangle in the derived category of `A`-modules, naturally in
the object of `D(𝒪_X)`: the connecting map is a natural transformation and the other four maps
are the right-derived restrictions. -/
@[stacks 08BX "the triangle, in D(A), A = Γ(X, 𝒪_X)"]
theorem linearUnboundedMayerVietoris (hUV : U ⊔ V = ⊤) :
    ∃ δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ),
      ∀ E, Triangle.mk
        (biprod.lift ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app E)
          ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app E))
        (biprod.desc ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app E)
          (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app E)))
        (δ.app E) ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X))) := by
  let b : DerivedCategory.Q ⋙ derivedLinearSections X (U ⊓ V) ⟶
      DerivedCategory.Q ⋙ (derivedLinearSections X ⊤ ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ)) :=
    (sectionsResolutionIso X (U ⊓ V)).inv ≫ coverBoundary X U V hUV ≫
      Functor.whiskerRight (sectionsResolutionIso X ⊤).hom
        (shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ))
  let G := (Functor.whiskeringLeft (CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (DerivedCategory (ModuleCat.{u} (baseRing X)))).obj DerivedCategory.Q
  have : G.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
  refine ⟨G.preimage b, distTriang_of_distTriang_Q_obj X U V _ (fun K => ?_)⟩
  exact distTriang_of_Q_obj X U V K hUV _ (NatTrans.congr_app (G.map_preimage b) K)

end Space

end Stacks.Cohomology.LinearMayerVietoris

end
