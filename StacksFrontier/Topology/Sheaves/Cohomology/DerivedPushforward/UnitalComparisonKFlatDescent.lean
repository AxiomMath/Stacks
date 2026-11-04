module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductTensorConstraints
public import StacksFrontier.Homology.Tor.ModuleKFlatDescent

/-!
# Unitality of a one-point comparison may be checked on K-flat representatives

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, and let `c` be a
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison S` with a map `u : L A ⟶ 𝒪_S`. Both
sides of each law of `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.IsUnitalWith`
are natural transformations on `D(A)`, resp. `D(A) × D(A)`, so each law holds as soon as it holds
at K-flat representatives.

## Main results

In the namespace `Stacks.Cohomology.DerivedGlobalCupProduct`:

* `baseComm_naturality`: the commutativity constraint of `⊗^𝐋_A` is natural in both complexes
  jointly.
* `OnePointComparison.oplaxRightUnit_of_kFlat`, `OnePointComparison.oplaxBraided_of_kFlat`: each
  oplax law holds as soon as it holds at K-flat representatives.
* `OnePointComparison.isUnitalWith_of_kFlat`: a one-point comparison is unital as soon as its two
  oplax laws hold at K-flat representatives.
* `isGlobalCupProduct_of_kFlat`: the global cup product of such a one-point comparison is a
  unital global cup product.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open CochainComplex.KFlatBifunctor
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

/-! ### The commutativity constraint of `⊗^𝐋_A` is natural in both variables -/

/-- A transformation `τ : T ⟶ T.flip` from a bifunctor to its flip is natural in both variables
jointly, as a square for the uncurried bifunctor. -/
private lemma uncurry_flipTrans_naturality {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    (τ : T ⟶ T.flip) {K K' L L' : C} (f : K ⟶ K') (g : L ⟶ L') :
    (Functor.uncurry.obj T).map (f ×ₘ g) ≫ (τ.app K').app L' =
      (τ.app K).app L ≫ (Functor.uncurry.obj T).map (g ×ₘ f) := by
  have hτg := (τ.app K').naturality g
  have hτf := congr_app (τ.naturality f) L
  have hint := ((T.map g).naturality f)
  simp only [Functor.flip_obj_map, Functor.flip_map_app, NatTrans.comp_app] at hτg hτf
  simp only [Functor.uncurry_obj_map, Category.assoc]
  rw [hτg, ← Category.assoc, hτf, Category.assoc, hint]

/-- Cancelling a fixed morphism `u : P.obj Z ⟶ oneD` against a natural unit constraint `ρ` is
natural, with the bifunctor's action on a pair written out. -/
lemma bifunctor_map_prod_cancel {D E : Type*} [Category D] [Category E]
    (TD : E ⥤ E ⥤ E) (P : D ⥤ E) {oneD : E} {Z : D} (u : P.obj Z ⟶ oneD)
    (ρ : ∀ y : E, (TD.obj y).obj oneD ⟶ y)
    (hρ : ∀ {Y Y' : E} (k : Y ⟶ Y'), (TD.map k).app oneD ≫ ρ Y' = ρ Y ≫ k)
    {x y : D} (f : x ⟶ y) :
    ((TD.map (P.map f)).app (P.obj Z) ≫ (TD.obj (P.obj y)).map (P.map (𝟙 Z))) ≫
        ((TD.obj (P.obj y)).map u ≫ ρ (P.obj y)) =
      ((TD.obj (P.obj x)).map u ≫ ρ (P.obj x)) ≫ P.map f := by
  have h := (TD.map (P.map f)).naturality u
  rw [P.map_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc,
    ← reassoc_of% h, hρ]

/-- A transformation out of a bifunctor with its second argument fixed to `one` is natural in
the first argument, with the bifunctor's action written as `(T.map f).app one`. -/
lemma flipObj_trans_naturality {C : Type*} [Category C] (T : C ⥤ C ⥤ C) (one : C)
    (G : C ⥤ C) (τ : T.flip.obj one ⟶ G) {x y : C} (f : x ⟶ y) :
    (T.map f).app one ≫ τ.app y = τ.app x ≫ G.map f :=
  (Functor.flip_obj_map T one f) ▸ τ.naturality f

/-- Carrying a natural unit constraint `ρ` over by a functor `P` is natural, with the action of
the bifunctor on a pair whose second component is an identity written out. -/
lemma bifunctor_map_prod_unitor {C E : Type*} [Category C] [Category E]
    (TC : C ⥤ C ⥤ C) (P : C ⥤ E) {oneC : C} (ρ : ∀ x : C, (TC.obj x).obj oneC ⟶ x)
    (hρ : ∀ {X Y : C} (k : X ⟶ Y), (TC.map k).app oneC ≫ ρ Y = ρ X ≫ k)
    {x y : C} (f : x ⟶ y) :
    P.map ((TC.map f).app oneC ≫ (TC.obj y).map (𝟙 oneC)) ≫ P.map (ρ y) =
      P.map (ρ x) ≫ P.map f := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id, ← P.map_comp, ← P.map_comp, hρ]

variable (S : RingedSpace.{u, u})

/-- The commutativity constraint of `⊗^𝐋_A` is natural in both complexes jointly, as a square
for the uncurried bifunctor. -/
theorem baseComm_naturality
    {K K' L L' : DerivedCategory (ModuleCat.{u} (baseRing S))} (f : K ⟶ K') (g : L ⟶ L') :
    (Functor.uncurry.obj (tensorBase S)).map (f ×ₘ g) ≫ (baseComm S K' L').hom =
      (baseComm S K L).hom ≫ (Functor.uncurry.obj (tensorBase S)).map (g ×ₘ f) :=
  uncurry_flipTrans_naturality (tensorBase S)
    (CochainComplex.DerivedTensor.derivedTensorProductKoszulBraiding (baseRing S)).iso.hom f g

namespace OnePointComparison

variable {S}

/-! ### The right unit law -/

section RightUnit

variable (c : OnePointComparison S) (u : c.pullback.obj (unitBase S) ⟶ unitSheaf S)

/-- The functor `x ↦ (x, A)` on `D(A)`. -/
abbrev unitPair :
    DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S)) ×
        DerivedCategory (ModuleCat.{u} (baseRing S)) :=
  Functor.prod' (𝟭 _)
    ((Functor.const (DerivedCategory (ModuleCat.{u} (baseRing S)))).obj (unitBase S))

/-- Cancelling `𝒪_S` against `u`, as a transformation `L x ⊗^𝐋_{𝒪_S} L A ⟶ L x`: tensoring with
`u` on the right and then the unit constraint of `⊗^𝐋_{𝒪_S}`. -/
def cancelUnit :
    unitPair (S := S) ⋙ c.pullback.prod c.pullback ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) ⟶ c.pullback where
  app x := ((derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj x)).map u ≫
    (sheafRightUnitor S (c.pullback.obj x)).hom
  naturality _ _ f :=
    bifunctor_map_prod_cancel (derivedTensorProductFunctor S.sheaf) c.pullback u
      (fun y => (sheafRightUnitor S y).hom)
      (fun k => DerivedTensorProduct.rightUnitIso_hom_naturality (baseSite S)
        (canonicalDerivedTensorProduct S.sheaf) k) f

/-- The unit constraint of `⊗^𝐋_A`, carried over by `L`, as a transformation
`L(x ⊗^𝐋_A A) ⟶ L x`. -/
def mapBaseRightUnitor :
    unitPair (S := S) ⋙ Functor.uncurry.obj (tensorBase S) ⋙ c.pullback ⟶ c.pullback where
  app x := c.pullback.map (baseRightUnitor S x).hom
  naturality _ _ f :=
    bifunctor_map_prod_unitor (tensorBase S) c.pullback (fun x => (baseRightUnitor S x).hom)
      (fun k => flipObj_trans_naturality (tensorBase S) (unitBase S) (𝟭 _)
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
          (baseRing S)).rightUnitor.hom k) f

/-- The left-hand side of the oplax right unit law, as a transformation on `D(A)`: the
comparison at `(x, A)`, then cancelling `𝒪_S` against `u`. -/
def comparisonThenCancelUnit :
    unitPair (S := S) ⋙ Functor.uncurry.obj (tensorBase S) ⋙ c.pullback ⟶ c.pullback :=
  Functor.whiskerLeft (unitPair (S := S)) c.tensorComparison ≫ cancelUnit c u

/-- The components of `comparisonThenCancelUnit`. -/
theorem comparisonThenCancelUnit_app (x : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    (comparisonThenCancelUnit c u).app x =
      c.tensorComparison.app (x, unitBase S) ≫
        ((derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj x)).map u ≫
          (sheafRightUnitor S (c.pullback.obj x)).hom :=
  rfl

/-- The components of `mapBaseRightUnitor`. -/
theorem mapBaseRightUnitor_app (x : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    (mapBaseRightUnitor c).app x = c.pullback.map (baseRightUnitor S x).hom :=
  rfl

/-- The oplax right unit law holds as soon as it holds at K-flat representatives. -/
theorem oplaxRightUnit_of_kFlat
    (h : ∀ K : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      c.tensorComparison.app (DerivedCategory.Q.obj K, unitBase S) ≫
          ((derivedTensorProductFunctor S.sheaf).obj
            (c.pullback.obj (DerivedCategory.Q.obj K))).map u ≫
            (sheafRightUnitor S (c.pullback.obj (DerivedCategory.Q.obj K))).hom =
        c.pullback.map (baseRightUnitor S (DerivedCategory.Q.obj K)).hom)
    (x : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    c.tensorComparison.app (x, unitBase S) ≫
        ((derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj x)).map u ≫
          (sheafRightUnitor S (c.pullback.obj x)).hom =
      c.pullback.map (baseRightUnitor S x).hom :=
  congr_app
    (CochainComplex.DerivedTensor.OneSided.natTrans_ext_of_kFlat ↥(baseRing S)
      (comparisonThenCancelUnit c u) (mapBaseRightUnitor c)
      (fun K hK => (comparisonThenCancelUnit_app c u _).trans
        ((h K hK).trans (mapBaseRightUnitor_app c _).symm)))
    x

end RightUnit

/-! ### The commutativity law -/

section Braided

variable (c : OnePointComparison S)

/-- The commutativity constraint of `⊗^𝐋_{𝒪_S}` at the images of `L`, as a transformation
`L x ⊗^𝐋_{𝒪_S} L y ⟶ L y ⊗^𝐋_{𝒪_S} L x`. -/
def sheafCommOfPullback (hS : AreNaturalTensorConstraints S) :
    c.pullback.prod c.pullback ⋙ Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        c.pullback.prod c.pullback ⋙
          Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) where
  app xy := (sheafComm S (c.pullback.obj xy.1) (c.pullback.obj xy.2)).hom
  naturality _ _ fg :=
    hS.comm_naturality (c.pullback.map fg.1) (c.pullback.map fg.2)

/-- The commutativity constraint of `⊗^𝐋_A`, carried over by `L`, as a transformation
`L(x ⊗^𝐋_A y) ⟶ L(y ⊗^𝐋_A x)`. -/
def mapBaseComm :
    Functor.uncurry.obj (tensorBase S) ⋙ c.pullback ⟶
      CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensorBase S) ⋙ c.pullback where
  app xy := c.pullback.map (baseComm S xy.1 xy.2).hom
  naturality _ _ fg := by
    dsimp only [Functor.comp_map]
    rw [← c.pullback.map_comp, ← c.pullback.map_comp]
    exact congrArg c.pullback.map (baseComm_naturality S fg.1 fg.2)

/-- The left-hand side of the oplax commutativity law, as a transformation on `D(A) × D(A)`. -/
def comparisonThenSheafComm (hS : AreNaturalTensorConstraints S) :
    Functor.uncurry.obj (tensorBase S) ⋙ c.pullback ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        c.pullback.prod c.pullback ⋙
          Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) :=
  c.tensorComparison ≫ sheafCommOfPullback c hS

/-- The right-hand side: the commutativity constraint of `⊗^𝐋_A` carried over by `L`, then the
comparison at the swapped pair. -/
def baseCommThenComparison :
    Functor.uncurry.obj (tensorBase S) ⋙ c.pullback ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        c.pullback.prod c.pullback ⋙
          Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) :=
  mapBaseComm c ≫ Functor.whiskerLeft (CategoryTheory.Prod.swap _ _) c.tensorComparison

/-- The components of `comparisonThenSheafComm`. -/
theorem comparisonThenSheafComm_app (hS : AreNaturalTensorConstraints S)
    (x y : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    (comparisonThenSheafComm c hS).app (x, y) =
      c.tensorComparison.app (x, y) ≫
        (sheafComm S (c.pullback.obj x) (c.pullback.obj y)).hom :=
  rfl

/-- The components of `baseCommThenComparison`. -/
theorem baseCommThenComparison_app
    (x y : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    (baseCommThenComparison c).app (x, y) =
      c.pullback.map (baseComm S x y).hom ≫ c.tensorComparison.app (y, x) :=
  rfl

/-- The oplax commutativity law holds as soon as it holds at pairs of K-flat representatives. -/
theorem oplaxBraided_of_kFlat (hS : AreNaturalTensorConstraints S)
    (h : ∀ K L : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) L →
      c.tensorComparison.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
          (sheafComm S (c.pullback.obj (DerivedCategory.Q.obj K))
            (c.pullback.obj (DerivedCategory.Q.obj L))).hom =
        c.pullback.map
            (baseComm S (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
          c.tensorComparison.app (DerivedCategory.Q.obj L, DerivedCategory.Q.obj K))
    (x y : DerivedCategory (ModuleCat.{u} (baseRing S))) :
    c.tensorComparison.app (x, y) ≫
        (sheafComm S (c.pullback.obj x) (c.pullback.obj y)).hom =
      c.pullback.map (baseComm S x y).hom ≫ c.tensorComparison.app (y, x) :=
  congr_app
    (CochainComplex.DerivedTensor.OneSided.natTrans_ext_of_kFlatPair ↥(baseRing S)
      (comparisonThenSheafComm c hS) (baseCommThenComparison c)
      (fun K L hK hL => (comparisonThenSheafComm_app c hS _ _).trans
        ((h K L hK hL).trans (baseCommThenComparison_app c _ _).symm)))
    (x, y)

end Braided

/-! ### Unitality from the two laws on K-flat representatives -/

/-- A one-point comparison is unital as soon as its two oplax laws hold at K-flat
representatives. -/
theorem isUnitalWith_of_kFlat (c : OnePointComparison S)
    (u : c.pullback.obj (unitBase S) ⟶ unitSheaf S)
    (hr : ∀ K : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      c.tensorComparison.app (DerivedCategory.Q.obj K, unitBase S) ≫
          ((derivedTensorProductFunctor S.sheaf).obj
            (c.pullback.obj (DerivedCategory.Q.obj K))).map u ≫
            (sheafRightUnitor S (c.pullback.obj (DerivedCategory.Q.obj K))).hom =
        c.pullback.map (baseRightUnitor S (DerivedCategory.Q.obj K)).hom)
    (hb : ∀ K L : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) L →
      c.tensorComparison.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
          (sheafComm S (c.pullback.obj (DerivedCategory.Q.obj K))
            (c.pullback.obj (DerivedCategory.Q.obj L))).hom =
        c.pullback.map
            (baseComm S (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
          c.tensorComparison.app (DerivedCategory.Q.obj L, DerivedCategory.Q.obj K)) :
    c.IsUnitalWith u where
  right_unit := oplaxRightUnit_of_kFlat c u hr
  braided := oplaxBraided_of_kFlat c (areNaturalTensorConstraints S) hb

end OnePointComparison

/-- The global cup product of a one-point comparison whose two oplax laws hold at K-flat
representatives is a unital global cup product. -/
theorem isGlobalCupProduct_of_kFlat {c : OnePointComparison S}
    {u : c.pullback.obj (unitBase S) ⟶ unitSheaf S}
    (hr : ∀ K : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      c.tensorComparison.app (DerivedCategory.Q.obj K, unitBase S) ≫
          ((derivedTensorProductFunctor S.sheaf).obj
            (c.pullback.obj (DerivedCategory.Q.obj K))).map u ≫
            (sheafRightUnitor S (c.pullback.obj (DerivedCategory.Q.obj K))).hom =
        c.pullback.map (baseRightUnitor S (DerivedCategory.Q.obj K)).hom)
    (hb : ∀ K L : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) K →
      CochainComplex.KFlatBifunctor.KFlat
        (curriedTensor (ModuleCat.{u} (baseRing S))) L →
      c.tensorComparison.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
          (sheafComm S (c.pullback.obj (DerivedCategory.Q.obj K))
            (c.pullback.obj (DerivedCategory.Q.obj L))).hom =
        c.pullback.map
            (baseComm S (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
          c.tensorComparison.app (DerivedCategory.Q.obj L, DerivedCategory.Q.obj K)) :
    IsGlobalCupProduct (globalCupProduct c) :=
  isGlobalCupProduct_of_isUnitalWith
    (OnePointComparison.isUnitalWith_of_kFlat c u hr hb)

end Stacks.Cohomology.DerivedGlobalCupProduct

end
