module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ClassifyingStackCechDerivedPushforward
public import StacksFrontier.AlgebraicTopology.TrivialBarComplexZModTwo

/-!
# The derived direct image of the structure sheaf of `B(ℤ/2)_S`

Let `S` be a scheme of a big fppf site, `G = (ℤ/2)_S = S ⊔ S` the constant group, `𝒳 = BG` its
classifying stack, `f : 𝒳 ⟶ S` the structure morphism and `Rf_*` the unbounded derived direct
image of fppf modules at module universe `u + 1`. This file computes `Rf_* 𝒪_𝒳`:

`Rf_*(𝒪_𝒳[0]) ≅ Q(K)`,

where `K` is the extension to `ℤ` of the alternating coface complex of a cosimplicial module `𝒦`
on `S` which is isomorphic to the bar cosimplicial object of `ℤ/2` with coefficients `𝒪_S`,
`[n] ↦ ∏_{(ℤ/2)ⁿ} 𝒪_S` (`Stacks.GroupCohomology.TrivialBar.cochainCosimplicial`).

## The proof

`𝒦` is the direct image `f_*` of the relative Čech cosimplicial module `n ↦ cₙ,* cₙ⁻¹ 𝒪_𝒳` of
the atlas `π : S ⟶ BG`. Its augmentation is a resolution (Stacks 06XE), injective modules have
injective Čech terms, and `f_* cₙ,* cₙ⁻¹` has no higher right derived functors at `𝒪_𝒳`
(`AlgebraicGeometry.Stack.ClassifyingZModTwo.isZero_rightDerived_cechDirectImage_uliftUnit`), so
the Čech complex computes `Rf_*` (`CategoryTheory.Functor.
rightDerivedFunctorPlusSingleIsoOfFunctorialResolution`). The sections of `𝒦ₙ` over an object
`y` lying over `T` are the functions on `T ×_S Gⁿ`, which are the families of functions on `T`
indexed by `(ℤ/2)ⁿ`: the component at a simplex `x` of the nerve of `ℤ/2` is the evaluation at the
canonical tuple of the constant points of `x`, and reindexing canonical tuples along the
simplicial operators is the simplicial structure of the nerve.

## Main definitions

* `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCosimplicial`: the cosimplicial module `𝒦`.
* `AlgebraicGeometry.Stack.ClassifyingZModTwo.cechCosimplicialIso`:
  `𝒦 ≅ cochainCosimplicial 𝒪_S`.
* `AlgebraicGeometry.Stack.ClassifyingZModTwo.derivedPushforwardUliftUnitIso`:
  `Rf_*(𝒪_𝒳[0]) ≅ Q(K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.Stack.ClassifyingAtlasCech Stacks.Examples
open Stacks.GroupCohomology.TrivialBar

universe u w

namespace AlgebraicGeometry.Stack.ClassifyingZModTwo

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  AlgebraicGeometry.Stack.fibredCategory CategoryTheory.BasedCategory.ofFunctor

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} (hS : C.Contains S)

/-! ### Points of `(ℤ/2)_S` attached to simplices of the nerve -/

section Points

variable {T : BigFppfOver C S hS} {n : ℕ}

/-- The constant points of `(ℤ/2)_S` over `T` given by the string of a simplex of the nerve of
`ℤ/2`. -/
def simplexPoints (T : BigFppfOver C S hS) (x : nerveZModTwo _⦋n⦌) :
    Fin n → (constantZModTwoGroup hS).SitePoint T :=
  fun k => constantPoint T (arr x k)

/-- The image under a simplex `x` of the arrow `a ⟶ b` of `[n]`, as an element of `ℤ/2`. -/
abbrev simplexValue (x : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (h : a ≤ b) :
    Multiplicative (ZMod 2) :=
  mapArr x (homOfLE h)

/-- The partial products of the string of a simplex are its values on the arrows out of `0`. -/
theorem partialProd_arr (x : nerveZModTwo _⦋n⦌) (i : Fin (n + 1)) :
    Fin.partialProd (arr x) i = simplexValue x (Fin.zero_le i) := by
  induction i using Fin.induction with
  | zero =>
    rw [Fin.partialProd_zero]
    exact (map_eq_one x _ rfl).symm
  | succ j ih =>
    rw [Fin.partialProd_succ, ih]
    have h : (homOfLE (Fin.zero_le j.succ) : (0 : Fin (n + 1)) ⟶ j.succ) =
        homOfLE (Fin.zero_le j.castSucc) ≫ homOfLE (Fin.castSucc_lt_succ (i := j)).le :=
      Subsingleton.elim _ _
    change _ = mapArr x (homOfLE (Fin.zero_le j.succ))
    rw [h, mapArr_comp]
    exact mul_comm _ _

/-- The values of a simplex on `a ⟶ b` is the quotient of its values on `0 ⟶ b` and `0 ⟶ a`. -/
theorem simplexValue_eq (x : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (h : a ≤ b) :
    simplexValue x h =
      (simplexValue x (Fin.zero_le a))⁻¹ * simplexValue x (Fin.zero_le b) := by
  have hc : (homOfLE (Fin.zero_le b) : (0 : Fin (n + 1)) ⟶ b) =
      homOfLE (Fin.zero_le a) ≫ homOfLE h := Subsingleton.elim _ _
  change _ = _ * mapArr x (homOfLE (Fin.zero_le b))
  rw [hc, mapArr_comp, mul_comm (mapArr x (homOfLE h)), inv_mul_cancel_left]

/-- The string of the image of a simplex under a simplicial operator. -/
theorem arr_map {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : nerveZModTwo _⦋n⦌) (j : Fin m) :
    arr (nerveZModTwo.map θ.op x) j =
      simplexValue x (θ.toOrderHom.monotone (Fin.castSucc_lt_succ (i := j)).le) :=
  rfl

/-- **The points of the image of a simplex under a simplicial operator are the bar map of its
points.** -/
theorem simplexPoints_map (T : BigFppfOver C S hS) {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : nerveZModTwo _⦋n⦌) :
    simplexPoints hS T (nerveZModTwo.map θ.op x) = barMap _ θ (simplexPoints hS T x) := by
  funext j
  change constantPoint T (arr (nerveZModTwo.map θ.op x) j) =
    (Fin.partialProd (fun k => constantPoint T (arr x k)) (θ.toOrderHom j.castSucc))⁻¹ *
      Fin.partialProd (fun k => constantPoint T (arr x k)) (θ.toOrderHom j.succ)
  rw [← map_partialProd (constantPoint T) (arr x), ← map_partialProd (constantPoint T) (arr x),
    ← map_inv (constantPoint T), ← map_mul (constantPoint T), arr_map, simplexValue_eq,
    partialProd_arr, partialProd_arr]

/-- The points of a simplex pull back to the points of the same simplex. -/
theorem pullback_simplexPoints {T T' : BigFppfOver C S hS} (m : T' ⟶ T)
    (x : nerveZModTwo _⦋n⦌) (k : Fin n) :
    Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) m
      (simplexPoints hS T x k) = simplexPoints hS T' x k :=
  pullback_constantPoint m _

/-- The additive string of a simplex. -/
def simplexString (x : nerveZModTwo _⦋n⦌) : Fin n → ZMod 2 :=
  fun k => Multiplicative.toAdd (arr x k)

/-- The simplex of the nerve of `ℤ/2` with a given string. -/
def simplexOfString (σ : Fin n → ZMod 2) : nerveZModTwo _⦋n⦌ :=
  ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star _)
    (fun k => (Multiplicative.ofAdd (σ k) : Multiplicative (ZMod 2)))

/-- The string of the simplex with a given string. -/
theorem arr_simplexOfString (σ : Fin n → ZMod 2) (k : Fin n) :
    arr (simplexOfString σ) k = Multiplicative.ofAdd (σ k) := by
  have e : (toArrows (simplexOfString σ)).map' k (k + 1) = arr (simplexOfString σ) k :=
    mapArr_congr _ _ _ (Fin.ext (by simp)) (Fin.ext (by simp))
  rw [← e]
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k k.isLt

/-- Simplices of the nerve of `ℤ/2` are their strings. -/
def simplexStringEquiv : nerveZModTwo _⦋n⦌ ≃ (Fin n → ZMod 2) where
  toFun := simplexString
  invFun := simplexOfString
  left_inv _ := ext_arr fun k => arr_simplexOfString _ k
  right_inv σ := funext fun k => congrArg Multiplicative.toAdd (arr_simplexOfString σ k)

end Points

/-! ### Evaluation at the canonical tuples -/

section Evaluation

variable (n : ℕ)

/-- The inverse image of the structure sheaf on the `n`-th term of the Čech nerve. -/
abbrev cechModule : SheafOfModules.{u + 1} (cechRing.{u, w} hS n) :=
  (cechInverseImage.{u, w} hS n).obj (structureModule.{u, w} hS)

/-- The isomorphism `π(T) ≅ y` of the stack of the base, for `y` over `T`, through which sections
over trivial torsors are compared with sections over `y`. -/
def toBaseHom (y : (base.{u, w} hS).val.val.obj) :
    (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).obj
        ((atlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)).obj (atlasObj y.left)) ⟶ y :=
  baseSliceHom y (eqToHom (stackProj_atlasFunctor_obj.{u, w} _
    (isSmooth_constantZModTwoGroup hS) y.left))

/-- The inverse of `toBaseHom`. -/
def fromBaseHom (y : (base.{u, w} hS).val.val.obj) :
    y ⟶ (CatFiberedInGroupoids.homFunctor (structureMap.{u, w} hS).hom).obj
        ((atlasFunctor.{u, w} _ (isSmooth_constantZModTwoGroup hS)).obj (atlasObj y.left)) :=
  Over.homMk (Over.homMk (eqToHom (stackProj_atlasFunctor_obj.{u, w} _
      (isSmooth_constantZModTwoGroup hS) y.left).symm).left
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Over.w _))) (Over.mkIdTerminal.hom_ext _ _)

/-- `fromBaseHom` is a right inverse of `toBaseHom`. -/
@[reassoc (attr := simp)]
theorem toBaseHom_fromBaseHom (y : (base.{u, w} hS).val.val.obj) :
    toBaseHom.{u, w} hS y ≫ fromBaseHom.{u, w} hS y = 𝟙 _ := by
  have e := stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS) y.left
  refine baseSlice_hom_ext _ _ ?_
  change (eqToHom e).left ≫ (eqToHom e.symm).left = 𝟙 _
  rw [← Over.comp_left, eqToHom_trans, eqToHom_refl]
  rfl

/-- `fromBaseHom` is a left inverse of `toBaseHom`. -/
@[reassoc (attr := simp)]
theorem fromBaseHom_toBaseHom (y : (base.{u, w} hS).val.val.obj) :
    fromBaseHom.{u, w} hS y ≫ toBaseHom.{u, w} hS y = 𝟙 _ := by
  have e := stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS) y.left
  refine baseSlice_hom_ext _ _ ?_
  change (eqToHom e.symm).left ≫ (eqToHom e).left = 𝟙 _
  rw [← Over.comp_left, eqToHom_trans, eqToHom_refl]
  rfl

/-- The canonical tuple over `y.left` of the constant points of a simplex. -/
abbrev simplexTuple (y : (base.{u, w} hS).val.val.obj) (x : nerveZModTwo _⦋n⦌) :
    CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n :=
  canonicalTuple.{u, w} _ _ y.left (simplexPoints hS y.left x)

/-- The structure sheaf of rings of the stack of the base. -/
abbrev baseRing :=
  FibredSite.ringStructureSheafCore C S hS (base.{u, w} hS).val.val.p
    (base.{u, w} hS).val.isFiberedInGroupoids .fppf

/-- The structure sheaf of rings of `B(ℤ/2)_S`. -/
abbrev stackRing :=
  FibredSite.ringStructureSheafCore C S hS (stack.{u, w} hS).val.val.p
    (stack.{u, w} hS).val.isFiberedInGroupoids .fppf

/-- The function on the object of `B(ℤ/2)_S` underlying a canonical tuple attached to a
section of `𝒦ₙ` over `y`: its component at the canonical tuple of `g`. -/
abbrev pointsEvalRaw (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    (stackRing.{u, w} hS).obj.obj
      (op ((cechProjection.{u, w} hS n).obj (canonicalTuple.{u, w} _ _ y.left g))) :=
  (cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y.left g)
    (toBaseHom.{u, w} hS y) s).down

/-- **The function over `y` attached to a section of `𝒦ₙ` and points `g` of `G` over `y.left`**:
the component of the section at the canonical tuple of `g`, transported to `y`. -/
def pointsEval (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    (baseRing.{u, w} hS).obj.obj (op y) :=
  ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
    (pointsEvalRaw.{u, w} hS n y g s)

/-- `pointsEval` is additive. -/
theorem pointsEval_add (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s s' : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y g (s + s') =
      pointsEval.{u, w} hS n y g s + pointsEval.{u, w} hS n y g s' :=
  (congrArg (fun v => ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
      (ULift.down v))
    (cechEval_add.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y.left g)
      (toBaseHom.{u, w} hS y) s s')).trans (map_add _ _ _)

/-- The component at a canonical tuple of a multiple of a section. -/
theorem pointsEvalRaw_smul (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (r : (baseRing.{u, w} hS).obj.obj (op y))
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    pointsEvalRaw.{u, w} hS n y g (r • s) =
      ((stackRing.{u, w} hS).obj.map
          (𝟙 (op ((cechProjection.{u, w} hS n).obj (canonicalTuple.{u, w} _ _ y.left g))))).hom
        (((baseRing.{u, w} hS).obj.map (toBaseHom.{u, w} hS y).op).hom r) *
        pointsEvalRaw.{u, w} hS n y g s :=
  (congrArg ULift.down (cechEval_eq.{u, w} hS n (cechModule.{u, w} hS n)
      (canonicalTuple.{u, w} _ _ y.left g) (toBaseHom.{u, w} hS y) (r • s))).trans
    (Eq.trans rfl (congrArg (fun v => ((stackRing.{u, w} hS).obj.map
        (𝟙 (op ((cechProjection.{u, w} hS n).obj (canonicalTuple.{u, w} _ _ y.left g))))).hom
          (((baseRing.{u, w} hS).obj.map (toBaseHom.{u, w} hS y).op).hom r) * ULift.down v)
      (cechEval_eq.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y.left g)
        (toBaseHom.{u, w} hS y) s)).symm)

/-- `pointsEval` is linear over the structure sheaf of the base. -/
theorem pointsEval_smul (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (r : (baseRing.{u, w} hS).obj.obj (op y))
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y g (r • s) = r * pointsEval.{u, w} hS n y g s := by
  have h1 : ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
      (((stackRing.{u, w} hS).obj.map
          (𝟙 (op ((cechProjection.{u, w} hS n).obj (canonicalTuple.{u, w} _ _ y.left g))))).hom
        (((baseRing.{u, w} hS).obj.map (toBaseHom.{u, w} hS y).op).hom r)) = r := by
    rw [CategoryTheory.Functor.map_id]
    change ((baseRing.{u, w} hS).obj.map (toBaseHom.{u, w} hS y).op ≫
      (baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom r = r
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, fromBaseHom_toBaseHom, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact (congrArg ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
    (pointsEvalRaw_smul.{u, w} hS n y g r s)).trans
      ((map_mul _ _ _).trans (congrArg (· * pointsEval.{u, w} hS n y g s) h1))

/-- The base of the canonical morphism of canonical tuples over a morphism `g` of the stack of
the base, composed with the comparison to the target, is the comparison followed by `g`. -/
@[reassoc]
theorem baseMap_canonicalTupleHom_comp_toBaseHom {y y' : (base.{u, w} hS).val.val.obj}
    (m : y' ⟶ y) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i) :
    (structureFunctor.{u, w} hS).map
        ((cechProjection.{u, w} hS n).map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg)) ≫
      toBaseHom.{u, w} hS y = toBaseHom.{u, w} hS y' ≫ m := by
  refine baseSlice_hom_ext _ _ ?_
  have hfac := IsHomLift.fac' (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS))
    m.left (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg).target
  change ((stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
      (canonicalTupleHom.{u, w} _ _ m.left g g' hg).target ≫
        eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
          y.left)).left =
    (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS) y'.left) ≫
      m.left).left
  rw [hfac, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The base of the canonical morphism of canonical tuples over `m`, between the comparisons
`fromBaseHom`. -/
theorem fromBaseHom_comp_baseMap_canonicalTupleHom {y y' : (base.{u, w} hS).val.val.obj}
    (m : y' ⟶ y) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i) :
    fromBaseHom.{u, w} hS y' ≫ (structureFunctor.{u, w} hS).map
        ((cechProjection.{u, w} hS n).map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg)) =
      m ≫ fromBaseHom.{u, w} hS y := by
  refine baseSlice_hom_ext _ _ ?_
  have hfac := IsHomLift.fac' (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS))
    m.left (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg).target
  change (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        y'.left).symm ≫
      (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
        (canonicalTupleHom.{u, w} _ _ m.left g g' hg).target).left =
    (m.left ≫ eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
      y.left).symm).left
  rw [hfac, ← Category.assoc, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The restriction maps of `cₙ⁻¹ 𝒪_𝒳` are those of the structure sheaf of `B(ℤ/2)_S`. -/
theorem cechModule_map_down
    {a a' : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n}
    (k : a ⟶ a') (v : (cechModule.{u, w} hS n).val.presheaf.obj (op a')) :
    (ConcreteCategory.hom ((cechModule.{u, w} hS n).val.presheaf.map k.op) v).down =
      ((stackRing.{u, w} hS).obj.map ((cechProjection.{u, w} hS n).map k).op).hom v.down :=
  rfl

/-- The restriction maps of `𝒦ₙ` are those of the composite direct image. -/
theorem cechCosimplicial_map_hom_eq {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    (((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.map m.op).hom s =
      ConcreteCategory.hom
        (((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.map
          m.op) s :=
  rfl

/-- The component of a restricted section of `𝒦ₙ` at the comparison `toBaseHom`. -/
theorem cechEval_restrict_toBaseHom {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.obj
      (op y)) :
    cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        (toBaseHom.{u, w} hS y')
        (ConcreteCategory.hom
          (((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.map
            m.op) s) =
      cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        (toBaseHom.{u, w} hS y' ≫ m) s :=
  cechEval_map.{u, w} hS n (cechModule.{u, w} hS n) m (canonicalTuple.{u, w} _ _ y'.left g')
    (toBaseHom.{u, w} hS y') s

/-- The comparison `toBaseHom` composed with `m` is the base of the canonical morphism of
canonical tuples followed by `toBaseHom`. -/
theorem cechEval_toBaseHom_comp {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.obj
      (op y)) :
    cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        (toBaseHom.{u, w} hS y' ≫ m) s =
      cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        ((structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS n).map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg)) ≫
          toBaseHom.{u, w} hS y) s := by
  rw [baseMap_canonicalTupleHom_comp_toBaseHom.{u, w} hS n m g g' hg]

/-- The restriction of a component along the canonical morphism of canonical tuples over `m`. -/
theorem cechEval_canonicalTupleHom {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.obj
      (op y)) :
    ConcreteCategory.hom ((cechModule.{u, w} hS n).val.presheaf.map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg).op)
        (cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y.left g)
          (toBaseHom.{u, w} hS y) s) =
      cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        ((structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS n).map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg)) ≫
          toBaseHom.{u, w} hS y) s :=
  cechEval_comp.{u, w} hS n (cechModule.{u, w} hS n)
    (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg)
    (toBaseHom.{u, w} hS y) s

/-- The component at a canonical tuple of the restriction of a section of `𝒦ₙ` along `m` is the
restriction of the component along the canonical morphism of canonical tuples. -/
theorem cechEval_canonicalTuple_map {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i)
    (s : ((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.obj
      (op y)) :
    cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y'.left g')
        (toBaseHom.{u, w} hS y')
        (ConcreteCategory.hom
          (((cechCompositeDirectImage.{u, w} hS n).obj (cechModule.{u, w} hS n)).val.presheaf.map
            m.op) s) =
      ConcreteCategory.hom ((cechModule.{u, w} hS n).val.presheaf.map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg).op)
        (cechEval.{u, w} hS n (cechModule.{u, w} hS n) (canonicalTuple.{u, w} _ _ y.left g)
          (toBaseHom.{u, w} hS y) s) :=
  (cechEval_restrict_toBaseHom.{u, w} hS n m g' s).trans
    ((cechEval_toBaseHom_comp.{u, w} hS n m g g' hg s).trans
      (cechEval_canonicalTupleHom.{u, w} hS n m g g' hg s).symm)

/-- The restriction maps of the structure sheaf of the base along the comparisons `fromBaseHom`
and the canonical morphism of canonical tuples over `m`. -/
theorem baseRing_map_fromBaseHom_comp {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i) :
    (baseRing.{u, w} hS).obj.map ((structureFunctor.{u, w} hS).map
        ((cechProjection.{u, w} hS n).map
          (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg))).op ≫
        (baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y').op =
      (baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op ≫
        (baseRing.{u, w} hS).obj.map m.op := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← op_comp,
    ← op_comp, fromBaseHom_comp_baseMap_canonicalTupleHom]

/-- **`pointsEval` is natural in `y`.** -/
theorem pointsEval_map {y y' : (base.{u, w} hS).val.val.obj} (m : y' ⟶ y)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (g' : Fin n → (constantZModTwoGroup hS).SitePoint y'.left)
    (hg : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback _ m.left (g i) = g' i)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y' g'
        ((((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.map m.op).hom s) =
      ((baseRing.{u, w} hS).obj.map m.op).hom (pointsEval.{u, w} hS n y g s) :=
  (congrArg (fun v => ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y').op).hom
      (ULift.down v))
    ((congrArg (cechEval.{u, w} hS n (cechModule.{u, w} hS n)
        (canonicalTuple.{u, w} _ _ y'.left g') (toBaseHom.{u, w} hS y'))
      (cechCosimplicial_map_hom_eq.{u, w} hS n m s)).trans
        (cechEval_canonicalTuple_map.{u, w} hS n m g g' hg s))).trans
    ((congrArg ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y').op).hom
      (cechModule_map_down.{u, w} hS n
        (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg) _)).trans
      ((ConcreteCategory.comp_apply ((baseRing.{u, w} hS).obj.map ((structureFunctor.{u, w} hS).map
          ((cechProjection.{u, w} hS n).map
            (canonicalTupleHom.{u, w} _ (isSmooth_constantZModTwoGroup hS) m.left g g' hg))).op)
        ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y').op)
        (pointsEvalRaw.{u, w} hS n y g s)).symm.trans
        ((ConcreteCategory.congr_hom (baseRing_map_fromBaseHom_comp.{u, w} hS n m g g' hg)
          (pointsEvalRaw.{u, w} hS n y g s)).trans
          (ConcreteCategory.comp_apply _ _ _))))

/-- The components of the image of a section under a coface or codegeneracy are the components
of the section at the reindexed tuples. -/
theorem cechEval_cechCosimplicial_map {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj)
    (a : CechTuple.{u, w} (constantZModTwoGroup hS) (isSmooth_constantZModTwoGroup hS) n)
    (φ : (structureFunctor.{u, w} hS).obj ((cechProjection.{u, w} hS n).obj a) ⟶ y)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋m⦌).val.obj (op y)) :
    cechEval.{u, w} hS n (cechModule.{u, w} hS n) a φ
        ((((cechCosimplicial.{u, w} hS).map θ).val.app (op y)).hom s) =
      cechEval.{u, w} hS m (cechModule.{u, w} hS m)
        ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj a) φ s :=
  cechEval_reindex.{u, w} hS θ (structureModule.{u, w} hS) a φ s

/-- The comparison of the reindexed canonical tuple with the canonical tuple of `barMap θ g` is
compatible with `fromBaseHom`. -/
theorem fromBaseHom_comp_canonicalTupleReindexIso_inv {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left) :
    fromBaseHom.{u, w} hS y ≫ (structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS m).map
      (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv) =
      fromBaseHom.{u, w} hS y := by
  refine baseSlice_hom_ext _ _ ?_
  have hfac := IsHomLift.fac' (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)) (𝟙 y.left)
    (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv.target
  change (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        y.left).symm ≫
      (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
        (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS)
          θ g).inv.target).left =
    (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
      y.left).symm).left
  rw [hfac, Category.id_comp, eqToHom_trans, eqToHom_trans]

/-- The comparison of the reindexed canonical tuple with the canonical tuple of `barMap θ g` is
compatible with `toBaseHom`. -/
theorem canonicalTupleReindexIso_inv_comp_toBaseHom {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left) :
    (structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS m).map
      (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv) ≫
        toBaseHom.{u, w} hS y = toBaseHom.{u, w} hS y := by
  refine baseSlice_hom_ext _ _ ?_
  have hfac := IsHomLift.fac' (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)) (𝟙 y.left)
    (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv.target
  change ((stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
      (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv.target ≫
        eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
          y.left)).left =
    (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
      y.left)).left
  rw [hfac, Category.id_comp, eqToHom_trans, eqToHom_trans]

/-- The restriction of the structure sheaf of the base along the comparison of the reindexed
canonical tuple with the canonical tuple of `barMap θ g`, followed by `fromBaseHom`. -/
theorem baseRing_map_canonicalTupleReindexIso_inv {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left) :
    (baseRing.{u, w} hS).obj.map ((structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS m).map
      (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv)).op ≫
        (baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op =
      (baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op := by
  rw [← CategoryTheory.Functor.map_comp, ← op_comp,
    fromBaseHom_comp_canonicalTupleReindexIso_inv.{u, w} hS n θ y g]

/-- The component of a section of `𝒦ₘ` at the canonical tuple of `barMap θ g` is the restriction
of its component at the reindexed canonical tuple of `g`. -/
theorem cechEval_canonicalTuple_barMap {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj) (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋m⦌).val.obj (op y)) :
    cechEval.{u, w} hS m (cechModule.{u, w} hS m)
        (canonicalTuple.{u, w} _ _ y.left (barMap _ θ g)) (toBaseHom.{u, w} hS y) s =
      ConcreteCategory.hom ((cechModule.{u, w} hS m).val.presheaf.map
          (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv.op)
        (cechEval.{u, w} hS m (cechModule.{u, w} hS m)
          ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
            (canonicalTuple.{u, w} _ _ y.left g)) (toBaseHom.{u, w} hS y) s) :=
  (congrArg (fun φ => cechEval.{u, w} hS m (cechModule.{u, w} hS m)
      (canonicalTuple.{u, w} _ _ y.left (barMap _ θ g)) φ s)
        (canonicalTupleReindexIso_inv_comp_toBaseHom.{u, w} hS n θ y g).symm).trans
    (cechEval_comp.{u, w} hS m (cechModule.{u, w} hS m)
      (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv
      (toBaseHom.{u, w} hS y) s).symm

/-- The function `pointsEval` of the image of a section under the coface or codegeneracy along
`θ` is the component of the section at the reindexed canonical tuple. -/
theorem pointsEval_cechCosimplicial_map_eq {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋m⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y g ((((cechCosimplicial.{u, w} hS).map θ).val.app (op y)).hom s) =
      ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
        (cechEval.{u, w} hS m (cechModule.{u, w} hS m)
          ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
            (canonicalTuple.{u, w} _ _ y.left g)) (toBaseHom.{u, w} hS y) s).down :=
  congrArg (fun v => ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
      (ULift.down v))
    (cechEval_cechCosimplicial_map.{u, w} hS n θ y (canonicalTuple.{u, w} _ _ y.left g)
      (toBaseHom.{u, w} hS y) s)

/-- The restriction of `cₘ⁻¹ 𝒪_𝒳` along the comparison of the reindexed canonical tuple with the
canonical tuple of `barMap θ g`, read in the structure sheaf of the base. -/
theorem baseRing_map_canonicalTupleReindexIso_inv_apply {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (v : (cechModule.{u, w} hS m).val.presheaf.obj
      (op ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
        (canonicalTuple.{u, w} _ _ y.left g)))) :
    ((baseRing.{u, w} hS).obj.map ((structureFunctor.{u, w} hS).map
      ((cechProjection.{u, w} hS m).map
        (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv)).op).hom
          v.down =
      (ConcreteCategory.hom ((cechModule.{u, w} hS m).val.presheaf.map
        (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv.op)
          v).down :=
  (cechModule_map_down.{u, w} hS m
    (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv v).symm

/-- **`pointsEval` and the simplicial structure.** The component of the image of a section under
the coface or codegeneracy along `θ` at the points `g` is the component of the section at
`barMap θ g`. -/
theorem pointsEval_cosimplicial_map {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (y : (base.{u, w} hS).val.val.obj)
    (g : Fin n → (constantZModTwoGroup hS).SitePoint y.left)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋m⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y g ((((cechCosimplicial.{u, w} hS).map θ).val.app (op y)).hom s) =
      pointsEval.{u, w} hS m y (barMap _ θ g) s :=
  (pointsEval_cechCosimplicial_map_eq.{u, w} hS n θ y g s).trans
    (((ConcreteCategory.congr_hom (baseRing_map_canonicalTupleReindexIso_inv.{u, w} hS n θ y g)
      (cechEval.{u, w} hS m (cechModule.{u, w} hS m)
        ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
          (canonicalTuple.{u, w} _ _ y.left g)) (toBaseHom.{u, w} hS y) s).down).symm.trans
      (ConcreteCategory.comp_apply
        ((baseRing.{u, w} hS).obj.map ((structureFunctor.{u, w} hS).map
          ((cechProjection.{u, w} hS m).map
            (canonicalTupleReindexIso.{u, w} _ (isSmooth_constantZModTwoGroup hS) θ g).inv)).op)
        ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op)
        (cechEval.{u, w} hS m (cechModule.{u, w} hS m)
          ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
            (canonicalTuple.{u, w} _ _ y.left g)) (toBaseHom.{u, w} hS y) s).down)).trans
      ((congrArg ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
        (baseRing_map_canonicalTupleReindexIso_inv_apply.{u, w} hS n θ y g
          (cechEval.{u, w} hS m (cechModule.{u, w} hS m)
          ((Stacks.RelativeCech.Tuple.reindex _ _ θ.toOrderHom).obj
            (canonicalTuple.{u, w} _ _ y.left g)) (toBaseHom.{u, w} hS y) s))).trans
        (congrArg (fun v => ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom
          (ULift.down v)) (cechEval_canonicalTuple_barMap.{u, w} hS n θ y g s)).symm))

/-- **The component at a simplex `x` of the nerve of `ℤ/2`**: the morphism `𝒦ₙ ⟶ 𝒪_S` sending a
section over `y` to its component at the canonical tuple of the constant points of `x`. -/
def simplexComponent (x : nerveZModTwo _⦋n⦌) :
    (cechCosimplicial.{u, w} hS).obj ⦋n⦌ ⟶
      baseStructureModule.{u, w} hS where
  val :=
    { app := fun y =>
        letI : Module ((ringStructureSheafCore C S hS (base.{u, w} hS).val.val.p
              (base.{u, w} hS).val.isFiberedInGroupoids C.topology le_rfl).obj.obj y)
            (((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj y) :=
          (((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj y).isModule
        letI : Module ((ringStructureSheafCore C S hS (base.{u, w} hS).val.val.p
              (base.{u, w} hS).val.isFiberedInGroupoids C.topology le_rfl).obj.obj y)
            ((baseStructureModule.{u, w} hS).val.obj y) :=
          ((baseStructureModule.{u, w} hS).val.obj y).isModule
        ModuleCat.ofHom
        (X := ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj y)
        (Y := (baseStructureModule.{u, w} hS).val.obj y)
        { toFun := fun s => ULift.up
            (pointsEval.{u, w} hS n y.unop (simplexPoints hS y.unop.left x) s)
          map_add' := fun s s' => congrArg ULift.up (pointsEval_add.{u, w} hS n _ _ s s')
          map_smul' := fun r s => congrArg ULift.up (pointsEval_smul.{u, w} hS n _ _ r s) }
      naturality := fun {y y'} m => by
        ext s
        exact congrArg ULift.up (pointsEval_map.{u, w} hS n m.unop _ _
          (pullback_simplexPoints hS m.unop.left x) s) }

/-- The component of `simplexComponent x` at a section. -/
theorem simplexComponent_apply (x : nerveZModTwo _⦋n⦌) (y : (base.{u, w} hS).val.val.obj)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    ((simplexComponent.{u, w} hS n x).val.app (op y)).hom s =
      ULift.up (pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s) :=
  rfl

end Evaluation

/-! ### The components are a family of functions on `2ⁿ` copies of the base -/

section Bijective

variable (n : ℕ)

/-- The object `y.left ×_S Gⁿ` underlies the trivial torsor of the terminal arrow. -/
theorem stackProj_cechSectionsObj (y : (base.{u, w} hS).val.val.obj) :
    (stack.{u, w} hS).val.val.p.obj (cechSectionsObj.{u, w} hS y n) = powerObj y.left n :=
  stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS) _

/-- The global functions on `y.left ×_S Gⁿ` attached to a section of `𝒦ₙ` over `y`: its
component at the terminal arrow, transported along `stackProj_cechSectionsObj`. -/
def terminalFunctions (y : (base.{u, w} hS).val.val.obj)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    Γ((BigFppfOver.toScheme C S hS).obj (powerObj y.left n), ⊤) :=
  ((BigFppfOver.toScheme C S hS).map
      (eqToHom (stackProj_cechSectionsObj.{u, w} hS n y).symm)).appTop.hom
    (cechEval.{u, w} hS n
      (cechModule.{u, w} hS n) (cechTerminal.{u, w} hS y n).left
      (cechTerminal.{u, w} hS y n).hom s).down

/-- `terminalFunctions` is bijective: the component at the terminal arrow is the sections formula,
and the transport is along an isomorphism. -/
theorem bijective_terminalFunctions (y : (base.{u, w} hS).val.val.obj) :
    Function.Bijective (terminalFunctions.{u, w} hS n y) := by
  have h1 : Function.Bijective (fun s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y) =>
        cechEval.{u, w} hS n
          (cechModule.{u, w} hS n) (cechTerminal.{u, w} hS y n).left
          (cechTerminal.{u, w} hS y n).hom s) :=
    (ConcreteCategory.bijective_of_isIso
      (cechSectionsIsoApp.{u, w} hS y n (cechModule.{u, w} hS n)).hom)
  have h2 : Function.Bijective ((BigFppfOver.toScheme C S hS).map
      (eqToHom (stackProj_cechSectionsObj.{u, w} hS n y).symm)).appTop.hom := by
    have : IsIso ((BigFppfOver.toScheme C S hS).map
        (eqToHom (stackProj_cechSectionsObj.{u, w} hS n y).symm)) := Functor.map_isIso _ _
    have : IsIso (((BigFppfOver.toScheme C S hS).map
        (eqToHom (stackProj_cechSectionsObj.{u, w} hS n y).symm)).app ⊤) := inferInstance
    exact ConcreteCategory.bijective_of_isIso (((BigFppfOver.toScheme C S hS).map
        (eqToHom (stackProj_cechSectionsObj.{u, w} hS n y).symm)).app ⊤)
  exact h2.comp (Equiv.ulift.bijective.comp h1)

/-- The morphism of tuples from the canonical tuple of a simplex to the terminal tuple. -/
abbrev simplexToTerminal (y : (base.{u, w} hS).val.val.obj) (x : nerveZModTwo _⦋n⦌) :
    simplexTuple.{u, w} hS n y x ⟶ (cechTerminal.{u, w} hS y n).left :=
  ((isTerminalCechTerminal.{u, w} hS y n).from
    (CostructuredArrow.mk (Y := simplexTuple.{u, w} hS n y x) (toBaseHom.{u, w} hS y))).left

/-- `simplexToTerminal` lies over the structure morphisms to `y`. -/
theorem simplexToTerminal_w (y : (base.{u, w} hS).val.val.obj) (x : nerveZModTwo _⦋n⦌) :
    (structureFunctor.{u, w} hS).map ((cechProjection.{u, w} hS n).map
        (simplexToTerminal.{u, w} hS n y x)) ≫ (cechTerminal.{u, w} hS y n).hom =
      toBaseHom.{u, w} hS y :=
  CostructuredArrow.w ((isTerminalCechTerminal.{u, w} hS y n).from
    (CostructuredArrow.mk (Y := simplexTuple.{u, w} hS n y x) (toBaseHom.{u, w} hS y)))

/-- The base morphism of `simplexToTerminal` is the section of `y.left ×_S Gⁿ` given by the
string of the simplex. -/
theorem canonicalTupleHomBase_simplexToTerminal (y : (base.{u, w} hS).val.val.obj)
    (x : nerveZModTwo _⦋n⦌) :
    canonicalTupleHomBase.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        (simplexToTerminal.{u, w} hS n y x) =
      powerObjSection y.left n (simplexString x) := by
  have hspec := canonicalTupleHom_spec.{u, w} _ (isSmooth_constantZModTwoGroup hS)
    (simplexToTerminal.{u, w} hS n y x)
  refine eq_powerObjSection y.left n _ _ ?_ (fun i => hspec.2.2 i)
  have hw := congrArg (fun φ => φ.left.left) (simplexToTerminal_w.{u, w} hS n y x)
  change ((stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
      (simplexToTerminal.{u, w} hS n y x).target ≫
      eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        (powerObj y.left n)) ≫
        powerObjProj y.left n).left =
    (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
      y.left)).left at hw
  have hw' := Over.OverMorphism.ext hw
  change (eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        y.left).symm ≫
      (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
        (simplexToTerminal.{u, w} hS n y x).target ≫
        eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
          (powerObj y.left n))) ≫
      powerObjProj y.left n = 𝟙 y.left
  rw [Category.assoc, Category.assoc, hw', eqToHom_trans, eqToHom_refl]

/-- The structure morphism of the stack of the base, on `fromBaseHom`. -/
theorem baseProj_map_fromBaseHom (y : (base.{u, w} hS).val.val.obj) :
    (base.{u, w} hS).val.val.p.map (fromBaseHom.{u, w} hS y) =
      eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
        y.left).symm :=
  Over.OverMorphism.ext rfl

/-- **The component at a simplex is the restriction of the functions on `y.left ×_S Gⁿ` along
the section of the string of the simplex.** -/
theorem pointsEval_simplexPoints (y : (base.{u, w} hS).val.val.obj) (x : nerveZModTwo _⦋n⦌)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s =
      ((BigFppfOver.toScheme C S hS).map
        (powerObjSection y.left n (simplexString x))).appTop.hom
        (terminalFunctions.{u, w} hS n y s) := by
  have h1 : pointsEvalRaw.{u, w} hS n y (simplexPoints hS y.left x) s =
      ((stackRing.{u, w} hS).obj.map (simplexToTerminal.{u, w} hS n y x).target.op).hom
        (cechEval.{u, w} hS n (cechModule.{u, w} hS n) (cechTerminal.{u, w} hS y n).left
          (cechTerminal.{u, w} hS y n).hom s).down :=
    congrArg ULift.down ((congrArg (fun φ => cechEval.{u, w} hS n (cechModule.{u, w} hS n)
        (simplexTuple.{u, w} hS n y x) φ s) (simplexToTerminal_w.{u, w} hS n y x).symm).trans
      (cechEval_comp.{u, w} hS n (cechModule.{u, w} hS n) (simplexToTerminal.{u, w} hS n y x)
        (cechTerminal.{u, w} hS y n).hom s).symm)
  have hmor : (base.{u, w} hS).val.val.p.map (fromBaseHom.{u, w} hS y) ≫
      (stackProj.{u, w} _ (isSmooth_constantZModTwoGroup hS)).map
        (simplexToTerminal.{u, w} hS n y x).target =
        powerObjSection y.left n (simplexString x) ≫
          eqToHom (stackProj_atlasFunctor_obj.{u, w} _ (isSmooth_constantZModTwoGroup hS)
            (powerObj y.left n)).symm := by
    rw [baseProj_map_fromBaseHom, ← canonicalTupleHomBase_simplexToTerminal]
    unfold canonicalTupleHomBase
    rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  have h2 := congrArg (fun f => ((BigFppfOver.toScheme C S hS).map f).appTop.hom
    (cechEval.{u, w} hS n (cechModule.{u, w} hS n) (cechTerminal.{u, w} hS y n).left
      (cechTerminal.{u, w} hS y n).hom s).down) hmor
  simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp] at h2
  exact (congrArg ((baseRing.{u, w} hS).obj.map (fromBaseHom.{u, w} hS y).op).hom h1).trans h2

/-- **The components of a section of `𝒦ₙ` over `y` at the simplices of the nerve determine it,
and every family of functions over `y` indexed by the simplices arises.** -/
theorem bijective_pointsEval_simplexPoints (y : (base.{u, w} hS).val.val.obj) :
    Function.Bijective (fun (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y))
        (x : nerveZModTwo _⦋n⦌) =>
      pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s) := by
  have hfun : (fun (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y))
      (x : nerveZModTwo _⦋n⦌) =>
      pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s) =
      (Equiv.arrowCongr (simplexStringEquiv (n := n)).symm (Equiv.refl _)) ∘
        (fun (r : Γ((BigFppfOver.toScheme C S hS).obj (powerObj y.left n), ⊤))
          (σ : Fin n → ZMod 2) =>
            ((BigFppfOver.toScheme C S hS).map (powerObjSection y.left n σ)).appTop.hom r) ∘
        terminalFunctions.{u, w} hS n y := by
    funext s x
    exact pointsEval_simplexPoints.{u, w} hS n y x s
  rw [hfun]
  exact (Equiv.bijective _).comp ((bijective_powerObjSection_appTop y.left n).comp
    (bijective_terminalFunctions.{u, w} hS n y))

end Bijective

/-! ### The isomorphism with the bar cosimplicial object -/

section Iso

/-- **The comparison `𝒦 ⟶ cochainCosimplicial 𝒪_S`**: in degree `n`, the components at the
simplices of the nerve of `ℤ/2`. -/
def cechCosimplicialHom :
    cechCosimplicial.{u, w} hS ⟶ cochainCosimplicial (baseStructureModule.{u, w} hS) where
  app Δ := Pi.lift fun x => simplexComponent.{u, w} hS Δ.len x
  naturality {Δ Δ'} θ := by
    induction Δ using SimplexCategory.rec with | _ m => ?_
    induction Δ' using SimplexCategory.rec with | _ n => ?_
    refine Pi.hom_ext _ _ fun x => ?_
    rw [Category.assoc, Pi.lift_comp_π, Category.assoc, powCosimplicial_map_π, Pi.lift_comp_π]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun y => ?_)
    ext s
    change ULift.up (pointsEval.{u, w} hS n y.unop (simplexPoints hS y.unop.left x)
        ((((cechCosimplicial.{u, w} hS).map θ).val.app y).hom s)) =
      ULift.up (pointsEval.{u, w} hS m y.unop
        (simplexPoints hS y.unop.left (nerveZModTwo.map θ.op x)) s)
    rw [pointsEval_cosimplicial_map, simplexPoints_map]

/-- The components of the comparison are the components at the simplices. -/
theorem cechCosimplicialHom_app_π (Δ : SimplexCategory) (x : nerveZModTwo.obj (op Δ)) :
    (cechCosimplicialHom.{u, w} hS).app Δ ≫
        Pi.π (fun _ : nerveZModTwo.obj (op Δ) => baseStructureModule.{u, w} hS) x =
      simplexComponent.{u, w} hS Δ.len x :=
  Pi.lift_comp_π _ _

/-- The sections of a product of copies of `𝒪_S` are the families of sections. -/
theorem bijective_sections_pi (Δ : SimplexCategory) (y : ((base.{u, w} hS).val.val.obj)ᵒᵖ) :
    Function.Bijective (fun (t : (∏ᶜ fun _ : nerveZModTwo.obj (op Δ) =>
        baseStructureModule.{u, w} hS).val.obj y) (x : nerveZModTwo.obj (op Δ)) =>
      ((Pi.π (fun _ : nerveZModTwo.obj (op Δ) => baseStructureModule.{u, w} hS) x).val.app
        y).hom t) := by
  let E := SheafOfModules.evaluation (baseRing.{u, w} hS) y
  let f := fun _ : nerveZModTwo.obj (op Δ) => baseStructureModule.{u, w} hS
  let e : E.obj (∏ᶜ f) ≅ ModuleCat.of _ (∀ x, (f x).val.obj y) :=
    asIso (piComparison E f) ≪≫ ModuleCat.piIsoPi _
  have he : ∀ t, e.hom.hom t = fun x => ((Pi.π f x).val.app y).hom t := by
    intro t
    funext x
    have h1 := ModuleCat.piIsoPi_hom_ker_subtype_apply (fun x => E.obj (f x)) x
      ((piComparison E f).hom t)
    refine h1.trans ?_
    exact ConcreteCategory.congr_hom (piComparison_comp_π E f x) t
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [funext he] at hb
  exact hb

/-- The component at a simplex `x` of the comparison applied to a section is the function
`pointsEval` at the constant points of `x`. -/
theorem pi_π_cechCosimplicialHom_app_apply (n : ℕ) (x : nerveZModTwo _⦋n⦌)
    (y : (base.{u, w} hS).val.val.obj)
    (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y)) :
    ((Pi.π (fun _ : nerveZModTwo _⦋n⦌ => baseStructureModule.{u, w} hS) x).val.app
        (op y)).hom ((((cechCosimplicialHom.{u, w} hS).app ⦋n⦌).val.app (op y)).hom s) =
      ULift.up (pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s) := by
  have h := congrArg (fun g => (g.val.app (op y)).hom s)
    (cechCosimplicialHom_app_π.{u, w} hS ⦋n⦌ x)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply] at h
  exact h.trans (simplexComponent_apply.{u, w} hS n x y s)

/-- The comparison is bijective on the sections over every object. -/
theorem bijective_cechCosimplicialHom_app (n : ℕ) (y : (base.{u, w} hS).val.val.obj) :
    Function.Bijective (((cechCosimplicialHom.{u, w} hS).app ⦋n⦌).val.app (op y)).hom := by
  have hcomp : (fun t (x : nerveZModTwo _⦋n⦌) =>
      ((Pi.π (fun _ : nerveZModTwo _⦋n⦌ => baseStructureModule.{u, w} hS) x).val.app
        (op y)).hom t) ∘ (((cechCosimplicialHom.{u, w} hS).app ⦋n⦌).val.app (op y)).hom =
      fun s x => ULift.up (pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s) :=
    funext fun s => funext fun x => pi_π_cechCosimplicialHom_app_apply.{u, w} hS n x y s
  have hb : Function.Bijective (fun (s : ((cechCosimplicial.{u, w} hS).obj ⦋n⦌).val.obj (op y))
      (x : nerveZModTwo _⦋n⦌) =>
        ULift.up.{u + 1} (pointsEval.{u, w} hS n y (simplexPoints hS y.left x) s)) :=
    (Equiv.arrowCongr (Equiv.refl _) Equiv.ulift.symm).bijective.comp
      (bijective_pointsEval_simplexPoints.{u, w} hS n y)
  rw [← hcomp] at hb
  exact (Function.Bijective.of_comp_iff' (bijective_sections_pi.{u, w} hS ⦋n⦌ (op y)) _).1 hb

/-- The comparison is an isomorphism in every degree. -/
instance isIso_cechCosimplicialHom_app (Δ : SimplexCategory) :
    IsIso ((cechCosimplicialHom.{u, w} hS).app Δ) := by
  induction Δ using SimplexCategory.rec with | _ n => ?_
  have : Mono ((cechCosimplicialHom.{u, w} hS).app ⦋n⦌) :=
    (SheafOfModules.forget _).mono_of_mono_map
      (PresheafOfModules.mono_of_injective fun {V} =>
        (bijective_cechCosimplicialHom_app.{u, w} hS n V.unop).1)
  have : Epi ((cechCosimplicialHom.{u, w} hS).app ⦋n⦌) :=
    (SheafOfModules.forget _).epi_of_epi_map
      (PresheafOfModules.epi_of_surjective fun {V} =>
        (bijective_cechCosimplicialHom_app.{u, w} hS n V.unop).2)
  exact isIso_of_mono_of_epi _

/-- The comparison is an isomorphism of cosimplicial objects. -/
instance isIso_cechCosimplicialHom : IsIso (cechCosimplicialHom.{u, w} hS) :=
  have := isIso_cechCosimplicialHom_app.{u, w} hS
  NatIso.isIso_of_isIso_app _

/-- **`𝒦` is the bar cosimplicial object of `ℤ/2` with coefficients `𝒪_S`**:
`[n] ↦ ∏_{(ℤ/2)ⁿ} 𝒪_S`, the cofaces and codegeneracies being induced by the simplicial structure of
the nerve of `ℤ/2`. -/
def cechCosimplicialIso :
    cechCosimplicial.{u, w} hS ≅ cochainCosimplicial (baseStructureModule.{u, w} hS) :=
  asIso (cechCosimplicialHom.{u, w} hS)

end Iso

/-! ### The derived direct image -/



end AlgebraicGeometry.Stack.ClassifyingZModTwo

end
