module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SitePoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.Examples.Spaces.DoubledOriginGroupSpace

/-!
# Points of the constant group `(ℤ/2)_S` and its powers

Let `S` be a scheme in a big fppf site and let `G = (ℤ/2)_S = S ⊔ S` be the constant group
algebraic space of order two over `S` (`Stacks.Examples.constantZModTwoGroup`). This module
describes the points of `G` with values in objects of the site and the objects `T ×_S G^n`.

## Main definitions

* `Stacks.Examples.constantPoint`: for an object `T` of the site, the homomorphism
  `ℤ/2 → G(T)` sending `b` to the point landing in the copy of `S` labelled `b`.
* `Stacks.Examples.powerObj`: the object `T ×_S G^n` of the site, with its projection
  `Stacks.Examples.powerObjProj` to `T` and its `n` universal points
  `Stacks.Examples.powerObjPoint`.
* `Stacks.Examples.powerObjSection`: for `σ : Fin n → ℤ/2`, the section of
  `T ×_S G^n ⟶ T` whose coordinates are the constant points `σ i`.

## Main results

* `Stacks.Examples.pullback_constantPoint`: constant points are stable under pullback.
* `Stacks.Examples.existsUnique_powerObj`: the universal property of `T ×_S G^n`.
* `Stacks.Examples.isAffineOver_powerObj`: `T ×_S G^n` is affine when `T` is.
* `Stacks.Examples.bijective_powerObjSection_appTop`: the global functions on `T ×_S G^n` are
  the functions on the `2^n` copies of `T` cut out by the sections `powerObjSection T n σ`.

## Implementation notes

The points of `G` are read through
`AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsMulEquiv` as morphisms over `S` into
`S ⊔ S`, and then, through the representability of the functor of points, as morphisms of the
site into the object `S ⊔ S`. The object `T ×_S G^n` is the iterated binary product
`(⋯(T ⨯ G) ⨯ ⋯) ⨯ G` in the big fppf site over `S`. Its underlying scheme is computed one factor
at a time: the image of a binary product with the terminal object `S` is a fibre product of
schemes, and `X ×_S (S ⊔ S)` is the disjoint union of two copies of `X` by extensivity of the
category of schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Examples

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} (hS : 𝒞.Contains S)

/-- The constant group algebraic space `(ℤ/2)_S = S ⊔ S` over `S`. For `S` the affine line over a
field this is `Stacks.Examples.constantZ2GroupSpace`. -/
abbrev constantZModTwoGroup :
    Space.GroupAlgebraicSpace 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (Space.terminalSpace 𝒞 S hS).property :=
  (trivialDoubleCover S).groupSpace hS (contains_trivialDoubleCover_total hS)

/-- The scheme `S ⊔ S` underlying `(ℤ/2)_S`, as an object of the big fppf site over `S`. -/
abbrev constantZModTwoObj : BigFppfOver 𝒞 S hS :=
  (trivialDoubleCover S).siteObject hS (contains_trivialDoubleCover_total hS)

/-- The label of the copy of `S` in `S ⊔ S` corresponding to an element of `ℤ/2`: `0` is the
copy labelled `false` and `1` the copy labelled `true`. -/
def zmodTwoToBool (a : ZMod 2) : Bool :=
  decide (a = 1)

/-- The label of `0` is `false`. -/
@[simp]
lemma zmodTwoToBool_zero : zmodTwoToBool 0 = false := rfl

/-- The label of `1` is `true`. -/
@[simp]
lemma zmodTwoToBool_one : zmodTwoToBool 1 = true := rfl

/-- The label of a sum is the `xor` of the labels. -/
lemma zmodTwoToBool_add (a b : ZMod 2) :
    zmodTwoToBool (a + b) = (zmodTwoToBool a ^^ zmodTwoToBool b) := by
  revert a b
  decide

/-- Every element of `ℤ/2` is `0` or `1`. -/
lemma zmodTwo_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-! ### Points of `(ℤ/2)_S` -/

variable {hS}

/-- The points of `(ℤ/2)_S` with values in an object `T` of the site are the morphisms over `S`
from `T` to `S ⊔ S`, as groups. -/
def constantZModTwoPointMulEquiv (T : BigFppfOver 𝒞 S hS) :
    (constantZModTwoGroup hS).SitePoint T ≃*
      (Space.pointsOnSite 𝒞 S hS (constantZModTwoObj hS) (trivialDoubleCover S).grpObj).obj
        (Opposite.op T) :=
  Space.GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS _ _ T _

/-- The points of `(ℤ/2)_S` with values in an object `T` of the site are the morphisms of the site
from `T` to the object `S ⊔ S`. -/
def constantZModTwoPointEquiv (T : BigFppfOver 𝒞 S hS) :
    (constantZModTwoGroup hS).SitePoint T ≃ (T ⟶ constantZModTwoObj hS) :=
  (constantZModTwoPointMulEquiv T).toEquiv.trans
    (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
      (trivialDoubleCover S).grpObj).homEquiv.symm

/-- The identification of the functor of points of `S ⊔ S` on the site with the morphisms of the
site is the action of `AlgebraicGeometry.Space.toSchemeOver` on morphisms. -/
lemma pointsOnSiteRepresentableBy_homEquiv_apply {T : BigFppfOver 𝒞 S hS}
    (f : T ⟶ constantZModTwoObj hS) :
    (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
      (trivialDoubleCover S).grpObj).homEquiv f =
      (Space.toSchemeOver 𝒞 S hS).map f :=
  rfl

/-- Reading back a morphism of the site as a point and then as a morphism over `S`. -/
lemma constantZModTwoPointMulEquiv_symm_apply {T : BigFppfOver 𝒞 S hS}
    (f : T ⟶ constantZModTwoObj hS) :
    constantZModTwoPointMulEquiv T ((constantZModTwoPointEquiv T).symm f) =
      (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
        (trivialDoubleCover S).grpObj).homEquiv f :=
  (constantZModTwoPointMulEquiv T).apply_symm_apply _

/-- The identification of points with morphisms over `S` is natural: pulling a point back along
`m : T' ⟶ T` precomposes the morphism over `S` with `m`. -/
lemma constantZModTwoPointMulEquiv_pullback {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (x : (constantZModTwoGroup hS).SitePoint T) :
    constantZModTwoPointMulEquiv T'
        (Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) m x) =
      (Space.pointsOnSite 𝒞 S hS (constantZModTwoObj hS) (trivialDoubleCover S).grpObj ⋙
        forget GrpCat).map m.op (constantZModTwoPointMulEquiv T x) := by
  change yonedaEquiv ((Space.GroupAlgebraicSpace.toBaseHom m ≫ x).left ≫ prod.snd) =
    (Space.pointsOnSite 𝒞 S hS (constantZModTwoObj hS) (trivialDoubleCover S).grpObj ⋙
      forget GrpCat).map m.op (yonedaEquiv (x.left ≫ prod.snd))
  rw [Over.comp_left]
  exact (congrArg yonedaEquiv (Category.assoc _ _ _)).trans (yonedaEquiv_naturality _ _).symm

/-- Reading a point as a morphism of the site and then as a morphism over `S`. -/
lemma homEquiv_constantZModTwoPointEquiv {T : BigFppfOver 𝒞 S hS}
    (x : (constantZModTwoGroup hS).SitePoint T) :
    (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
      (trivialDoubleCover S).grpObj).homEquiv
        (constantZModTwoPointEquiv T x) =
      constantZModTwoPointMulEquiv T x :=
  (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
    (trivialDoubleCover S).grpObj).homEquiv.apply_symm_apply _

/-- The identification of points with morphisms of the site is natural: pulling a point back
along `m : T' ⟶ T` precomposes with `m`. -/
lemma constantZModTwoPointEquiv_pullback {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (x : (constantZModTwoGroup hS).SitePoint T) :
    constantZModTwoPointEquiv T'
        (Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) m x) =
      m ≫ constantZModTwoPointEquiv T x := by
  apply (Space.pointsOnSiteRepresentableBy 𝒞 S hS (constantZModTwoObj hS)
    (trivialDoubleCover S).grpObj).homEquiv.injective
  rw [Functor.RepresentableBy.homEquiv_comp, homEquiv_constantZModTwoPointEquiv,
    homEquiv_constantZModTwoPointEquiv]
  exact constantZModTwoPointMulEquiv_pullback m x

/-- The morphism of the site from `X` to `S ⊔ S` through the copy of `S` labelled `b`. -/
def constantHom (X : BigFppfOver 𝒞 S hS) (b : Bool) : X ⟶ constantZModTwoObj hS :=
  Over.homMk (ObjectProperty.homMk (X.hom.hom ≫ (trivialDoubleCover S).chart b)) (by
    ext
    change (X.hom.hom ≫ (trivialDoubleCover S).chart b) ≫ (trivialDoubleCover S).proj = X.hom.hom
    rw [Category.assoc, SectionCoverData.chart_comp_proj, Category.comp_id])

/-- The underlying morphism of schemes of `Stacks.Examples.constantHom` is the structure morphism
followed by the coprojection labelled `b`. -/
lemma toScheme_map_constantHom (X : BigFppfOver 𝒞 S hS) (b : Bool) :
    (BigFppfOver.toScheme 𝒞 S hS).map (constantHom X b) =
      X.hom.hom ≫ (trivialDoubleCover S).chart b :=
  rfl

/-- The morphisms through a fixed copy of `S` are compatible with precomposition. -/
@[reassoc (attr := simp)]
lemma comp_constantHom {X Y : BigFppfOver 𝒞 S hS} (m : X ⟶ Y) (b : Bool) :
    m ≫ constantHom Y b = constantHom X b := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  change m.left.hom ≫ Y.hom.hom ≫ _ = X.hom.hom ≫ _
  rw [← Over.w m]
  exact (Category.assoc _ _ _).symm

/-- `Stacks.Examples.constantHom`, read as a morphism over `S`, is the section labelled `b`. -/
lemma toSchemeOver_map_constantHom (X : BigFppfOver 𝒞 S hS) (b : Bool) :
    (Space.toSchemeOver 𝒞 S hS).map (constantHom X b) =
      overUnit _ ≫ (trivialDoubleCover S).partHom b :=
  Over.OverMorphism.ext rfl

/-- Products of points through fixed copies of `S` are computed by `xor` of the labels. -/
lemma overUnit_partHom_mul (X : CategoryTheory.Over S) (b c : Bool) :
    letI := (trivialDoubleCover S).grpObj
    (overUnit X ≫ (trivialDoubleCover S).partHom b) *
        (overUnit X ≫ (trivialDoubleCover S).partHom c) =
      overUnit X ≫ (trivialDoubleCover S).partHom (b ^^ c) :=
  (trivialDoubleCover S).lift_partHom_comp_mulHom b c _ _

/-- **The constant points of `(ℤ/2)_S`.** For an object `T` of the site, the group homomorphism
`ℤ/2 → (ℤ/2)_S(T)` sending `b` to the point `T ⟶ S ⟶ S ⊔ S` through the copy of `S` labelled `b`
(`0` is the copy labelled `false`, `1` the copy labelled `true`). -/
def constantPoint (T : BigFppfOver 𝒞 S hS) :
    Multiplicative (ZMod 2) →* (constantZModTwoGroup hS).SitePoint T :=
  MonoidHom.mk' (fun a => (constantZModTwoPointEquiv T).symm
      (constantHom T (zmodTwoToBool (Multiplicative.toAdd a)))) (by
    intro a b
    apply (constantZModTwoPointMulEquiv T).injective
    rw [map_mul (constantZModTwoPointMulEquiv T), constantZModTwoPointMulEquiv_symm_apply,
      constantZModTwoPointMulEquiv_symm_apply,
      constantZModTwoPointMulEquiv_symm_apply, pointsOnSiteRepresentableBy_homEquiv_apply,
      pointsOnSiteRepresentableBy_homEquiv_apply, pointsOnSiteRepresentableBy_homEquiv_apply,
      toSchemeOver_map_constantHom, toSchemeOver_map_constantHom, toSchemeOver_map_constantHom,
      toAdd_mul, zmodTwoToBool_add]
    exact (overUnit_partHom_mul _ _ _).symm)

/-- A constant point, read as a morphism of the site, is the morphism through the copy of `S`
with the corresponding label. -/
lemma constantZModTwoPointEquiv_constantPoint (T : BigFppfOver 𝒞 S hS)
    (a : Multiplicative (ZMod 2)) :
    constantZModTwoPointEquiv T (constantPoint T a) =
      constantHom T (zmodTwoToBool (Multiplicative.toAdd a)) :=
  (constantZModTwoPointEquiv T).apply_symm_apply _

/-- **Constant points are stable under pullback.** -/
theorem pullback_constantPoint {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (a : Multiplicative (ZMod 2)) :
    Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) m (constantPoint T a) =
      constantPoint T' a := by
  apply (constantZModTwoPointEquiv T').injective
  rw [constantZModTwoPointEquiv_pullback, constantZModTwoPointEquiv_constantPoint,
    constantZModTwoPointEquiv_constantPoint, comp_constantHom]

/-! ### The objects `T ×_S G^n` -/

/-- The object `T ×_S G^n` of the site, for `G = (ℤ/2)_S`: the iterated binary product
`(⋯(T ⨯ G) ⨯ ⋯) ⨯ G` in the big fppf site over `S`. -/
def powerObj (T : BigFppfOver 𝒞 S hS) : ℕ → BigFppfOver 𝒞 S hS
  | 0 => T
  | n + 1 => powerObj T n ⨯ constantZModTwoObj hS

/-- The projection `T ×_S G^n ⟶ T`. -/
def powerObjProj (T : BigFppfOver 𝒞 S hS) : (n : ℕ) → (powerObj T n ⟶ T)
  | 0 => 𝟙 T
  | n + 1 => prod.fst ≫ powerObjProj T n

/-- The `i`-th coordinate `T ×_S G^n ⟶ G`, as a morphism of the site to `S ⊔ S`. -/
def powerObjCoord (T : BigFppfOver 𝒞 S hS) :
    (n : ℕ) → Fin n → (powerObj T n ⟶ constantZModTwoObj hS)
  | 0 => fun i => i.elim0
  | n + 1 => fun i => Fin.lastCases (motive := fun _ => powerObj T (n + 1) ⟶ _)
      prod.snd (fun j => prod.fst ≫ powerObjCoord T n j) i

/-- The `i`-th universal point of `G` on `T ×_S G^n`. -/
def powerObjPoint (T : BigFppfOver 𝒞 S hS) (n : ℕ) (i : Fin n) :
    (constantZModTwoGroup hS).SitePoint (powerObj T n) :=
  (constantZModTwoPointEquiv (powerObj T n)).symm (powerObjCoord T n i)

/-- The morphism to `T ×_S G^n` with prescribed projection to `T` and prescribed coordinates. -/
def powerObjLift (T : BigFppfOver 𝒞 S hS) {T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T) :
    (n : ℕ) → (Fin n → (T' ⟶ constantZModTwoObj hS)) → (T' ⟶ powerObj T n)
  | 0, _ => m
  | n + 1, g => prod.lift (powerObjLift T m n fun i => g i.castSucc) (g (Fin.last n))

/-- The projection of `T ×_S G^(n+1)` is the first projection followed by that of
`T ×_S G^n`. -/
lemma powerObjProj_succ (T : BigFppfOver 𝒞 S hS) (n : ℕ) :
    powerObjProj T (n + 1) = prod.fst ≫ powerObjProj T n :=
  rfl

/-- The last coordinate of `T ×_S G^(n+1)` is the second projection. -/
lemma powerObjCoord_last (T : BigFppfOver 𝒞 S hS) (n : ℕ) :
    powerObjCoord T (n + 1) (Fin.last n) = prod.snd := by
  unfold powerObjCoord
  exact Fin.lastCases_last

/-- The earlier coordinates of `T ×_S G^(n+1)` are those of `T ×_S G^n`. -/
lemma powerObjCoord_castSucc (T : BigFppfOver 𝒞 S hS) (n : ℕ) (j : Fin n) :
    powerObjCoord T (n + 1) j.castSucc = prod.fst ≫ powerObjCoord T n j :=
  Fin.lastCases_castSucc (motive := fun _ => powerObj T (n + 1) ⟶ constantZModTwoObj hS) j

/-- The lift has the prescribed projection. -/
@[reassoc (attr := simp)]
lemma powerObjLift_proj (T : BigFppfOver 𝒞 S hS) {T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (n : ℕ) (g : Fin n → (T' ⟶ constantZModTwoObj hS)) :
    powerObjLift T m n g ≫ powerObjProj T n = m := by
  induction n with
  | zero => exact Category.comp_id m
  | succ n ih =>
    rw [powerObjProj_succ]
    change prod.lift _ _ ≫ prod.fst ≫ _ = m
    rw [prod.lift_fst_assoc, ih]

/-- The lift has the prescribed coordinates. -/
@[reassoc (attr := simp)]
lemma powerObjLift_coord (T : BigFppfOver 𝒞 S hS) {T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (n : ℕ) (g : Fin n → (T' ⟶ constantZModTwoObj hS)) (i : Fin n) :
    powerObjLift T m n g ≫ powerObjCoord T n i = g i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last =>
      rw [powerObjCoord_last]
      exact prod.lift_snd _ _
    | cast j =>
      rw [powerObjCoord_castSucc]
      change prod.lift _ _ ≫ prod.fst ≫ _ = _
      rw [prod.lift_fst_assoc, ih]

/-- A morphism to `T ×_S G^n` is determined by its projection and its coordinates. -/
lemma eq_powerObjLift (T : BigFppfOver 𝒞 S hS) {T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T)
    (n : ℕ) (g : Fin n → (T' ⟶ constantZModTwoObj hS)) (k : T' ⟶ powerObj T n)
    (hk : k ≫ powerObjProj T n = m) (hg : ∀ i, k ≫ powerObjCoord T n i = g i) :
    k = powerObjLift T m n g := by
  induction n with
  | zero => exact (Category.comp_id k).symm.trans hk
  | succ n ih =>
    change k = prod.lift _ _
    refine prod.hom_ext ?_ ?_
    · rw [prod.lift_fst]
      refine ih _ (k ≫ prod.fst) ?_ fun j => ?_
      · exact (Category.assoc _ _ _).trans hk
      · exact (Category.assoc _ _ _).trans
          ((congrArg (k ≫ ·) (powerObjCoord_castSucc T n j)).symm.trans (hg _))
    · rw [prod.lift_snd]
      exact (congrArg (k ≫ ·) (powerObjCoord_last T n)).symm.trans (hg _)

/-- Pulling back a universal point of `T ×_S G^n` along `k` gives the point whose morphism of the
site is `k` followed by the corresponding coordinate. -/
lemma constantZModTwoPointEquiv_pullback_powerObjPoint (T : BigFppfOver 𝒞 S hS) (n : ℕ)
    {T' : BigFppfOver 𝒞 S hS} (k : T' ⟶ powerObj T n) (i : Fin n) :
    constantZModTwoPointEquiv T'
        (Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) k
          (powerObjPoint T n i)) =
      k ≫ powerObjCoord T n i := by
  rw [constantZModTwoPointEquiv_pullback, powerObjPoint, Equiv.apply_symm_apply]

/-- **The universal property of `T ×_S G^n`.** A morphism to `T ×_S G^n` is the same as a morphism
to `T` together with `n` points of `G`. -/
theorem existsUnique_powerObj (T : BigFppfOver 𝒞 S hS) (n : ℕ) :
    ∀ (T' : BigFppfOver 𝒞 S hS) (m : T' ⟶ T) (g : Fin n → (constantZModTwoGroup hS).SitePoint T'),
      ∃! k : T' ⟶ powerObj T n, k ≫ powerObjProj T n = m ∧
        ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) k
          (powerObjPoint T n i) = g i := by
  intro T' m g
  have key (k : T' ⟶ powerObj T n) (i : Fin n) :
      Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) k
          (powerObjPoint T n i) = g i ↔
        k ≫ powerObjCoord T n i = constantZModTwoPointEquiv T' (g i) := by
    rw [← constantZModTwoPointEquiv_pullback_powerObjPoint, Equiv.apply_eq_iff_eq]
  refine ⟨powerObjLift T m n fun i => constantZModTwoPointEquiv T' (g i),
    ⟨powerObjLift_proj T m n _, fun i => (key _ i).2 (powerObjLift_coord T m n _ i)⟩,
    fun k hk => eq_powerObjLift T m n _ k hk.1 fun i => (key k i).1 (hk.2 i)⟩

/-! ### The underlying scheme of `T ×_S G^n` -/

/-- The image under `AlgebraicGeometry.BigFppfOver.toScheme` of a binary product with `S ⊔ S` is
the fibre product over `S`. -/
lemma isPullback_toScheme_prod (X : BigFppfOver 𝒞 S hS) :
    IsPullback ((BigFppfOver.toScheme 𝒞 S hS).map (prod.fst : X ⨯ constantZModTwoObj hS ⟶ X))
      ((BigFppfOver.toScheme 𝒞 S hS).map (prod.snd : X ⨯ constantZModTwoObj hS ⟶ _))
      X.hom.hom (trivialDoubleCover S).proj := by
  have h := (BigFppfOver.toScheme 𝒞 S hS).map_isPullback
    (IsPullback.of_is_product' (prodIsProd X (constantZModTwoObj hS))
      (isTerminal_mkId_bigFppfOver 𝒞 S hS))
  have hX (Y : BigFppfOver 𝒞 S hS) :
      (BigFppfOver.toScheme 𝒞 S hS).map ((isTerminal_mkId_bigFppfOver 𝒞 S hS).from Y) =
        Y.hom.hom := by
    have h' := (Category.comp_id _).symm.trans
      (Over.w ((isTerminal_mkId_bigFppfOver 𝒞 S hS).from Y))
    change ((isTerminal_mkId_bigFppfOver 𝒞 S hS).from Y).left.hom = Y.hom.hom
    rw [h']
  rw [hX, hX] at h
  exact h

/-- The projection `T ×_S G^(n+1) ⟶ T ×_S G^n` is affine on underlying schemes. -/
lemma isAffineHom_toScheme_prod_fst (X : BigFppfOver 𝒞 S hS) :
    IsAffineHom ((BigFppfOver.toScheme 𝒞 S hS).map
      (prod.fst : X ⨯ constantZModTwoObj hS ⟶ X)) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_toScheme_prod X).flip
    (inferInstanceAs (IsAffineHom (trivialDoubleCover S).proj))

/-- **`T ×_S G^n` is affine when `T` is.** -/
theorem isAffineOver_powerObj (T : BigFppfOver 𝒞 S hS) (n : ℕ)
    (hT : IsAffineOver 𝒞 S hS T) : IsAffineOver 𝒞 S hS (powerObj T n) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    have hA : IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj (powerObj T n)) := ih
    exact @isAffine_of_isAffineHom _ _ _ (isAffineHom_toScheme_prod_fst (powerObj T n)) hA

/-- The section `X ⟶ X ⨯ (S ⊔ S)` through the copy of `S` labelled `b`. -/
def prodSection (X : BigFppfOver 𝒞 S hS) (b : Bool) : X ⟶ X ⨯ constantZModTwoObj hS :=
  prod.lift (𝟙 X) (constantHom X b)

/-- The section through the copy labelled `b` is the base change of the coprojection labelled
`b`. -/
lemma isPullback_prodSection (X : BigFppfOver 𝒞 S hS) (b : Bool) :
    IsPullback ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X b)) X.hom.hom
      ((BigFppfOver.toScheme 𝒞 S hS).map (prod.snd : X ⨯ constantZModTwoObj hS ⟶ _))
      ((trivialDoubleCover S).chart b) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_toScheme_prod X)
  · have h₁ : (BigFppfOver.toScheme 𝒞 S hS).map (prodSection X b) ≫
        (BigFppfOver.toScheme 𝒞 S hS).map (prod.fst : X ⨯ constantZModTwoObj hS ⟶ X) = 𝟙 _ := by
      rw [← Functor.map_comp, prodSection, prod.lift_fst, CategoryTheory.Functor.map_id]
    have h₂ : (trivialDoubleCover S).chart b ≫ (trivialDoubleCover S).proj = 𝟙 S :=
      (trivialDoubleCover S).chart_comp_proj b
    exact h₁ ▸ h₂ ▸ IsPullback.id_horiz X.hom.hom
  · rw [← Functor.map_comp, prodSection, prod.lift_snd]
    rfl

/-- **`X ×_S (S ⊔ S)` is the disjoint union of two copies of `X`**, embedded by the two sections
`Stacks.Examples.prodSection`. -/
lemma isIso_coprodDesc_prodSection (X : BigFppfOver 𝒞 S hS) :
    IsIso (coprod.desc ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X false))
      ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X true))) := by
  have hvk := FinitaryExtensive.van_kampen' (BinaryCofan.mk (coprod.inl : S ⟶ S ⨿ S) coprod.inr)
    (coprodIsCoprod S S)
  have hc := ((BinaryCofan.isVanKampen_iff _).1 hvk
    (BinaryCofan.mk ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X false))
      ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X true)))
    X.hom.hom X.hom.hom
    ((BigFppfOver.toScheme 𝒞 S hS).map (prod.snd : X ⨯ constantZModTwoObj hS ⟶ _))
    (isPullback_prodSection X false).w.symm (isPullback_prodSection X true).w.symm).2
    ⟨isPullback_prodSection X false, isPullback_prodSection X true⟩
  obtain ⟨hc⟩ := hc
  let e := (coprodIsCoprod _ _).coconePointUniqueUpToIso hc
  have he : e.hom = coprod.desc ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X false))
      ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X true)) := by
    refine coprod.hom_ext ?_ ?_
    · exact (IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _) hc ⟨.left⟩).trans
        (coprod.inl_desc _ _).symm
    · exact (IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _) hc ⟨.right⟩).trans
        (coprod.inr_desc _ _).symm
  rw [← he]
  exact Iso.isIso_hom e

/-- **Global functions on `X ×_S (S ⊔ S)`** are pairs of global functions on `X`, by pullback
along the two sections. -/
lemma bijective_prodSection_appTop (X : BigFppfOver 𝒞 S hS) :
    Function.Bijective (RingHom.prod
      ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X false)).appTop.hom
      ((BigFppfOver.toScheme 𝒞 S hS).map (prodSection X true)).appTop.hom) := by
  have := isIso_coprodDesc_prodSection X
  exact bijective_prod_appTop _ _

/-- For `σ : Fin n → ℤ/2`, the section of `T ×_S G^n ⟶ T` whose `i`-th coordinate is the constant
point `σ i`: the unique morphism of `Stacks.Examples.existsUnique_powerObj` for the identity of `T`
and the constant points `σ i` (`Stacks.Examples.powerObjSection_proj`,
`Stacks.Examples.pullback_powerObjSection_powerObjPoint` and
`Stacks.Examples.eq_powerObjSection`). -/
def powerObjSection (T : BigFppfOver 𝒞 S hS) (n : ℕ) (σ : Fin n → ZMod 2) :
    T ⟶ powerObj T n :=
  powerObjLift T (𝟙 T) n fun i => constantHom T (zmodTwoToBool (σ i))

/-- The section `powerObjSection T n σ` is a section of the projection to `T`. -/
@[reassoc (attr := simp)]
lemma powerObjSection_proj (T : BigFppfOver 𝒞 S hS) (n : ℕ) (σ : Fin n → ZMod 2) :
    powerObjSection T n σ ≫ powerObjProj T n = 𝟙 T :=
  powerObjLift_proj T _ n _

/-- The coordinates of `powerObjSection T n σ` are the constant points `σ i`. -/
theorem pullback_powerObjSection_powerObjPoint (T : BigFppfOver 𝒞 S hS) (n : ℕ)
    (σ : Fin n → ZMod 2) (i : Fin n) :
    Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS)
        (powerObjSection T n σ) (powerObjPoint T n i) =
      constantPoint T (Multiplicative.ofAdd (σ i)) := by
  apply (constantZModTwoPointEquiv T).injective
  rw [constantZModTwoPointEquiv_pullback_powerObjPoint, constantZModTwoPointEquiv_constantPoint,
    powerObjSection, powerObjLift_coord]
  rfl

/-- `powerObjSection T n σ` is the unique morphism `k` with `k ≫ powerObjProj T n = 𝟙 T` whose
coordinates are the constant points `σ i`. -/
theorem eq_powerObjSection (T : BigFppfOver 𝒞 S hS) (n : ℕ) (σ : Fin n → ZMod 2)
    (k : T ⟶ powerObj T n) (hk : k ≫ powerObjProj T n = 𝟙 T)
    (hpt : ∀ i, Space.GroupAlgebraicSpace.SitePoint.pullback (constantZModTwoGroup hS) k
      (powerObjPoint T n i) = constantPoint T (Multiplicative.ofAdd (σ i))) :
    k = powerObjSection T n σ :=
  (existsUnique_powerObj T n T (𝟙 T) fun i => constantPoint T (Multiplicative.ofAdd (σ i))).unique
    ⟨hk, hpt⟩ ⟨powerObjSection_proj T n σ, pullback_powerObjSection_powerObjPoint T n σ⟩

/-- The section for `σ : Fin (n+1) → ℤ/2` is the section for its first `n` values followed by the
section through the copy of `S` labelled by its last value. -/
lemma powerObjSection_succ (T : BigFppfOver 𝒞 S hS) (n : ℕ) (σ : Fin (n + 1) → ZMod 2) :
    powerObjSection T (n + 1) σ =
      powerObjSection T n (Fin.init σ) ≫
        prodSection (powerObj T n) (zmodTwoToBool (σ (Fin.last n))) := by
  change prod.lift _ _ = _
  refine prod.hom_ext ?_ ?_
  · rw [prod.lift_fst, prodSection, Category.assoc, prod.lift_fst, Category.comp_id]
    rfl
  · rw [prod.lift_snd, prodSection, Category.assoc, prod.lift_snd, comp_constantHom]

/-- The restriction of a global function on `T ×_S G^(n+1)` to the copy indexed by `σ` is its
restriction along the section labelled by the last value of `σ`, then to the copy of `T` indexed
by the first `n` values. -/
lemma powerObjSection_succ_appTop (T : BigFppfOver 𝒞 S hS) (n : ℕ) (σ : Fin (n + 1) → ZMod 2)
    (r : Γ((BigFppfOver.toScheme 𝒞 S hS).obj (powerObj T (n + 1)), ⊤)) :
    ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T (n + 1) σ)).appTop.hom r =
      ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T n (Fin.init σ))).appTop.hom
        (((BigFppfOver.toScheme 𝒞 S hS).map
          (prodSection (powerObj T n) (zmodTwoToBool (σ (Fin.last n))))).appTop.hom r) :=
  (congrArg (fun f => ((BigFppfOver.toScheme 𝒞 S hS).map f).appTop.hom r)
    (powerObjSection_succ T n σ)).trans
    ((congrArg (fun f => f.appTop.hom r) ((BigFppfOver.toScheme 𝒞 S hS).map_comp
      (powerObjSection T n (Fin.init σ))
      (prodSection (powerObj T n) (zmodTwoToBool (σ (Fin.last n)))))).trans
      (congrArg (fun f => CommRingCat.Hom.hom f r) (Scheme.Hom.comp_appTop
        ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T n (Fin.init σ)))
        ((BigFppfOver.toScheme 𝒞 S hS).map
          (prodSection (powerObj T n) (zmodTwoToBool (σ (Fin.last n))))))))

/-- **Global functions on `T ×_S G^n` are the families of global functions on the `2^n` copies of
`T`.** Mathematically `T ×_S G^n` is the disjoint union of copies of `T` indexed by
`σ : Fin n → ℤ/2`, the copy indexed by `σ` being the image of `powerObjSection T n σ`; so
restricting a global function to these copies is a bijection. -/
theorem bijective_powerObjSection_appTop (T : BigFppfOver 𝒞 S hS) (n : ℕ) :
    Function.Bijective
      (fun (r : Γ((BigFppfOver.toScheme 𝒞 S hS).obj (powerObj T n), ⊤))
          (σ : Fin n → ZMod 2) =>
        ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T n σ)).appTop.hom r) := by
  induction n with
  | zero =>
    have h0 (σ : Fin 0 → ZMod 2) (r : Γ((BigFppfOver.toScheme 𝒞 S hS).obj (powerObj T 0), ⊤)) :
        ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T 0 σ)).appTop.hom r = r := by
      change ((BigFppfOver.toScheme 𝒞 S hS).map (𝟙 T)).appTop.hom r = r
      exact (congrArg (fun f => f.appTop.hom r) ((BigFppfOver.toScheme 𝒞 S hS).map_id T)).trans
        (congrArg (fun f => CommRingCat.Hom.hom f r)
          (Scheme.Hom.id_appTop (X := (BigFppfOver.toScheme 𝒞 S hS).obj T)))
    refine ⟨fun r r' h => ?_, fun φ => ⟨φ finZeroElim, ?_⟩⟩
    · have := congrFun h finZeroElim
      simp only [h0] at this
      exact this
    · funext σ
      exact (h0 σ _).trans (congrArg φ (funext fun i => i.elim0))
  | succ n ih =>
    have hsnoc (r : Γ((BigFppfOver.toScheme 𝒞 S hS).obj (powerObj T (n + 1)), ⊤))
        (τ : Fin n → ZMod 2) (a : ZMod 2) :
        ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T (n + 1) (Fin.snoc τ a))).appTop.hom
            r =
          ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T n τ)).appTop.hom
            (((BigFppfOver.toScheme 𝒞 S hS).map
              (prodSection (powerObj T n) (zmodTwoToBool a))).appTop.hom r) :=
      (powerObjSection_succ_appTop T n (Fin.snoc τ a) r).trans
        (congrArg₂ (fun (τ' : Fin n → ZMod 2) (a' : ZMod 2) =>
          ((BigFppfOver.toScheme 𝒞 S hS).map (powerObjSection T n τ')).appTop.hom
            (((BigFppfOver.toScheme 𝒞 S hS).map
              (prodSection (powerObj T n) (zmodTwoToBool a'))).appTop.hom r))
          (Fin.init_snoc (α := fun _ => ZMod 2) (p := τ) (x := a))
          (Fin.snoc_last (α := fun _ => ZMod 2) (p := τ) (x := a)))
    have hpair := bijective_prodSection_appTop (powerObj T n)
    refine ⟨fun r r' h => hpair.1 ?_, fun φ => ?_⟩
    · have hb (a : ZMod 2) :
          ((BigFppfOver.toScheme 𝒞 S hS).map
              (prodSection (powerObj T n) (zmodTwoToBool a))).appTop.hom r =
            ((BigFppfOver.toScheme 𝒞 S hS).map
              (prodSection (powerObj T n) (zmodTwoToBool a))).appTop.hom r' := by
        exact ih.1 (funext fun τ =>
          (hsnoc r τ a).symm.trans ((congrFun h (Fin.snoc τ a)).trans (hsnoc r' τ a)))
      exact Prod.ext (hb 0) (hb 1)
    · obtain ⟨u₀, hu₀⟩ := ih.2 fun τ => φ (Fin.snoc τ 0)
      obtain ⟨u₁, hu₁⟩ := ih.2 fun τ => φ (Fin.snoc τ 1)
      obtain ⟨r, hr⟩ := hpair.2 (u₀, u₁)
      refine ⟨r, funext fun σ => ?_⟩
      obtain ⟨τ, a, rfl⟩ : ∃ (τ : Fin n → ZMod 2) (a : ZMod 2), σ = Fin.snoc τ a :=
        ⟨Fin.init σ, σ (Fin.last n), (Fin.snoc_init_self σ).symm⟩
      refine (hsnoc r τ a).trans ?_
      rcases zmodTwo_eq_zero_or_eq_one a with rfl | rfl
      · have : ((BigFppfOver.toScheme 𝒞 S hS).map
            (prodSection (powerObj T n) false)).appTop.hom r = u₀ := congrArg Prod.fst hr
        rw [zmodTwoToBool_zero, this]
        exact congrFun hu₀ τ
      · have : ((BigFppfOver.toScheme 𝒞 S hS).map
            (prodSection (powerObj T n) true)).appTop.hom r = u₁ := congrArg Prod.snd hr
        rw [zmodTwoToBool_one, this]
        exact congrFun hu₁ τ

end Stacks.Examples
