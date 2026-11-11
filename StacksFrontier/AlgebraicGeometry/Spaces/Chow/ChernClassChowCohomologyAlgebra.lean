module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassCommutation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassNonConstantRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra

/-!
# Chern classes in the Chow cohomology algebra

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. The Chern classes `c_j(ℰ) ∈ A^j(X)` of Stacks 0ERZ (`AlgebraicGeometry.Space.chernClass`)
are bivariant classes of the graded group `AlgebraicGeometry.Space.chowCohomologyCanonical`, whose
cap operations land in the Chow groups of `X ×_X X'`. This file places them in the graded ring
`A^*(X) = AlgebraicGeometry.Space.ChowCohomologyAlgebra` of Stacks 0ERK, where `X ×_X X'` is
taken to be `X'`, and makes `A^*(X)` act on the Chow homology `CH_*(X') = ⨁_k CH_k(X')` of every
good test space `X' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.ChowCohomologyClass.chernClass`: the `j`-th Chern class
  `c_j(ℰ) ∈ A^j(X)` as an element of `AlgebraicGeometry.Space.ChowCohomologyClass`, capping on a
  test space `X'` as `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')`
  (`AlgebraicGeometry.Space.chernCap`).
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass`: the total Chern class
  `c(ℰ) = c₀(ℰ) + … + c_r(ℰ)` in the ring `A^*(X)`.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.capChowHomology`: the ring homomorphism
  `A^*(X) ⟶ End(CH_*(X'))` of the cap product on a good test space `X' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyClass.chernClass_cap_eq`: the two models of
  `c_j(ℰ)` have the same cap operations, read on `X ×_X X' ≅ X'`.
* `AlgebraicGeometry.Space.ChowCohomologyClass.capChowHomology_comp` and
  `AlgebraicGeometry.Space.ChowCohomologyClass.capChowHomology_one`: the cap product on Chow
  homology is multiplicative and unital.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.ext_capChowHomology`: an element of `A^*(X)` is
  determined by its cap products on the Chow homology of all good test spaces.
* `AlgebraicGeometry.Space.ChowCohomologyClass.chernClass_capChowHomology_of`: on `CH_k(X')`
  the class `c_j(ℰ)` caps as `c_j(ℰ) ∩ -`.

## Implementation notes

The cap operation of a class in `AlgebraicGeometry.Space.ChowCohomologyClass` is indexed by a
target degree `l` with `l + p = k`; for `c_j(ℰ)` it is `c_j(ℰ) ∩ -` followed by the
identification `CH_{k-j} = CH_l` (`AlgebraicGeometry.Space.chowGroupCanonicalDegreeCongr`). Its
three axioms are `AlgebraicGeometry.Space.chernCap_properPushforward`,
`AlgebraicGeometry.Space.chernCap_flatPullback` and `AlgebraicGeometry.Space.chernCap_gysin`,
the proper axiom (1) being read on a cycle representative of `c_j(ℰ) ∩ [α]`.

## References

* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

/-! ### Transport of degrees -/

section DegreeCongr

variable (D : BaseSpaceDimensionSituation.{u})

/-- Flat pullback into a degree `a'`, transported along `a' = b'`, is flat pullback into
degree `b'`. -/
theorem chowGroupCanonicalDegreeCongr_flatPullbackChowMapCanonical {Y Y' : D.Ambient}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY')
    (f : Y' ⟶ Y) (hf : f ≫ sY = sY') (m : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hm : HasRelativeDimension m D.site D.base D.base_mem f) {a a' b' : ℤ} (h : a' = b')
    (ha : a + (m : ℤ) = a') (hb : a + (m : ℤ) = b') (x : chowGroupCanonical.{u + 1} D sY hY a) :
    chowGroupCanonicalDegreeCongr D sY' hY' h
        (flatPullbackChowMapCanonical.{u + 1} D sY' hY' sY hY f hf m hflat hm a a' ha x) =
      flatPullbackChowMapCanonical.{u + 1} D sY' hY' sY hY f hf m hflat hm a b' hb x := by
  subst h
  rfl

end DegreeCongr

/-! ### The Chern classes in `A^*(X)` -/

section Chern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)

/-- **The `j`-th Chern class `c_j(ℰ) ∈ A^j(X)`** (Stacks 0ERZ) of a finite locally free module
`ℰ` of rank `r` on a good algebraic space `X/B`, `j = 0, …, r`, as an element of the degree `j`
component of the Chow cohomology ring `A^*(X)` (Stacks 0ERK). On a good test space
`g : X' ⟶ X` it caps as `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')`
(`AlgebraicGeometry.Space.chernCap`), the target degree being written `l` with `l + j = k`. It
has the cap operations of `AlgebraicGeometry.Space.chernClass`, read on `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.ChowCohomologyClass.chernClass_cap_eq`). -/
def ChowCohomologyClass.chernClass (j : Fin (r + 1)) :
    ChowCohomologyClass D sX hX ((j : ℕ) : ℤ) where
  cap g hY k l hl :=
    (chowGroupCanonicalDegreeCongr D (g ≫ sX) hY
      (by omega : k - ((j : ℕ) : ℤ) = l)).toAddMonoidHom.comp
        (Space.chernCap D sX hX E r hE g hY j k)
  proper_naturality g hY' h hY'' hh k l hkl α := by
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    obtain ⟨β, hβ⟩ : ∃ β, chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' (k - ((j : ℕ) : ℤ)) β =
        Space.chernCap D sX hX E r hE (h ≫ g) hY'' j k
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' k α) :=
      QuotientAddGroup.mk'_surjective _ _
    refine ⟨β, ?_, ?_⟩
    · simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        chowGroupCanonicalDegreeCongr_refl]
      exact hβ.symm
    · simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        chowGroupCanonicalDegreeCongr_refl]
      rw [← chowGroupCanonicalProperPushforward_chowClassCanonical D _ hY'' _ hY'
        (Category.assoc h g sX).symm hh, chernCap_properPushforward, ← hβ,
        chowGroupCanonicalProperPushforward_chowClassCanonical]
  flat_naturality g hY' h hY'' m hh hm k l hkl k' l' hk hl x := by
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    subst hk hl
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      chowGroupCanonicalDegreeCongr_refl]
    rw [chernCap_flatPullback]
    exact chowGroupCanonicalDegreeCongr_flatPullbackChowMapCanonical D _ hY' _ hY'' h _ m hh hm
      _ _ _ _
  gysin_naturality g hY' L σ hL k l hkl x := by
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      chowGroupCanonicalDegreeCongr_refl]
    exact (chernCap_gysin D sX hX E r hE j g hY' L σ hL k x).trans
      (congrArg _ (degreeCast_eq_chowGroupCanonicalDegreeCongr (g ≫ sX) hY' _ _))

/-- The class `c_j(ℰ) ∈ A^j(X)` caps on a test space `g : X' ⟶ X` as `c_j(ℰ) ∩ -`, followed by
the identification `CH_{k-j}(X') = CH_l(X')`. -/
theorem ChowCohomologyClass.chernClass_cap (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k l : ℤ) (hl : l + ((j : ℕ) : ℤ) = k)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (ChowCohomologyClass.chernClass D sX hX E r hE j).cap g hY k l hl α =
      chowGroupCanonicalDegreeCongr D (g ≫ sX) hY (by omega)
        (Space.chernCap D sX hX E r hE g hY j k α) :=
  rfl

/-- In the target degree `k - j`, the class `c_j(ℰ) ∈ A^j(X)` caps as `c_j(ℰ) ∩ -`. -/
theorem ChowCohomologyClass.chernClass_cap_sub (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (ChowCohomologyClass.chernClass D sX hX E r hE j).cap g hY k (k - ((j : ℕ) : ℤ))
        (by omega) α =
      Space.chernCap D sX hX E r hE g hY j k α :=
  rfl

/-- **The two models of `c_j(ℰ)` carry the same cap operations.** The cap operation of the
bivariant class `AlgebraicGeometry.Space.chernClass` on a test space `g : X' ⟶ X`, which lands in
the Chow group of `X ×_X X'`, is the cap operation of
`AlgebraicGeometry.Space.ChowCohomologyClass.chernClass` on `X'` read along the identification
`X ×_X X' ≅ X'` (`AlgebraicGeometry.Space.testSpacePullbackChowMap`). -/
theorem ChowCohomologyClass.chernClass_cap_eq (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (hXg : D.IsGood (Limits.pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (Space.chernClass D sX hX E r hE j).cap g hY hXg k α =
      testSpacePullbackChowMap D sX hX g hY hXg _
        ((ChowCohomologyClass.chernClass D sX hX E r hE j).cap g hY k (k - ((j : ℕ) : ℤ))
          (by omega) α) :=
  rfl

/-- **The total Chern class** `c(ℰ) = c₀(ℰ) + c₁(ℰ) + … + c_r(ℰ)` (Stacks 0ERZ) of a finite
locally free module `ℰ` of rank `r`, as an element of the Chow cohomology ring `A^*(X)`
(Stacks 0ERK): the sum of the homogeneous elements
`AlgebraicGeometry.Space.ChowCohomologyClass.chernClass` of degrees `0, …, r`. -/
def ChowCohomologyAlgebra.totalChernClass : ChowCohomologyAlgebra D sX hX :=
  ∑ j : Fin (r + 1), DirectSum.of (ChowCohomologyClass D sX hX) ((j : ℕ) : ℤ)
    (ChowCohomologyClass.chernClass D sX hX E r hE j)

end Chern

/-! ### The cap product of `A^*(X)` on Chow homology -/

namespace ChowCohomologyClass

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- On the summand `CH_k(Y)`, the cap operation of `c ∈ A^p(X)` on Chow homology is `c ∩ -`
into the summand `CH_l(Y)`, `l + p = k`, read through
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
theorem capChowHomology_of {p : ℤ} (c : ChowCohomologyClass D sX hX p) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k l : ℤ) (hl : l + p = k)
    (y : chowGroup.{u + 1} D (g ≫ sX) hY k) :
    c.capChowHomology g hY (DirectSum.of _ k y) =
      DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY k) l
        (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY l
          (c.cap g hY k l hl ((chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k).symm
            y))) := by
  obtain rfl : l = k + -p := by omega
  rw [capChowHomology, gradedChowMap_of]
  rfl

/-- The cap operation of `c ∈ A^p(X)` on a class of `CH_k(Y)`, read through
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
theorem capChowHomology_of_chowGroupCanonicalEquivChowGroup {p : ℤ}
    (c : ChowCohomologyClass D sX hX p) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (k l : ℤ) (hl : l + p = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    c.capChowHomology g hY
        (DirectSum.of _ k (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k x)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY k) l
        (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY l (c.cap g hY k l hl x)) := by
  rw [capChowHomology_of c g hY k l hl, AddEquiv.symm_apply_apply]

/-- The zero class caps as zero on Chow homology. -/
@[simp]
theorem zero_capChowHomology {p : ℤ} {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    (0 : ChowCohomologyClass D sX hX p).capChowHomology g hY = 0 :=
  DirectSum.addHom_ext fun k y => by
    rw [capChowHomology_of _ g hY k (k - p) (by omega), zero_cap, map_zero, map_zero,
      AddMonoidHom.zero_apply]

/-- The cap operation on Chow homology is additive in the class. -/
@[simp]
theorem add_capChowHomology {p : ℤ} (c d : ChowCohomologyClass D sX hX p) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    (c + d).capChowHomology g hY = c.capChowHomology g hY + d.capChowHomology g hY :=
  DirectSum.addHom_ext fun k y => by
    rw [AddMonoidHom.add_apply, capChowHomology_of _ g hY k (k - p) (by omega),
      capChowHomology_of c g hY k (k - p) (by omega),
      capChowHomology_of d g hY k (k - p) (by omega), add_cap, map_add, map_add]

/-- **The cap product on Chow homology is multiplicative**: `(c ∘ d) ∩ α = c ∩ (d ∩ α)` on
`CH_*(Y)`. -/
theorem capChowHomology_comp {p q : ℤ} (c : ChowCohomologyClass D sX hX p)
    (d : ChowCohomologyClass D sX hX q) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    (c.comp d).capChowHomology g hY =
      (c.capChowHomology g hY).comp (d.capChowHomology g hY) :=
  DirectSum.addHom_ext fun k y => by
    rw [AddMonoidHom.comp_apply, capChowHomology_of _ g hY k (k - (p + q)) (by omega),
      capChowHomology_of d g hY k (k - (p + q) + p) (by omega),
      capChowHomology_of c g hY (k - (p + q) + p) (k - (p + q)) rfl,
      AddEquiv.symm_apply_apply, comp_cap]

/-- **The cap product on Chow homology is unital**: `1 ∈ A^0(X)` caps as the identity of
`CH_*(Y)`. -/
theorem capChowHomology_one {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    (one : ChowCohomologyClass D sX hX 0).capChowHomology g hY = AddMonoidHom.id _ :=
  DirectSum.addHom_ext fun k y => by
    rw [capChowHomology_of _ g hY k k (by omega), one_cap, chowGroupCanonicalDegreeCongr_refl,
      AddEquiv.apply_symm_apply, AddMonoidHom.id_apply]

/-- The cap operation on Chow homology of a good test space `g : Y ⟶ X`, as an additive map
`A^p(X) ⟶ End(CH_*(Y))`. -/
def capChowHomologyAddHom {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (p : ℤ) :
    ChowCohomologyClass D sX hX p →+ AddMonoid.End (chowHomology.{u, u + 1} D (g ≫ sX) hY) where
  toFun c := c.capChowHomology g hY
  map_zero' := zero_capChowHomology g hY
  map_add' c d := add_capChowHomology c d g hY

/-- The additive map `A^p(X) ⟶ End(CH_*(Y))` sends `c` to its cap operation. -/
@[simp]
theorem capChowHomologyAddHom_apply {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    {p : ℤ} (c : ChowCohomologyClass D sX hX p) :
    capChowHomologyAddHom g hY p c = c.capChowHomology g hY :=
  rfl

end ChowCohomologyClass

namespace ChowCohomologyAlgebra

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **The action of `A^*(X)` on Chow homology.** For a good test space `g : Y ⟶ X`, the ring
homomorphism `A^*(X) ⟶ End(CH_*(Y))` sending a homogeneous class `c ∈ A^p(X)` to its cap
operation `c ∩ -` on `CH_*(Y) = ⨁_k CH_k(Y)`
(`AlgebraicGeometry.Space.ChowCohomologyClass.capChowHomology`): the product of `A^*(X)`,
composition of bivariant classes, acts as composition of endomorphisms. -/
def capChowHomology {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    ChowCohomologyAlgebra D sX hX →+* AddMonoid.End (chowHomology.{u, u + 1} D (g ≫ sX) hY) :=
  DirectSum.toSemiring (ChowCohomologyClass.capChowHomologyAddHom g hY)
    (ChowCohomologyClass.capChowHomology_one g hY)
    (fun c d => ChowCohomologyClass.capChowHomology_comp c d g hY)

/-- On a homogeneous class `c ∈ A^p(X)` the action of `A^*(X)` on Chow homology is the cap
operation of `c`. -/
@[simp]
theorem capChowHomology_of {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) {p : ℤ}
    (c : ChowCohomologyClass D sX hX p) :
    capChowHomology g hY (DirectSum.of _ p c) = c.capChowHomology g hY :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- On a homogeneous class `c ∈ A^p(X)` the action of `A^*(X)` on a class `y ∈ CH_*(Y)` is
`c ∩ y`. -/
theorem capChowHomology_of_apply {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) {p : ℤ}
    (c : ChowCohomologyClass D sX hX p) (y : chowHomology.{u, u + 1} D (g ≫ sX) hY) :
    capChowHomology g hY (DirectSum.of _ p c) y = c.capChowHomology g hY y :=
  DFunLike.congr_fun (capChowHomology_of g hY c) y

/-- The component in degree `l` of `x ∩ α`, for `α ∈ CH_k(Y)`, is the cap of the degree `p`
component of `x`, where `l + p = k`. -/
theorem capChowHomology_apply_of_apply {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (x : ChowCohomologyAlgebra D sX hX) (k l p : ℤ) (hl : l + p = k)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    capChowHomology g hY x
        (DirectSum.of _ k (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k α)) l =
      chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY l ((x p).cap g hY k l hl α) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero, AddMonoid.End.zero_apply, DirectSum.zero_apply, DirectSum.zero_apply,
      ChowCohomologyClass.zero_cap, map_zero]
  | of p' c =>
    rw [capChowHomology_of_apply,
      ChowCohomologyClass.capChowHomology_of_chowGroupCanonicalEquivChowGroup
      c g hY k (k - p') (by omega)]
    by_cases hp : p' = p
    · subst hp
      obtain rfl : l = k - p' := by omega
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp),
        ChowCohomologyClass.zero_cap, map_zero]
  | add x y hx hy =>
    rw [map_add]
    change (capChowHomology g hY x _ + capChowHomology g hY y _) l = _
    rw [DirectSum.add_apply, hx, hy, DirectSum.add_apply,
      ChowCohomologyClass.add_cap, map_add]

/-- An element of `A^*(X)` acting as zero on the Chow homology of every good test space is
zero. -/
theorem eq_zero_of_capChowHomology_eq_zero {x : ChowCohomologyAlgebra D sX hX}
    (h : ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)), capChowHomology g hY x = 0) :
    x = 0 := by
  refine DirectSum.ext fun p => ChowCohomologyClass.ext fun g hY k l hl α => ?_
  apply (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY l).injective
  rw [← capChowHomology_apply_of_apply g hY x k l p hl α, h g hY, AddMonoid.End.zero_apply,
    DirectSum.zero_apply, DirectSum.zero_apply, ChowCohomologyClass.zero_cap, map_zero]

/-- **An element of `A^*(X)` is determined by its action on Chow homology**: two elements with
the same cap products on `CH_*(Y)` for every good test space `g : Y ⟶ X` are equal. -/
theorem ext_capChowHomology {x y : ChowCohomologyAlgebra D sX hX}
    (h : ∀ {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)),
      capChowHomology g hY x = capChowHomology g hY y) :
    x = y :=
  sub_eq_zero.1 (eq_zero_of_capChowHomology_eq_zero fun g hY => by
    rw [map_sub, h g hY, sub_self])

end ChowCohomologyAlgebra

/-! ### The Chern classes on Chow homology -/

section ChernHomology

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)

/-- On the summand `CH_k(Y)` of the Chow homology of a test space `g : Y ⟶ X`, the class
`c_j(ℰ) ∈ A^j(X)` caps as `c_j(ℰ) ∩ - : CH_k(Y) ⟶ CH_{k-j}(Y)`
(`AlgebraicGeometry.Space.chernCap`). -/
theorem ChowCohomologyClass.chernClass_capChowHomology_of (j : Fin (r + 1)) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (ChowCohomologyClass.chernClass D sX hX E r hE j).capChowHomology g hY
        (DirectSum.of _ k (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k α)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY k) (k - ((j : ℕ) : ℤ))
        (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ))
          (Space.chernCap D sX hX E r hE g hY j k α)) :=
  ChowCohomologyClass.capChowHomology_of_chowGroupCanonicalEquivChowGroup _ g hY k _
    (by omega) α

/-- The total Chern class `c(ℰ) ∈ A^*(X)` acts on the Chow homology of a test space as the sum
of the cap operations of `c₀(ℰ), …, c_r(ℰ)`. -/
theorem ChowCohomologyAlgebra.capChowHomology_totalChernClass {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    ChowCohomologyAlgebra.capChowHomology g hY
        (ChowCohomologyAlgebra.totalChernClass D sX hX E r hE) =
      ∑ j : Fin (r + 1), ((ChowCohomologyClass.chernClass D sX hX E r hE j).capChowHomology g hY :
        AddMonoid.End (chowHomology.{u, u + 1} D (g ≫ sX) hY)) := by
  rw [ChowCohomologyAlgebra.totalChernClass, map_sum]
  exact Finset.sum_congr rfl fun j _ => ChowCohomologyAlgebra.capChowHomology_of g hY _

end ChernHomology

/-! ### From `A^*(X)` to the bivariant classes over the fibre products `X ×_X X'` -/

namespace ChowCohomologyClass

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {p : ℤ}

/-- The cap operation `c ∩ - : CH_k(X') ⟶ CH_{k-p}(X')` of `c ∈ A^p(X)` on a good test space
`g : X' ⟶ X`, with the target degree written `k - p`. -/
abbrev capSub (c : ChowCohomologyClass D sX hX p) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) :
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY k →+
      chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - p) :=
  c.cap g hY k (k - p) (by omega)

/-- `c ∩ -` commutes with proper pushforward on Chow groups (Stacks 0ERJ (1)). -/
theorem capSub_properPushforward (c : ChowCohomologyClass D sX hX p) {Y₁ Y₂ : D.Ambient}
    (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k) :
    c.capSub g hY₁ k (chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁
        (Category.assoc h g sX).symm hh k α) =
      chowGroupCanonicalProperPushforward.{u + 1} D _ hY₂ _ hY₁ (Category.assoc h g sX).symm hh _
        (c.capSub (h ≫ g) hY₂ k α) := by
  obtain ⟨a, rfl⟩ : ∃ a, chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY₂ k a = α :=
    QuotientAddGroup.mk'_surjective _ α
  obtain ⟨β, h₁, h₂⟩ := c.proper_naturality g hY₁ h hY₂ hh k (k - p) (by omega) a
  rw [chowGroupCanonicalProperPushforward_chowClassCanonical, capSub, h₂, capSub, h₁,
    chowGroupCanonicalProperPushforward_chowClassCanonical]

/-- `c ∩ -` commutes with flat pullback on Chow groups (Stacks 0ERJ (2)). -/
theorem capSub_flatPullback (c : ChowCohomologyClass D sX hX p) {Y₁ Y₂ : D.Ambient}
    (g : Y₁ ⟶ X) (hY₁ : D.IsGood (g ≫ sX)) (h : Y₂ ⟶ Y₁) (hY₂ : D.IsGood ((h ≫ g) ≫ sX))
    (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY₁ k) :
    c.capSub (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
        (Category.assoc h g sX).symm m hhf hhr k (k + m) rfl α) =
      flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h (Category.assoc h g sX).symm m hhf hhr
        (k - p) (k + m - p) (chernDegree_sub_add k m p) (c.capSub g hY₁ k α) := by
  have hfl := c.flat_naturality g hY₁ h hY₂ m hhf hhr k (k - p) (by omega) (k + m) (k - p + m)
    rfl rfl α
  calc c.capSub (h ≫ g) hY₂ (k + m) (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
          (Category.assoc h g sX).symm m hhf hhr k (k + m) rfl α) =
        chowGroupCanonicalDegreeCongr D _ hY₂ (by omega : k - p + m = k + m - p)
          (c.cap (h ≫ g) hY₂ (k + m) (k - p + m) (by omega)
            (flatPullbackChowMapCanonical.{u + 1} D _ hY₂ _ hY₁ h
              (Category.assoc h g sX).symm m hhf hhr k (k + m) rfl α)) :=
        (cap_degreeCongr_target c (h ≫ g) hY₂ _ _ _ _).symm
    _ = _ := by
        rw [hfl]
        exact chowGroupCanonicalDegreeCongr_flatPullbackChowMapCanonical D _ hY₁ _ hY₂ h _ m hhf
          hhr _ _ _ _

/-- `c ∩ -` commutes with the Gysin map of a section of an invertible module (Stacks 0ERJ (3)). -/
theorem capSub_gysin (c : ChowCohomologyClass D sX hX p) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (t : M.sections) (hM : IsInvertibleSheaf D (g ≫ sX) hY M) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    c.capSub ((vanishingLocus D (g ≫ sX) hY M t).1.ι ≫ g) (isGood_vanishingLocus D (g ≫ sX) hY M t)
        k (sectionGysinChowGroupMap D (g ≫ sX) hY M t hM k α) =
      sectionGysinChowGroupMap D (g ≫ sX) hY M t hM (k - p)
        (ProjectiveBundleRelation.degreeCast
          (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (chernDegree_add_one_sub k p)
          (c.capSub g hY (k + 1) α)) := by
  rw [degreeCast_eq_chowGroupCanonicalDegreeCongr, capSub, capSub,
    cap_degreeCongr_target c g hY _ _ (by omega : k - p + 1 + p = k + 1)]
  exact c.gysin_naturality g hY M t hM k (k - p) (by omega) α

/-- **A class of `A^p(X)` as a bivariant class for `id_X` over the fibre products `X ×_X X'`**
(`AlgebraicGeometry.Space.chowCohomologyComponentCanonical`): its cap operation on a test space
`g : X' ⟶ X` is `c ∩ -` on `X'` read on `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.testSpacePullbackChowMap`). -/
def toChowCohomologyComponentCanonical (c : ChowCohomologyClass D sX hX p) :
    chowCohomologyComponentCanonical.{u + 1} D sX hX p :=
  bivariantClassOfTestCaps D sX hX p (fun g hY k => c.capSub g hY k)
    (fun g hY₁ h hY₂ hh k α => c.capSub_properPushforward g hY₁ h hY₂ hh k α)
    (fun g hY₁ h hY₂ m hhf hhr k α => c.capSub_flatPullback g hY₁ h hY₂ m hhf hhr k α)
    (fun g hY M t hM k α => c.capSub_gysin g hY M t hM k α)

/-- The cap operation of `toChowCohomologyComponentCanonical c` is that of `c`, read on
`X ×_X X' ≅ X'`. -/
theorem toChowCohomologyComponentCanonical_cap (c : ChowCohomologyClass D sX hX p)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hXg : D.IsGood (Limits.pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    c.toChowCohomologyComponentCanonical.cap g hY hXg k α =
      testSpacePullbackChowMap D sX hX g hY hXg (k - p) (c.cap g hY k (k - p) (by omega) α) :=
  rfl

variable (D sX hX p) in
/-- `toChowCohomologyComponentCanonical`, as an additive map
`A^p(X) ⟶ A^p(X ⟶ X)`. -/
def toChowCohomologyComponentCanonicalHom :
    ChowCohomologyClass D sX hX p →+ chowCohomologyComponentCanonical.{u + 1} D sX hX p where
  toFun c := c.toChowCohomologyComponentCanonical
  map_zero' := BivariantClassCanonical.ext _ _ _ _ _ _ _ _ fun g hY hXg k α => by
    rw [toChowCohomologyComponentCanonical_cap, zero_cap, map_zero,
      BivariantClassCanonical.zero_cap]
  map_add' c d := BivariantClassCanonical.ext _ _ _ _ _ _ _ _ fun g hY hXg k α => by
    rw [toChowCohomologyComponentCanonical_cap, add_cap, map_add,
      BivariantClassCanonical.add_cap, toChowCohomologyComponentCanonical_cap,
      toChowCohomologyComponentCanonical_cap]

end ChowCohomologyClass

namespace ChowCohomologyAlgebra

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

variable (D sX hX) in
/-- **`A^*(X)` inside the graded group of bivariant classes over the fibre products.** The
additive map `A^*(X) ⟶ ⊕_p A^p(X ⟶ X)` (`AlgebraicGeometry.Space.chowCohomologyCanonical`) which
on each degree reads a class on `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.ChowCohomologyClass.toChowCohomologyComponentCanonical`). It carries
the Chern classes of `A^*(X)` to `AlgebraicGeometry.Space.chernClass` and
`AlgebraicGeometry.Space.totalChernClass`. -/
def toChowCohomologyCanonical :
    ChowCohomologyAlgebra D sX hX →+ chowCohomologyCanonical.{u + 1} D sX hX :=
  DirectSum.toAddMonoid fun p =>
    (DirectSum.of (fun p => chowCohomologyComponentCanonical.{u + 1} D sX hX p) p).comp
      (ChowCohomologyClass.toChowCohomologyComponentCanonicalHom D sX hX p)

/-- On a homogeneous class, `toChowCohomologyCanonical` is
`ChowCohomologyClass.toChowCohomologyComponentCanonical` in the same degree. -/
theorem toChowCohomologyCanonical_of {p : ℤ} (c : ChowCohomologyClass D sX hX p) :
    toChowCohomologyCanonical D sX hX (DirectSum.of _ p c) =
      DirectSum.of (fun p => chowCohomologyComponentCanonical.{u + 1} D sX hX p) p
        c.toChowCohomologyComponentCanonical :=
  DirectSum.toAddMonoid_of _ _ _

end ChowCohomologyAlgebra

section ChernCanonical

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)

/-- **The two models of `c_j(ℰ)` agree**: read over the fibre products `X ×_X X'`, the Chern
class `c_j(ℰ)` of `A^*(X)` is the bivariant class `AlgebraicGeometry.Space.chernClass` of
Stacks 0ERZ. -/
theorem ChowCohomologyClass.toChowCohomologyComponentCanonical_chernClass (j : Fin (r + 1)) :
    (ChowCohomologyClass.chernClass D sX hX E r hE j).toChowCohomologyComponentCanonical =
      Space.chernClass D sX hX E r hE j :=
  BivariantClassCanonical.ext _ _ _ _ _ _ _ _ fun _ _ _ _ _ => rfl

/-- **The two models of `c(ℰ)` agree**: the total Chern class of `A^*(X)` is carried to the total
Chern class `AlgebraicGeometry.Space.totalChernClass` of Stacks 0ERZ. -/
theorem ChowCohomologyAlgebra.toChowCohomologyCanonical_totalChernClass :
    ChowCohomologyAlgebra.toChowCohomologyCanonical D sX hX
        (ChowCohomologyAlgebra.totalChernClass D sX hX E r hE) =
      Space.totalChernClass D sX hX E r hE := by
  rw [ChowCohomologyAlgebra.totalChernClass, map_sum, Space.totalChernClass]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ChowCohomologyAlgebra.toChowCohomologyCanonical_of,
    ChowCohomologyClass.toChowCohomologyComponentCanonical_chernClass]

end ChernCanonical

end AlgebraicGeometry.Space

end
