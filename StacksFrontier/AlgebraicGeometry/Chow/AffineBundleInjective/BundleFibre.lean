module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleReduced
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.ChainRestrict
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.SurjectiveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows

/-!
# The fibres of an affine-space bundle, and pulling Milnor K-chains back along it

Let `(S, δ)` be the base situation of chapter 42 and let `f : X ⟶ Y` be an affine-space bundle
of rank `r` (`Stacks.Chow.IsAffineSpaceBundle`) between schemes locally of finite type over `S`.
Every fibre of `f` is irreducible, so it has a generic point, and the relative dimension of a
point of `X` exceeds that of its image by the transcendence degree of the residue field
extension, which is at most `r`. Together:

* over every point `y` there is a point `ξ` of `X` with `δ(ξ) = δ(y) + r`, specializing to every
  point of the fibre over `y`, and it is the only point of that fibre with `δ(ξ) = δ(y) + r`;
* every point of `X` has `δ(ξ) ≤ δ(f ξ) + r`.

These are the facts the dévissage of a Milnor K-chain on `X` into its fibres runs on. They also
make the pullback of a locally finite Milnor K-chain along `f` well defined: the class at a point
`y` is carried, through `κ(y) → κ(ξ)`, to the generic point `ξ` of the fibre over `y`
(`Stacks.Chow.bundleChainPullback`). In Milnor degree zero this is flat pullback of cycles
(Stacks 02RB): the multiplicity of the generic point of a fibre is one.

## Main definitions

* `Stacks.Chow.bundleChainPullback` — the pullback of a locally finite Milnor K-chain along an
  affine-space bundle.

## Main results

* `Stacks.Chow.exists_specializes_fibre_of_isAffineSpaceBundle` — every fibre has a generic
  point.
* `Stacks.Chow.relativeDimension_le_add_of_isAffineSpaceBundle` — `δ(ξ) ≤ δ(f ξ) + r`.
* `Stacks.Chow.exists_relativeDimension_eq_add_of_isAffineSpaceBundle` and
  `Stacks.Chow.eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle` — existence and uniqueness
  of the point of the fibre with `δ(ξ) = δ(y) + r`.
* `Stacks.Chow.flatPullbackWeight_eq_one_of_isAffineSpaceBundle` — the flat pullback
  multiplicity there is one.
* `Stacks.Chow.pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle` — in Milnor degree zero
  the pullback of chains is flat pullback of cycles.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The generic point of a fibre -/

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {r : ℕ}

/-- **Every fibre of an affine-space bundle has a generic point.** The fibres of a geometrically
irreducible morphism are irreducible, and the fibre embeds into `X`. -/
theorem exists_specializes_fibre_of_isAffineSpaceBundle (hb : IsAffineSpaceBundle f r) (y : Y) :
    ∃ ξ : X, f.base ξ = y ∧ ∀ ξ' : X, f.base ξ' = y → ξ ⤳ ξ' := by
  have := geometricallyIrreducible_of_isAffineSpaceBundle f r hb
  have hrange : ∀ ξ' : X, ξ' ∈ Set.range (f.fiberι y).base ↔ f.base ξ' = y := fun ξ' ↦ by
    rw [Scheme.Hom.range_fiberι]
    rfl
  refine ⟨(f.fiberι y).base (genericPoint (f.fiber y)), (hrange _).mp ⟨_, rfl⟩, ?_⟩
  · intro ξ' hξ'
    obtain ⟨z, rfl⟩ := (hrange ξ').mpr hξ'
    exact (genericPoint_specializes z).map (f.fiberι y).continuous

end Fibre

/-! ### Relative dimensions along an affine-space bundle -/

section Dimension

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb

/-- **Along an affine-space bundle of rank `r` the relative dimension grows by at most `r`.** It
grows by the transcendence degree of the residue field extension, which is at most the dimension
`r` of the fibre. -/
theorem relativeDimension_le_add_of_isAffineSpaceBundle (x : X) :
    relativeDimension C.dimensionFunction sX x ≤
      relativeDimension C.dimensionFunction sY (f.base x) + r := by
  have := locallyOfFiniteType_of_isAffineSpaceBundle f r hb
  subst hbase
  rw [relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x]
  have := toNat_residueTrdeg_le_of_relativeDimension f r
    (relativeDimension_of_isAffineSpaceBundle f r hb) x
  omega

/-- **Over every point there is a point of the fibre of relative dimension `r` more**, and it is
the generic point of the fibre: it specializes to every point of the fibre. -/
theorem exists_relativeDimension_eq_add_of_isAffineSpaceBundle (y : Y) :
    ∃ ξ : X, f.base ξ = y ∧
      relativeDimension C.dimensionFunction sX ξ =
        relativeDimension C.dimensionFunction sY y + r ∧
      ∀ ξ' : X, f.base ξ' = y → ξ ⤳ ξ' := by
  have := locallyOfFiniteType_of_isAffineSpaceBundle f r hb
  obtain ⟨ξ, hξ, hspec⟩ := exists_specializes_fibre_of_isAffineSpaceBundle f hb y
  obtain ⟨x, hx, htr⟩ := exists_toNat_residueTrdeg_eq_of_relativeDimension f r
    (relativeDimension_of_isAffineSpaceBundle f r hb) y ⟨ξ, hξ⟩
  refine ⟨ξ, hξ, le_antisymm ?_ ?_, hspec⟩
  · simpa [hξ] using relativeDimension_le_add_of_isAffineSpaceBundle C sX sY f hbase hb ξ
  · have hle := relativeDimension_le_of_specializes C sX (hspec x hx)
    have hxdim : relativeDimension C.dimensionFunction sX x =
        relativeDimension C.dimensionFunction sY y + r := by
      subst hbase
      rw [relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x, hx, htr]
    omega

/-- **A point of relative dimension `r` more than its image is the generic point of its fibre**:
it specializes to every point of that fibre. -/
theorem specializes_of_relativeDimension_eq_add_of_isAffineSpaceBundle {ξ ξ' : X}
    (hξ : relativeDimension C.dimensionFunction sX ξ =
      relativeDimension C.dimensionFunction sY (f.base ξ) + r)
    (h : f.base ξ' = f.base ξ) : ξ ⤳ ξ' := by
  obtain ⟨g, hg, hgdim, hgspec⟩ :=
    exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb (f.base ξ)
  have hgξ : g = ξ := by
    by_contra hne
    have := relativeDimension_lt_of_specializes C sX (hgspec ξ rfl) hne
    omega
  rw [← hgξ]
  exact hgspec ξ' h

/-- **The point of a fibre of relative dimension `r` more than the base point is unique.** -/
theorem eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle {ξ ξ' : X}
    (h : f.base ξ = f.base ξ')
    (hξ : relativeDimension C.dimensionFunction sX ξ =
      relativeDimension C.dimensionFunction sY (f.base ξ) + r)
    (hξ' : relativeDimension C.dimensionFunction sX ξ' =
      relativeDimension C.dimensionFunction sY (f.base ξ') + r) : ξ = ξ' := by
  by_contra hne
  have hs := specializes_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb
    hξ h.symm
  have := relativeDimension_lt_of_specializes C sX hs hne
  rw [h] at hξ
  omega

end Dimension

/-! ### Pulling Milnor K-chains back along an affine-space bundle -/

section Pullback

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

open Classical in
/-- The pullback of a family of Milnor K-classes along `f`, before the local-finiteness
condition: the coordinate at a point `ξ` of relative dimension `m'` is the class at `f ξ`, carried
along `κ(f ξ) → κ(ξ)`, when `f ξ` has relative dimension `m`, and zero otherwise. -/
def bundleChainPullbackPi (m m' : ℤ) (n : ℕ)
    (a : ∀ y : pointsOfDimension C sY m, MilnorKTheory (Y.residueField y.1) n) :
    ∀ ξ : pointsOfDimension C sX m', MilnorKTheory (X.residueField ξ.1) n := fun ξ ↦
  if h : f.base ξ.1 ∈ pointsOfDimension C sY m then
    milnorKTransport (f.residueFieldMap ξ.1).hom n (a ⟨f.base ξ.1, h⟩)
  else 0

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The coordinate of `bundleChainPullbackPi` at a point `ξ` whose image `f ξ` has relative
dimension `m` is the class at `f ξ` carried along `κ(f ξ) → κ(ξ)`. -/
theorem bundleChainPullbackPi_of_mem {m m' : ℤ} {n : ℕ}
    (a : ∀ y : pointsOfDimension C sY m, MilnorKTheory (Y.residueField y.1) n)
    (ξ : pointsOfDimension C sX m') (h : f.base ξ.1 ∈ pointsOfDimension C sY m) :
    bundleChainPullbackPi C sX sY f m m' n a ξ =
      milnorKTransport (f.residueFieldMap ξ.1).hom n (a ⟨f.base ξ.1, h⟩) := by
  classical
  rw [bundleChainPullbackPi, dite_eq_left h]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] in
/-- The coordinate of `bundleChainPullbackPi` at a point `ξ` whose image `f ξ` is not of relative
dimension `m` is zero. -/
theorem bundleChainPullbackPi_of_notMem {m m' : ℤ} {n : ℕ}
    (a : ∀ y : pointsOfDimension C sY m, MilnorKTheory (Y.residueField y.1) n)
    (ξ : pointsOfDimension C sX m') (h : f.base ξ.1 ∉ pointsOfDimension C sY m) :
    bundleChainPullbackPi C sX sY f m m' n a ξ = 0 := by
  classical
  rw [bundleChainPullbackPi, dite_eq_right h]

/-- If the coordinate of `bundleChainPullbackPi` at `ξ` is nonzero, then `f ξ` has relative
dimension `m`. -/
private theorem mem_of_bundleChainPullbackPi_ne_zero {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    (sY : Y ⟶ C.S) (f : X ⟶ Y) {m m' : ℤ} {n : ℕ}
    (a : ∀ y : pointsOfDimension C sY m, MilnorKTheory (Y.residueField y.1) n)
    (ξ : pointsOfDimension C sX m') (h : bundleChainPullbackPi C sX sY f m m' n a ξ ≠ 0) :
    f.base ξ.1 ∈ pointsOfDimension C sY m := by
  by_contra h'
  exact h (bundleChainPullbackPi_of_notMem C sX sY f a ξ h')

include hbase hb in
/-- The pullback of a locally finite family is locally finite: a quasi-compact open of `X` maps
into a quasi-compact open of `Y`, which carries only finitely many classes, and over each point
only the generic point of the fibre has the right relative dimension. -/
theorem bundleChainPullbackPi_mem {m m' : ℤ} (hm : m' = m + r) {n : ℕ}
    (a : MilnorChainGroup C sY m n) :
    bundleChainPullbackPi C sX sY f m m' n a.1 ∈
      locallyFiniteDirectSum X (pointsOfDimension C sX m')
        fun ξ ↦ MilnorKTheory (X.residueField ξ.1) n := by
  classical
  intro W hW
  obtain ⟨V, hV, hWV⟩ := exists_isCompact_opens_superset (hW.image f.continuous)
  have hF := a.2 V hV
  refine Set.Finite.of_finite_image (f := fun ξ : pointsOfDimension C sX m' ↦ f.base ξ.1)
    ((hF.image fun y : pointsOfDimension C sY m ↦ (y : Y)).subset ?_) ?_
  · rintro _ ⟨ξ, ⟨hξW, hξne⟩, rfl⟩
    by_cases h : f.base ξ.1 ∈ pointsOfDimension C sY m
    · refine ⟨⟨f.base ξ.1, h⟩, ⟨hWV ⟨ξ.1, hξW, rfl⟩, fun h0 ↦ hξne ?_⟩, rfl⟩
      rw [bundleChainPullbackPi_of_mem C sX sY f a.1 ξ h, h0, map_zero]
    · exact absurd (bundleChainPullbackPi_of_notMem C sX sY f a.1 ξ h) hξne
  · rintro ξ ⟨-, hξ⟩ ξ' ⟨-, hξ'⟩ heq
    have hdim : ∀ η : pointsOfDimension C sX m',
        bundleChainPullbackPi C sX sY f m m' n a.1 η ≠ 0 →
          relativeDimension C.dimensionFunction sX η.1 =
            relativeDimension C.dimensionFunction sY (f.base η.1) + r := fun η hη ↦ by
      rw [(mem_pointsOfDimension C sX).mp η.2, (mem_pointsOfDimension C sY).mp
        (mem_of_bundleChainPullbackPi_ne_zero C sX sY f a.1 η hη), hm]
    exact Subtype.ext (eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb
      heq (hdim ξ hξ) (hdim ξ' hξ'))

/-- **The pullback of locally finite Milnor K-chains along an affine-space bundle** of rank `r`,
from relative dimension `m` to relative dimension `m' = m + r`: the class at a point `y` is
carried, along `κ(y) → κ(ξ)`, to the generic point `ξ` of the fibre over `y`, the unique point of
that fibre of relative dimension `m'`. -/
def bundleChainPullback (m m' : ℤ) (hm : m' = m + r) (n : ℕ) :
    MilnorChainGroup C sY m n →+ MilnorChainGroup C sX m' n where
  toFun a := ⟨bundleChainPullbackPi C sX sY f m m' n a.1,
    bundleChainPullbackPi_mem C sX sY f hbase hb hm a⟩
  map_zero' := Subtype.ext (funext fun ξ ↦ by
    classical
    change bundleChainPullbackPi C sX sY f m m' n 0 ξ = 0
    by_cases h : f.base ξ.1 ∈ pointsOfDimension C sY m
    · rw [bundleChainPullbackPi_of_mem C sX sY f _ ξ h]
      exact map_zero _
    · exact bundleChainPullbackPi_of_notMem C sX sY f _ ξ h)
  map_add' a b := Subtype.ext (funext fun ξ ↦ by
    classical
    change bundleChainPullbackPi C sX sY f m m' n (a.1 + b.1) ξ =
      bundleChainPullbackPi C sX sY f m m' n a.1 ξ + bundleChainPullbackPi C sX sY f m m' n b.1 ξ
    by_cases h : f.base ξ.1 ∈ pointsOfDimension C sY m
    · rw [bundleChainPullbackPi_of_mem C sX sY f _ ξ h,
        bundleChainPullbackPi_of_mem C sX sY f _ ξ h,
        bundleChainPullbackPi_of_mem C sX sY f _ ξ h]
      exact map_add _ _ _
    · rw [bundleChainPullbackPi_of_notMem C sX sY f _ ξ h,
        bundleChainPullbackPi_of_notMem C sX sY f _ ξ h,
        bundleChainPullbackPi_of_notMem C sX sY f _ ξ h, add_zero])

/-- At a point `ξ` whose image `f ξ` has relative dimension `m`, the pullback of a chain is the
class at `f ξ` carried along `κ(f ξ) → κ(ξ)`. -/
theorem bundleChainPullback_apply_of_mem {m m' : ℤ} (hm : m' = m + r) {n : ℕ}
    (a : MilnorChainGroup C sY m n) (ξ : pointsOfDimension C sX m')
    (h : f.base ξ.1 ∈ pointsOfDimension C sY m) :
    (bundleChainPullback C sX sY f hbase hb m m' hm n a).1 ξ =
      milnorKTransport (f.residueFieldMap ξ.1).hom n (a.1 ⟨f.base ξ.1, h⟩) :=
  bundleChainPullbackPi_of_mem C sX sY f a.1 ξ h

/-- The pullback of a chain vanishes at a point `ξ` whose image `f ξ` is not of relative
dimension `m`. -/
theorem bundleChainPullback_apply_of_notMem {m m' : ℤ} (hm : m' = m + r) {n : ℕ}
    (a : MilnorChainGroup C sY m n) (ξ : pointsOfDimension C sX m')
    (h : f.base ξ.1 ∉ pointsOfDimension C sY m) :
    (bundleChainPullback C sX sY f hbase hb m m' hm n a).1 ξ = 0 :=
  bundleChainPullbackPi_of_notMem C sX sY f a.1 ξ h

/-- **Pulling back commutes with restriction to the preimage of a set.** -/
theorem milnorChainRestrict_preimage_bundleChainPullback (T : Set Y) {m m' : ℤ}
    (hm : m' = m + r) {n : ℕ} (a : MilnorChainGroup C sY m n) :
    milnorChainRestrict C sX (f.base ⁻¹' T) m' n
        (bundleChainPullback C sX sY f hbase hb m m' hm n a) =
      bundleChainPullback C sX sY f hbase hb m m' hm n (milnorChainRestrict C sY T m n a) := by
  refine Subtype.ext (funext fun ξ ↦ ?_)
  by_cases h : f.base ξ.1 ∈ pointsOfDimension C sY m
  · by_cases hT : f.base ξ.1 ∈ T
    · rw [milnorChainRestrict_apply_of_mem _ (show ξ.1 ∈ f.base ⁻¹' T from hT),
        bundleChainPullback_apply_of_mem C sX sY f hbase hb hm _ ξ h,
        bundleChainPullback_apply_of_mem C sX sY f hbase hb hm _ ξ h,
        milnorChainRestrict_apply_of_mem (x := ⟨f.base ξ.1, h⟩) _ hT]
    · rw [milnorChainRestrict_apply_of_notMem _ (show ξ.1 ∉ f.base ⁻¹' T from hT),
        bundleChainPullback_apply_of_mem C sX sY f hbase hb hm _ ξ h,
        milnorChainRestrict_apply_of_notMem (x := ⟨f.base ξ.1, h⟩) _ hT, map_zero]
  · by_cases hT : f.base ξ.1 ∈ T
    · rw [milnorChainRestrict_apply_of_mem _ (show ξ.1 ∈ f.base ⁻¹' T from hT),
        bundleChainPullback_apply_of_notMem C sX sY f hbase hb hm _ ξ h,
        bundleChainPullback_apply_of_notMem C sX sY f hbase hb hm _ ξ h]
    · rw [milnorChainRestrict_apply_of_notMem _ (show ξ.1 ∉ f.base ⁻¹' T from hT),
        bundleChainPullback_apply_of_notMem C sX sY f hbase hb hm _ ξ h]

/-- **The pullback of chains is supported at the generic points of the fibres.** -/
theorem relativeDimension_eq_add_of_bundleChainPullback_ne_zero {m m' : ℤ} (hm : m' = m + r)
    {n : ℕ} (a : MilnorChainGroup C sY m n) {ξ : pointsOfDimension C sX m'}
    (h : (bundleChainPullback C sX sY f hbase hb m m' hm n a).1 ξ ≠ 0) :
    f.base ξ.1 ∈ pointsOfDimension C sY m ∧ a.1 ⟨f.base ξ.1, by
      by_contra h'
      exact h (bundleChainPullback_apply_of_notMem C sX sY f hbase hb hm a ξ h')⟩ ≠ 0 := by
  have hmem := mem_of_bundleChainPullbackPi_ne_zero C sX sY f a.1 ξ h
  refine ⟨hmem, fun h0 ↦ h ?_⟩
  rw [bundleChainPullback_apply_of_mem C sX sY f hbase hb hm a ξ hmem, h0, map_zero]

include hbase hb in
/-- **Pulling back cycles along an affine-space bundle is injective.** A nonzero coefficient at
`y` reappears at the generic point of the fibre over `y`, because transport of degree-zero Milnor
K-theory along a map of fields is the identity of `ℤ`. -/
theorem bundleChainPullback_zero_injective {m m' : ℤ} (hm : m' = m + r) :
    Function.Injective (bundleChainPullback C sX sY f hbase hb m m' hm 0) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine Subtype.ext (funext fun y ↦ ?_)
  rcases y with ⟨y, hyd⟩
  obtain ⟨ξ, hξ, hξdim, -⟩ :=
    exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb y
  subst hξ
  have hξm : ξ ∈ pointsOfDimension C sX m' := by
    rw [mem_pointsOfDimension, hξdim, (mem_pointsOfDimension C sY).mp hyd, hm]
  have h0 := congrArg (fun c : MilnorChainGroup C sX m' 0 ↦ c.1 ⟨ξ, hξm⟩) ha
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at h0
  rw [bundleChainPullback_apply_of_mem C sX sY f hbase hb hm a _ hyd] at h0
  have h1 := congrArg (milnorKTheoryZeroAddEquiv (X.residueField ξ)) h0
  rw [milnorKTheoryZeroAddEquiv_milnorKTransport, map_zero] at h1
  exact (milnorKTheoryZeroAddEquiv _).injective (h1.trans (map_zero _).symm)

end Pullback

end Stacks.Chow

end
