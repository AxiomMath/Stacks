module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackNaturalityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# Shifting the degree of a bivariant class along a smooth morphism

Let `(S, δ)` be as in Situation 02QL of the Stacks Project, let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of schemes locally of finite type over `S`, and let `g` be smooth of relative dimension
`d`. **Stacks 0FBT** asserts that

  `A^p(X ⟶ Y) ⟶ A^{p-d}(X ⟶ Z)`,   `c ↦ c ∘ g^*`,

is an isomorphism. Its inverse sends `c'` to `res(Δ^!) ∘ res(c')`, where `res(c') ∈
A^{p-d}(X ×_Z Y ⟶ Y)` is the restriction (Stacks 0F9Z) of `c'` along `g`, `Δ : Y ⟶ Y ×_Z Y` is the
diagonal, `Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)` is its Gysin class, and `res(Δ^!) ∈ A^d(X ⟶ X ×_Z Y)` is its
restriction along `f × 𝟙 : X ×_Z Y ⟶ Y ×_Z Y`, the square formed by `f`, `Δ`, `f × 𝟙` and the
graph `X ⟶ X ×_Z Y` being cartesian.

The source proof uses exactly two properties of `Δ^!`:

1. `Δ^!` commutes, in the sense of Stacks 0FA2, with every bivariant class over `Y ×_Z Y`
   (Stacks 0FBP, through Stacks 0FF6);
2. `Δ^! ∘ pr_i^* = 1` in `A^0(Y)` for both projections `pr_i : Y ×_Z Y ⟶ Y` (Stacks 0FBS).

This file proves the proposition for an **arbitrary** class `D ∈ A^d(Y ⟶ Y ×_Z Y)` with these two
properties, which are hypotheses of the statements below. The tagged form of Stacks 0FBT will
instantiate `D` with the canonical Gysin class `c(Y ⟶ Y ×_Z Y, 𝒩)` of Stacks 0FBK once that class
is available, discharging the two hypotheses by Stacks 0FBP and Stacks 0FBS. The first
computation of the source, `res(D) ∘ res(c ∘ g^*) = c`, uses both properties (the second for
`pr₂`); the second computation, `res(D) ∘ res(c') ∘ g^* = c'`, uses only `D ∘ pr₁^* = 1`.

## Main definitions

* `Stacks.Chow.smoothShiftForward` — the map `A^p(X ⟶ Y) ⟶ A^{p-d}(X ⟶ Z)`, `c ↦ c ∘ g^*`.
* `Stacks.Chow.smoothShiftBackward` — the map `A^{p-d}(X ⟶ Z) ⟶ A^p(X ⟶ Y)`,
  `c' ↦ res(D) ∘ res(c')`.
* `Stacks.Chow.BivariantClass.CompFlatPullbackEqOne` — the identity `D ∘ pr^* = 1` on cap
  operations, for a class `D` for a section `Δ` of a flat morphism `pr`.
* `Stacks.Chow.smoothShiftEquiv` — the additive equivalence
  `A^p(X ⟶ Y) ≃+ A^{p-d}(X ⟶ Z)` with forward map `c ↦ c ∘ g^*`.

## Main results

* `Stacks.Chow.smoothShiftBackward_smoothShiftForward` — the first computation of the source:
  `res(D) ∘ res(c ∘ g^*) = c`.
* `Stacks.Chow.smoothShiftForward_smoothShiftBackward` — the second computation of the source:
  `res(D) ∘ res(c') ∘ g^* = c'`.
* `Stacks.Chow.BivariantClass.CompFlatPullbackEqOne.cap_flatPullbackChow` — `D ∘ pr^* = 1` read
  on an arbitrary presentation of the fibre product `(Y ×_Z Y) ×_Y T`.

## Implementation notes

### The class `g^*`

The source writes `g^!` for the Gysin class of the smooth morphism `g`; the class used here is the
flat pullback class `g^* ∈ A^{-d}(Y ⟶ Z)` of Stacks 0B78, which for `g` smooth is that Gysin
class. It exists as soon as `g` is flat of relative dimension `d`, so the forward map and both
computations are stated under that hypothesis; smoothness enters only through the two properties
of `D`, which for the Gysin class of the diagonal need `Δ` to be a regular immersion. The backward
map needs no hypothesis on `g` at all.

### Degrees

A composite of classes of degrees `p` and `q` has degree `p + q`, so `c ∘ g^*` has degree
`p + (-d)` and `res(D) ∘ res(c')` has degree `d + (p - d)`. Both are transported along the
equalities `p + (-d) = p - d` and `d + (p - d) = p` by `Stacks.Chow.bivariantClassDegreeCongr`.

### Identifications of fibre products

The composite `res(D) ∘ res(c')` is a class for the morphism `Y ×_{Y ×_Z Y} (X ×_Z Y) ⟶ Y`, and is
carried to a class for `f` along the isomorphism `Stacks.Chow.smoothShiftDiagonalPullbackIso` of
its source with `X` by `Stacks.Chow.bivariantTransport`. Every cap operation lands on a chosen
categorical fibre product, so the two computations are equalities of cap operations read through
explicit isomorphisms of fibre products; those isomorphisms are pinned down by their projections,
and every comparison of two of them is an equality of morphisms into a fibre product checked on
the projections. The condition `D ∘ pr^* = 1` is likewise stated on the chosen fibre product
`(Y ×_Z Y) ×_Y T`, and `Stacks.Chow.BivariantClass.CompFlatPullbackEqOne.cap_flatPullbackChow`
transfers it to any cartesian square, which is how both computations consume it.

## References

* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Pushforward along isomorphisms up to heterogeneous equality -/

section Transport

variable {C : ChowSituation.{u}}

/-- Pushing forward along `u` and then along `v` is pushing forward along `u ≫ v`, read up to
heterogeneous equality, so that the intermediate class may be presented over an equal structure
morphism and in an equal degree. -/
theorem chowPushforwardOfIso_heq_comp_of_comp_eq {A B D : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sB'] {sD sD' : D ⟶ C.S} [LocallyOfFiniteType sD]
    [LocallyOfFiniteType sD'] (u : A ⟶ B) [IsIso u] (v : B ⟶ D) [IsIso v] (w : A ⟶ D) [IsIso w]
    (huvw : u ≫ v = w) (hu : u ≫ sB = sA) (hv : v ≫ sD = sB') (hB : sB = sB') (hD : sD = sD')
    {k l : ℤ} (hkl : k = l) (x : chowGroup C sA k) (y : chowGroup C sB' l)
    (hxy : y ≍ chowPushforwardOfIso C sA sB u hu k x) :
    chowPushforwardOfIso C sB' sD v hv l y ≍
      chowPushforwardOfIso C sA sD' w (by rw [← huvw, Category.assoc, ← hD, hv, ← hB, hu]) k x := by
  subst hB hD hkl huvw
  obtain rfl := eq_of_heq hxy
  exact heq_of_eq (chowPushforwardOfIso_comp_apply C sA sB sD u v hu hv k x)

/-- **Stacks 0B76 (1) for an isomorphism of test schemes**, up to heterogeneous equality: the cap
operation of a bivariant class at `g` of a class pushed forward along an isomorphism `u` of test
schemes is the cap operation at `u ≫ g`, pushed forward along the induced isomorphism of base
changes. -/
theorem BivariantClass.cap_heq_chowPushforwardOfIso {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (u : T' ⟶ T) [IsIso u] (m : T' ⟶ Y) [LocallyOfFiniteType m]
    (hm : u ≫ g = m) {qm : T' ⟶ C.S} [LocallyOfFiniteType qm] {k k' : ℤ} (hk : k = k')
    (x : chowGroup C qm k) (y : chowGroup C (g ≫ sY) k') (hux : u ≫ (g ≫ sY) = qm)
    (hy : y ≍ chowPushforwardOfIso C qm (g ≫ sY) u hux k x) (x' : chowGroup C (m ≫ sY) k)
    (hx : x' ≍ x) :
    c.cap g k' y ≍
      chowPushforwardOfIso C (pullback.fst f m ≫ sX) (pullback.fst f g ≫ sX)
        (testBaseChangeIso f g u m hm).hom (by simp) (k - p) (c.cap m k x') := by
  subst hk
  obtain rfl := eq_of_heq hy
  have hqm : qm = m ≫ sY := by rw [← hux, ← hm, Category.assoc]
  exact heq_of_eq (c.cap_chowPushforwardOfIso g u m hm qm hqm k hux x x'
    (eq_of_heq ((chowGroupCongr_heq C hqm k x).trans hx.symm)))

/-- If `y` is the pushforward of `x` along an isomorphism `u`, then `x` is the pushforward of `y`
along `inv u`, up to heterogeneous equality. -/
theorem heq_chowPushforwardOfIso_inv {A B : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (u : A ⟶ B) [IsIso u]
    (hu : u ≫ sB = sA) (hB : sB = sB') {k l : ℤ} (hkl : k = l) (x : chowGroup C sA k)
    (y : chowGroup C sB' l) (hxy : y ≍ chowPushforwardOfIso C sA sB u hu k x) :
    x ≍ chowPushforwardOfIso C sB' sA (inv u) (by rw [IsIso.inv_comp_eq, ← hB, hu]) l y := by
  subst hB hkl
  obtain rfl := eq_of_heq hxy
  exact (heq_of_eq (chowPushforwardOfIso_inv_comp C sA sB u hu k x)).symm

/-- Pushforward along a morphism equal to the identity does not change a class, up to the
presentation of its structure morphism. -/
theorem chowPushforwardOfIso_heq_of_eq_id {A : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (u : A ⟶ A) [IsIso u] (hu1 : u = 𝟙 A)
    (hu : u ≫ sA' = sA) {k : ℤ} (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sA' u hu k x ≍ x := by
  have h : sA' = sA := by rw [← hu, hu1, Category.id_comp]
  subst h hu1
  exact heq_of_eq (chowPushforwardOfIso_id C _ k x)

end Transport

/-! ### The pullback of a section along a base change of its retraction -/

section Section

variable {Y P T : Scheme.{u}} (Δ : Y ⟶ P) (pr : P ⟶ Y) (hdiag : Δ ≫ pr = 𝟙 Y) (t : T ⟶ Y)

/-- The inverse of `Stacks.Chow.sectionPullbackIso`. -/
def sectionPullbackIsoInv : T ⟶ pullback Δ (pullback.fst pr t) :=
  pullback.lift t (pullback.lift (t ≫ Δ) (𝟙 T)
    (by rw [Category.assoc, hdiag, Category.comp_id, Category.id_comp]))
    (pullback.lift_fst _ _ _).symm

include hdiag in
/-- The first projection of `Y ×_P (P ×_Y T)`, read through `T`. -/
@[reassoc]
theorem sectionPullback_fst_eq :
    pullback.fst Δ (pullback.fst pr t) =
      pullback.snd _ _ ≫ pullback.snd pr t ≫ t := by
  have h := congrArg (· ≫ pr) (pullback.condition (f := Δ) (g := pullback.fst pr t))
  simp only [Category.assoc, hdiag, Category.comp_id] at h
  rw [h, pullback.condition]

/-- If `Δ : Y ⟶ P` is a section of `pr : P ⟶ Y`, then for every `t : T ⟶ Y` the pullback of `Δ`
along the base change `P ×_Y T ⟶ P` is `T`. -/
def sectionPullbackIso : pullback Δ (pullback.fst pr t) ≅ T where
  hom := pullback.snd _ _ ≫ pullback.snd _ _
  inv := sectionPullbackIsoInv Δ pr hdiag t
  hom_inv_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [sectionPullbackIsoInv, Category.assoc, pullback.lift_fst, Category.id_comp]
      exact (sectionPullback_fst_eq Δ pr hdiag t).symm
    · simp only [sectionPullbackIsoInv, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_fst, Category.id_comp]
      rw [← sectionPullback_fst_eq_assoc Δ pr hdiag t, pullback.condition]
    · simp only [sectionPullbackIsoInv, Category.assoc, pullback.lift_snd, Category.comp_id,
        Category.id_comp]
  inv_hom_id := by
    simp only [sectionPullbackIsoInv, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The isomorphism `Stacks.Chow.sectionPullbackIso` is the composite of the two second
projections. -/
@[simp]
theorem sectionPullbackIso_hom :
    (sectionPullbackIso Δ pr hdiag t).hom = pullback.snd _ _ ≫ pullback.snd _ _ := rfl

/-- `Stacks.Chow.sectionPullbackIso` is an isomorphism over the base. -/
theorem sectionPullbackIso_hom_comp_structureMorphism {C : ChowSituation.{u}} {sY : Y ⟶ C.S}
    {sP : P ⟶ C.S} (hpr : pr ≫ sY = sP) :
    (sectionPullbackIso Δ pr hdiag t).hom ≫ (t ≫ sY) =
      pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP) := by
  rw [sectionPullbackIso_hom, pullback.condition_assoc, ← hpr, pullback.condition_assoc,
    Category.assoc]

include hdiag in
/-- A morphism `e : T ⟶ Y ×_P W` whose first projection is `t` and whose second projection is a
section of `v : W ⟶ T` is an isomorphism, when `Δ` is a section of `pr` and `W` is the fibre
product `P ×_Y T`. -/
theorem isIso_of_isPullback_of_section {W : Scheme.{u}} {w : W ⟶ P} {v : W ⟶ T}
    (sq : IsPullback w v pr t) (e : T ⟶ pullback Δ w) (he₁ : e ≫ pullback.fst Δ w = t)
    (he₂ : e ≫ pullback.snd Δ w ≫ v = 𝟙 T) : IsIso e := by
  have hfst : pullback.snd Δ w ≫ v ≫ t = pullback.fst Δ w := by
    rw [← sq.w, ← pullback.condition_assoc, hdiag, Category.comp_id]
  refine ⟨⟨pullback.snd Δ w ≫ v, he₂, ?_⟩⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, he₁, hfst, Category.id_comp]
  · refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% he₁,
        reassoc_of% hfst, Category.id_comp, pullback.condition]
    · rw [Category.assoc, Category.assoc, Category.assoc, he₂, Category.comp_id,
        Category.id_comp]

end Section

/-! ### The identity `D ∘ pr^* = 1` on cap operations -/

section CompFlatPullback

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Y P : Scheme.{u}} {sY : Y ⟶ C.S}
  [LocallyOfFiniteType sY] {sP : P ⟶ C.S} [LocallyOfFiniteType sP] {Δ : Y ⟶ P}
  [LocallyOfFiniteType Δ] {r : ℕ}

/-- The assertion `D ∘ pr^* = 1` in `A^0(Y)` for a class `D ∈ A^r(Y ⟶ P)` and a flat morphism
`pr : P ⟶ Y` of relative dimension `r` with section `Δ`: for every test scheme `t : T ⟶ Y` and
every `α ∈ CH_k(T)`, capping the flat pullback of `α` to `P ×_Y T` with `D` returns `α`, read on
`T` through `Stacks.Chow.sectionPullbackIso`. -/
def BivariantClass.CompFlatPullbackEqOne (D : BivariantClass C G (Δ ≫ sP) sP Δ rfl r)
    (pr : P ⟶ Y) [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = sP)
    (hdiag : Δ ≫ pr = 𝟙 Y) (hr : AlgebraicGeometry.RelativeDimension pr r) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k),
    chowPushforwardOfIso C (pullback.fst Δ (pullback.fst pr t) ≫ (Δ ≫ sP)) (t ≫ sY)
        (sectionPullbackIso Δ pr hdiag t).hom
        (sectionPullbackIso_hom_comp_structureMorphism Δ pr hdiag t hpr) (k + r - r)
        (D.cap (pullback.fst pr t) (k + r)
          (flatPullbackChow C (pullback.fst pr t ≫ sP) (t ≫ sY) (pullback.snd pr t)
            (pullbackSnd_comp_structureMorphism hpr t) r (relativeDimension_pullbackSnd pr hr t) k
            (flatPullbackDescends C _ _ _ _ _ _ _) α)) =
      chowGroupDegreeEquiv C (t ≫ sY) (by ring) α

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sP] [LocallyOfFiniteType Δ] in
/-- The structure morphism of `Y ×_P W` over the base, through a section of `v`. -/
theorem comp_fst_comp_structureMorphism_of_section {pr : P ⟶ Y} (hpr : pr ≫ sY = sP)
    (hdiag : Δ ≫ pr = 𝟙 Y) {T W : Scheme.{u}} (t : T ⟶ Y) (w : W ⟶ P)
    (e : T ⟶ pullback Δ w) (he₁ : e ≫ pullback.fst Δ w = t) :
    e ≫ (pullback.fst Δ w ≫ (Δ ≫ sP)) = t ≫ sY := by
  rw [reassoc_of% he₁, ← hpr, reassoc_of% hdiag]

/-- **`D ∘ pr^* = 1`, for any presentation of the fibre product.** If `D ∘ pr^* = 1` on cap
operations, then for every cartesian square `W = P ×_Y T` and every `α ∈ CH_k(T)`, capping the flat
pullback of `α` to `W` with `D` gives `α`, read on `Y ×_P W` through the isomorphism `T ≅ Y ×_P W`
given by `t` and the section of `W ⟶ T`. -/
theorem BivariantClass.CompFlatPullbackEqOne.cap_flatPullbackChow
    {D : BivariantClass C G (Δ ≫ sP) sP Δ rfl r} {pr : P ⟶ Y} [LocallyOfFiniteType pr] [Flat pr]
    {hpr : pr ≫ sY = sP} {hdiag : Δ ≫ pr = 𝟙 Y} {hr : AlgebraicGeometry.RelativeDimension pr r}
    (hD : D.CompFlatPullbackEqOne pr hpr hdiag hr) {T W : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (w : W ⟶ P) [LocallyOfFiniteType w] (v : W ⟶ T)
    [LocallyOfFiniteType v] [Flat v] (sq : IsPullback w v pr t)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (hv : v ≫ (t ≫ sY) = w ≫ sP)
    (e : T ⟶ pullback Δ w) [IsIso e] (he₁ : e ≫ pullback.fst Δ w = t)
    (he₂ : e ≫ pullback.snd Δ w ≫ v = 𝟙 T) (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    D.cap w (k + r) (flatPullbackChow C (w ≫ sP) (t ≫ sY) v hv r hvr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      chowGroupDegreeEquiv C (pullback.fst Δ w ≫ (Δ ≫ sP)) (by ring)
        (chowPushforwardOfIso C (t ≫ sY) (pullback.fst Δ w ≫ (Δ ≫ sP)) e
          (comp_fst_comp_structureMorphism_of_section hpr hdiag t w e he₁) k α) := by
  have hφ₁ := sq.isoPullback_hom_fst
  have hφ₂ := sq.isoPullback_hom_snd
  have hc := hD t k α
  -- the flat pullback to the chosen fibre product is the pushforward of the one to `W`
  have hflat := flatPullbackChow_chowPushforwardOfIso C (t ≫ sY) (w ≫ sP) (t ≫ sY)
    (pullback.fst pr t ≫ sP) (𝟙 T) (Category.id_comp _) sq.isoPullback.hom
    (by rw [reassoc_of% hφ₁]) v hv (pullback.snd pr t) (pullbackSnd_comp_structureMorphism hpr t)
    (by rw [Category.comp_id, hφ₂]) r hvr (relativeDimension_pullbackSnd pr hr t) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  rw [chowPushforwardOfIso_id] at hflat
  rw [hflat] at hc
  rw [D.cap_chowPushforwardOfIso (pullback.fst pr t) sq.isoPullback.hom w hφ₁ (w ≫ sP) rfl
    (k + r) (by rw [reassoc_of% hφ₁])
    (flatPullbackChow C (w ≫ sP) (t ≫ sY) v hv r hvr k (flatPullbackDescends C _ _ _ _ _ _ _) α)
    (flatPullbackChow C (w ≫ sP) (t ≫ sY) v hv r hvr k (flatPullbackDescends C _ _ _ _ _ _ _) α)
    rfl, chowPushforwardOfIso_comp_apply] at hc
  -- the composite isomorphism `Y ×_P W ⟶ T` is inverse to `e`
  have he : e ≫ (testBaseChangeIso Δ (pullback.fst pr t) sq.isoPullback.hom w hφ₁).hom ≫
      (sectionPullbackIso Δ pr hdiag t).hom = 𝟙 T := by
    simp only [sectionPullbackIso_hom, testBaseChangeIso_hom_snd_assoc, hφ₂, he₂]
  have he' : ((testBaseChangeIso Δ (pullback.fst pr t) sq.isoPullback.hom w hφ₁).hom ≫
      (sectionPullbackIso Δ pr hdiag t).hom) ≫ e = 𝟙 _ := by
    rw [← cancel_epi e, ← Category.assoc, he, Category.id_comp, Category.comp_id]
  have h2 := congrArg (chowPushforwardOfIso C (t ≫ sY) (pullback.fst Δ w ≫ (Δ ≫ sP)) e
    (comp_fst_comp_structureMorphism_of_section hpr hdiag t w e he₁) (k + r - r)) hc
  rwa [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) he' _
    (Category.id_comp _), chowPushforwardOfIso_id,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso] at h2

end CompFlatPullback

/-! ### The diagonal square -/

section DiagonalSquare

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 02NK** for the first projection of `Y ×_Z Y`: it has the relative dimension of
`g`. -/
theorem relativeDimension_pullback_fst_self [LocallyOfFiniteType g] {d : ℕ}
    (hgd : AlgebraicGeometry.RelativeDimension g d) :
    AlgebraicGeometry.RelativeDimension (pullback.fst g g) d :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback g g).flip hgd

/-- The morphism `f × 𝟙 : X ×_Z Y ⟶ Y ×_Z Y`. -/
abbrev smoothShiftBaseMap : pullback (f ≫ g) g ⟶ pullback g g :=
  pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 Z) (by simp) (by simp)

/-- The inverse of `smoothShiftDiagonalPullbackIso`. -/
def smoothShiftDiagonalPullbackIsoInv :
    X ⟶ pullback (pullback.diagonal g) (smoothShiftBaseMap f g) :=
  pullback.lift f (pullback.lift (f := f ≫ g) (g := g) (𝟙 X) f (by simp)) (by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullbackMap_fst,
        pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd])

/-- The first projection of the pullback of the diagonal along `m`, read through the first
projection of `Y ×_Z Y`. -/
private theorem diagonal_fst_eq_snd_comp_fst {W : Scheme.{u}} (m : W ⟶ pullback g g) :
    pullback.fst (pullback.diagonal g) m = pullback.snd _ _ ≫ m ≫ pullback.fst g g := by
  simpa using congrArg (· ≫ pullback.fst g g)
    (pullback.condition (f := pullback.diagonal g) (g := m))

/-- The first projection of the pullback of the diagonal along `m`, read through the second
projection of `Y ×_Z Y`. -/
private theorem diagonal_fst_eq_snd_comp_snd {W : Scheme.{u}} (m : W ⟶ pullback g g) :
    pullback.fst (pullback.diagonal g) m = pullback.snd _ _ ≫ m ≫ pullback.snd g g := by
  simpa using congrArg (· ≫ pullback.snd g g)
    (pullback.condition (f := pullback.diagonal g) (g := m))

/-- The first projection of the pullback of the diagonal along `f × 𝟙`, read through `X`. -/
@[reassoc]
theorem smoothShift_diagonal_fst_eq_fst :
    pullback.fst (pullback.diagonal g) (smoothShiftBaseMap f g) =
      pullback.snd _ _ ≫ pullback.fst (f ≫ g) g ≫ f := by
  simp [diagonal_fst_eq_snd_comp_fst]

/-- The first projection of the pullback of the diagonal along `f × 𝟙`, read through `Y`. -/
@[reassoc]
theorem smoothShift_diagonal_fst_eq_snd :
    pullback.fst (pullback.diagonal g) (smoothShiftBaseMap f g) =
      pullback.snd _ _ ≫ pullback.snd (f ≫ g) g := by
  simp [diagonal_fst_eq_snd_comp_snd]

/-- The square formed by `f : X ⟶ Y`, the diagonal `Y ⟶ Y ×_Z Y` and `f × 𝟙` is cartesian:
the pullback of the diagonal along `f × 𝟙` is `X`. -/
def smoothShiftDiagonalPullbackIso :
    pullback (pullback.diagonal g) (smoothShiftBaseMap f g) ≅ X where
  hom := pullback.snd _ _ ≫ pullback.fst _ _
  inv := smoothShiftDiagonalPullbackIsoInv f g
  hom_inv_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [smoothShiftDiagonalPullbackIsoInv, Category.assoc, pullback.lift_fst,
        Category.id_comp]
      exact (smoothShift_diagonal_fst_eq_fst f g).symm
    · simp only [smoothShiftDiagonalPullbackIsoInv, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_fst, Category.comp_id, Category.id_comp]
    · simp only [smoothShiftDiagonalPullbackIsoInv, Category.assoc, pullback.lift_snd,
        Category.id_comp]
      rw [← smoothShift_diagonal_fst_eq_fst, smoothShift_diagonal_fst_eq_snd]
  inv_hom_id := by
    simp only [smoothShiftDiagonalPullbackIsoInv, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The isomorphism `Stacks.Chow.smoothShiftDiagonalPullbackIso` is the second projection followed
by the first projection. -/
@[reassoc (attr := simp)]
theorem smoothShiftDiagonalPullbackIso_hom :
    (smoothShiftDiagonalPullbackIso f g).hom = pullback.snd _ _ ≫ pullback.fst _ _ := rfl

/-- The isomorphism `Stacks.Chow.smoothShiftDiagonalPullbackIso` lies over `Y`. -/
theorem smoothShiftDiagonalPullbackIso_hom_comp :
    (smoothShiftDiagonalPullbackIso f g).hom ≫ f =
      pullback.snd _ _ ≫ pullback.snd (f ≫ g) g := by
  rw [smoothShiftDiagonalPullbackIso_hom, Category.assoc, ← smoothShift_diagonal_fst_eq_fst,
    smoothShift_diagonal_fst_eq_snd]

/-- The test morphism `X ×_Z T ⟶ Y ×_Z Y`, `(x, τ) ↦ (f x, t τ)`, of a test scheme
`t : T ⟶ Y`. -/
abbrev smoothShiftTestMap {T : Scheme.{u}} (t : T ⟶ Y) :
    pullback (f ≫ g) (t ≫ g) ⟶ pullback g g :=
  pullback.map (f ≫ g) (t ≫ g) g g f t (𝟙 Z) (by simp) (by simp)

variable {T : Scheme.{u}} (t : T ⟶ Y)

/-- The first projection of the pullback of the diagonal along the test morphism, read through
`X`. -/
@[reassoc]
theorem smoothShift_diagonal_testMap_fst_eq_fst :
    pullback.fst (pullback.diagonal g) (smoothShiftTestMap f g t) =
      pullback.snd _ _ ≫ pullback.fst (f ≫ g) (t ≫ g) ≫ f := by
  simp [diagonal_fst_eq_snd_comp_fst]

/-- The first projection of the pullback of the diagonal along the test morphism, read through
`T`. -/
@[reassoc]
theorem smoothShift_diagonal_testMap_fst_eq_snd :
    pullback.fst (pullback.diagonal g) (smoothShiftTestMap f g t) =
      pullback.snd _ _ ≫ pullback.snd (f ≫ g) (t ≫ g) ≫ t := by
  simp [diagonal_fst_eq_snd_comp_snd]

/-- The pullback of the diagonal of `g` along the test morphism `X ×_Z T ⟶ Y ×_Z Y` is
`X ×_Y T`. -/
def smoothShiftCapIso :
    pullback (pullback.diagonal g) (smoothShiftTestMap f g t) ≅ pullback f t where
  hom := pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
    (by rw [Category.assoc, Category.assoc, ← smoothShift_diagonal_testMap_fst_eq_fst,
      smoothShift_diagonal_testMap_fst_eq_snd])
  inv := pullback.lift (pullback.fst f t ≫ f)
    (pullback.lift (f := f ≫ g) (g := t ≫ g) (pullback.fst f t) (pullback.snd f t)
      (by rw [← Category.assoc, pullback.condition, Category.assoc]))
    (by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullbackMap_fst,
          pullback.lift_fst_assoc]
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullbackMap_snd,
          pullback.lift_snd_assoc, pullback.condition])
  hom_inv_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      exact (smoothShift_diagonal_testMap_fst_eq_fst f g t).symm
    · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]

/-- The isomorphism `Stacks.Chow.smoothShiftCapIso` followed by the projection to `X` is the
projection to `X` through `X ×_Z T`. -/
@[reassoc (attr := simp)]
theorem smoothShiftCapIso_hom_fst :
    (smoothShiftCapIso f g t).hom ≫ pullback.fst f t =
      pullback.snd _ _ ≫ pullback.fst (f ≫ g) (t ≫ g) :=
  pullback.lift_fst _ _ _

/-- The isomorphism `Stacks.Chow.smoothShiftCapIso` followed by the projection to `T` is the
projection to `T` through `X ×_Z T`. -/
@[reassoc (attr := simp)]
theorem smoothShiftCapIso_hom_snd :
    (smoothShiftCapIso f g t).hom ≫ pullback.snd f t =
      pullback.snd _ _ ≫ pullback.snd (f ≫ g) (t ≫ g) :=
  pullback.lift_snd _ _ _

section Diagonal

/-- The test morphism `Y ×_Z T ⟶ Y ×_Z Y`, `(y, τ) ↦ (y, t τ)`. -/
abbrev smoothShiftDiagonalTestMap : pullback g (t ≫ g) ⟶ pullback g g :=
  pullback.map g (t ≫ g) g g (𝟙 Y) t (𝟙 Z) (by simp) (by simp)

/-- The square formed by `Y ×_Z T ⟶ Y ×_Z Y`, `Y ×_Z T ⟶ T`, the second projection of
`Y ×_Z Y` and `t` is cartesian. -/
theorem isPullback_smoothShiftDiagonalTestMap :
    IsPullback (smoothShiftDiagonalTestMap g t) (pullback.snd g (t ≫ g)) (pullback.snd g g) t :=
  IsPullback.of_right (h₁₂ := pullback.fst g g) (h₂₂ := g) (v₁₃ := g)
    (by simpa using IsPullback.of_hasPullback g (t ≫ g)) (by simp)
    (IsPullback.of_hasPullback g g)

/-- The section `T ⟶ Y ×_{Y ×_Z Y} (Y ×_Z T)`, `τ ↦ (t τ, (t τ, τ))`. -/
def smoothShiftDiagonalSection :
    T ⟶ pullback (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) :=
  pullback.lift t (pullback.lift (f := g) (g := t ≫ g) t (𝟙 T) (by simp)) (by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullbackMap_snd,
        pullback.lift_snd_assoc, Category.id_comp])

/-- The section `Stacks.Chow.smoothShiftDiagonalSection` followed by the projection to `Y` is
`t`. -/
@[reassoc (attr := simp)]
theorem smoothShiftDiagonalSection_fst :
    smoothShiftDiagonalSection g t ≫ pullback.fst _ _ = t :=
  pullback.lift_fst _ _ _

/-- The section `Stacks.Chow.smoothShiftDiagonalSection` followed by the projection to `T` is the
identity. -/
@[reassoc (attr := simp)]
theorem smoothShiftDiagonalSection_snd_snd :
    smoothShiftDiagonalSection g t ≫ pullback.snd _ _ ≫ pullback.snd g (t ≫ g) = 𝟙 T := by
  simp only [smoothShiftDiagonalSection, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The section `Stacks.Chow.smoothShiftDiagonalSection` followed by the projection to the factor
`Y` of `Y ×_Z T` is `t`. -/
@[reassoc (attr := simp)]
theorem smoothShiftDiagonalSection_snd_fst :
    smoothShiftDiagonalSection g t ≫ pullback.snd _ _ ≫ pullback.fst g (t ≫ g) = t := by
  simp only [smoothShiftDiagonalSection, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The section `T ⟶ Y ×_{Y ×_Z Y} (Y ×_Z T)` is an isomorphism. -/
instance : IsIso (smoothShiftDiagonalSection g t) :=
  isIso_of_isPullback_of_section (pullback.diagonal g) (pullback.snd g g)
    (pullback.diagonal_snd g) t (isPullback_smoothShiftDiagonalTestMap g t) _
    (smoothShiftDiagonalSection_fst g t) (smoothShiftDiagonalSection_snd_snd g t)

end Diagonal

section Forget

variable (s : T ⟶ Z)

/-- The projection `X ×_Z (Y ×_Z T) ⟶ X ×_Z T` forgetting the point of `Y`. -/
abbrev smoothShiftForgetMap :
    pullback (f ≫ g) (pullback.fst g s ≫ g) ⟶ pullback (f ≫ g) s :=
  pullback.map (f ≫ g) (pullback.fst g s ≫ g) (f ≫ g) s (𝟙 X) (pullback.snd g s) (𝟙 Z)
    (by simp) (by simp [pullback.condition])

/-- A point of `Y ×_Z Y` and a point of `X ×_Z T` with the same image in `Y` have the same image
in `Z`. -/
@[reassoc]
theorem smoothShift_fst_comp_snd_comp_eq {Q : Scheme.{u}} (q₁ : Q ⟶ pullback g g)
    (q₂ : Q ⟶ pullback (f ≫ g) s)
    (hq : q₁ ≫ pullback.fst g g = q₂ ≫ pullback.fst (f ≫ g) s ≫ f) :
    q₁ ≫ pullback.snd g g ≫ g = q₂ ≫ pullback.snd (f ≫ g) s ≫ s := by
  rw [← pullback.condition (f := g) (g := g), reassoc_of% hq,
    ← pullback.condition (f := f ≫ g) (g := s)]

/-- The square formed by `X ×_Z (Y ×_Z T) ⟶ Y ×_Z Y`, the projection forgetting `Y`, the first
projection of `Y ×_Z Y` and `X ×_Z T ⟶ X ⟶ Y` is cartesian. -/
theorem isPullback_smoothShiftForgetMap :
    IsPullback (smoothShiftTestMap f g (pullback.fst g s)) (smoothShiftForgetMap f g s)
      (pullback.fst g g) (pullback.fst (f ≫ g) s ≫ f) := by
  have hc : smoothShiftTestMap f g (pullback.fst g s) ≫ pullback.fst g g =
      smoothShiftForgetMap f g s ≫ pullback.fst (f ≫ g) s ≫ f := by
    simp only [pullbackMap_fst, pullbackMap_fst_assoc, Category.id_comp]
  refine IsPullback.of_iso_pullback ⟨hc⟩
    { hom := pullback.lift _ _ hc
      inv := pullback.lift (pullback.snd _ _ ≫ pullback.fst (f ≫ g) s)
        (pullback.lift (f := g) (g := s) (pullback.fst _ _ ≫ pullback.snd g g)
          (pullback.snd _ _ ≫ pullback.snd (f ≫ g) s)
          (by rw [Category.assoc, Category.assoc]
              exact smoothShift_fst_comp_snd_comp_eq f g s _ _ pullback.condition))
        (by
          have h1 := pullback.condition (f := pullback.fst g g) (g := pullback.fst (f ≫ g) s ≫ f)
          simp only [Category.assoc, pullback.lift_fst_assoc]
          rw [← pullback.condition (f := g) (g := g), reassoc_of% h1])
      hom_inv_id := by
        refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc,
            Category.comp_id, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst,
            pullback.lift_fst_assoc, pullbackMap_snd, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
        · simp only [Category.assoc, pullback.lift_fst_assoc, pullbackMap_fst, Category.id_comp]
          exact pullback.condition.symm
        · simp only [Category.assoc, pullbackMap_snd, pullback.lift_snd_assoc, pullback.lift_fst,
            Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst, Category.comp_id,
            Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp] }
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The projection forgetting `Y` is the base change of `Y ×_Z T ⟶ T`. -/
theorem isPullback_smoothShiftForgetMap_snd :
    IsPullback (pullback.snd (f ≫ g) (pullback.fst g s ≫ g)) (smoothShiftForgetMap f g s)
      (pullback.snd g s) (pullback.snd (f ≫ g) s) := by
  refine (isPullback_bivariantBaseChangeMap (f ≫ g) s (pullback.snd g s)).of_iso
    (pullback.congrHom rfl pullback.condition.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp [pullback.congrHom_hom]
  · refine pullback.hom_ext ?_ ?_ <;> simp [pullback.congrHom_hom, bivariantBaseChangeMap]

/-- The section `X ×_Z T ⟶ X ×_Z (Y ×_Z T)`, `(x, τ) ↦ (x, f x, τ)`, of the projection
forgetting `Y`. -/
def smoothShiftForgetSection : pullback (f ≫ g) s ⟶ pullback (f ≫ g) (pullback.fst g s ≫ g) :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (f := g) (g := s) (pullback.fst _ _ ≫ f) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition]))
    (by rw [pullback.lift_fst_assoc, Category.assoc])

/-- The section `Stacks.Chow.smoothShiftForgetSection` followed by the test morphism to `Y ×_Z Y`
is `(x, τ) ↦ (f x, f x)`. -/
@[reassoc (attr := simp)]
theorem smoothShiftForgetSection_testMap :
    smoothShiftForgetSection f g s ≫ smoothShiftTestMap f g (pullback.fst g s) =
      (pullback.fst (f ≫ g) s ≫ f) ≫ pullback.diagonal g := by
  refine pullback.hom_ext ?_ ?_
  · simp only [smoothShiftForgetSection, Category.assoc, pullbackMap_fst, pullback.lift_fst_assoc,
      pullback.diagonal_fst, Category.comp_id]
  · simp only [smoothShiftForgetSection, Category.assoc, pullbackMap_snd, pullback.lift_snd_assoc,
      pullback.lift_fst, pullback.diagonal_snd, Category.comp_id]

/-- `Stacks.Chow.smoothShiftForgetSection` is a section of the projection forgetting `Y`. -/
@[reassoc (attr := simp)]
theorem smoothShiftForgetSection_forgetMap :
    smoothShiftForgetSection f g s ≫ smoothShiftForgetMap f g s = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · simp only [smoothShiftForgetSection, Category.assoc, pullback.lift_fst, Category.comp_id,
      Category.id_comp]
  · simp only [smoothShiftForgetSection, Category.assoc, pullback.lift_snd_assoc,
      pullback.lift_snd, Category.id_comp]

/-- The isomorphism `X ×_Z T ≅ Y ×_{Y ×_Z Y} (X ×_Z (Y ×_Z T))`. -/
def smoothShiftForgetIso :
    pullback (f ≫ g) s ⟶
      pullback (pullback.diagonal g) (smoothShiftTestMap f g (pullback.fst g s)) :=
  pullback.lift (pullback.fst (f ≫ g) s ≫ f) (smoothShiftForgetSection f g s)
    (smoothShiftForgetSection_testMap f g s).symm

/-- The projection of `Stacks.Chow.smoothShiftForgetIso` to `Y` is `(x, τ) ↦ f x`. -/
@[reassoc (attr := simp)]
theorem smoothShiftForgetIso_fst :
    smoothShiftForgetIso f g s ≫ pullback.fst _ _ = pullback.fst (f ≫ g) s ≫ f :=
  pullback.lift_fst _ _ _

/-- The second projection of `Stacks.Chow.smoothShiftForgetIso` is
`Stacks.Chow.smoothShiftForgetSection`. -/
@[reassoc (attr := simp)]
theorem smoothShiftForgetIso_snd :
    smoothShiftForgetIso f g s ≫ pullback.snd _ _ = smoothShiftForgetSection f g s :=
  pullback.lift_snd _ _ _

/-- The morphism `X ×_Z T ⟶ Y ×_{Y ×_Z Y} (X ×_Z (Y ×_Z T))` is an isomorphism. -/
instance : IsIso (smoothShiftForgetIso f g s) :=
  isIso_of_isPullback_of_section (pullback.diagonal g) (pullback.fst g g)
    (pullback.diagonal_fst g) _ (isPullback_smoothShiftForgetMap f g s) _
    (smoothShiftForgetIso_fst f g s)
    (by rw [smoothShiftForgetIso_snd_assoc, smoothShiftForgetSection_forgetMap])

end Forget

end DiagonalSquare

section Maps

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (d : ℕ) (hgd : AlgebraicGeometry.RelativeDimension g d)
  (p : ℤ)

omit [Flat g] in
/-- The morphism `f × 𝟙 : X ×_Z Y ⟶ Y ×_Z Y` is locally of finite type. -/
instance : LocallyOfFiniteType (smoothShiftBaseMap f g) := by
  have : LocallyOfFiniteType (smoothShiftBaseMap f g ≫ pullback.snd g g) := by
    rw [pullbackMap_snd, Category.comp_id]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.snd g g)

omit [Flat g] in
/-- The test morphism `X ×_Z T ⟶ Y ×_Z Y` is locally of finite type when `t` is. -/
instance {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] :
    LocallyOfFiniteType (smoothShiftTestMap f g t) := by
  have : LocallyOfFiniteType (smoothShiftTestMap f g t ≫ pullback.snd g g) := by
    rw [pullbackMap_snd]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.snd g g)

omit [Flat g] in
/-- The test morphism `Y ×_Z T ⟶ Y ×_Z Y` is locally of finite type when `t` is. -/
instance {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] :
    LocallyOfFiniteType (smoothShiftDiagonalTestMap g t) := by
  have : LocallyOfFiniteType (smoothShiftDiagonalTestMap g t ≫ pullback.snd g g) := by
    rw [pullbackMap_snd]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (pullback.snd g g)

/-- The flat pullback class `g^* ∈ A^{-d}(Y ⟶ Z)` of Stacks 0B78, at the Gysin system of the
first Chern class rule, with all of its inputs discharged. -/
abbrev smoothShiftFlatPullbackClass :
    BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg (-(d : ℤ)) :=
  flatPullbackBivariantClassOfInvertible C sY sZ g hg d hgd

/-- **The forward map of Stacks 0FBT**: `A^p(X ⟶ Y) ⟶ A^{p-d}(X ⟶ Z)`, `c ↦ c ∘ g^*`, the
composite (Stacks 0B75) with the flat pullback class of `g`. -/
def smoothShiftForward :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p →+
      BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p - d) :=
  (bivariantCompositeBilinearOfInvertible C sX sY sZ f g hf hg p (-(d : ℤ))).flip
    (smoothShiftFlatPullbackClass C sY sZ g hg d hgd)

/-- The forward map is the composite with `g^*`, by definition. -/
theorem smoothShiftForward_apply (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    smoothShiftForward C sX sY sZ f g hf hg d hgd p c =
      bivariantCompositeOfInvertible C sX sY sZ f g hf hg p (-(d : ℤ)) c
        (smoothShiftFlatPullbackClass C sY sZ g hg d hgd) :=
  rfl

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [Flat g] in
include hf in
/-- The morphism `f × 𝟙` is a morphism over the base. -/
theorem smoothShiftBaseMap_comp_structureMorphism :
    smoothShiftBaseMap f g ≫ (pullback.fst g g ≫ sY) = pullback.fst (f ≫ g) g ≫ sX := by
  simp [hf]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Flat g] in
include hf hg in
/-- The second projection `X ×_Z Y ⟶ Y` is a morphism over the base. -/
theorem smoothShift_snd_comp_structureMorphism :
    pullback.snd (f ≫ g) g ≫ sY = pullback.fst (f ≫ g) g ≫ sX := by
  rw [← hg]
  exact pullbackSnd_comp_structureMorphism_eq C sX sZ (f ≫ g)
    (comp_comp_structureMorphism_eq hf hg) g

omit [Flat g] in
/-- **The backward map of Stacks 0FBT**, for a class `D ∈ A^d(Y ⟶ Y ×_Z Y)` for the diagonal:
`A^{p-d}(X ⟶ Z) ⟶ A^p(X ⟶ Y)`, `c' ↦ res(D) ∘ res(c')`. Here `res(c')` is the restriction of `c'`
along `g` and `res(D)` that of `D` along `f × 𝟙 : X ×_Z Y ⟶ Y ×_Z Y` (Stacks 0F9Z); the composite
is a class for `Y ×_{Y ×_Z Y} (X ×_Z Y) ⟶ Y`, carried to a class for `f` along
`Stacks.Chow.smoothShiftDiagonalPullbackIso`.

Stacks 0FBT takes `D` to be the Gysin class of the diagonal; the tagged statement will instantiate
`D` with the canonical class of Stacks 0FBK once it is available. -/
def smoothShiftBackward
    (D : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
      (pullback.diagonal g) rfl d) :
    BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p - d) →+
      BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p :=
  (bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX sY f hf
      (show (d : ℤ) + (p - d) = p by ring)).toAddMonoidHom.comp <|
    (bivariantTransportAddHom C (gysinSystemOfInvertible C) _ sX sY
      (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g) ≫ pullback.snd (f ≫ g) g)
      (by rw [Category.assoc, ← smoothShift_diagonal_fst_eq_snd_assoc, pullback.diagonal_fst_assoc])
      f hf (smoothShiftDiagonalPullbackIso f g)
      (smoothShiftDiagonalPullbackIso_hom_comp f g) _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)).comp <|
    (bivariantCompositeBilinearOfInvertible C _ (pullback.fst (f ≫ g) g ≫ sX) sY
      (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g)) (pullback.snd (f ≫ g) g)
      (by rw [pullback.diagonal_fst_assoc, smoothShift_diagonal_fst_eq_fst_assoc, hf])
      (smoothShift_snd_comp_structureMorphism C sX sY sZ f g hf hg) (d : ℤ) (p - d)
      (bivariantClassCongrBase C (gysinSystemOfInvertible C)
        (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g)) rfl
        (smoothShiftBaseMap_comp_structureMorphism C sX sY f g hf) (d : ℤ)
        (bivariantRestriction C (gysinSystemOfInvertible C) _ _ (pullback.diagonal g) rfl
          (smoothShiftBaseMap f g) (d : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) D))).comp <|
    (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd (f ≫ g) g) rfl hg
      (p - d)).toAddMonoidHom.comp <|
    bivariantRestrictionAddHom C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) g (p - d)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)

/-- The cap operation of `c ∘ g^*` at a test scheme `u : T ⟶ Z` is `c` capped at `Y ×_Z T ⟶ Y`
with the flat pullback of `α` to `Y ×_Z T`, read on `X ×_Z T`. -/
theorem smoothShiftForward_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}}
    (u : T ⟶ Z) [LocallyOfFiniteType u] (k : ℤ) (α : chowGroup C (u ≫ sZ) k) :
    (smoothShiftForward C sX sY sZ f g hf hg d hgd p c).cap u k α ≍
      chowPushforwardOfIso C (pullback.fst f (pullback.fst g u) ≫ sX)
        (pullback.fst (f ≫ g) u ≫ sX) (pullbackRightPullbackFstIso g u f).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g u) (k + d - p)
        (c.cap (pullback.fst g u) (k + d)
          (flatPullbackChow C (pullback.fst g u ≫ sY) (u ≫ sZ) (pullback.snd g u)
            (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg u) d
            (relativeDimension_pullback_snd g u d hgd) k
            (flatPullbackDescends C _ _ _ _ _ _ _) α)) := by
  rw [smoothShiftForward_apply]
  refine HEq.trans (chowGroupDegreeEquiv_heq C _ _ _) ?_
  rw [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso]
  refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ ?_
  refine c.cap_heq_congr (pullback.fst g u) (by ring) _ _ ?_
  exact flatPullbackBivariantCap_heq C sY sZ g hg d hgd (flatPullbackDescends C) u k α

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [Flat g] in
include hf in
/-- The test morphism `X ×_Z T ⟶ Y ×_Z Y` is a morphism over the base. -/
theorem smoothShiftTestMap_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ Y) :
    pullback.fst (f ≫ g) (t ≫ g) ≫ sX = smoothShiftTestMap f g t ≫ (pullback.fst g g ≫ sY) := by
  simp [hf]

variable (D : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
      (pullback.diagonal g) rfl d)

omit [Flat g] in
/-- The backward map, unfolded: the composite of the restrictions of `D` and of `c'`, carried to a
class for `f` and read in degree `p`. -/
theorem smoothShiftBackward_apply
    (c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) (p - d)) :
    smoothShiftBackward C sX sY sZ f g hf hg d p D c' =
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) sX sY f hf
        (show (d : ℤ) + (p - d) = p by ring)
        (bivariantTransport C (gysinSystemOfInvertible C) _ sX sY
          (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g) ≫ pullback.snd (f ≫ g) g)
          (by rw [Category.assoc, ← smoothShift_diagonal_fst_eq_snd_assoc,
            pullback.diagonal_fst_assoc])
          f hf (smoothShiftDiagonalPullbackIso f g) (smoothShiftDiagonalPullbackIso_hom_comp f g) _
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (bivariantCompositeOfInvertible C _ (pullback.fst (f ≫ g) g ≫ sX) sY
            (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g))
            (pullback.snd (f ≫ g) g)
            (by rw [pullback.diagonal_fst_assoc, smoothShift_diagonal_fst_eq_fst_assoc, hf])
            (smoothShift_snd_comp_structureMorphism C sX sY sZ f g hf hg) (d : ℤ) (p - d)
            (bivariantClassCongrBase C (gysinSystemOfInvertible C)
              (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g)) rfl
              (smoothShiftBaseMap_comp_structureMorphism C sX sY f g hf) (d : ℤ)
              (bivariantRestriction C (gysinSystemOfInvertible C) _ _ (pullback.diagonal g) rfl
                (smoothShiftBaseMap f g) (d : ℤ)
                (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) D))
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd (f ≫ g) g) rfl
              hg (p - d)
              (bivariantRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
                (comp_comp_structureMorphism_eq hf hg) g (p - d)
                (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c')))) :=
  rfl

omit [Flat g] in
/-- The cap operation of `res(D) ∘ res(c')`, read on `X ×_Y T`: it is `D` capped at
`X ×_Z T ⟶ Y ×_Z Y` with `c' ∩ α`, carried to `X ×_Y T` along any isomorphism over the two
projections. -/
theorem smoothShiftBackward_cap
    (c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) (p - d)) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k)
    (Ξ : pullback (pullback.diagonal g) (smoothShiftTestMap f g t) ⟶ pullback f t) [IsIso Ξ]
    (hΞ₁ : Ξ ≫ pullback.fst f t = pullback.snd _ _ ≫ pullback.fst (f ≫ g) (t ≫ g))
    (hΞ₂ : Ξ ≫ pullback.snd f t = pullback.snd _ _ ≫ pullback.snd (f ≫ g) (t ≫ g))
    (hΞ : Ξ ≫ (pullback.fst f t ≫ sX) =
      pullback.fst _ _ ≫ (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))) :
    (smoothShiftBackward C sX sY sZ f g hf hg d p D c').cap t k α ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal g) (smoothShiftTestMap f g t) ≫
          (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)))
        (pullback.fst f t ≫ sX) Ξ hΞ (k - (p - d) - d)
        (D.cap (smoothShiftTestMap f g t) (k - (p - d))
          (chowGroupCongr C (smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t)
            (k - (p - d))
            (c'.cap (t ≫ g) k
              (chowGroupCongr C (by rw [Category.assoc, hg]) k α)))) := by
  rw [smoothShiftBackward_apply]
  refine HEq.trans (bivariantClassDegreeCongr_cap C _ sX sY f hf _ _ t k α) ?_
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantCompositeOfInvertible,
    bivariantComposite_cap, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso]
  -- the restriction of `c'`, read on the test scheme
  have hα₀ : t ≫ sY = t ≫ (g ≫ sZ) := by rw [hg]
  have ha := bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.snd (f ≫ g) g)
    rfl hg (p - d) (bivariantRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) g (p - d)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c') t k
    (chowGroupCongr C hα₀ k α) α (chowGroupCongr_heq C hα₀ k α)
    (hv := pullbackSnd_comp_structureMorphism_eq C sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) g)
    (hv' := smoothShift_snd_comp_structureMorphism C sX sY sZ f g hf hg)
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply] at ha
  -- the restriction of `D`, read on the test scheme
  have hs := smoothShiftBaseMap_comp_structureMorphism C sX sY f g hf
  have hsy : pullback.fst (pullback.snd (f ≫ g) g) t ≫ (pullback.fst (f ≫ g) g ≫ sX) =
      pullback.fst (pullback.snd (f ≫ g) g) t ≫ (smoothShiftBaseMap f g ≫
        (pullback.fst g g ≫ sY)) := by rw [hs]
  set y := ((bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd (f ≫ g) g) rfl
    hg (p - d) (hv := pullbackSnd_comp_structureMorphism_eq C sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) g)
    (hv' := smoothShift_snd_comp_structureMorphism C sX sY sZ f g hf hg))
    (bivariantRestriction C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) g (p - d)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c')).cap t k α with hy
  have hb := bivariantClassCongrBase_cap C (gysinSystemOfInvertible C)
    (pullback.snd (pullback.diagonal g) (smoothShiftBaseMap f g)) rfl hs (d : ℤ)
    (bivariantRestriction C (gysinSystemOfInvertible C) _ _ (pullback.diagonal g) rfl
      (smoothShiftBaseMap f g) (d : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) D)
    (pullback.fst (pullback.snd (f ≫ g) g) t) (k - (p - d)) (chowGroupCongr C hsy _ y) y
    (chowGroupCongr_heq C hsy _ y)
    (hv := pullbackSnd_comp_structureMorphism_eq C _ _ (pullback.diagonal g) rfl
      (smoothShiftBaseMap f g))
    (hv' := by rw [pullback.diagonal_fst_assoc, smoothShift_diagonal_fst_eq_fst_assoc, hf])
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply] at hb
  have hm : (pullbackLeftPullbackSndIso (f ≫ g) g t).inv ≫
      (pullback.fst (pullback.snd (f ≫ g) g) t ≫ smoothShiftBaseMap f g) =
        smoothShiftTestMap f g t := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  have hD := D.cap_heq_chowPushforwardOfIso
    (pullback.fst (pullback.snd (f ≫ g) g) t ≫ smoothShiftBaseMap f g)
    (pullbackLeftPullbackSndIso (f ≫ g) g t).inv (smoothShiftTestMap f g t) hm rfl
    (c'.cap (t ≫ g) k (chowGroupCongr C (by rw [Category.assoc, hg]) k α))
    (chowGroupCongr C (Category.assoc _ _ _).symm (k - (p - d))
      (chowGroupCongr C hsy (k - (p - d)) y))
    (by rw [← Category.assoc, hm,
      ← smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t]) ?_
    (chowGroupCongr C (smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t)
      (k - (p - d)) (c'.cap (t ≫ g) k (chowGroupCongr C (by rw [Category.assoc, hg]) k α)))
    (chowGroupCongr_heq C _ _ _)
  rotate_left
  · refine (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
      (ha.trans ?_))
    refine chowPushforwardOfIso_heq _ _ _ rfl (by rw [Category.assoc, hs]) rfl ?_
    refine c'.cap_heq_congr (t ≫ g) rfl _ _ ?_
    exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
      (chowGroupCongr_heq C _ _ _).symm)
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)) ?_
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ HEq.rfl) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ hb) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ hD) ?_
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  refine pullback.hom_ext ?_ ?_
  · rw [hΞ₁]
    simp
  · rw [hΞ₂]
    simp

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ] [LocallyOfFiniteType g] [Flat g] in
include hg in
/-- The two projections of `Y ×_Z Y` agree over the base. -/
theorem smoothShift_pullback_snd_comp_structureMorphism :
    pullback.snd g g ≫ sY = pullback.fst g g ≫ sY := by
  rw [← hg, pullback.condition_assoc]

/-- **The second computation of Stacks 0FBT**: `res(D) ∘ res(c') ∘ g^* = c'`, from
`D ∘ pr₁^* = 1`. -/
theorem smoothShiftForward_smoothShiftBackward
    (hD₁ : D.CompFlatPullbackEqOne (pullback.fst g g) rfl (pullback.diagonal_fst g)
      (relativeDimension_pullback_fst_self g hgd))
    (c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) (p - d)) :
    smoothShiftForward C sX sY sZ f g hf hg d hgd p
        (smoothShiftBackward C sX sY sZ f g hf hg d p D c') =
      c' := by
  refine BivariantClass.ext C _ sX sZ (f ≫ g) _ (p - d) ?_
  intro T u _ k α
  refine eq_of_heq ?_
  refine HEq.trans (smoothShiftForward_cap C sX sY sZ f g hf hg d hgd p _ u k α) ?_
  have hr : AlgebraicGeometry.RelativeDimension (pullback.snd g u) d :=
    relativeDimension_pullback_snd g u d hgd
  set β := flatPullbackChow C (pullback.fst g u ≫ sY) (u ≫ sZ) (pullback.snd g u)
    (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg u) d hr k
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  have hB := smoothShiftBackward_cap C sX sY sZ f g hf hg d p D c' (pullback.fst g u) (k + d) β
    (smoothShiftCapIso f g (pullback.fst g u)).hom (by simp) (by simp) (by
      rw [smoothShiftCapIso_hom_fst_assoc, pullback.diagonal_fst_assoc,
        smoothShift_diagonal_testMap_fst_eq_fst_assoc, hf])
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by ring) _ _ hB) ?_
  -- the flat-pullback law of `c'` along `Y ×_Z T ⟶ T`
  have sq := isPullback_smoothShiftForgetMap_snd f g u
  have : LocallyOfFiniteType (smoothShiftForgetMap f g u) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have : Flat (smoothShiftForgetMap f g u) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension (smoothShiftForgetMap f g u) d :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hfst : smoothShiftForgetMap f g u ≫ pullback.fst (f ≫ g) u =
      pullback.fst (f ≫ g) (pullback.fst g u ≫ g) := by simp
  have hmb : pullback.snd g u ≫ (u ≫ sZ) = (pullback.fst g u ≫ g) ≫ sZ := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have hflat := c'.flat_naturality_of_test_eq u (pullback.snd g u) d hr (pullback.fst g u ≫ g)
    pullback.condition.symm (smoothShiftForgetMap f g u) sq hfst k hmb hr'
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  -- `D ∘ pr₁^* = 1` at the test scheme `X ×_Z T ⟶ Y`
  have hv : smoothShiftForgetMap f g u ≫ ((pullback.fst (f ≫ g) u ≫ f) ≫ sY) =
      smoothShiftTestMap f g (pullback.fst g u) ≫ (pullback.fst g g ≫ sY) := by
    simp
  have hγ : pullback.fst (f ≫ g) u ≫ sX = (pullback.fst (f ≫ g) u ≫ f) ≫ sY := by
    rw [Category.assoc, hf]
  have hP := hD₁.cap_flatPullbackChow (pullback.fst (f ≫ g) u ≫ f)
    (smoothShiftTestMap f g (pullback.fst g u)) (smoothShiftForgetMap f g u)
    (isPullback_smoothShiftForgetMap f g u) hr' hv (smoothShiftForgetIso f g u)
    (smoothShiftForgetIso_fst f g u)
    (by rw [smoothShiftForgetIso_snd_assoc, smoothShiftForgetSection_forgetMap]) (k - (p - d))
    (chowGroupCongr C hγ _ (c'.cap u k α))
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _
    (chowPushforwardOfIso C _ _ (smoothShiftForgetIso f g u)
      (comp_fst_comp_structureMorphism_of_section rfl (pullback.diagonal_fst g) _ _ _
        (smoothShiftForgetIso_fst f g u)) (k - (p - d))
      (chowGroupCongr C hγ _ (c'.cap u k α))) ?_) ?_
  · refine HEq.trans (D.cap_heq_congr _ (by ring) _ _ ?_) (heq_of_eq hP |>.trans
      (chowGroupDegreeEquiv_heq C _ _ _))
    refine (chowGroupCongr_heq C _ _ _).trans (HEq.trans ?_ (hflat.trans ?_))
    · refine c'.cap_heq_congr _ rfl _ _ ?_
      refine (chowGroupCongr_heq C _ _ _).trans ?_
      exact flatPullbackChow_heq_congr_base C (by rw [Category.assoc, hg]) rfl rfl _ _ rfl _ _
        rfl _ _ _ _ HEq.rfl
    · exact flatPullbackChow_heq_congr_base C
        (smoothShiftTestMap_comp_structureMorphism C sX sY f g hf _) hγ rfl _ _ rfl _ _ rfl _ _ _ _
        (chowGroupCongr_heq C _ _ _).symm
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ HEq.rfl) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_of_eq_id _ ?_ _ _) (chowGroupCongr_heq C _ _ _)
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_fst, smoothShiftCapIso_hom_fst,
      smoothShiftForgetIso_snd_assoc, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, pullbackRightPullbackFstIso_hom_snd, smoothShiftCapIso_hom_snd_assoc,
      smoothShiftForgetIso_snd_assoc, Category.id_comp, smoothShiftForgetSection,
      pullback.lift_snd_assoc, pullback.lift_snd]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ] [LocallyOfFiniteType g] [Flat g] in
include hg in
/-- The base change `Y ×_Z T ⟶ T` of `g` is a morphism over the base, `Y ×_Z T` being read over
`Y ×_Z Y`. -/
theorem smoothShiftDiagonalTestMap_comp_structureMorphism {T : Scheme.{u}} (t : T ⟶ Y) :
    pullback.snd g (t ≫ g) ≫ (t ≫ sY) =
      smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY) := by
  simp only [pullbackMap_fst_assoc, Category.id_comp]
  rw [← hg, pullback.condition_assoc, Category.assoc]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [Flat g] in
include hf in
/-- The second projection `X ×_Y (Y ×_Z Y) ⟶ Y ×_Z Y` is a morphism over the base. -/
theorem smoothShift_restriction_structureMorphism :
    pullback.fst f (pullback.fst g g) ≫ sX =
      pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY) :=
  (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g g)).symm

omit [Flat g] in
/-- The restriction `res(c) ∈ A^p(X ×_Z Y ⟶ Y ×_Z Y)` of `c ∈ A^p(X ⟶ Y)` along the first
projection `Y ×_Z Y ⟶ Y` (Stacks 0F9Z), presented as a class over `Y ×_Z Y`. -/
def smoothShiftRestriction (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
      (pullback.snd f (pullback.fst g g)) rfl p :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f (pullback.fst g g))
    (smoothShift_restriction_structureMorphism C sX sY f g hf) rfl p
    (hv := pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g g)) (hv' := rfl)
    (bivariantRestriction C (gysinSystemOfInvertible C) sX sY f hf (pullback.fst g g) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)

omit [Flat g] in
/-- The cap operation of `c` at `m' ≫ pr₁` is that of `res(c)` at a test scheme
`m' : T' ⟶ Y ×_Z Y`, carried along any isomorphism over the two projections. -/
theorem smoothShiftRestriction_cap (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    {T' : Scheme.{u}} (m' : T' ⟶ pullback g g) [LocallyOfFiniteType m'] (m : T' ⟶ Y)
    [LocallyOfFiniteType m] (hm : m' ≫ pullback.fst g g = m) (k : ℤ)
    (x : chowGroup C (m' ≫ (pullback.fst g g ≫ sY)) k) (y : chowGroup C (m ≫ sY) k) (hxy : x ≍ y)
    (Ψ : pullback (pullback.snd f (pullback.fst g g)) m' ⟶ pullback f m) [IsIso Ψ]
    (hΨ₁ : Ψ ≫ pullback.fst f m = pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g))
    (hΨ₂ : Ψ ≫ pullback.snd f m = pullback.snd _ _)
    (hΨ : Ψ ≫ (pullback.fst f m ≫ sX) = pullback.fst (pullback.snd f (pullback.fst g g)) m' ≫
      (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY))) :
    c.cap m k y ≍
      chowPushforwardOfIso C _ (pullback.fst f m ≫ sX) Ψ hΨ (k - p)
        ((smoothShiftRestriction C sX sY f g hf p c).cap m' k x) := by
  have hmY : m' ≫ (pullback.fst g g ≫ sY) = m ≫ sY := by rw [← Category.assoc, hm]
  have hs := smoothShift_restriction_structureMorphism C sX sY f g hf
  have hW₁ : (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫
      pullback.congrHom rfl hm).hom ≫ pullback.fst f m =
        pullback.fst (pullback.snd f (pullback.fst g g)) m' ≫
          pullback.fst f (pullback.fst g g) := by
    simp [pullback.congrHom_hom]
  have hW₂ : (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫
      pullback.congrHom rfl hm).hom ≫ pullback.snd f m =
        pullback.snd (pullback.snd f (pullback.fst g g)) m' := by
    simp [pullback.congrHom_hom]
  have hW₃ : (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫
      pullback.congrHom rfl hm).inv ≫ (pullback.fst (pullback.snd f (pullback.fst g g)) m' ≫
        (pullback.fst f (pullback.fst g g) ≫ sX)) = pullback.fst f m ≫ sX := by
    simp [pullback.congrHom_inv]
  have hW₄ : (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫
      pullback.congrHom rfl hm).hom ≫ (pullback.fst f m ≫ sX) =
        pullback.fst (pullback.snd f (pullback.fst g g)) m' ≫
          (pullback.fst f (pullback.fst g g) ≫ sX) := by
    rw [reassoc_of% hW₁]
  have H := bivariantRestrictionCap_eq C (gysinSystemOfInvertible C) sX sY f hf
    (pullback.fst g g) p c m' m hm hmY
    (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫ pullback.congrHom rfl hm) hW₁ hW₂ k
    hW₃ (properPushforwardDescends C _ _ _ _ _) x
  rw [properChowPushforward_eq_chowPushforwardOfIso] at H
  have hΨW : Ψ = (pullbackLeftPullbackSndIso f (pullback.fst g g) m' ≪≫
      pullback.congrHom rfl hm).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hΨ₁, hW₁]
    · rw [hΨ₂, hW₂]
  subst hΨW
  refine HEq.symm (HEq.trans (chowPushforwardOfIso_heq (C := C) _ _ hW₄ (by rw [hs]) rfl rfl
    (bivariantClassCongrBase_cap C _ _ hs rfl p _ m' k x x HEq.rfl
      (hv := pullbackSnd_comp_structureMorphism_eq C sX sY f hf (pullback.fst g g))
      (hv' := rfl))) ?_)
  rw [bivariantRestriction_cap, H]
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl rfl _ _ HEq.rfl) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_of_eq_id _ (Iso.inv_hom_id _) _ _) ?_
  exact c.cap_heq_congr _ rfl _ _ ((chowGroupCongr_heq C _ _ _).trans hxy)

/-- **The restricted class at the test scheme of the forward map.** The cap operation of `c ∘ g^*`
at `t ≫ g`, read over `Y ×_Z Y`, is `res(c)` capped at `Y ×_Z T ⟶ Y ×_Z Y` with the flat pullback
of `α`, carried along any isomorphism over the two projections. -/
theorem smoothShiftForward_cap_eq_restriction
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k)
    (Φ : pullback (pullback.snd f (pullback.fst g g)) (smoothShiftDiagonalTestMap g t) ⟶
      pullback (f ≫ g) (t ≫ g)) [IsIso Φ]
    (hΦ₁ : Φ ≫ pullback.fst (f ≫ g) (t ≫ g) =
      pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g))
    (hΦ₂ : Φ ≫ pullback.snd (f ≫ g) (t ≫ g) = pullback.snd _ _ ≫ pullback.snd g (t ≫ g))
    (hΦ : Φ ≫ (smoothShiftTestMap f g t ≫ (pullback.fst g g ≫ sY)) =
      pullback.fst (pullback.snd f (pullback.fst g g)) (smoothShiftDiagonalTestMap g t) ≫
        (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY))) :
    chowGroupCongr C (smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t) (k - (p - d))
        ((smoothShiftForward C sX sY sZ f g hf hg d hgd p c).cap (t ≫ g) k
          (chowGroupCongr C (by rw [Category.assoc, hg]) k α)) ≍
      chowPushforwardOfIso C _ _ Φ hΦ (k + d - p)
        ((smoothShiftRestriction C sX sY f g hf p c).cap (smoothShiftDiagonalTestMap g t) (k + d)
          (flatPullbackChow C (smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY))
            (t ≫ sY) (pullback.snd g (t ≫ g))
            (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t) d
            (relativeDimension_pullback_snd g (t ≫ g) d hgd) k
            (flatPullbackDescends C _ _ _ _ _ _ _) α)) := by
  refine (chowGroupCongr_heq C _ _ _).trans
    ((smoothShiftForward_cap C sX sY sZ f g hf hg d hgd p c (t ≫ g) k _).trans ?_)
  have hm₀ : smoothShiftDiagonalTestMap g t ≫ pullback.fst g g = pullback.fst g (t ≫ g) := by
    simp
  have hsnd : Φ ≫ (pullbackRightPullbackFstIso g (t ≫ g) f).inv ≫
      pullback.snd f (pullback.fst g (t ≫ g)) = pullback.snd _ _ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst, reassoc_of% hΦ₁]
      rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hm₀]
    · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd, hΦ₂]
  have hR := smoothShiftRestriction_cap C sX sY f g hf p c
    (smoothShiftDiagonalTestMap g t) (pullback.fst g (t ≫ g)) hm₀ (k + d)
    (flatPullbackChow C (smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY))
      (t ≫ sY) (pullback.snd g (t ≫ g))
      (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t) d
      (relativeDimension_pullback_snd g (t ≫ g) d hgd) k
      (flatPullbackDescends C _ _ _ _ _ _ _) α)
    (flatPullbackChow C (pullback.fst g (t ≫ g) ≫ sY) ((t ≫ g) ≫ sZ) (pullback.snd g (t ≫ g))
      (pullbackSnd_comp_structureMorphism_eq C sY sZ g hg (t ≫ g)) d
      (relativeDimension_pullback_snd g (t ≫ g) d hgd) k (flatPullbackDescends C _ _ _ _ _ _ _)
      (chowGroupCongr C (by rw [Category.assoc, hg]) k α))
    (flatPullbackChow_heq_congr_base C (by rw [← Category.assoc, hm₀])
      (by rw [Category.assoc, hg]) rfl _ _ rfl _ _ rfl _ _ _ _ (chowGroupCongr_heq C _ _ _).symm)
    (Φ ≫ (pullbackRightPullbackFstIso g (t ≫ g) f).inv)
    (by simp [hΦ₁]) hsnd (by
      rw [Category.assoc, pullbackRightPullbackFstIso_inv_fst_assoc, ← hΦ,
        smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t])
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ rfl _ _ hR) ?_
  exact chowPushforwardOfIso_heq_comp_of_comp_eq _ _ Φ (by simp) _ _ rfl
    (smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t) rfl _ _ HEq.rfl

omit [LocallyOfFiniteType sZ] in
/-- **`D ∘ pr₂^* = 1` read through the restriction of `c`.** Capping `D` at `Y ×_Z T ⟶ Y ×_Z Y`
with the flat pullback of `α` and then `res(c)` gives `c ∩ α`, carried along any isomorphism over
the two projections. -/
theorem smoothShiftRestriction_cap_diagonal
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd g g)
      (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
      (relativeDimension_pullback_snd g g d hgd))
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k)
    (Θ : pullback f t ⟶ pullback (pullback.snd f (pullback.fst g g))
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g))
    [IsIso Θ]
    (hΘ₁ : Θ ≫ pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g) = pullback.fst f t)
    (hΘ₂ : Θ ≫ pullback.snd _ _ = pullback.snd f t ≫ smoothShiftDiagonalSection g t)
    (hΘ : Θ ≫ (pullback.fst (pullback.snd f (pullback.fst g g))
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g) ≫
        (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY))) = pullback.fst f t ≫ sX) :
    (smoothShiftRestriction C sX sY f g hf p c).cap
        (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g)
        (k + d - d)
        (chowGroupCongr C (Category.assoc _ _ _).symm (k + d - d)
          (D.cap (smoothShiftDiagonalTestMap g t) (k + d)
            (flatPullbackChow C (smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY))
              (t ≫ sY) (pullback.snd g (t ≫ g))
              (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t) d
              (relativeDimension_pullback_snd g (t ≫ g) d hgd) k
              (flatPullbackDescends C _ _ _ _ _ _ _) α))) ≍
      chowPushforwardOfIso C (pullback.fst f t ≫ sX) _ Θ hΘ (k - p) (c.cap t k α) := by
  have hP2 := hD₂.cap_flatPullbackChow t (smoothShiftDiagonalTestMap g t) (pullback.snd g (t ≫ g))
    (isPullback_smoothShiftDiagonalTestMap g t) (relativeDimension_pullback_snd g (t ≫ g) d hgd)
    (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t)
    (smoothShiftDiagonalSection g t) (smoothShiftDiagonalSection_fst g t)
    (smoothShiftDiagonalSection_snd_snd g t) k α
  have hm8 : smoothShiftDiagonalSection g t ≫
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫
        pullback.diagonal g) = t ≫ pullback.diagonal g := by
    rw [smoothShiftDiagonalSection_fst_assoc]
  have hux8 : smoothShiftDiagonalSection g t ≫
      ((pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫
        pullback.diagonal g) ≫ (pullback.fst g g ≫ sY)) = t ≫ sY := by
    rw [← Category.assoc, hm8]
    simp
  have h8 : t ≫ sY = (t ≫ pullback.diagonal g) ≫ (pullback.fst g g ≫ sY) := by simp
  have hy8 : chowGroupCongr C (Category.assoc _ _ _).symm (k + d - d)
      (D.cap (smoothShiftDiagonalTestMap g t) (k + d)
        (flatPullbackChow C (smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY))
          (t ≫ sY) (pullback.snd g (t ≫ g))
          (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t) d
          (relativeDimension_pullback_snd g (t ≫ g) d hgd) k
          (flatPullbackDescends C _ _ _ _ _ _ _) α)) ≍
      chowPushforwardOfIso C (t ≫ sY) _ (smoothShiftDiagonalSection g t) hux8 k α := by
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    rw [hP2]
    exact (chowGroupDegreeEquiv_heq C _ _ _).trans
      (chowPushforwardOfIso_heq _ _ _ rfl (Category.assoc _ _ _).symm rfl HEq.rfl)
  have H8 := (smoothShiftRestriction C sX sY f g hf p c).cap_heq_chowPushforwardOfIso
    (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g)
    (smoothShiftDiagonalSection g t) (t ≫ pullback.diagonal g) hm8
    (add_sub_cancel_right k (d : ℤ)).symm α _ hux8 hy8
    (chowGroupCongr C h8 k α) (chowGroupCongr_heq C _ _ _)
  refine H8.trans ?_
  -- the restriction of `c`, capped at `t ≫ Δ`, is `c` capped at `t`
  set TB := testBaseChangeIso (pullback.snd f (pullback.fst g g))
    (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g)
    (smoothShiftDiagonalSection g t) (t ≫ pullback.diagonal g) hm8 with hTB
  have hinv₁ : inv Θ ≫ pullback.fst f t =
      pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g) := by
    rw [IsIso.inv_comp_eq, hΘ₁]
  have hinv₂ : inv Θ ≫ pullback.snd f t =
      pullback.snd _ _ ≫ pullback.snd _ _ ≫ pullback.snd g (t ≫ g) := by
    rw [IsIso.inv_comp_eq, reassoc_of% hΘ₂, smoothShiftDiagonalSection_snd_snd, Category.comp_id]
  have hm9 : (t ≫ pullback.diagonal g) ≫ pullback.fst g g = t := by simp
  have hR := smoothShiftRestriction_cap C sX sY f g hf p c (t ≫ pullback.diagonal g) t hm9 k
    (chowGroupCongr C h8 k α) α (chowGroupCongr_heq C _ _ _) (TB.hom ≫ inv Θ)
    (by rw [Category.assoc, hinv₁, hTB, testBaseChangeIso_hom_fst_assoc])
    (by rw [Category.assoc, hinv₂, hTB, testBaseChangeIso_hom_snd_assoc,
      smoothShiftDiagonalSection_snd_snd, Category.comp_id])
    (by rw [Category.assoc, ← Category.assoc (inv Θ), hinv₁, hTB, Category.assoc,
      testBaseChangeIso_hom_fst_assoc, smoothShift_restriction_structureMorphism C sX sY f g hf])
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ rfl _ _
    (heq_chowPushforwardOfIso_inv _ _ rfl rfl _ _ hR)) ?_
  exact chowPushforwardOfIso_heq_comp_of_comp_eq _ _ Θ (by simp) _ _ rfl rfl rfl _ _ HEq.rfl

/-- **The first computation of Stacks 0FBT**: `res(D) ∘ res(c ∘ g^*) = c`, from the commutation
of `D` with every bivariant class over `Y ×_Z Y` and `D ∘ pr₂^* = 1`. -/
theorem smoothShiftBackward_smoothShiftForward
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback g g) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ (pullback.fst g g ≫ sY))
        (pullback.fst g g ≫ sY) f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C) (pullback.fst g g ≫ sY) (pullback.diagonal g)
        f₂ d p₂ D c₂)
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd g g)
      (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
      (relativeDimension_pullback_snd g g d hgd))
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    smoothShiftBackward C sX sY sZ f g hf hg d p D
        (smoothShiftForward C sX sY sZ f g hf hg d hgd p c) = c := by
  refine BivariantClass.ext C _ sX sY f hf p ?_
  intro T t _ k α
  refine eq_of_heq ?_
  have H1 := smoothShiftBackward_cap C sX sY sZ f g hf hg d p D
    (smoothShiftForward C sX sY sZ f g hf hg d hgd p c) t k α (smoothShiftCapIso f g t).hom
    (by simp) (by simp) (by
      rw [smoothShiftCapIso_hom_fst_assoc, pullback.diagonal_fst_assoc,
        smoothShift_diagonal_testMap_fst_eq_fst_assoc, hf])
  refine H1.trans ?_
  -- the forward class at `t ≫ g`, read through the restriction of `c`
  have hm₀ : smoothShiftDiagonalTestMap g t ≫ pullback.fst g g = pullback.fst g (t ≫ g) := by
    simp
  set Φ := pullbackLeftPullbackSndIso f (pullback.fst g g) (smoothShiftDiagonalTestMap g t) ≪≫
    pullback.congrHom rfl hm₀ ≪≫ pullbackRightPullbackFstIso g (t ≫ g) f with hΦ
  have hΦ₁ : Φ.hom ≫ pullback.fst (f ≫ g) (t ≫ g) =
      pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g) := by
    simp [hΦ, pullback.congrHom_hom]
  have hΦ₂ : Φ.hom ≫ pullback.snd (f ≫ g) (t ≫ g) =
      pullback.snd _ _ ≫ pullback.snd g (t ≫ g) := by
    simp [hΦ, pullback.congrHom_hom]
  have hΦs : Φ.hom ≫ (smoothShiftTestMap f g t ≫ (pullback.fst g g ≫ sY)) =
      pullback.fst (pullback.snd f (pullback.fst g g)) (smoothShiftDiagonalTestMap g t) ≫
        (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY)) := by
    rw [← smoothShiftTestMap_comp_structureMorphism C sX sY f g hf t, reassoc_of% hΦ₁,
      smoothShift_restriction_structureMorphism C sX sY f g hf]
  have hy := smoothShiftForward_cap_eq_restriction C sX sY sZ f g hf hg d hgd p c t k α Φ.hom
    hΦ₁ hΦ₂ hΦs
  have hm4 : Φ.hom ≫ smoothShiftTestMap f g t =
      pullback.fst (pullback.snd f (pullback.fst g g)) (smoothShiftDiagonalTestMap g t) ≫
        pullback.snd f (pullback.fst g g) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackMap_fst, reassoc_of% hΦ₁, pullback.condition, Category.assoc]
    · rw [Category.assoc, pullbackMap_snd, reassoc_of% hΦ₂, Category.assoc,
        pullback.condition_assoc, pullbackMap_snd]
  set β := flatPullbackChow C (smoothShiftDiagonalTestMap g t ≫ (pullback.fst g g ≫ sY))
    (t ≫ sY) (pullback.snd g (t ≫ g))
    (smoothShiftDiagonalTestMap_comp_structureMorphism C sY sZ g hg t) d
    (relativeDimension_pullback_snd g (t ≫ g) d hgd) k
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  have H4 := D.cap_heq_chowPushforwardOfIso (smoothShiftTestMap f g t) Φ.hom
    (pullback.fst (pullback.snd f (pullback.fst g g)) (smoothShiftDiagonalTestMap g t) ≫
      pullback.snd f (pullback.fst g g)) hm4 (by ring) _ _ _ hy
    (chowGroupCongr C (Category.assoc _ _ _).symm (k + d - p)
      ((smoothShiftRestriction C sX sY f g hf p c).cap (smoothShiftDiagonalTestMap g t) (k + d) β))
    (chowGroupCongr_heq C _ _ _)
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by ring) _ _ H4) ?_
  -- the commutation of `D` with the restriction of `c`
  have hP1 := hcomm (pullback.snd f (pullback.fst g g)) p
    (smoothShiftRestriction C sX sY f g hf p c) (smoothShiftDiagonalTestMap g t) (k + d) β
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply] at hP1
  have h6 := heq_chowPushforwardOfIso_inv _ _ rfl rfl _ _ (heq_of_eq hP1.symm)
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by ring) _ _ h6) ?_
  refine HEq.trans (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)) ?_
  -- `D ∘ pr₂^* = 1`, read through the restriction of `c`
  have hm8 : smoothShiftDiagonalSection g t ≫
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫
        pullback.diagonal g) = t ≫ pullback.diagonal g := by
    rw [smoothShiftDiagonalSection_fst_assoc]
  have hm9 : (t ≫ pullback.diagonal g) ≫ pullback.fst g g = t := by simp
  set Θ := (pullback.congrHom (rfl : f = f) hm9).symm ≪≫
    (pullbackLeftPullbackSndIso f (pullback.fst g g) (t ≫ pullback.diagonal g)).symm ≪≫
    testBaseChangeIso (pullback.snd f (pullback.fst g g))
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g)
      (smoothShiftDiagonalSection g t) (t ≫ pullback.diagonal g) hm8 with hΘ
  have hΘ₁ : Θ.hom ≫ pullback.fst _ _ ≫ pullback.fst f (pullback.fst g g) = pullback.fst f t := by
    simp [hΘ, pullback.congrHom_inv]
  have hΘ₂ : Θ.hom ≫ pullback.snd _ _ = pullback.snd f t ≫ smoothShiftDiagonalSection g t := by
    simp [hΘ, pullback.congrHom_inv]
  have hΘs : Θ.hom ≫ (pullback.fst (pullback.snd f (pullback.fst g g))
      (pullback.fst (pullback.diagonal g) (smoothShiftDiagonalTestMap g t) ≫ pullback.diagonal g) ≫
        (pullback.snd f (pullback.fst g g) ≫ (pullback.fst g g ≫ sY))) =
      pullback.fst f t ≫ sX := by
    rw [← smoothShift_restriction_structureMorphism C sX sY f g hf, reassoc_of% hΘ₁]
  have hL := smoothShiftRestriction_cap_diagonal C sX sY sZ f g hf hg d hgd p D hD₂ c t k α
    Θ.hom hΘ₁ hΘ₂ hΘs
  refine HEq.trans
    (chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by ring) _ _ hL) ?_
  refine chowPushforwardOfIso_heq_of_eq_id _ ?_ _ _
  refine pullback.hom_ext ?_ ?_ <;> simp [hΘ, hΦ, pullback.congrHom_inv, pullback.congrHom_hom]

/-- **The core of Stacks 0FBT.** Let `g : Y ⟶ Z` be flat of relative dimension `d` and let
`D ∈ A^d(Y ⟶ Y ×_Z Y)` be a class for the diagonal which commutes with every bivariant class over
`Y ×_Z Y` and satisfies `D ∘ pr₁^* = 1` and `D ∘ pr₂^* = 1`. Then `c ↦ c ∘ g^*` is an isomorphism
`A^p(X ⟶ Y) ≃ A^{p-d}(X ⟶ Z)`, with inverse `c' ↦ res(D) ∘ res(c')`.

For `g` smooth of relative dimension `d` the Gysin class `Δ^!` of the diagonal has these three
properties, by Stacks 0FBP (with Stacks 0FF6) and Stacks 0FBS, and Stacks 0FBT is this equivalence
for `D = Δ^!`. -/
def smoothShiftEquiv
    (hcomm : ∀ {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback g g) [LocallyOfFiniteType f₂] (p₂ : ℤ)
      (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ (pullback.fst g g ≫ sY))
        (pullback.fst g g ≫ sY) f₂ rfl p₂),
      BivariantCommute C (gysinSystemOfInvertible C) (pullback.fst g g ≫ sY) (pullback.diagonal g)
        f₂ d p₂ D c₂)
    (hD₁ : D.CompFlatPullbackEqOne (pullback.fst g g) rfl (pullback.diagonal_fst g)
      (relativeDimension_pullback_fst_self g hgd))
    (hD₂ : D.CompFlatPullbackEqOne (pullback.snd g g)
      (smoothShift_pullback_snd_comp_structureMorphism C sY sZ g hg) (pullback.diagonal_snd g)
      (relativeDimension_pullback_snd g g d hgd)) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p ≃+
      BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p - d) where
  toFun := smoothShiftForward C sX sY sZ f g hf hg d hgd p
  invFun := smoothShiftBackward C sX sY sZ f g hf hg d p D
  left_inv := smoothShiftBackward_smoothShiftForward C sX sY sZ f g hf hg d hgd p D hcomm hD₂
  right_inv := smoothShiftForward_smoothShiftBackward C sX sY sZ f g hf hg d hgd p D hD₁
  map_add' := map_add _

/-- The equivalence `Stacks.Chow.smoothShiftEquiv` is `Stacks.Chow.smoothShiftForward`. -/
@[simp]
theorem smoothShiftEquiv_apply (hcomm) (hD₁) (hD₂)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    smoothShiftEquiv C sX sY sZ f g hf hg d hgd p D hcomm hD₁ hD₂ c =
      smoothShiftForward C sX sY sZ f g hf hg d hgd p c :=
  rfl

/-- The inverse of `Stacks.Chow.smoothShiftEquiv` is `Stacks.Chow.smoothShiftBackward`. -/
@[simp]
theorem smoothShiftEquiv_symm_apply (hcomm) (hD₁) (hD₂)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) (p - d)) :
    (smoothShiftEquiv C sX sY sZ f g hf hg d hgd p D hcomm hD₁ hD₂).symm c' =
      smoothShiftBackward C sX sY sZ f g hf hg d p D c' :=
  rfl

end Maps

end Stacks.Chow

end
