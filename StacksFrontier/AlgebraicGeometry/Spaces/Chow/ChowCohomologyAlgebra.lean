module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection

/-!
# The Chow cohomology algebra of a good algebraic space

In the situation of Stacks 0EDT let `X/B` be good. **Stacks 0ERK** defines the *Chow
cohomology* of `X` to be the graded `ℤ`-algebra

  `A^*(X) = ⊕_p A^p(X)`,  where  `A^p(X) = A^p(X ⟶ X)`,

whose degree `p` part is the group of bivariant classes of degree `p` (Stacks 0ERJ) for the
identity of `X`, the product being composition of bivariant classes.

## Main definitions

* `AlgebraicGeometry.Space.ChowCohomologyClass` — **Stacks 0ERK**, the group
  `A^p(X) = A^p(X ⟶ X)` of bivariant classes of degree `p` for `id_X`, over the constructed Chow
  groups `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 and the constructed proper
  pushforward (Stacks 0EP1), flat pullback (Stacks 0EP8, descended by Stacks 0EQB) and Gysin
  maps (Stacks 0ER1, descended by Stacks 0ERA).
* `AlgebraicGeometry.Space.ChowCohomologyClass.comp` — the composition
  `A^p(X) × A^q(X) ⟶ A^{p+q}(X)`, `(c ∘ d) ∩ α = c ∩ (d ∩ α)`.
* `AlgebraicGeometry.Space.ChowCohomologyClass.one` — the class `1 ∈ A^0(X)`, capping as the
  identity.
* `AlgebraicGeometry.Space.ChowCohomologyClass.instGRing` — **Stacks 0ERK**, the graded ring
  structure on `p ↦ A^p(X)`.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra` — **Stacks 0ERK**, the graded `ℤ`-algebra
  `A^*(X) = ⊕_p A^p(X)`; its ring structure is `DirectSum.ring` and its `ℤ`-algebra structure the
  one of any ring.

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyClass.ext` — a class is determined by its cap
  operations.
* `AlgebraicGeometry.Space.ChowCohomologyClass.comp_assoc`,
  `AlgebraicGeometry.Space.ChowCohomologyClass.one_comp`,
  `AlgebraicGeometry.Space.ChowCohomologyClass.comp_one` — associativity and the unit laws.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.of_mul_of` — the product of homogeneous
  elements of `A^*(X)` is their composite.

## Implementation notes

### Nothing is parameterized

The Chow groups are `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6, the quotient of
`Z_k(Y')` by the cycles rationally equivalent to zero, with the presenting families indexed in
the universe `u + 1` in which the descended operations below are stated. The flat pullback on
Chow groups is `AlgebraicGeometry.Space.flatPullbackChowMapCanonical` (Stacks 0EQB), the Gysin
map of a triple `(ℒ', s', i' : D' → Y')` as in Definition 0ER1 is
`AlgebraicGeometry.Space.sectionGysinChowGroupMap` (Stacks 0ERA), and proper pushforward of
cycles is `AlgebraicGeometry.Space.properCyclePushforward` (Stacks 0EP1). Nothing is a parameter
or a field of a structure that postulates them.

### The fibre product `Y' ×_X X` is `Y'`

For `f = id_X` the fibre product `X' = Y' ×_X X` of Stacks 0ERJ is `Y'` itself, with
`X' → Y'` the identity; this file takes that fibre product. Accordingly the cap operation of a
class `c ∈ A^p(X)` on a good test space `g : Y' ⟶ X` is a map `CH_k(Y') ⟶ CH_{k-p}(Y')`, the
morphism `X'' → X'` of axioms (1) and (2) is the given `Y'' → Y'`, and the pullback
`(𝒩', t', j' : E' → X')` of a triple `(ℒ', s', i' : D' → Y')` in axiom (3) is that triple
itself. The test space `D'` of axiom (3) lies over `X` through `D' → Y' → X`.

### The degrees

The cap operation is indexed by a pair of degrees `(k, l)` with `l + p = k`, mapping
`CH_k(Y') ⟶ CH_l(Y')`; for each `k` there is exactly one such `l`, namely `k - p`, and the
equation is a proposition, so this is the source's single map `CH_k(Y') ⟶ CH_{k-p}(Y')`. It is
written this way because composition adds degrees: with the target degree a free variable the
composite `c ∘ d` caps by `d` into degree `l + p` and then by `c` into degree `l`, and its
naturality and the ring axioms need no transport of Chow groups along equations of integers.
In the same way the flat axiom (2) quantifies over the shifted degrees `k + r = k'`,
`l + r = l'`, which is the same as asking it at `k' = k + r` and `l' = l + r`.

### Axiom (1) through cycle representatives

The descent of proper pushforward to Chow groups (Stacks 0EQC) is not used, so axiom (1) is
stated through cycle representatives: for every cycle `α''` on `Y''` there is a cycle `β''` on
`Y''` with `c ∩ [α''] = [β'']` and `c ∩ [h_*α''] = [h_*β'']`. Given the descent of `h_*` this is
the source's `c ∩ h_*α'' = h_*(c ∩ α'')`: one direction picks a representative `β''` of
`c ∩ [α'']`, the other rewrites `[h_*β''] = h_*[β'']`. The existential form is the faithful one;
the universally quantified "for every representative `β''`" would make each class carry a proof
that `h_*` respects rational equivalence.

### Composition

For `c ∈ A^p(X)` and `d ∈ A^q(X)` the composite caps as `(c ∘ d) ∩ α = c ∩ (d ∩ α)`: since every
fibre product over `id_X` is the test space itself, this is literally the composition
`A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)` stated after Stacks 0ERJ. Each of its three axioms
is the corresponding axiom of `d` followed by that of `c`. The product of `A^*(X)` is this
composition, and the unit is the class capping as the identity.

## References

* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### Transport of Chow groups along an equality of degrees -/

/-- The Chow group `CH_k(Y)` transported along an equality of degrees `k = l`. -/
def chowGroupCanonicalDegreeCongr {Y : D.Ambient} (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {k l : ℤ} (h : k = l) :
    chowGroupCanonical.{u + 1} D sY hY k ≃+ chowGroupCanonical.{u + 1} D sY hY l := by
  subst h
  exact AddEquiv.refl _

/-- Transport along `rfl : k = k` is the identity. -/
@[simp]
theorem chowGroupCanonicalDegreeCongr_refl {Y : D.Ambient} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (k : ℤ) (x : chowGroupCanonical.{u + 1} D sY hY k) :
    chowGroupCanonicalDegreeCongr D sY hY (rfl : k = k) x = x :=
  rfl

/-- The vanishing locus `D' ⊆ Y'` of a section on a good test space `g : Y' ⟶ X` is good over
the base through `D' → Y' → X → B`. -/
theorem isGood_vanishingLocus_comp {X Y' : D.Ambient} (sX : X ⟶ D.space) (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1)
    (σ : L.sections) :
    D.IsGood (((vanishingLocus D (g ≫ sX) hY' L σ).1.ι ≫ g) ≫ sX) := by
  rw [Category.assoc]
  exact isGood_vanishingLocus D (g ≫ sX) hY' L σ

/-! ### Chow cohomology classes -/

variable {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- The group `A^p(X) = A^p(X ⟶ X)` of bivariant classes of degree `p` (Stacks 0ERJ) for the
identity of a good algebraic space `X/B`: a rule assigning to every good test space `g : Y' ⟶ X`
over the base and every `k` an additive map `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(Y')` (the fibre product
`Y' ×_X X` being `Y'`), such that

1. for `h : Y'' ⟶ Y'` proper, `c ∩ h_*α'' = h_*(c ∩ α'')` for all `α''` on `Y''`;
2. for `h : Y'' ⟶ Y'` flat of relative dimension `r`, `c ∩ h^*α' = h^*(c ∩ α')` for all `α'`;
3. for `(ℒ', s', i' : D' → Y')` as in Definition 0ER1, `c ∩ (i')^*α' = (i')^*(c ∩ α')` for all
   `α'` on `Y'`.

The Chow groups are the constructed `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6;
`h^*` is the flat pullback of Stacks 0EQB, `(i')^*` the Gysin map of Stacks 0ERA, and `h_*` the
proper pushforward of cycles of Stacks 0EP1, axiom (1) being read through cycle representatives.
The cap operation in degree `k` is indexed by its target degree `l`, with `l + p = k`. See the
implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra`. -/
@[stacks 0ERK "the degree p component A^p(X) = A^p(X → X): bivariant classes of degree p for \
id_X over the constructed Chow groups of Stacks 0EQ6, with the fibre product Y' ×_X X taken to be \
Y'; flat pullback and Gysin maps are the descended ones of Stacks 0EQB and 0ERA, the proper axiom \
is stated through cycle representatives"]
structure ChowCohomologyClass (hX : D.IsGood sX) (p : ℤ) where
  /-- The cap operation `c ∩ - : CH_k(Y') ⟶ CH_l(Y')`, `l = k - p`, on every good test space
  `g : Y' ⟶ X`. -/
  cap : ∀ {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k l : ℤ), l + p = k →
    chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k →+ chowGroupCanonical.{u + 1} D (g ≫ sX) hY' l
  /-- Stacks 0ERJ (1): cap product commutes with proper pushforward. -/
  proper_naturality : ∀ {Y' Y'' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (h : Y'' ⟶ Y') (hY'' : D.IsGood ((h ≫ g) ≫ sX)) (hh : IsProper D.site D.base D.base_mem h)
    (k l : ℤ) (hkl : l + p = k) (α : CycleGroup D ((h ≫ g) ≫ sX) k),
    ∃ β : CycleGroup D ((h ≫ g) ≫ sX) l,
      cap (h ≫ g) hY'' k l hkl (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' k α) =
          chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' l β ∧
        cap g hY' k l hkl (chowClassCanonical.{u + 1} D (g ≫ sX) hY' k
            (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY'
              (Category.assoc h g sX).symm hh.2.1.2 k α)) =
          chowClassCanonical.{u + 1} D (g ≫ sX) hY' l
            (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY'
              (Category.assoc h g sX).symm hh.2.1.2 l β)
  /-- Stacks 0ERJ (2): cap product commutes with flat pullback of relative dimension `r`. -/
  flat_naturality : ∀ {Y' Y'' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (h : Y'' ⟶ Y') (hY'' : D.IsGood ((h ≫ g) ≫ sX)) (r : ℕ)
    (hh : IsFlat D.site D.base D.base_mem h)
    (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (k l : ℤ) (hkl : l + p = k) (k' l' : ℤ) (hk : k + (r : ℤ) = k') (hl : l + (r : ℤ) = l')
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k),
    cap (h ≫ g) hY'' k' l' (by omega)
        (flatPullbackChowMapCanonical D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY' h
          (Category.assoc h g sX).symm r hh hr k k' hk x) =
      flatPullbackChowMapCanonical D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY' h
        (Category.assoc h g sX).symm r hh hr l l' hl (cap g hY' k l hkl x)
  /-- Stacks 0ERJ (3): cap product commutes with the Gysin map of every triple
  `(ℒ', s', i' : D' → Y')` as in Definition 0ER1. -/
  gysin_naturality : ∀ {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D (g ≫ sX) hY' L) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' (k + 1)),
    cap ((vanishingLocus D (g ≫ sX) hY' L σ).1.ι ≫ g) (isGood_vanishingLocus_comp D sX g hY' L σ)
        k l hkl (sectionGysinChowGroupMap D (g ≫ sX) hY' L σ hL k x) =
      sectionGysinChowGroupMap D (g ≫ sX) hY' L σ hL l (cap g hY' (k + 1) (l + 1) (by omega) x)

namespace ChowCohomologyClass

variable {D sX hX}

/-- A Chow cohomology class is determined by its cap operations. -/
@[ext]
theorem ext {p : ℤ} {c d : ChowCohomologyClass D sX hX p}
    (h : ∀ {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k)
      (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k),
      c.cap g hY' k l hkl x = d.cap g hY' k l hkl x) : c = d := by
  cases c with
  | mk ccap _ _ _ =>
    cases d with
    | mk dcap _ _ _ =>
      have hcap : @ccap = @dcap := by
        funext Y' g hY' k l hkl
        exact AddMonoidHom.ext (h g hY' k l hkl)
      subst hcap
      rfl

/-- Two classes of equal degrees with the same cap operations are the same element of the
graded object `p ↦ A^p(X)`. -/
theorem gradedMonoid_mk_eq {p p' : ℤ} (hp : p = p') {c : ChowCohomologyClass D sX hX p}
    {d : ChowCohomologyClass D sX hX p'}
    (h : ∀ {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k)
      (hkl' : l + p' = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k),
      c.cap g hY' k l hkl x = d.cap g hY' k l hkl' x) :
    (⟨p, c⟩ : GradedMonoid (ChowCohomologyClass D sX hX)) = ⟨p', d⟩ := by
  subst hp
  exact congrArg (GradedMonoid.mk p) (ext fun g hY' k l hkl x => h g hY' k l hkl hkl x)

/-- The cap operation does not depend on how its target degree is written. -/
theorem cap_degreeCongr_target {p : ℤ} (c : ChowCohomologyClass D sX hX p) {Y' : D.Ambient}
    (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) {k m m' : ℤ} (hm : m = m') (h : m + p = k)
    (h' : m' + p = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    chowGroupCanonicalDegreeCongr D (g ≫ sX) hY' hm (c.cap g hY' k m h x) =
      c.cap g hY' k m' h' x := by
  subst hm
  rfl

/-- The cap operation does not depend on how its source degree is written. -/
theorem cap_degreeCongr_source {p : ℤ} (c : ChowCohomologyClass D sX hX p) {Y' : D.Ambient}
    (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) {k k' l : ℤ} (hk : k = k') (h : l + p = k)
    (h' : l + p = k') (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    c.cap g hY' k' l h' (chowGroupCanonicalDegreeCongr D (g ≫ sX) hY' hk x) =
      c.cap g hY' k l h x := by
  subst hk
  rfl

/-- Capping twice does not depend on how the intermediate degree is written. -/
theorem cap_cap_congr {p q : ℤ} (c : ChowCohomologyClass D sX hX p)
    (d : ChowCohomologyClass D sX hX q) {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) {k l m m' : ℤ} (hm : m = m') (h₁ : l + p = m) (h₂ : m + q = k)
    (h₁' : l + p = m') (h₂' : m' + q = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    c.cap g hY' m l h₁ (d.cap g hY' k m h₂ x) = c.cap g hY' m' l h₁' (d.cap g hY' k m' h₂' x) := by
  subst hm
  rfl

/-! ### The abelian group `A^p(X)` -/

section Group

variable {p : ℤ}

/-- The zero class, capping as the zero map. -/
instance : Zero (ChowCohomologyClass D sX hX p) where
  zero :=
    { cap := fun _ _ _ _ _ => 0
      proper_naturality := fun _ _ _ _ _ _ _ _ _ => ⟨0, by simp, by simp⟩
      flat_naturality := by intros; simp
      gysin_naturality := by intros; simp }

/-- The sum of two classes, capping as the sum of their cap operations. -/
instance : Add (ChowCohomologyClass D sX hX p) where
  add c d :=
    { cap := fun g hY' k l hkl => c.cap g hY' k l hkl + d.cap g hY' k l hkl
      proper_naturality := fun g hY' h hY'' hh k l hkl α => by
        obtain ⟨β₁, h₁, h₁'⟩ := c.proper_naturality g hY' h hY'' hh k l hkl α
        obtain ⟨β₂, h₂, h₂'⟩ := d.proper_naturality g hY' h hY'' hh k l hkl α
        exact ⟨β₁ + β₂, by simp only [AddMonoidHom.add_apply, h₁, h₂, map_add],
          by simp only [AddMonoidHom.add_apply, h₁', h₂', map_add]⟩
      flat_naturality := fun g hY' h hY'' r hh hr k l hkl k' l' hk hl x => by
        simp only [AddMonoidHom.add_apply, map_add,
          c.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x,
          d.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x]
      gysin_naturality := fun g hY' L σ hL k l hkl x => by
        simp only [AddMonoidHom.add_apply, map_add,
          c.gysin_naturality g hY' L σ hL k l hkl x, d.gysin_naturality g hY' L σ hL k l hkl x] }

/-- The negative of a class, capping as the negative of its cap operation. -/
instance : Neg (ChowCohomologyClass D sX hX p) where
  neg c :=
    { cap := fun g hY' k l hkl => -c.cap g hY' k l hkl
      proper_naturality := fun g hY' h hY'' hh k l hkl α => by
        obtain ⟨β, h₁, h₁'⟩ := c.proper_naturality g hY' h hY'' hh k l hkl α
        exact ⟨-β, by simp only [AddMonoidHom.neg_apply, h₁, map_neg],
          by simp only [AddMonoidHom.neg_apply, h₁', map_neg]⟩
      flat_naturality := fun g hY' h hY'' r hh hr k l hkl k' l' hk hl x => by
        simp only [AddMonoidHom.neg_apply, map_neg,
          c.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x]
      gysin_naturality := fun g hY' L σ hL k l hkl x => by
        simp only [AddMonoidHom.neg_apply, map_neg, c.gysin_naturality g hY' L σ hL k l hkl x] }

/-- The difference of two classes, capping as the difference of their cap operations. -/
instance : Sub (ChowCohomologyClass D sX hX p) where
  sub c d :=
    { cap := fun g hY' k l hkl => c.cap g hY' k l hkl - d.cap g hY' k l hkl
      proper_naturality := fun g hY' h hY'' hh k l hkl α => by
        obtain ⟨β₁, h₁, h₁'⟩ := c.proper_naturality g hY' h hY'' hh k l hkl α
        obtain ⟨β₂, h₂, h₂'⟩ := d.proper_naturality g hY' h hY'' hh k l hkl α
        exact ⟨β₁ - β₂, by simp only [AddMonoidHom.sub_apply, h₁, h₂, map_sub],
          by simp only [AddMonoidHom.sub_apply, h₁', h₂', map_sub]⟩
      flat_naturality := fun g hY' h hY'' r hh hr k l hkl k' l' hk hl x => by
        simp only [AddMonoidHom.sub_apply, map_sub,
          c.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x,
          d.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x]
      gysin_naturality := fun g hY' L σ hL k l hkl x => by
        simp only [AddMonoidHom.sub_apply, map_sub,
          c.gysin_naturality g hY' L σ hL k l hkl x, d.gysin_naturality g hY' L σ hL k l hkl x] }

/-- The `n`-th multiple of a class, capping as `n` times its cap operation. -/
instance : SMul ℕ (ChowCohomologyClass D sX hX p) where
  smul n c :=
    { cap := fun g hY' k l hkl => n • c.cap g hY' k l hkl
      proper_naturality := fun g hY' h hY'' hh k l hkl α => by
        obtain ⟨β, h₁, h₁'⟩ := c.proper_naturality g hY' h hY'' hh k l hkl α
        exact ⟨n • β, by simp only [AddMonoidHom.nsmul_apply, h₁, map_nsmul],
          by simp only [AddMonoidHom.nsmul_apply, h₁', map_nsmul]⟩
      flat_naturality := fun g hY' h hY'' r hh hr k l hkl k' l' hk hl x => by
        simp only [AddMonoidHom.nsmul_apply, map_nsmul,
          c.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x]
      gysin_naturality := fun g hY' L σ hL k l hkl x => by
        simp only [AddMonoidHom.nsmul_apply, map_nsmul,
          c.gysin_naturality g hY' L σ hL k l hkl x] }

/-- The `n`-th integer multiple of a class, capping as `n` times its cap operation. -/
instance : SMul ℤ (ChowCohomologyClass D sX hX p) where
  smul n c :=
    { cap := fun g hY' k l hkl => n • c.cap g hY' k l hkl
      proper_naturality := fun g hY' h hY'' hh k l hkl α => by
        obtain ⟨β, h₁, h₁'⟩ := c.proper_naturality g hY' h hY'' hh k l hkl α
        exact ⟨n • β, by simp only [AddMonoidHom.zsmul_apply, h₁, map_zsmul],
          by simp only [AddMonoidHom.zsmul_apply, h₁', map_zsmul]⟩
      flat_naturality := fun g hY' h hY'' r hh hr k l hkl k' l' hk hl x => by
        simp only [AddMonoidHom.zsmul_apply, map_zsmul,
          c.flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x]
      gysin_naturality := fun g hY' L σ hL k l hkl x => by
        simp only [AddMonoidHom.zsmul_apply, map_zsmul,
          c.gysin_naturality g hY' L σ hL k l hkl x] }

/-- **Stacks 0ERK, the degree `p` component.** `A^p(X)` is an abelian group under the pointwise
operations on cap operations. -/
instance instAddCommGroup : AddCommGroup (ChowCohomologyClass D sX hX p) where
  add_assoc _ _ _ := ext fun _ _ _ _ _ _ => add_assoc _ _ _
  zero_add _ := ext fun _ _ _ _ _ _ => zero_add _
  add_zero _ := ext fun _ _ _ _ _ _ => add_zero _
  add_comm _ _ := ext fun _ _ _ _ _ _ => add_comm _ _
  nsmul n c := n • c
  nsmul_zero _ := ext fun _ _ _ _ _ _ => AddMonoid.nsmul_zero _
  nsmul_succ n _ := ext fun _ _ _ _ _ _ => AddMonoid.nsmul_succ n _
  zsmul n c := n • c
  zsmul_zero' _ := ext fun _ _ _ _ _ _ => SubNegMonoid.zsmul_zero' _
  zsmul_succ' n _ := ext fun _ _ _ _ _ _ => SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n _ := ext fun _ _ _ _ _ _ => SubNegMonoid.zsmul_neg' n _
  neg_add_cancel _ := ext fun _ _ _ _ _ _ => neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ _ _ _ _ _ => sub_eq_add_neg _ _

/-- The zero class caps as zero. -/
@[simp]
theorem zero_cap {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k l : ℤ)
    (hkl : l + p = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (0 : ChowCohomologyClass D sX hX p).cap g hY' k l hkl x = 0 :=
  rfl

/-- The sum of two classes caps as the sum of their cap operations. -/
@[simp]
theorem add_cap (c d : ChowCohomologyClass D sX hX p) {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (c + d).cap g hY' k l hkl x = c.cap g hY' k l hkl x + d.cap g hY' k l hkl x :=
  rfl

/-- An integer multiple of a class caps as that multiple of its cap operation. -/
@[simp]
theorem zsmul_cap (n : ℤ) (c : ChowCohomologyClass D sX hX p) {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (n • c).cap g hY' k l hkl x = n • c.cap g hY' k l hkl x :=
  rfl

/-- A natural multiple of a class caps as that multiple of its cap operation. -/
@[simp]
theorem nsmul_cap (n : ℕ) (c : ChowCohomologyClass D sX hX p) {Y' : D.Ambient} (g : Y' ⟶ X)
    (hY' : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (n • c).cap g hY' k l hkl x = n • c.cap g hY' k l hkl x :=
  rfl

end Group

/-! ### Composition and the unit -/

section Composition

/-- **Stacks 0ERK, the product.** The composite `c ∘ d ∈ A^{p+q}(X)` of `c ∈ A^p(X)` and
`d ∈ A^q(X)`: on a test space `Y' ⟶ X` it caps as `(c ∘ d) ∩ α = c ∩ (d ∩ α)`, first by `d`
from degree `k` to `l + p`, then by `c` to degree `l`. This is the composition
`A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)` of bivariant classes. -/
def comp {p q : ℤ} (c : ChowCohomologyClass D sX hX p) (d : ChowCohomologyClass D sX hX q) :
    ChowCohomologyClass D sX hX (p + q) where
  cap g hY' k l hkl := (c.cap g hY' (l + p) l rfl).comp (d.cap g hY' k (l + p) (by omega))
  proper_naturality g hY' h hY'' hh k l hkl α := by
    obtain ⟨β, h₁, h₁'⟩ := d.proper_naturality g hY' h hY'' hh k (l + p) (by omega) α
    obtain ⟨γ, h₂, h₂'⟩ := c.proper_naturality g hY' h hY'' hh (l + p) l rfl β
    exact ⟨γ, by simp only [AddMonoidHom.comp_apply, h₁, h₂],
      by simp only [AddMonoidHom.comp_apply, h₁', h₂']⟩
  flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x := by
    simp only [AddMonoidHom.comp_apply]
    rw [d.flat_naturality g hY' h hY'' r hh hr k (l + p) (by omega) k' (l' + p) hk (by omega) x,
      c.flat_naturality g hY' h hY'' r hh hr (l + p) l rfl (l' + p) l' (by omega) hl]
  gysin_naturality g hY' L σ hL k l hkl x := by
    simp only [AddMonoidHom.comp_apply]
    rw [d.gysin_naturality g hY' L σ hL k (l + p) (by omega) x,
      c.gysin_naturality g hY' L σ hL (l + p) l rfl,
      cap_cap_congr c d g hY' (by omega : l + p + 1 = l + 1 + p)]

/-- The composite `c ∘ d` caps as `c ∩ (d ∩ -)`. -/
theorem comp_cap {p q : ℤ} (c : ChowCohomologyClass D sX hX p)
    (d : ChowCohomologyClass D sX hX q) {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX))
    (k l : ℤ) (hkl : l + (p + q) = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (c.comp d).cap g hY' k l hkl x = c.cap g hY' (l + p) l rfl (d.cap g hY' k (l + p)
      (by omega) x) :=
  rfl

/-- **Stacks 0ERK, the unit.** The class `1 ∈ A^0(X)`, capping as the identity of every Chow
group. -/
def one : ChowCohomologyClass D sX hX 0 where
  cap g hY' k l hkl :=
    (chowGroupCanonicalDegreeCongr D (g ≫ sX) hY' (by omega : k = l)).toAddMonoidHom
  proper_naturality g hY' h hY'' hh k l hkl α := by
    obtain rfl : k = l := by omega
    exact ⟨α, rfl, rfl⟩
  flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x := by
    obtain rfl : k = l := by omega
    subst hk hl
    rfl
  gysin_naturality g hY' L σ hL k l hkl x := by
    obtain rfl : k = l := by omega
    rfl

/-- The class `1 ∈ A^0(X)` caps as the transport along `k = l`, that is, as the identity. -/
theorem one_cap {Y' : D.Ambient} (g : Y' ⟶ X) (hY' : D.IsGood (g ≫ sX)) (k l : ℤ)
    (hkl : l + 0 = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY' k) :
    (one : ChowCohomologyClass D sX hX 0).cap g hY' k l hkl x =
      chowGroupCanonicalDegreeCongr D (g ≫ sX) hY' (by omega : k = l) x :=
  rfl

/-- **Associativity of composition.** -/
theorem comp_assoc {p q r : ℤ} (a : ChowCohomologyClass D sX hX p)
    (b : ChowCohomologyClass D sX hX q) (c : ChowCohomologyClass D sX hX r) :
    (⟨p + q + r, (a.comp b).comp c⟩ : GradedMonoid (ChowCohomologyClass D sX hX)) =
      ⟨p + (q + r), a.comp (b.comp c)⟩ :=
  gradedMonoid_mk_eq (add_assoc p q r) fun g hY' k l _ _ x => by
    simp only [comp_cap]
    exact congrArg _ (cap_cap_congr b c g hY' (by omega) _ _ _ _ x)

/-- **The left unit law.** -/
theorem one_comp {p : ℤ} (a : ChowCohomologyClass D sX hX p) :
    (⟨0 + p, one.comp a⟩ : GradedMonoid (ChowCohomologyClass D sX hX)) = ⟨p, a⟩ :=
  gradedMonoid_mk_eq (zero_add p) fun g hY' k l _ _ x => by
    rw [comp_cap, one_cap]
    exact cap_degreeCongr_target a g hY' _ _ _ x

/-- **The right unit law.** -/
theorem comp_one {p : ℤ} (a : ChowCohomologyClass D sX hX p) :
    (⟨p + 0, a.comp one⟩ : GradedMonoid (ChowCohomologyClass D sX hX)) = ⟨p, a⟩ :=
  gradedMonoid_mk_eq (add_zero p) fun g hY' k l _ hkl' x => by
    rw [comp_cap, one_cap]
    exact cap_degreeCongr_source a g hY' _ hkl' _ x

/-- Composition with the zero class on the right is zero. -/
theorem comp_zero {p q : ℤ} (a : ChowCohomologyClass D sX hX p) :
    a.comp (0 : ChowCohomologyClass D sX hX q) = 0 :=
  ext fun g hY' k l hkl x => by simp [comp_cap]

/-- Composition with the zero class on the left is zero. -/
theorem zero_comp {p q : ℤ} (b : ChowCohomologyClass D sX hX q) :
    (0 : ChowCohomologyClass D sX hX p).comp b = 0 :=
  ext fun g hY' k l hkl x => by simp [comp_cap]

/-- Composition is additive in its right argument. -/
theorem comp_add {p q : ℤ} (a : ChowCohomologyClass D sX hX p)
    (b b' : ChowCohomologyClass D sX hX q) : a.comp (b + b') = a.comp b + a.comp b' :=
  ext fun g hY' k l hkl x => by simp [comp_cap]

/-- Composition is additive in its left argument. -/
theorem add_comp {p q : ℤ} (a a' : ChowCohomologyClass D sX hX p)
    (b : ChowCohomologyClass D sX hX q) : (a + a').comp b = a.comp b + a'.comp b :=
  ext fun g hY' k l hkl x => by simp [comp_cap]

end Composition

/-! ### The graded ring -/

/-- The unit `1 ∈ A^0(X)` of the graded object `p ↦ A^p(X)`. -/
instance : GradedMonoid.GOne (ChowCohomologyClass D sX hX) where
  one := one

/-- The graded multiplication `A^p(X) × A^q(X) ⟶ A^{p+q}(X)`, composition of classes. -/
instance : GradedMonoid.GMul (ChowCohomologyClass D sX hX) where
  mul c d := c.comp d

/-- The graded ring structure on `p ↦ A^p(X) = A^p(X ⟶ X)`: the product of the degree `p` and `q`
components is the composition `A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)` of bivariant classes,
associative and bilinear, with unit `1 ∈ A^0(X)`; the integers act through the multiples of `1`. -/
@[stacks 0ERK "the graded Z-algebra structure on A^*(X): the product of the degree p and q \
components is the composition A^p(X → X) × A^q(X → X) → A^{p+q}(X → X) of bivariant classes, \
associative and bilinear, with unit 1 ∈ A^0(X)"]
instance instGRing : DirectSum.GRing (ChowCohomologyClass D sX hX) where
  one_mul := fun ⟨_, a⟩ => one_comp a
  mul_one := fun ⟨_, a⟩ => comp_one a
  mul_assoc := fun ⟨_, a⟩ ⟨_, b⟩ ⟨_, c⟩ => comp_assoc a b c
  mul_zero := comp_zero
  zero_mul := zero_comp
  mul_add := comp_add
  add_mul := add_comp
  natCast n := n • one
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • one
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- The graded multiplication of `p ↦ A^p(X)` is composition of classes. -/
theorem gMul_eq_comp {p q : ℤ} (a : ChowCohomologyClass D sX hX p)
    (b : ChowCohomologyClass D sX hX q) : GradedMonoid.GMul.mul a b = a.comp b :=
  rfl

end ChowCohomologyClass

/-- The Chow cohomology `A^*(X)` of a good algebraic space `X/B`: the graded `ℤ`-algebra
`⊕_p A^p(X)` whose degree `p` component is the group `A^p(X ⟶ X)` of bivariant classes of degree
`p` for `id_X` over the constructed Chow groups of Stacks 0EQ6, with multiplication the composition
of bivariant classes (`DirectSum.ring` of `AlgebraicGeometry.Space.ChowCohomologyClass.instGRing`)
and its `ℤ`-algebra structure the one of any ring. -/
@[stacks 0ERK "the Chow cohomology A^*(X): the graded Z-algebra ⊕_p A^p(X → X), with \
multiplication the composition of bivariant classes"]
abbrev ChowCohomologyAlgebra : Type _ :=
  DirectSum ℤ (ChowCohomologyClass D sX hX)

namespace ChowCohomologyAlgebra

example : Ring (ChowCohomologyAlgebra D sX hX) := inferInstance

example : Algebra ℤ (ChowCohomologyAlgebra D sX hX) := inferInstance

/-- The product of homogeneous elements of `A^*(X)` is their composite. -/
theorem of_mul_of {p q : ℤ} (a : ChowCohomologyClass D sX hX p)
    (b : ChowCohomologyClass D sX hX q) :
    DirectSum.of (ChowCohomologyClass D sX hX) p a * DirectSum.of _ q b =
      DirectSum.of _ (p + q) (a.comp b) :=
  DirectSum.of_mul_of a b

/-- The unit of `A^*(X)` is the identity class in degree `0`. -/
theorem one_def :
    (1 : ChowCohomologyAlgebra D sX hX) =
      DirectSum.of (ChowCohomologyClass D sX hX) 0 ChowCohomologyClass.one :=
  rfl

end ChowCohomologyAlgebra

end AlgebraicGeometry.Space

end
