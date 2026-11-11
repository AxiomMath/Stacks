module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension

/-!
# Flat pullback as a bivariant Chow class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
flat morphism of relative dimension `r` between schemes locally of finite type over `S`. Stacks
0B78 asserts that the rule sending a test scheme `g : T ⟶ Y` and a class `α ∈ A_k(T)` to

  `(f')^* α ∈ A_{k+r}(T ×_Y X)`,

where `f' : T ×_Y X ⟶ T` is the base change of `f` along `g`, is a bivariant class of degree
`-r` for `f`.

This file supplies the rule and the flat-pullback condition of Stacks 0B76 for it, the part of
the source proof carried by Stacks 02RD. It also supplies the substrate that condition needs —
flat pullback on Chow groups through a commuting square of flat morphisms, and the composition
rule of Stacks 02RD on Chow groups rather than on cycles. The class of Stacks 0B78 itself is
assembled in `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward` and
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackChowClass`.

## Main definitions

* `Stacks.Chow.flatPullbackBivariantCap` — the rule `α ↦ (f')^* α` of Stacks 0B78, read as a map
  into degree `k - (-r)`, which is the degree a bivariant class of degree `-r` produces.
* `Stacks.Chow.IsBivariantFlatPullback` — the assertion that a bivariant class of degree `-r` for
  `f` caps by that rule. This is the defining property of the class of Stacks 0B78.

## Main results

* `Stacks.Chow.flatPullback_comm_of_comp_eq` and `Stacks.Chow.flatPullbackChow_comm_of_comp_eq` —
  two composites of flat morphisms that agree pull a cycle, resp. a Chow class, back to the same
  thing. This is Stacks 02RD read across a commuting square.
* `Stacks.Chow.flatPullbackChow_comp` — **Stacks 02RD on Chow groups**: `f^* ∘ g^* = (f ≫ g)^*`.
* `Stacks.Chow.flatPullbackBivariantCap_flat_naturality` — **the flat-pullback condition of
  Stacks 0B76 for the rule of Stacks 0B78**, from Stacks 02RD.
* `Stacks.Chow.eq_of_isBivariantFlatPullback` — two bivariant classes capping by the rule of
  Stacks 0B78 are equal.

## Implementation notes

### Why the rule is stated over a descent hypothesis

The rule pulls back along the base change of `f`, so writing it down needs an instance of Stacks
02S1 for that morphism at every test scheme and every degree. The declarations below quantify
over all the instances at once, in the shape `Stacks.Chow.ProperPushforwardDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic` uses for Stacks 02S2. The
quantification is written out rather than named, so that it is exactly — definitionally — the
statement `Stacks.Chow.FlatPullbackDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction`. That statement is
Stacks 02S1, and it is a theorem of this repository, `Stacks.Chow.flatPullbackDescends` of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent`, which a consumer
passes here. The quantification is a hypothesis of the enclosing declarations and is **not** put
inside `Stacks.Chow.IsBivariantFlatPullback`: inside, it would weaken the characterization.

Quantifying over every degree also does real work in the proof of the flat-pullback condition:
the comparison there is between flat pullback at two degrees that are the same integer written two
ways, and transporting a heterogeneous equality through `Stacks.Chow.heq_map_index` needs the map
at *every* degree, not just at the two in question.

### The transport of degrees

A bivariant class of degree `p` caps `A_k(T)` into `A_{k-p}`, while flat pullback of relative
dimension `r` lands in `A_{k+r}`. With `p = -r` these are the same integer and not the same term,
so the rule is flat pullback followed by `Stacks.Chow.chowGroupDegreeEquiv`, and the
flat-pullback condition is a heterogeneous equality, as the field of
`Stacks.Chow.BivariantClass` is.

### Where the class is assembled

Constructing the class of Stacks 0B78 is filling the three naturality fields of
`Stacks.Chow.BivariantClass` for `Stacks.Chow.flatPullbackBivariantCap`. The source proof
invokes Stacks 02S1, 02RD, 02RG and 0B71. This file proves the flat field from Stacks 02RD,
`Stacks.Chow.flatPullbackBivariantCap_flat_naturality`. The other two, and the class itself, are
in later files: the proper field from Stacks 02RG,
`Stacks.Chow.flatPullbackBivariantCap_proper_naturality_unconditional`, the Gysin field from
Stacks 0B71 with the identification of Remark 0B6Y,
`Stacks.Chow.gysinSystemOfInvertible_flatPullbackNaturalityAtZeroSchemeComparison`, and the
class, `Stacks.Chow.flatPullbackBivariantClassOfInvertible` and
`Stacks.Chow.flatPullbackBivariantChowClass`, which carry `@[stacks 0B78]`. No declaration in
this file carries the tag: each states one step of the proof, not the lemma.

## References

* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Flat pullback through a commuting square -/

/-- Two elements of the group of cycles on a scheme, of degrees that are the same integer written
two ways, are heterogeneously equal as soon as their coefficient functions agree. -/
private theorem cycleGroup_heq_of_apply_eq (C : ChowSituation.{u}) {A : Scheme.{u}} (q : A ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) {a : CycleGroup C q i}
    {b : CycleGroup C q j} (hab : ∀ x : A, a.1 x = b.1 x) : a ≍ b := by
  subst hij
  exact heq_of_eq (Subtype.ext (Function.locallyFinsuppWithin.ext hab))

/-- Flat pullback of cycles depends on the morphism and on its relative dimension only through
their values: equal morphisms of equal relative dimension pull a cycle back to the same thing. -/
private theorem flatPullback_congr (C : ChowSituation.{u}) {A D : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] {w w' : A ⟶ D}
    [LocallyOfFiniteType w] [Flat w] [LocallyOfFiniteType w'] [Flat w'] (hww' : w = w')
    {m n : ℕ} (hmn : m = n) (hw : w ≫ sD = sA) (hw' : w' ≫ sD = sA)
    (hwm : AlgebraicGeometry.RelativeDimension w m)
    (hw'n : AlgebraicGeometry.RelativeDimension w' n) (k : ℤ) (a : CycleGroup C sD k) :
    flatPullback C sA sD w hw m hwm k a ≍ flatPullback C sA sD w' hw' n hw'n k a := by
  subst hww'
  subst hmn
  rfl

/-- The class of a cycle determines the class of any cycle heterogeneously equal to it. -/
private theorem chowGroup_mk_heq_of_heq (C : ChowSituation.{u}) {A : Scheme.{u}} (q : A ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) {a : CycleGroup C q i}
    {b : CycleGroup C q j} (hab : a ≍ b) :
    (QuotientAddGroup.mk' (rationalEquivalences C q i) a : chowGroup C q i) ≍
      (QuotientAddGroup.mk' (rationalEquivalences C q j) b : chowGroup C q j) := by
  subst hij
  rw [eq_of_heq hab]

/-- Flat pullback along `g` and then `f` is heterogeneously equal to flat pullback along `f ≫ g`:
the degrees `(k + s) + r` and `k + (r + s)` are the same integer written two ways. -/
private theorem flatPullback_comp_heq (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ) (c : CycleGroup C sZ k) :
    flatPullback C sX sY f hfbase r hf (k + (s : ℤ)) (flatPullback C sY sZ g hgbase s hg k c) ≍
      flatPullback C sX sZ (f ≫ g) (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k c :=
  cycleGroup_heq_of_apply_eq C sX (by push_cast; ring) fun x₀ ↦
    flatPullback_comp_apply C sX sY sZ f g hfbase hgbase r s hf hg k c x₀

/-- **Stacks 02RD across a commuting square.** Let `u ≫ y = x ≫ v` be two factorizations of one
morphism `A ⟶ D` through flat morphisms, `u` and `v` of relative dimension `m` and `y` and `x` of
relative dimension `n`. Then pulling a cycle back along `y` and then along `u` gives the same
thing as pulling it back along `v` and then along `x`; the two live in degrees `k + n + m` and
`k + m + n`, so the identity is a heterogeneous equality. -/
theorem flatPullback_comm_of_comp_eq (C : ChowSituation.{u}) {A B B' D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
    (u : A ⟶ B) [LocallyOfFiniteType u] [Flat u] (y : B ⟶ D) [LocallyOfFiniteType y] [Flat y]
    (x : A ⟶ B') [LocallyOfFiniteType x] [Flat x] (v : B' ⟶ D) [LocallyOfFiniteType v] [Flat v]
    (hu : u ≫ sB = sA) (hy : y ≫ sD = sB) (hx : x ≫ sB' = sA) (hv : v ≫ sD = sB')
    (m n : ℕ) (hum : AlgebraicGeometry.RelativeDimension u m)
    (hyn : AlgebraicGeometry.RelativeDimension y n)
    (hxn : AlgebraicGeometry.RelativeDimension x n)
    (hvm : AlgebraicGeometry.RelativeDimension v m) (hcomm : u ≫ y = x ≫ v) (k : ℤ)
    (a : CycleGroup C sD k) :
    flatPullback C sA sB u hu m hum (k + (n : ℤ)) (flatPullback C sB sD y hy n hyn k a) ≍
      flatPullback C sA sB' x hx n hxn (k + (m : ℤ)) (flatPullback C sB' sD v hv m hvm k a) := by
  have hbu : (u ≫ y) ≫ sD = sA := by rw [Category.assoc, hy, hu]
  have hbx : (x ≫ v) ≫ sD = sA := by rw [Category.assoc, hv, hx]
  have hleft := flatPullback_comp_heq C sA sB sD u y hu hy m n hum hyn k a
  have hright := flatPullback_comp_heq C sA sB' sD x v hx hv n m hxn hvm k a
  refine hleft.trans (HEq.trans ?_ hright.symm)
  exact flatPullback_congr C sA sD hcomm (Nat.add_comm m n) hbu hbx _ _ k a

/-- **Stacks 02RD across a commuting square, on Chow groups.** The Chow-group form of
`Stacks.Chow.flatPullback_comm_of_comp_eq`. -/
theorem flatPullbackChow_comm_of_comp_eq (C : ChowSituation.{u}) {A B B' D : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
    (u : A ⟶ B) [LocallyOfFiniteType u] [Flat u] (y : B ⟶ D) [LocallyOfFiniteType y] [Flat y]
    (x : A ⟶ B') [LocallyOfFiniteType x] [Flat x] (v : B' ⟶ D) [LocallyOfFiniteType v] [Flat v]
    (hu : u ≫ sB = sA) (hy : y ≫ sD = sB) (hx : x ≫ sB' = sA) (hv : v ≫ sD = sB')
    (m n : ℕ) (hum : AlgebraicGeometry.RelativeDimension u m)
    (hyn : AlgebraicGeometry.RelativeDimension y n)
    (hxn : AlgebraicGeometry.RelativeDimension x n)
    (hvm : AlgebraicGeometry.RelativeDimension v m) (hcomm : u ≫ y = x ≫ v) (k : ℤ)
    (hfacu : FlatPullbackFactorsThroughRationalEquivalence C sA sB u hu m hum (k + (n : ℤ)))
    (hfacy : FlatPullbackFactorsThroughRationalEquivalence C sB sD y hy n hyn k)
    (hfacx : FlatPullbackFactorsThroughRationalEquivalence C sA sB' x hx n hxn (k + (m : ℤ)))
    (hfacv : FlatPullbackFactorsThroughRationalEquivalence C sB' sD v hv m hvm k)
    (α : chowGroup C sD k) :
    flatPullbackChow C sA sB u hu m hum (k + (n : ℤ)) hfacu
          (flatPullbackChow C sB sD y hy n hyn k hfacy α) ≍
      flatPullbackChow C sA sB' x hx n hxn (k + (m : ℤ)) hfacx
        (flatPullbackChow C sB' sD v hv m hvm k hfacv α) := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hmk : (a : chowGroup C sD k) = QuotientAddGroup.mk' (rationalEquivalences C sD k) a := rfl
    rw [hmk, flatPullbackChow_mk, flatPullbackChow_mk, flatPullbackChow_mk, flatPullbackChow_mk]
    refine chowGroup_mk_heq_of_heq C sA (by ring) ?_
    exact flatPullback_comm_of_comp_eq C sA sB sB' sD u y x v hu hy hx hv m n hum hyn hxn hvm
      hcomm k a

/-- **Stacks 02RD on Chow groups.** For flat morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of relative
dimensions `r` and `s`, flat pullback on Chow groups satisfies `f^* ∘ g^* = (g ∘ f)^*` as maps
`A_k(Z) ⟶ A_{k+r+s}(X)`; the two sides land in degrees `k + s + r` and `k + (r + s)`, so the
identity is a heterogeneous equality. -/
theorem flatPullbackChow_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ Z)
    [LocallyOfFiniteType g] [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ)))
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacfg : FlatPullbackFactorsThroughRationalEquivalence C sX sZ (f ≫ g)
      (by rw [Category.assoc, hgbase, hfbase]) (r + s)
      (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k)
    (α : chowGroup C sZ k) :
    flatPullbackChow C sX sY f hfbase r hf (k + (s : ℤ)) hfacf
          (flatPullbackChow C sY sZ g hgbase s hg k hfacg α) ≍
      flatPullbackChow C sX sZ (f ≫ g) (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k hfacfg α := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hmk : (a : chowGroup C sZ k) = QuotientAddGroup.mk' (rationalEquivalences C sZ k) a := rfl
    rw [hmk, flatPullbackChow_mk, flatPullbackChow_mk, flatPullbackChow_mk]
    refine chowGroup_mk_heq_of_heq C sX (by push_cast; ring) ?_
    exact flatPullback_comp_heq C sX sY sZ f g hfbase hgbase r s hf hg k a

/-! ### The rule of Stacks 0B78 -/

section Rule

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (r : ℕ) (hfr : AlgebraicGeometry.RelativeDimension f r)
  (hfp : ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA)
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension v d) (j : ℤ),
    FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv d hd j)

/-- **Stacks 0B78.** The rule of the flat-pullback bivariant class: on a test scheme
`g : T ⟶ Y` it is flat pullback along the base change `T ×_Y X ⟶ T` of `f`, read as a map into
degree `k - (-r)`, which is the degree a bivariant class of degree `-r` produces.

The base change is flat of relative dimension `r` by Stacks 02NK, and its flat pullback descends
to Chow groups by the bundled Stacks 02S1 statement `Stacks.Chow.FlatPullbackDescends`, which is
the theorem `Stacks.Chow.flatPullbackDescends`. -/
def flatPullbackBivariantCap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - -(r : ℤ)) :=
  (chowGroupDegreeEquiv C (pullback.fst f g ≫ sX)
      (by ring : k + (r : ℤ) = k - -(r : ℤ))).toAddMonoidHom.comp
    (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
      (relativeDimension_pullback_snd f g r hfr) k
      (hfp _ _ _ _ _ _ _))

/-- The rule of Stacks 0B78, read on an element. -/
theorem flatPullbackBivariantCap_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf r hfr hfp g k α =
      chowGroupDegreeEquiv C (pullback.fst f g ≫ sX) (by ring : k + (r : ℤ) = k - -(r : ℤ))
        (flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
          (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
          (relativeDimension_pullback_snd f g r hfr) k (hfp _ _ _ _ _ _ _) α) :=
  rfl

/-- The rule of Stacks 0B78 is flat pullback along the base change of `f`: the transport of
degrees it carries changes nothing. -/
theorem flatPullbackBivariantCap_heq {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf r hfr hfp g k α ≍
      flatPullbackChow C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r
        (relativeDimension_pullback_snd f g r hfr) k (hfp _ _ _ _ _ _ _) α := by
  rw [flatPullbackBivariantCap_apply]
  exact chowGroupDegreeEquiv_heq C (pullback.fst f g ≫ sX) _ _

/-- The flat-pullback condition of Stacks 0B76 for the rule of Stacks 0B78: the
rule `α ↦ (f')^* α` commutes with flat pullback of fixed relative dimension along a morphism
`h : T' ⟶ T` of test schemes.

The base change of `f` over `T'` followed by `h`, and the base change of `h` followed by the base
change of `f` over `T`, are the same morphism `T' ×_Y X ⟶ T`, because the two cartesian squares
paste; Stacks 02RD then traverses that morphism both ways. The two sides land in degrees
`(k + s) - (-r)` and `(k - (-r)) + s`, so the identity is a heterogeneous equality, exactly as
the corresponding field of `Stacks.Chow.BivariantClass` is. -/
theorem flatPullbackBivariantCap_flat_naturality {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (s : ℕ)
    (hs : AlgebraicGeometry.RelativeDimension h s)
    (h' : pullback f (h ≫ g) ⟶ pullback f g) [LocallyOfFiniteType h'] [Flat h']
    (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ)
    (hs' : AlgebraicGeometry.RelativeDimension h' s)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) s hs k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C (pullback.fst f (h ≫ g) ≫ sX)
      (pullback.fst f g ≫ sX) h' (by rw [← Category.assoc, hfst]) s hs' (k - -(r : ℤ)))
    (α : chowGroup C (g ≫ sY) k) :
    flatPullbackBivariantCap C sX sY f hf r hfr hfp (h ≫ g) (k + (s : ℤ))
          (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) s hs k
            hfac α) ≍
      flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) s hs' (k - -(r : ℤ)) hfac'
        (flatPullbackBivariantCap C sX sY f hf r hfr hfp g k α) := by
  have hcore := flatPullbackChow_comm_of_comp_eq C (pullback.fst f (h ≫ g) ≫ sX)
    ((h ≫ g) ≫ sY) (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f (h ≫ g)) h h'
    (pullback.snd f g) (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (h ≫ g))
    (by simp [Category.assoc]) (by rw [← Category.assoc, hfst])
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) r s
    (relativeDimension_pullback_snd f (h ≫ g) r hfr) hs hs'
    (relativeDimension_pullback_snd f g r hfr) sq.w k (hfp _ _ _ _ _ _ _) hfac
    (hfp _ _ _ _ _ _ _) (hfp _ _ _ _ _ _ _) α
  refine (flatPullbackBivariantCap_heq C sX sY f hf r hfr hfp (h ≫ g) (k + (s : ℤ)) _).trans
    (hcore.trans ?_)
  refine heq_map_index (by ring : k + (r : ℤ) = k - -(r : ℤ))
    (flatPullbackBivariantCap_heq C sX sY f hf r hfr hfp g k α).symm fun n β ↦
      flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
        (by rw [← Category.assoc, hfst]) s hs' n (hfp _ _ _ _ _ _ _) β

end Rule

/-! ### The defining property of the class of Stacks 0B78 -/

section Characterization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (r : ℕ)
  (hfr : AlgebraicGeometry.RelativeDimension f r)
  (hfp : ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA)
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension v d) (j : ℤ),
    FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv d hd j)

/-- **Stacks 0B78.** The assertion that a bivariant class of degree `-r` for `f` is *the*
flat-pullback class: on every test scheme its cap operation is flat pullback along the base change
of `f`. -/
def IsBivariantFlatPullback (c : BivariantClass C G sX sY f hf (-(r : ℤ))) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k),
    c.cap g k α = flatPullbackBivariantCap C sX sY f hf r hfr hfp g k α

/-- The rule of Stacks 0B78 determines the flat-pullback class: two bivariant classes that both
cap by flat pullback along the base change of `f` are equal. -/
theorem eq_of_isBivariantFlatPullback {c d : BivariantClass C G sX sY f hf (-(r : ℤ))}
    (hc : IsBivariantFlatPullback C G sX sY f hf r hfr hfp c)
    (hd : IsBivariantFlatPullback C G sX sY f hf r hfr hfp d) : c = d := by
  refine BivariantClass.ext C G sX sY f hf (-(r : ℤ)) ?_
  intro T g _ k α
  exact (hc g k α).trans (hd g k α).symm

end Characterization

end Stacks.Chow

end
