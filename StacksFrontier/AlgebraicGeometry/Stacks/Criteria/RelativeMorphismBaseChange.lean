module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsEtale

/-!
# Base change of the relative morphism functor (Stacks 05Y4)

Let `S` be a scheme contained in a big fppf site and let `z : Z ⟶ Q`, `x : X ⟶ Q` and
`q : Q' ⟶ Q` be morphisms of algebraic spaces over `S`; the source writes the base `Q` as `B` and
`Q'` as `B'`, names that here belong to the site. Set `Z' = Q' ×_Q Z` and `X' = Q' ×_Q X`. Stacks
05Y4 asserts

```text
Mor_{Q'}(Z', X') = Q' ×_Q Mor_Q(Z, X),
```

that is, the square

```text
Mor_{Q'}(Z', X') ⟶ Mor_Q(Z, X)
       |                 |
       v                 v
       Q'         ⟶      Q
```

is cartesian, its vertical arrows being the projections reading off the first component of a pair
of Stacks 05Y1.

## The shape of the argument

A pair of Stacks 05Y1 for `z' : Z' ⟶ Q'` and `x' : X' ⟶ Q'` at a test object `T` is a morphism
`a' : T ⟶ Q'` together with a morphism `b' : T ×_{a', Q'} Z' ⟶ X'` over `Q'`. Now
`T ×_{a', Q'} Z' = T ×_{a' ≫ q, Q} Z`, because `Z' ⟶ Q'` is the base change of `z` along `q`, and a
morphism to `X' = Q' ×_Q X` over `Q'` is a morphism to `X`; so such a pair is the same thing as a
morphism `a' : T ⟶ Q'` together with a pair `(a, b)` for `z` and `x` whose first component `a`
factors as `a' ≫ q`. That is exactly a `T`-valued point of `Q' ×_Q Mor_Q(Z, X)`, and the
identification is the one the source calls immediate from the definitions.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism.ofBaseChange`: the pair of Stacks 05Y1 for `z` and `x`
  underlying a pair for the base-changed morphisms `z'` and `x'`.
* `AlgebraicGeometry.Space.RelativeMorphism.baseChange`: conversely, the pair for `z'` and `x'`
  determined by a pair for `z` and `x` together with a factorization of its first component
  through `q`.
* `AlgebraicGeometry.Space.relativeHomOfBaseChange`: the arrow
  `Mor_{Q'}(Z', X') ⟶ Mor_Q(Z, X)` of the square.
* `AlgebraicGeometry.Space.relativeHomBaseChangeLift`: the lift the square provides, built from a
  morphism to `Mor_Q(Z, X)` and a morphism to `Q'` whose first components agree.
* `AlgebraicGeometry.Space.relativeHomBaseChangeIso` and
  `AlgebraicGeometry.Space.relativeHomSheafBaseChangeIso`: the resulting identification of
  `Mor_{Q'}(Z', X')` with the fibre product `Q' ×_Q Mor_Q(Z, X)`, in presheaves and in fppf
  sheaves.
* `AlgebraicGeometry.Space.RelativeHomConstruction.isoRelativeHom`: the isomorphism of an
  arbitrary realization of the relative morphism functor with the one of Stacks 05Y2.

## Main results

* `AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.isPullback_relativeHomSheafOfBaseChange`: **Stacks 05Y4**, the
  identification in `Sh((Sch/S)_fppf)` with nothing assumed beyond the algebraicity the source
  assumes — for arbitrary realizations of the two relative morphism functors, and for the
  functor of Stacks 05Y2 together with the fibre products of algebraic spaces of Stacks 02X2.
* `AlgebraicGeometry.Space.RelativeHomConstruction.isSheaf_functor`: part (1) of Stacks 05Y3
  for an arbitrary realization of the relative morphism functor, which is what discharges the
  sheaf hypotheses.
* `AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange` and
  `AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange_relativeHomData`: the same
  two statements with the sheaf property of the relative morphism functors carried as an
  explicit hypothesis rather than discharged.
* `AlgebraicGeometry.Space.isPullback_relativeHomOfBaseChange` and
  `AlgebraicGeometry.Space.isPullback_relativeHomOfBaseChange_relativeHomData`: the same square,
  cartesian in presheaves on the big fppf site of `S`. This is the first step of the source's
  proof.
* `AlgebraicGeometry.Space.RelativeMorphism.ofBaseChange_baseChange`,
  `AlgebraicGeometry.Space.RelativeMorphism.baseChange_ofBaseChange` and
  `AlgebraicGeometry.Space.RelativeMorphism.ofBaseChange_injective`: the two constructions on
  pairs are mutually inverse, which is the content of the cartesian square.

## Implementation notes

The source states the identification in `Sh((Sch/S)_fppf)`, and its proof is in two steps: the
square is cartesian as a square of functors, and both sides are sheaves by part (1) of
Stacks 05Y3, so that the square is cartesian in sheaves as well. The passage from presheaves to
sheaves is formal, because the inclusion of fppf sheaves into presheaves creates limits. That
`Q` and `Q'` are fppf sheaves is part of being an algebraic space.

Part (1) of Stacks 05Y3 is `AlgebraicGeometry.Space.isSheaf_relativeHom`, for the functor of
Stacks 05Y2; `AlgebraicGeometry.Space.RelativeHomConstruction.isSheaf_functor` transports it to
an arbitrary realization through
`AlgebraicGeometry.Space.RelativeHomConstruction.isoRelativeHom`. The sheaf-level statements are
therefore available with nothing assumed; the versions that carry the sheaf property as an
explicit hypothesis are kept because they assume nothing about the two realizations at all, not
even that their sources are algebraic spaces.

Everything is stated for an arbitrary `AlgebraicGeometry.Space.RelativeHomConstruction` of either
functor, as in the companion lemmas of this section, and the construction of Stacks 05Y2 is one.
The second component of a pair lives over its first component, so the two constructions on pairs
are not inverse on the nose; the comparisons go through
`AlgebraicGeometry.Space.RelativeMorphism.ext_of_base_eq` and its converse
`AlgebraicGeometry.Space.RelativeMorphism.morphism_eq_of_eq`, and the identification
`T ×_{a', Q'} (Q' ×_Q Z) = T ×_{a' ≫ q, Q} Z` is the library's
`CategoryTheory.Limits.pullbackBaseChangeIso`.

The compatibility of `AlgebraicGeometry.Space.RelativeMorphism.baseChange` with restriction of
pairs is deduced from that of `AlgebraicGeometry.Space.RelativeMorphism.ofBaseChange` through
`AlgebraicGeometry.Space.RelativeMorphism.ofBaseChange_injective`, rather than computed a second
time.

## References

* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]

/-- The inverse of the comparison of two fibre products differing only in their first factor is
the comparison along the reversed equality. -/
theorem pullback.congrHom_inv_eq_symm_hom {Xc Yc Zc : C} {f₁ f₂ : Xc ⟶ Zc} (h : f₁ = f₂)
    (g : Yc ⟶ Zc) :
    (pullback.congrHom h (rfl : g = g)).inv = (pullback.congrHom h.symm (rfl : g = g)).hom :=
  pullback.hom_ext
    (by rw [pullback.congrHom_inv_fst, pullback.congrHom_hom_fst])
    (by rw [pullback.congrHom_inv_snd, pullback.congrHom_hom_snd])

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Base change of a pair -/

section Pairs

variable {Z X Q Q' T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

variable (B S hS Z X Q z x) in
/-- **Stacks 05Y3**, part (1), as an object of the category of fppf sheaves of sets on the big
fppf site of `S`.

The sheaf condition is `AlgebraicGeometry.Space.isSheaf_relativeHom` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf`; this bundles it as a
`Sheaf`, which is the form the base change statement of Stacks 05Y4 below is phrased in. -/
noncomputable def relativeHomSheaf (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hQ : IsAlgebraicSpace B S hS Q) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ⟨relativeHom B S hS Z X Q z x hZ hX hQ,
    isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ⟩

/-- **The pair of Stacks 05Y1 for `z : Z ⟶ Q` and `x : X ⟶ Q` underlying a pair for the base
changes `z' : Q' ×_Q Z ⟶ Q'` and `x' : Q' ×_Q X ⟶ Q'` along `q : Q' ⟶ Q`.** Its first component
is the composite with `q`, and its second component is the second component of the given pair,
read through the identification `T ×_{a', Q'} (Q' ×_Q Z) = T ×_{a' ≫ q, Q} Z` and followed by the
projection `Q' ×_Q X ⟶ X`. -/
noncomputable def RelativeMorphism.ofBaseChange (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    RelativeMorphism B S hS Z X Q z x T where
  base := p.base ≫ q
  morphism := (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x
  commutes := by
    have h1 : p.morphism ≫ pullback.snd q x ≫ x =
        pullback.snd p.base (pullback.fst q z) ≫ pullback.snd q z ≫ z := by
      rw [← pullback.condition (f := q) (g := x), ← Category.assoc, p.commutes, Category.assoc,
        pullback.condition (f := q) (g := z)]
    calc ((pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x) ≫ x
        = (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x ≫ x := by
          simp only [Category.assoc]
      _ = (pullbackBaseChangeIso q z p.base).inv ≫
            (pullback.snd p.base (pullback.fst q z) ≫ pullback.snd q z) ≫ z := by
          rw [h1, Category.assoc]
      _ = pullback.snd (p.base ≫ q) z ≫ z := by
          rw [← Category.assoc, pullbackBaseChangeIso_inv_snd]

/-- The first component of the pair underlying a pair for the base-changed morphisms. -/
@[simp] theorem RelativeMorphism.ofBaseChange_base (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    (RelativeMorphism.ofBaseChange q p).base = p.base ≫ q := rfl

/-- The second component of the pair underlying a pair for the base-changed morphisms. -/
@[simp] theorem RelativeMorphism.ofBaseChange_morphism (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    (RelativeMorphism.ofBaseChange q p).morphism =
      (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x := rfl

/-- **The pair of Stacks 05Y1 for the base changes `z'` and `x'` along `q : Q' ⟶ Q` determined by
a pair `(a, b)` for `z` and `x` together with a factorization `a = a' ≫ q` of its first
component.** Its first component is `a'`, and its second component is `b`, read through the
identification `T ×_{a', Q'} (Q' ×_Q Z) = T ×_{a, Q} Z` and lifted to `Q' ×_Q X` along the
projection to `Q'`. -/
noncomputable def RelativeMorphism.baseChange (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q) :
    RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T where
  base := a
  morphism :=
    pullback.lift (pullback.snd a (pullback.fst q z) ≫ pullback.fst q z)
      ((pullbackBaseChangeIso q z a).hom ≫ (pullback.congrHom ha rfl).inv ≫ p.morphism) (by
        have h2 : (pullback.congrHom ha (rfl : z = z)).inv ≫ p.morphism ≫ x =
            pullback.snd (a ≫ q) z ≫ z := by
          rw [p.commutes, ← Category.assoc, pullback.congrHom_inv_snd]
        calc (pullback.snd a (pullback.fst q z) ≫ pullback.fst q z) ≫ q
            = pullback.snd a (pullback.fst q z) ≫ pullback.snd q z ≫ z := by
              rw [Category.assoc, pullback.condition (f := q) (g := z)]
          _ = (pullbackBaseChangeIso q z a).hom ≫ pullback.snd (a ≫ q) z ≫ z := by
              simp only [pullbackBaseChangeIso_hom_snd_assoc]
          _ = ((pullbackBaseChangeIso q z a).hom ≫ (pullback.congrHom ha rfl).inv ≫
                p.morphism) ≫ x := by
              rw [Category.assoc, Category.assoc, h2])
  commutes := pullback.lift_fst _ _ _

/-- The first component of the pair for the base-changed morphisms determined by a pair and a
factorization of its first component. -/
@[simp] theorem RelativeMorphism.baseChange_base (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q) :
    (RelativeMorphism.baseChange q p a ha).base = a := rfl

/-- Two pairs for the base-changed morphisms built from equal data agree; the factorizations are
propositions, so they need not be compared. -/
theorem RelativeMorphism.baseChange_congr (q : Q' ⟶ Q)
    {p p' : RelativeMorphism B S hS Z X Q z x T} {a a' : T ⟶ Q'} (hp : p = p') (hb : a = a')
    (ha : p.base = a ≫ q) (ha' : p'.base = a' ≫ q) :
    RelativeMorphism.baseChange q p a ha = RelativeMorphism.baseChange q p' a' ha' := by
  cases hp
  cases hb
  rfl

/-- The second component of the pair for the base-changed morphisms, read on the projection to
`Q'`. This is the `commutes` field of the pair. -/
@[simp] theorem RelativeMorphism.baseChange_morphism_fst (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q) :
    (RelativeMorphism.baseChange q p a ha).morphism ≫ pullback.fst q x =
      pullback.snd a (pullback.fst q z) ≫ pullback.fst q z :=
  pullback.lift_fst _ _ _

/-- The second component of the pair for the base-changed morphisms, read on the projection
to `X`: it is the second component of the given pair. -/
@[simp] theorem RelativeMorphism.baseChange_morphism_snd (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q) :
    (RelativeMorphism.baseChange q p a ha).morphism ≫ pullback.snd q x =
      (pullbackBaseChangeIso q z a).hom ≫ (pullback.congrHom ha rfl).inv ≫ p.morphism :=
  pullback.lift_snd _ _ _

/-- **The two constructions are mutually inverse**, in the direction which forgets the
factorization. -/
theorem RelativeMorphism.ofBaseChange_baseChange (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q) :
    RelativeMorphism.ofBaseChange q (RelativeMorphism.baseChange q p a ha) = p := by
  refine RelativeMorphism.ext_of_base_eq ha.symm ?_
  refine Eq.trans (congrArg (fun m => (pullbackBaseChangeIso q z a).inv ≫ m)
    (RelativeMorphism.baseChange_morphism_snd q p a ha)) ?_
  rw [Iso.inv_hom_id_assoc, pullback.congrHom_inv_eq_symm_hom]
  rfl

/-- **A pair for the base-changed morphisms is determined by its first component together with
the pair of Stacks 05Y1 underlying it.** The second component of a pair for the base-changed
morphisms is a morphism to `Q' ×_Q X`, so it is determined by its two components; the one to `Q'`
is determined by the first component of the pair, and the one to `X` is the second component of
the underlying pair. -/
theorem RelativeMorphism.ofBaseChange_injective (q : Q' ⟶ Q)
    {p p' : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T} (hbase : p.base = p'.base)
    (h : RelativeMorphism.ofBaseChange q p = RelativeMorphism.ofBaseChange q p') : p = p' := by
  have h₀ : p.base ≫ q = p'.base ≫ q := congrArg (fun k => k ≫ q) hbase
  have hm : (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x =
      (pullback.congrHom h₀ (rfl : z = z)).hom ≫
        (pullbackBaseChangeIso q z p'.base).inv ≫ p'.morphism ≫ pullback.snd q x :=
    RelativeMorphism.morphism_eq_of_eq h h₀
  have hiso : (pullbackBaseChangeIso q z p.base).hom ≫
        (pullback.congrHom h₀ (rfl : z = z)).hom ≫
          (pullbackBaseChangeIso q z p'.base).inv =
      (pullback.congrHom hbase (rfl : pullback.fst q z = pullback.fst q z)).hom := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullbackBaseChangeIso_inv_fst, pullback.congrHom_hom_fst,
        pullbackBaseChangeIso_hom_fst]
    · calc (pullbackBaseChangeIso q z p.base).hom ≫
            (pullback.congrHom h₀ (rfl : z = z)).hom ≫
              (pullbackBaseChangeIso q z p'.base).inv ≫
                pullback.snd p'.base (pullback.fst q z) ≫ pullback.fst q z
          = (pullbackBaseChangeIso q z p.base).hom ≫
              (pullback.congrHom h₀ (rfl : z = z)).hom ≫
                (pullbackBaseChangeIso q z p'.base).inv ≫
                  pullback.fst p'.base (pullback.fst q z) ≫ p'.base := by
            rw [pullback.condition (f := p'.base) (g := pullback.fst q z)]
        _ = pullback.fst p.base (pullback.fst q z) ≫ p'.base := by
            simp only [pullbackBaseChangeIso_inv_fst_assoc, pullback.congrHom_hom_fst_assoc,
              pullbackBaseChangeIso_hom_fst_assoc]
        _ = pullback.snd p.base (pullback.fst q z) ≫ pullback.fst q z := by
            rw [← hbase]
            exact pullback.condition
        _ = ((pullback.congrHom hbase (rfl : pullback.fst q z = pullback.fst q z)).hom ≫
              pullback.snd p'.base (pullback.fst q z)) ≫ pullback.fst q z := by
            rw [pullback.congrHom_hom_snd]
    · simp only [Category.assoc, pullbackBaseChangeIso_inv_snd, pullback.congrHom_hom_snd,
        pullbackBaseChangeIso_hom_snd]
  refine RelativeMorphism.ext_of_base_eq hbase (pullback.hom_ext ?_ ?_)
  · rw [p.commutes, Category.assoc, p'.commutes, ← Category.assoc,
      pullback.congrHom_hom_snd]
  · calc p.morphism ≫ pullback.snd q x
        = (pullbackBaseChangeIso q z p.base).hom ≫
            (pullbackBaseChangeIso q z p.base).inv ≫ p.morphism ≫ pullback.snd q x := by
          rw [Iso.hom_inv_id_assoc]
      _ = (pullbackBaseChangeIso q z p.base).hom ≫
            (pullback.congrHom h₀ (rfl : z = z)).hom ≫
              (pullbackBaseChangeIso q z p'.base).inv ≫ p'.morphism ≫ pullback.snd q x := by
          rw [hm]
      _ = (pullback.congrHom hbase (rfl : pullback.fst q z = pullback.fst q z)).hom ≫
            p'.morphism ≫ pullback.snd q x :=
          congrArg (fun m => m ≫ p'.morphism ≫ pullback.snd q x) hiso

/-- **The two constructions are mutually inverse**, in the direction which rebuilds a pair for
the base-changed morphisms from the pair underlying it. -/
theorem RelativeMorphism.baseChange_ofBaseChange (q : Q' ⟶ Q)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    RelativeMorphism.baseChange q (RelativeMorphism.ofBaseChange q p) p.base
      (RelativeMorphism.ofBaseChange_base q p) = p :=
  RelativeMorphism.ofBaseChange_injective q rfl
    (RelativeMorphism.ofBaseChange_baseChange q (RelativeMorphism.ofBaseChange q p) p.base
      (RelativeMorphism.ofBaseChange_base q p))

/-! ### Compatibility with restriction of pairs -/

/-- **Forgetting the base change commutes with restriction of pairs.** -/
theorem RelativeMorphism.restrict_ofBaseChange (q : Q' ⟶ Q) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x) T) :
    RelativeMorphism.restrict t (RelativeMorphism.ofBaseChange q p) =
      RelativeMorphism.ofBaseChange q (RelativeMorphism.restrict t p) := by
  have key : pullback.map (t ≫ p.base ≫ q) z (p.base ≫ q) z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫
        (pullbackBaseChangeIso q z p.base).inv =
      (pullback.congrHom (Category.assoc t p.base q).symm (rfl : z = z)).hom ≫
        (pullbackBaseChangeIso q z (t ≫ p.base)).inv ≫
          pullback.map (t ≫ p.base) (pullback.fst q z) p.base (pullback.fst q z) t
            (𝟙 (pullback q z)) (𝟙 Q') (by simp) (by simp) := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp
    · simp only [Category.assoc]
      rw [← pullback.condition (f := p.base) (g := pullback.fst q z)]
      simp
    · simp
  refine RelativeMorphism.ext_of_base_eq (Category.assoc t p.base q).symm ?_
  exact congrArg (fun m => m ≫ p.morphism ≫ pullback.snd q x) key

/-- **Base change of pairs commutes with restriction of pairs.** -/
theorem RelativeMorphism.restrict_baseChange (q : Q' ⟶ Q) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x T) (a : T ⟶ Q') (ha : p.base = a ≫ q)
    (ha' : (RelativeMorphism.restrict t p).base = (t ≫ a) ≫ q) :
    RelativeMorphism.restrict t (RelativeMorphism.baseChange q p a ha) =
      RelativeMorphism.baseChange q (RelativeMorphism.restrict t p) (t ≫ a) ha' := by
  refine RelativeMorphism.ofBaseChange_injective q ?_ ?_
  · rw [RelativeMorphism.restrict_base, RelativeMorphism.baseChange_base,
      RelativeMorphism.baseChange_base]
  · rw [← RelativeMorphism.restrict_ofBaseChange, RelativeMorphism.ofBaseChange_baseChange,
      RelativeMorphism.ofBaseChange_baseChange]

end Pairs

/-! ### The cartesian square -/

section Functors

variable {Z X Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- **The top arrow `Mor_{Q'}(Z', X') ⟶ Mor_Q(Z, X)` of the square**: it sends a pair for the
base-changed morphisms to the pair of Stacks 05Y1 underlying it. -/
noncomputable def relativeHomOfBaseChange (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) :
    H'.functor ⟶ H.functor :=
  relativeHomOfPairs H (fun T p => RelativeMorphism.ofBaseChange q (H'.sections T.unop p))
    fun {T _U} f p => by
      rw [H'.sections_map_eq f p]
      exact (RelativeMorphism.restrict_ofBaseChange q (yoneda.map f.unop)
        (H'.sections T.unop p)).symm

/-- **The top arrow of the square, read on sections**: it forgets the base change. -/
@[simp] theorem sections_relativeHomOfBaseChange (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) (T : (BigFppfOver B S hS)ᵒᵖ) (p : H'.functor.obj T) :
    H.sections T.unop ((relativeHomOfBaseChange q H H').app T p) =
      RelativeMorphism.ofBaseChange q (H'.sections T.unop p) :=
  sections_relativeHomOfPairs H _ _ T p

/-- **The square commutes**: both arrows out of `Mor_{Q'}(Z', X')` read off the first component
of a pair, one of them after composing with `q`. -/
theorem relativeHomOfBaseChange_comp_projection (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) :
    relativeHomOfBaseChange q H H' ≫ H.projection = H'.projection ≫ q := by
  ext T p
  change H.projection.app T ((relativeHomOfBaseChange q H H').app T p) =
    q.app T (H'.projection.app T p)
  rw [H.projection_sections, sections_relativeHomOfBaseChange,
    RelativeMorphism.ofBaseChange_base, yonedaEquiv_comp, H'.projection_sections]

/-- **The first component of a pair of a morphism to `Mor_Q(Z, X)` factors through `q`**, as soon
as the morphism agrees with a morphism to `Q'` after composing with the projections. -/
theorem relativeHomBaseChange_base (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : W ⟶ H.functor) (a : W ⟶ Q') (hva : v ≫ H.projection = a ≫ q)
    (T : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj T) :
    (H.sections T.unop (v.app T w)).base = yonedaEquiv.symm (a.app T w) ≫ q := by
  refine (yonedaEquiv (X := T.unop) (F := Q)).injective ?_
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← H.projection_sections T.unop (v.app T w)]
  exact types_congr_hom (NatTrans.congr_app hva T) w

/-- **The morphism `W ⟶ Mor_{Q'}(Z', X')` determined by a morphism `W ⟶ Mor_Q(Z, X)` and a
morphism `W ⟶ Q'` whose first components agree.** This is the lift the cartesian square
provides. -/
noncomputable def relativeHomBaseChangeLift (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : W ⟶ H.functor) (a : W ⟶ Q') (hva : v ≫ H.projection = a ≫ q) : W ⟶ H'.functor :=
  relativeHomOfPairs H'
    (fun T w => RelativeMorphism.baseChange q (H.sections T.unop (v.app T w))
      (yonedaEquiv.symm (a.app T w)) (relativeHomBaseChange_base q H v a hva T w))
    fun {T U} f w => by
      have hp : H.sections U.unop (v.app U (W.map f w)) =
          RelativeMorphism.restrict (yoneda.map f.unop) (H.sections T.unop (v.app T w)) :=
        (congrArg (H.sections U.unop) (types_congr_hom (v.naturality f) w)).trans
          (H.sections_map_eq f (v.app T w))
      have hb : yonedaEquiv.symm (a.app U (W.map f w)) =
          yoneda.map f.unop ≫ yonedaEquiv.symm (a.app T w) :=
        (congrArg yonedaEquiv.symm (types_congr_hom (a.naturality f) w)).trans
          (yonedaEquiv_symm_naturality (a.app T w) f.unop)
      have ha' : (RelativeMorphism.restrict (yoneda.map f.unop)
            (H.sections T.unop (v.app T w))).base =
          (yoneda.map f.unop ≫ yonedaEquiv.symm (a.app T w)) ≫ q := by
        rw [RelativeMorphism.restrict_base, relativeHomBaseChange_base q H v a hva T w,
          Category.assoc]
      rw [RelativeMorphism.restrict_baseChange q (yoneda.map f.unop)
        (H.sections T.unop (v.app T w)) (yonedaEquiv.symm (a.app T w))
        (relativeHomBaseChange_base q H v a hva T w) ha']
      exact RelativeMorphism.baseChange_congr q hp hb _ _

/-- **The lift, read on sections.** -/
@[simp] theorem sections_relativeHomBaseChangeLift (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : W ⟶ H.functor) (a : W ⟶ Q') (hva : v ≫ H.projection = a ≫ q)
    (T : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj T) :
    H'.sections T.unop ((relativeHomBaseChangeLift q H H' v a hva).app T w) =
      RelativeMorphism.baseChange q (H.sections T.unop (v.app T w))
        (yonedaEquiv.symm (a.app T w)) (relativeHomBaseChange_base q H v a hva T w) :=
  sections_relativeHomOfPairs H' _ _ T w

/-- The lift composed with the top arrow of the square is the given morphism to
`Mor_Q(Z, X)`. -/
theorem relativeHomBaseChangeLift_comp (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : W ⟶ H.functor) (a : W ⟶ Q') (hva : v ≫ H.projection = a ≫ q) :
    relativeHomBaseChangeLift q H H' v a hva ≫ relativeHomOfBaseChange q H H' = v := by
  ext T w
  refine (H.sections T.unop).injective ?_
  change H.sections T.unop ((relativeHomOfBaseChange q H H').app T
      ((relativeHomBaseChangeLift q H H' v a hva).app T w)) = H.sections T.unop (v.app T w)
  rw [sections_relativeHomOfBaseChange, sections_relativeHomBaseChangeLift,
    RelativeMorphism.ofBaseChange_baseChange]

/-- The lift composed with the projection of `Mor_{Q'}(Z', X')` is the given morphism to
`Q'`. -/
theorem relativeHomBaseChangeLift_comp_projection (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v : W ⟶ H.functor) (a : W ⟶ Q') (hva : v ≫ H.projection = a ≫ q) :
    relativeHomBaseChangeLift q H H' v a hva ≫ H'.projection = a := by
  ext T w
  change H'.projection.app T ((relativeHomBaseChangeLift q H H' v a hva).app T w) = a.app T w
  rw [H'.projection_sections, sections_relativeHomBaseChangeLift,
    RelativeMorphism.baseChange_base, Equiv.apply_symm_apply]

/-- **The two arrows out of `Mor_{Q'}(Z', X')` are jointly monic**: a pair for the base-changed
morphisms is determined by its first component together with the pair of Stacks 05Y1 underlying
it. This is the uniqueness half of the cartesian square. -/
theorem relativeHom_baseChange_hom_ext (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {m₁ m₂ : W ⟶ H'.functor}
    (h₁ : m₁ ≫ relativeHomOfBaseChange q H H' = m₂ ≫ relativeHomOfBaseChange q H H')
    (h₂ : m₁ ≫ H'.projection = m₂ ≫ H'.projection) : m₁ = m₂ := by
  ext T w
  refine (H'.sections T.unop).injective (RelativeMorphism.ofBaseChange_injective q ?_ ?_)
  · refine (yonedaEquiv (X := T.unop) (F := Q')).injective ?_
    refine Eq.trans (H'.projection_sections T.unop (m₁.app T w)).symm ?_
    refine Eq.trans (types_congr_hom (NatTrans.congr_app h₂ T) w) ?_
    exact H'.projection_sections T.unop (m₂.app T w)
  · refine Eq.trans (sections_relativeHomOfBaseChange q H H' T (m₁.app T w)).symm ?_
    refine Eq.trans (congrArg (H.sections T.unop)
      (types_congr_hom (NatTrans.congr_app h₁ T) w)) ?_
    exact sections_relativeHomOfBaseChange q H H' T (m₂.app T w)

/-- **Stacks 05Y4.** Let `z : Z ⟶ Q`, `x : X ⟶ Q` and `q : Q' ⟶ Q` be morphisms of algebraic
spaces over `S`, and set `Z' = Q' ×_Q Z` and `X' = Q' ×_Q X`. Then

```text
Mor_{Q'}(Z', X') = Q' ×_Q Mor_Q(Z, X)
```

as presheaves on the big fppf site of `S`: the square formed by the two projections reading off
the first component of a pair of Stacks 05Y1, the morphism `q` and the morphism forgetting the
base change is cartesian.

This is the first step of the source's proof, the identification as functors. The identification
in `Sh((Sch/S)_fppf)` follows from it because the inclusion of fppf sheaves into presheaves
creates limits; that is
`AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange`, which carries the sheaf
property of the two relative morphism functors — part (1) of Stacks 05Y3 — as a hypothesis. -/
theorem isPullback_relativeHomOfBaseChange (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) :
    IsPullback H'.projection (relativeHomOfBaseChange q H H') q H.projection := by
  have hw := relativeHomOfBaseChange_comp_projection q H H'
  refine IsPullback.flip
    { w := hw
      isLimit' := ⟨PullbackCone.IsLimit.mk hw
        (fun s => relativeHomBaseChangeLift q H H' s.fst s.snd s.condition)
        (fun s => relativeHomBaseChangeLift_comp q H H' s.fst s.snd s.condition)
        (fun s => relativeHomBaseChangeLift_comp_projection q H H' s.fst s.snd s.condition)
        fun s m hm hm' => relativeHom_baseChange_hom_ext q H H'
          (hm.trans (relativeHomBaseChangeLift_comp q H H' s.fst s.snd s.condition).symm)
          (hm'.trans
            (relativeHomBaseChangeLift_comp_projection q H H' s.fst s.snd s.condition).symm)⟩ }

/-- **Stacks 05Y4**, as an identification of `Mor_{Q'}(Z', X')` with the fibre product
`Q' ×_Q Mor_Q(Z, X)`. -/
noncomputable def relativeHomBaseChangeIso (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x)) :
    H'.functor ≅ pullback q H.projection :=
  (isPullback_relativeHomOfBaseChange q H H').isoPullback

/-- **Stacks 05Y4.** The identification

```text
Mor_{Q'}(Z', X') = Q' ×_Q Mor_Q(Z, X)
```

**in `Sh((Sch/S)_fppf)`**: the square of fppf sheaves formed by the two projections reading off
the first component of a pair of Stacks 05Y1, the morphism `q` and the morphism forgetting the
base change is cartesian.

This is the source's statement. Its proof is the source's: the square of presheaves is
cartesian, which is `AlgebraicGeometry.Space.isPullback_relativeHomOfBaseChange`, and the
inclusion of fppf sheaves into presheaves creates limits, so a square of sheaves is cartesian as
soon as the underlying square of presheaves is. The sheaf property of the two relative morphism
functors is part (1) of Stacks 05Y3, which this library does not carry; it is taken as the
hypotheses `hH` and `hH'`, and nothing else about the two functors is assumed. The sheaf
property of `Q` and of `Q'` is automatic for algebraic spaces. -/
@[stacks 05Y4 "the identification in `Sh((Sch/S)_fppf)`, with the sheaf property of the two \
relative morphism functors — part (1) of the cited Stacks 05Y3 — carried as a hypothesis"]
theorem isPullback_sheaf_relativeHomOfBaseChange (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x))
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (hQ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q')
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H.functor)
    (hH' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H'.functor) :
    IsPullback
      (ObjectProperty.homMk H'.projection :
        (⟨H'.functor, hH'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q', hQ'⟩)
      (ObjectProperty.homMk (relativeHomOfBaseChange q H H') :
        (⟨H'.functor, hH'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨H.functor, hH⟩)
      (ObjectProperty.homMk q :
        (⟨Q', hQ'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q, hQ⟩)
      (ObjectProperty.homMk H.projection :
        (⟨H.functor, hH⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q, hQ⟩) :=
  IsPullback.of_map_of_faithful (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
    (isPullback_relativeHomOfBaseChange q H H')

/-- **Stacks 05Y4** read as an identification of fppf sheaves:
`Mor_{Q'}(Z', X') = Q' ×_Q Mor_Q(Z, X)` in `Sh((Sch/S)_fppf)`. The sheaf property of the two
relative morphism functors is part (1) of Stacks 05Y3 and is carried as a hypothesis. -/
noncomputable def relativeHomSheafBaseChangeIso (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x))
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (hQ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q')
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H.functor)
    (hH' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H'.functor) :
    (⟨H'.functor, hH'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ≅
      Limits.pullback
        (ObjectProperty.homMk q : (⟨Q', hQ'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨Q, hQ⟩)
        (ObjectProperty.homMk H.projection :
          (⟨H.functor, hH⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q, hQ⟩) :=
  (isPullback_sheaf_relativeHomOfBaseChange q H H' hQ hQ' hH hH').isoPullback

end Functors

/-- The identification of Stacks 05Y4 as presheaves, for the relative morphism functor of
Stacks 05Y2 and the fibre products of algebraic spaces of Stacks 02X2: for morphisms
`z : Z ⟶ Q`, `x : X ⟶ Q` and `q : Q' ⟶ Q` of algebraic spaces over `S`,

```text
Mor_{Q'}(Q' ×_Q Z, Q' ×_Q X) = Q' ×_Q Mor_Q(Z, X)
```

as presheaves on the big fppf site of `S`. The identification in `Sh((Sch/S)_fppf)`, which is
the source's statement, is
`AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange_relativeHomData`. -/
theorem isPullback_relativeHomOfBaseChange_relativeHomData {Z X Q Q' : AlgebraicSpaces B S hS}
    (z : Z ⟶ Q) (x : X ⟶ Q) (q : Q' ⟶ Q) :
    IsPullback
      (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
        (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
        (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
        (AlgebraicSpaces.fiberProduct B S hS q z).property
        (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property).projection
      (relativeHomOfBaseChange q.hom
        (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property)
        (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
          (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
          (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
          (AlgebraicSpaces.fiberProduct B S hS q z).property
          (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property))
      q.hom
      (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property
        Q.property).projection :=
  isPullback_relativeHomOfBaseChange _ _ _

/-- **Stacks 05Y4** for the relative morphism functor of Stacks 05Y2 and the fibre products of
algebraic spaces of Stacks 02X2: for morphisms `z : Z ⟶ Q`, `x : X ⟶ Q` and `q : Q' ⟶ Q` of
algebraic spaces over `S`,

```text
Mor_{Q'}(Q' ×_Q Z, Q' ×_Q X) = Q' ×_Q Mor_Q(Z, X)
```

**in `Sh((Sch/S)_fppf)`**. The sheaf property of the two relative morphism functors is part (1)
of Stacks 05Y3, which this library does not carry; it is taken as the hypotheses `hH` and `hH'`.
That `Q` and `Q'` are sheaves is part of being an algebraic space, so nothing else is assumed. -/
@[stacks 05Y4 "the identification in `Sh((Sch/S)_fppf)` for the functor of Stacks 05Y2 and the \
fibre products of Stacks 02X2, with the sheaf property of the two relative morphism functors — \
part (1) of the cited Stacks 05Y3 — carried as a hypothesis"]
theorem isPullback_sheaf_relativeHomOfBaseChange_relativeHomData
    {Z X Q Q' : AlgebraicSpaces B S hS} (z : Z ⟶ Q) (x : X ⟶ Q) (q : Q' ⟶ Q)
    (hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property
        Q.property).functor)
    (hH' : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
        (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
        (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
        (AlgebraicSpaces.fiberProduct B S hS q z).property
        (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property).functor) :
    IsPullback
      (ObjectProperty.homMk
        (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
          (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
          (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
          (AlgebraicSpaces.fiberProduct B S hS q z).property
          (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property).projection :
        (⟨_, hH'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨Q'.obj, Q'.property.isSheaf⟩)
      (ObjectProperty.homMk
        (relativeHomOfBaseChange q.hom
          (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property)
          (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
            (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
            (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
            (AlgebraicSpaces.fiberProduct B S hS q z).property
            (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property)) :
        (⟨_, hH'⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨_, hH⟩)
      (ObjectProperty.homMk q.hom :
        (⟨Q'.obj, Q'.property.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨Q.obj, Q.property.isSheaf⟩)
      (ObjectProperty.homMk
        (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property
          Q.property).projection :
        (⟨_, hH⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨Q.obj, Q.property.isSheaf⟩) :=
  isPullback_sheaf_relativeHomOfBaseChange q.hom _ _ Q.property.isSheaf Q'.property.isSheaf hH hH'

/-! ### Discharging the sheaf hypotheses -/

/-- **Any realization of the relative morphism functor is isomorphic to the one of
Stacks 05Y2.** The identification of the sections of a realization with the pairs of
Stacks 05Y1 is natural
(`AlgebraicGeometry.Space.RelativeHomConstruction.sections_map_eq`), so composing the two
identifications gives an isomorphism of presheaves. -/
noncomputable def RelativeHomConstruction.isoRelativeHom
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (H : RelativeHomConstruction B S hS Z X Q z x) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hQ : IsAlgebraicSpace B S hS Q) :
    H.functor ≅ relativeHom B S hS Z X Q z x hZ hX hQ :=
  NatIso.ofComponents
    (fun T => Equiv.toIso ((H.sections T.unop).trans
      (relativeHomSections B S hS Z X Q z x hZ hX hQ T.unop).symm))
    fun {T U} f => by
      apply ConcreteCategory.ext
      ext p
      refine (relativeHomSections B S hS Z X Q z x hZ hX hQ U.unop).injective ?_
      have hL : relativeHomSections B S hS Z X Q z x hZ hX hQ U.unop
          ((relativeHomSections B S hS Z X Q z x hZ hX hQ U.unop).symm
            (H.sections U.unop (H.functor.map f p))) =
          RelativeMorphism.restrict (yoneda.map f.unop) (H.sections T.unop p) := by
        rw [Equiv.apply_symm_apply, H.sections_map_eq]
      have hR := relativeHomSections_map B S hS Z X Q z x hZ hX hQ f.unop
        ((relativeHomSections B S hS Z X Q z x hZ hX hQ T.unop).symm (H.sections T.unop p))
      rw [Equiv.apply_symm_apply] at hR
      exact hL.trans hR.symm

/-- **Part (1) of Stacks 05Y3 for an arbitrary realization of the relative morphism
functor**: it is a sheaf on the big fppf site of `S`, because it is isomorphic to the functor
of Stacks 05Y2, which is a sheaf by
`AlgebraicGeometry.Space.isSheaf_relativeHom`. This is what discharges the hypotheses `hH` and
`hH'` of `AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange`. -/
theorem RelativeHomConstruction.isSheaf_functor
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (H : RelativeHomConstruction B S hS Z X Q z x) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hQ : IsAlgebraicSpace B S hS Q) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) H.functor :=
  (Presheaf.isSheaf_of_iso_iff (H.isoRelativeHom hZ hX hQ)).mpr
    (isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ)

section Unconditional

variable {Z X Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- **Stacks 05Y4**, unconditionally. The identification

```text
Mor_{Q'}(Z', X') = Q' ×_Q Mor_Q(Z, X)
```

**in `Sh((Sch/S)_fppf)`**, for arbitrary realizations of the two relative morphism functors.
This is `AlgebraicGeometry.Space.isPullback_sheaf_relativeHomOfBaseChange` with its two sheaf
hypotheses discharged by part (1) of Stacks 05Y3, in the form
`AlgebraicGeometry.Space.RelativeHomConstruction.isSheaf_functor`; the algebraicity of the
sources and of the two bases is all that remains. -/
@[stacks 05Y4 "the identification in `Sh((Sch/S)_fppf)`"]
theorem isPullback_sheaf_relativeHomOfBaseChange_of_isAlgebraicSpace (q : Q' ⟶ Q)
    (H : RelativeHomConstruction B S hS Z X Q z x)
    (H' : RelativeHomConstruction B S hS (pullback q z) (pullback q x) Q'
      (pullback.fst q z) (pullback.fst q x))
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (hQ' : IsAlgebraicSpace B S hS Q')
    (hZ' : IsAlgebraicSpace B S hS (pullback q z))
    (hX' : IsAlgebraicSpace B S hS (pullback q x)) :
    IsPullback
      (ObjectProperty.homMk H'.projection :
        (⟨H'.functor, H'.isSheaf_functor hZ' hX' hQ'⟩ :
          Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q', hQ'.isSheaf⟩)
      (ObjectProperty.homMk (relativeHomOfBaseChange q H H') :
        (⟨H'.functor, H'.isSheaf_functor hZ' hX' hQ'⟩ :
            Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨H.functor, H.isSheaf_functor hZ hX hQ⟩)
      (ObjectProperty.homMk q :
        (⟨Q', hQ'.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q, hQ.isSheaf⟩)
      (ObjectProperty.homMk H.projection :
        (⟨H.functor, H.isSheaf_functor hZ hX hQ⟩ :
          Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨Q, hQ.isSheaf⟩) :=
  isPullback_sheaf_relativeHomOfBaseChange q H H' hQ.isSheaf hQ'.isSheaf
    (H.isSheaf_functor hZ hX hQ) (H'.isSheaf_functor hZ' hX' hQ')

end Unconditional

variable (B S hS) in
/-- **Stacks 05Y4**, unconditionally, for the relative morphism functor of Stacks 05Y2 and the
fibre products of algebraic spaces of Stacks 02X2: for morphisms `z : Z ⟶ Q`, `x : X ⟶ Q` and
`q : Q' ⟶ Q` of algebraic spaces over `S`,

```text
Mor_{Q'}(Q' ×_Q Z, Q' ×_Q X) = Q' ×_Q Mor_Q(Z, X)
```

**in `Sh((Sch/S)_fppf)`**. This is the source's statement with nothing assumed: the sheaf
property of the two relative morphism functors is part (1) of Stacks 05Y3,
`AlgebraicGeometry.Space.isSheaf_relativeHom`. -/
@[stacks 05Y4 "the identification in `Sh((Sch/S)_fppf)` for the functor of Stacks 05Y2 and the \
fibre products of Stacks 02X2"]
theorem isPullback_relativeHomSheafOfBaseChange {Z X Q Q' : AlgebraicSpaces B S hS}
    (z : Z ⟶ Q) (x : X ⟶ Q) (q : Q' ⟶ Q) :
    IsPullback
      (ObjectProperty.homMk
        (relativeHomProjection B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
          (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
          (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
          (AlgebraicSpaces.fiberProduct B S hS q z).property
          (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property) :
        relativeHomSheaf B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
            (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
            (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
            (AlgebraicSpaces.fiberProduct B S hS q z).property
            (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property ⟶
          ⟨Q'.obj, Q'.property.isSheaf⟩)
      (ObjectProperty.homMk
        (relativeHomOfBaseChange q.hom
          (relativeHomData B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property)
          (relativeHomData B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
            (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
            (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
            (AlgebraicSpaces.fiberProduct B S hS q z).property
            (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property)) :
        relativeHomSheaf B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
            (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
            (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
            (AlgebraicSpaces.fiberProduct B S hS q z).property
            (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property ⟶
          relativeHomSheaf B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property)
      (ObjectProperty.homMk q.hom :
        (⟨Q'.obj, Q'.property.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨Q.obj, Q.property.isSheaf⟩)
      (ObjectProperty.homMk
        (relativeHomProjection B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property
          Q.property) :
        relativeHomSheaf B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property ⟶
          ⟨Q.obj, Q.property.isSheaf⟩) :=
  isPullback_sheaf_relativeHomOfBaseChange_relativeHomData z x q
    (isSheaf_relativeHom B S hS Z.obj X.obj Q.obj z.hom x.hom Z.property X.property Q.property)
    (isSheaf_relativeHom B S hS (AlgebraicSpaces.fiberProduct B S hS q z).obj
      (AlgebraicSpaces.fiberProduct B S hS q x).obj Q'.obj
      (pullback.fst q.hom z.hom) (pullback.fst q.hom x.hom)
      (AlgebraicSpaces.fiberProduct B S hS q z).property
      (AlgebraicSpaces.fiberProduct B S hS q x).property Q'.property)

end AlgebraicGeometry.Space

end
