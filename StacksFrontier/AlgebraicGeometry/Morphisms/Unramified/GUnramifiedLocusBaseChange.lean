module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
import StacksCore.Tactic.StacksAttribute

/-!
# The G-unramified locus, and base change of both unramified loci

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let

```
T = {x ∈ X | X_{f x} is unramified over κ(f x) at x}
  = {x ∈ X | X is unramified over S at x}
```

be the set of [Stacks, Tag 0475]. This file proves the two statements of that tag that the
pointwise base-change lemma leaves open: that the two descriptions of `T` agree as sets, and that
`T` commutes with arbitrary base change in the set form `T' = (g')⁻¹ T`. It then proves the
tag's second half, which replaces `T` by the locus of points where `f` is G-unramified and
strengthens "locally of finite type" to "locally of finite presentation".

The second half rests on the G-unramified clause of [Stacks, Tag 02GF], which is proved here as
well: for `f` locally of finite presentation, `f` is G-unramified at `x` exactly when it is
unramified at `x`, so the G-unramified locus of such an `f` *is* the set `T`. That clause is the
"(resp. G-unramified)" reading of condition (1) of Tag 02GF, whose other conditions are unchanged
between the two readings, and it is what makes the source's one-line deduction of the second half
from the first work.

## Main results

* `AlgebraicGeometry.gUnramifiedAt_iff_unramifiedAt`: for a morphism locally of finite
  presentation, G-unramifiedness at a point is unramifiedness at that point.
* `AlgebraicGeometry.gUnramifiedAt_tfae`: the G-unramified reading of the equivalent conditions
  of Tag 02GF.
* `AlgebraicGeometry.setOf_unramifiedAt_fiber_eq_setOf_unramifiedAt` and
  `AlgebraicGeometry.setOf_unramifiedAt_fiber_eq_setOf_gUnramifiedAt`: the two descriptions of
  `T` agree, in the locally-of-finite-type and the locally-of-finite-presentation reading.
* `AlgebraicGeometry.setOf_unramifiedAt_eq_preimage_of_isPullback` and
  `AlgebraicGeometry.setOf_gUnramifiedAt_eq_preimage_of_isPullback`: `T' = (g')⁻¹ T` for the
  unramified and the G-unramified locus.
* `AlgebraicGeometry.gUnramifiedAt_iff_of_isPullback`: the pointwise form of the latter.

## Implementation notes

`AlgebraicGeometry.GUnramifiedAt` and `AlgebraicGeometry.UnramifiedAt` are both stated as the
existence of an affine chart on which the map of sections is G-unramified, respectively
unramified, and the two notions on rings differ only in finite presentation versus finite type.
So one chart serves both directions of `gUnramifiedAt_iff_unramifiedAt`: a G-unramified chart is
unramified because finite presentation implies finite type, and an unramified chart is
G-unramified because `AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE`
supplies finite presentation of the map of sections on *any* pair of affine opens, in particular
on the chart already in hand. No shrinking of the chart and no Noetherian hypothesis is involved;
this is weaker than
`AlgebraicGeometry.gUnramifiedAt_of_unramifiedAt`, which gets finite presentation from a
Noetherian target instead.

Both base-change statements reduce to
`AlgebraicGeometry.unramifiedAt_iff_of_isPullback`, the pointwise unramified case, which already
assumes nothing but local finite type of `f`; local finite presentation of the base-changed
morphism comes from the square by
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`, so it is not assumed.

The equality of the two descriptions of `T` is the equivalence of conditions (1) and (2) of Tag
02GF, `AlgebraicGeometry.unramifiedAt_iff_unramifiedAt_fiberToSpecResidueField`, read as an
equality of sets. The fibre condition is spelled with `AlgebraicGeometry.UnramifiedAt` and not
with its G-variant in both readings: the fibre lies over a field, where finite type and finite
presentation agree, and correspondingly the source leaves conditions (2)–(6) of Tag 02GF
untouched when passing to the G-unramified reading.

## References

* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
-/

@[expose] public section

open CategoryTheory
open Stacks.SmoothAtJacobian

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### The G-unramified clause of Tag 02GF -/

/-- **Stacks Project, Tag 02GF, the G-unramified clause.** A morphism of schemes locally of
finite presentation is G-unramified at a point exactly when it is unramified there: the affine
chart witnessing either notion witnesses the other, local finite presentation of the morphism
supplying finite presentation of the map of sections. -/
@[stacks 02GF "the G-unramified reading of condition (1): for `f` locally of finite presentation,
G-unramified at `x` is equivalent to unramified at `x`"]
public theorem gUnramifiedAt_iff_unramifiedAt (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) : GUnramifiedAt f x ↔ UnramifiedAt f x := by
  refine ⟨fun ⟨U, hU, hxU, V, hV, e, halg⟩ ↦ ⟨U, hU, hxU, V, hV, e, ?_⟩,
    fun ⟨U, hU, hxU, V, hV, e, halg⟩ ↦ ⟨U, hU, hxU, V, hV, e, ?_⟩⟩
  · let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have _ : Algebra.FinitePresentation Γ(S, V) Γ(X, U) := halg.finitePresentation
    exact ⟨halg.formallyUnramified, Algebra.FiniteType.of_finitePresentation⟩
  · let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    exact ⟨halg.formallyUnramified,
      RingHom.finitePresentation_algebraMap.mp (f.finitePresentation_appLE hV hU e)⟩

/-- **Stacks Project, Tag 02GF, the G-unramified reading.** For a morphism of schemes `f : X ⟶ S`
locally of finite presentation and a point `x` of `X` with image `s = f x`, the following are
equivalent: `f` is G-unramified at `x`; `f` is unramified at `x`; the fibre `X_s` is unramified
over `κ(s)` at `x`; the `𝒪_{X,x}`-module `Ω_{X/S,x}` is zero; the `𝒪_{X_s,x}`-module
`Ω_{X_s/s,x}` is zero; the `κ(x)`-vector space `Ω_{X_s/s,x} ⊗ κ(x) = Ω_{X/S,x} ⊗ κ(x)` is zero,
in either of its two canonically identified spellings; and `𝔪_s 𝒪_{X,x} = 𝔪_x` with
`κ(x)/κ(s)` finite separable. -/
@[stacks 02GF "the `resp. G-unramified` reading, under local finite presentation; the unramified
reading is `AlgebraicGeometry.unramifiedAt_tfae`"]
public theorem gUnramifiedAt_tfae (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    List.TFAE [
      GUnramifiedAt f x,
      UnramifiedAt f x,
      UnramifiedAt (f.fiberToSpecResidueField (f x)) (f.asFiber x),
      Subsingleton (relativeDifferentialStalk f x),
      Subsingleton (relativeDifferentialStalk (f.fiberToSpecResidueField (f x))
        (f.asFiber x)),
      Subsingleton (fiberRelativeCotangentSpace f x),
      Subsingleton (relativeCotangentSpace f x),
      Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (letI := (f.residueFieldMap x).hom.toAlgebra
         Module.Finite (S.residueField (f x)) (X.residueField x) ∧
           Algebra.IsSeparable (S.residueField (f x)) (X.residueField x))] := by
  have hU := unramifiedAt_tfae f x
  refine List.tfae_of_forall (b := UnramifiedAt f x) ?_
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gUnramifiedAt_iff_unramifiedAt f x
  · exact Iff.rfl
  · exact hU.out 2 1
  · exact hU.out 3 1
  · exact hU.out 4 1
  · exact hU.out 5 1
  · exact hU.out 6 1
  · exact hU.out 7 1

/-! ### The two descriptions of the unramified locus -/

/-- **Stacks Project, Tag 0475, the equality of the two descriptions of `T`.** For a morphism of
schemes locally of finite type, the set of points at which the scheme-theoretic fibre is
unramified over the residue field of its image is the set of points at which the morphism itself
is unramified. -/
@[stacks 0475 "the two descriptions of `T` agree, locally-of-finite-type reading",
  ega "IV 17.4.1" "more general",
  ega "IV 17.8.1" "case Y = S",
  sga "1 I 5.8" "Net clause, special case",
  sga "3 VIB 2.7" "(iii) ⇔ (iv)"]
public theorem setOf_unramifiedAt_fiber_eq_setOf_unramifiedAt (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    {x : X | UnramifiedAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)} =
      {x : X | UnramifiedAt f x} :=
  Set.ext fun x ↦ (unramifiedAt_iff_unramifiedAt_fiberToSpecResidueField f x).symm

/-- **Stacks Project, Tag 0475, the equality of the two descriptions of `T`, G-unramified
reading.** For a morphism of schemes locally of finite presentation, the set of points at which
the scheme-theoretic fibre is unramified over the residue field of its image is the set of points
at which the morphism itself is G-unramified. Hence that set is the open G-unramified locus, which
is what makes the second half of the tag follow from the first. -/
@[stacks 0475 "the two descriptions of `T` agree in the locally-of-finite-presentation reading,
identifying `T` with the G-unramified locus",
  ega "IV 17.4.1",
  ega "IV 17.8.1" "case Y = S",
  sga "1 I 5.8" "Net clause, special case",
  sga "3 VIB 2.7" "(iii) ⇔ (iv)"]
public theorem setOf_unramifiedAt_fiber_eq_setOf_gUnramifiedAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    {x : X | UnramifiedAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)} =
      {x : X | GUnramifiedAt f x} :=
  Set.ext fun x ↦
    (unramifiedAt_iff_unramifiedAt_fiberToSpecResidueField f x).symm.trans
      (gUnramifiedAt_iff_unramifiedAt f x).symm

/-! ### Base change of the two loci -/

/-- **Stacks Project, Tag 0475, the base-change half in set form.** Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes with `f : X ⟶ S` locally of finite type and `f' : X' ⟶ S'` the
base change of `f` along `g : S' ⟶ S`. Then the unramified locus `T'` of `f'` is the inverse
image under `g' : X' ⟶ X` of the unramified locus `T` of `f`. -/
@[stacks 0475 "`T' = (g')⁻¹ T` in set form, for the unramified locus",
  ega "IV 17.7.2" "more general"]
public theorem setOf_unramifiedAt_eq_preimage_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    {x' : X' | UnramifiedAt f' x'} = g'.base ⁻¹' {x : X | UnramifiedAt f x} :=
  Set.ext fun x' ↦ (unramifiedAt_iff_of_isPullback sq x').symm

/-- **Stacks Project, Tag 0475, the base-change half for the G-unramified locus, pointwise.** Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes with `f : X ⟶ S` locally of finite presentation and
`f' : X' ⟶ S'` the base change of `f` along `g : S' ⟶ S`. A point `x'` of `X'` is a point of
G-unramifiedness of `f'` if and only if its image `g' x'` in `X` is a point of G-unramifiedness
of `f`. -/
@[stacks 0475 "base change of the G-unramified locus, pointwise",
  sga "1 I 3.5" "more general",
  sga "3 XI 1.3" "more general"]
public theorem gUnramifiedAt_iff_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) [LocallyOfFinitePresentation f] (x' : X') :
    GUnramifiedAt f (g'.base x') ↔ GUnramifiedAt f' x' := by
  have _ : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFinitePresentation f›
  rw [gUnramifiedAt_iff_unramifiedAt f (g'.base x'), gUnramifiedAt_iff_unramifiedAt f' x']
  exact unramifiedAt_iff_of_isPullback sq x'

/-- **Stacks Project, Tag 0475, the second half in set form.** For a cartesian diagram of schemes
with `f : X ⟶ S` locally of finite presentation, the G-unramified locus of the base change
`f' : X' ⟶ S'` is the inverse image under `g' : X' ⟶ X` of the G-unramified locus of `f`. -/
@[stacks 0475 "`T' = (g')⁻¹ T` in set form, for the G-unramified locus, under local finite
presentation"]
public theorem setOf_gUnramifiedAt_eq_preimage_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) [LocallyOfFinitePresentation f] :
    {x' : X' | GUnramifiedAt f' x'} = g'.base ⁻¹' {x : X | GUnramifiedAt f x} :=
  Set.ext fun x' ↦ (gUnramifiedAt_iff_of_isPullback sq x').symm

end AlgebraicGeometry

end
