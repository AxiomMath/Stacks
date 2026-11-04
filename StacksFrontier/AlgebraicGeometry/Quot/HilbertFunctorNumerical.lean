module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor

/-!
# The Hilbert functor with prescribed numerical invariants (Stacks 0DPG)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
separated and of finite presentation — the standing hypothesis of the source's section on the
properties of the Hilbert functor, under which `Hilb_{X/Y}` is an algebraic space locally of
finite presentation over `Y` (Stacks 0D01).  Stacks 0DPG fixes a set `I`, a perfect object
`E i ∈ D(𝒪_X)` for each `i ∈ I` and prescribed invariants `P : I → ℤ`, and *defines*

`Hilb^P_{X/Y} = Quot^P_{𝒪_X/X/Y}`

through the identification `Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` of Quot, Lemma 0D00, where
`Quot^P_{𝒪_X/X/Y}` is the fibre product `Quot_{𝒪_X/X/Y} ×_{Coh_{X/Y}} Coh^P_{X/Y}` of
Remark 0DP6.  It then asserts that `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` is a flat closed immersion, and
an open and closed immersion when `I` is finite, or `Y` is locally Noetherian, or `I = ℤ` and
`E i = L^{⊗ i}` for an invertible `𝒪_X`-module `L` — in which case the notation is
`Hilb^{P, L}_{X/Y}`.

**Stacks 0DPG is a definition, not a proof obligation.**  What is formalized here is that
definition, carried out directly on the Hilbert functor of Stacks 0CZY rather than as a fibre
product: a family classified by `Hilb_{X/Y}` over a test scheme `T` lies in `Hilb^P_{X/Y}(T)`
exactly when its fibrewise invariants are the prescribed ones at every point of `T`, and the
subfunctor so cut out is the source's `Hilb^P_{X/Y}`.  That is the same subfunctor the fibre
product computes, and it is available here while the fibre product is not; see "What is and is
not proved".

## Main definitions

* `AlgebraicGeometry.Space.HilbertEulerData`: the fibrewise numerical invariants of the families
  classified by the Hilbert functor, as data, together with their compatibility with base change.
* `AlgebraicGeometry.Space.HilbertEulerData.IsPrescribed`: the membership condition of
  Stacks 0DPG — the invariants of the family are the prescribed `P` at every point of the test
  scheme.
* `AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertFunctor`: **Stacks 0DPG**, the functor
  `Hilb^P_{X/Y}`.
* `AlgebraicGeometry.Space.HilbertEulerData.numericalHilbertInclusion`: **Stacks 0DPG**, the
  morphism `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}`.

## Main results

* `AlgebraicGeometry.Space.HilbertEulerData.isPrescribed_baseChange`: the membership condition is
  stable under base change, which is what makes `Hilb^P_{X/Y}` a subfunctor at all.
* `AlgebraicGeometry.Space.HilbertEulerData.mono_numericalHilbertInclusion`: the morphism
  `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` is a monomorphism.
* `AlgebraicGeometry.Space.HilbertEulerData.not_isPrescribed_of_ne`: distinct prescribed
  invariants cut out subfunctors with no common family over a test scheme that has a point.

## Implementation notes

**Why the invariants are data.**  The source's condition on a family `Z ⊆ X_T` is
`χ(X_t, E_{i,t} ⊗^𝐋 (i_*𝒪_Z)_t) = P i` for every `i ∈ I` and every `t ∈ T`.  The Euler
characteristic of a perfect object on an algebraic space is not constructible in this
development — the obstruction is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/NumericalInvariants.lean` — so the family of fibrewise
invariants is *given*, exactly as `AlgebraicGeometry.Space.IsPrescribedTwistedEuler` of
Stacks 0DNF and `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreChi` give theirs.  The
compatibility `χ_baseChange` with base change is the only property of the invariants the
definition uses, and it is the fibrewise statement that an invariant of a family depends only on
the fibre; it is what makes the condition stable under base change.

**The indexing data `I`, `E` and `P` of the source.**  The index set `I` and the prescribed
`P : I → ℤ` appear below; the perfect objects `E i ∈ D(𝒪_X)` appear only through the invariants
they define, which is what `HilbertEulerData` records.  The standing data of Stacks 0DNC, with
the perfect objects themselves, is `AlgebraicGeometry.Space.NumericalSituation`, and its
specialisation to `I = ℤ` and `E i = L^{⊗ i}` — the case in which the source writes
`Hilb^{P, L}_{X/Y}` — is `AlgebraicGeometry.Space.NumericalSituation.ofInvertibleTwists`, built
from `AlgebraicGeometry.Space.invertibleTwistObject`.  Supplying a `HilbertEulerData` from that
situation is exactly what the absent Euler characteristic would do.

## What is and is not proved

Proved: the definition of `Hilb^P_{X/Y}` as a subfunctor of `Hilb_{X/Y}`, the morphism
`Hilb^P_{X/Y} ⟶ Hilb_{X/Y}`, the stability of the membership condition under base change, that
the morphism is a monomorphism, and the disjointness of the subfunctors for distinct `P`.

Not proved, and therefore not claimed by the tag:

* the identification `Hilb^P_{X/Y} = Quot^P_{𝒪_X/X/Y}` with the fibre product of Remark 0DP6.
  That fibre product is not formed in this development and cannot be: `Coh^P_{X/Y}` does not
  exist here, only the standing data of Stacks 0DNC and the membership condition of Stacks 0DNF,
  as the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStack.lean` record.  Nor is the
  identification `Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` of Quot, Lemma 0D00 available: it is carried as a
  hypothesis wherever this development needs it, as in
  `AlgebraicGeometry.Space.exists_hilbertPresheafModel_isAlgebraicSpace`.
* that `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` is a **flat closed immersion**, and an **open and closed
  immersion** in the three listed cases.  The source attributes both to the corresponding
  assertion of Remark 0DP6, which rests on Lemmas 0DND and 0DNE; neither is present in this
  development, as the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Quot/NumericalInvariantsTwist.lean` record.  What is proved
  below is that the morphism is a monomorphism, which is the part of "closed immersion" that
  holds of a subfunctor inclusion; nothing here makes closedness or openness true by fiat.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe v u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The fibrewise numerical invariants of the families classified by the Hilbert functor of
`f : X ⟶ Y`, indexed by a set `I`.

For a test scheme `T` over `Y`, a family `z` classified by `Hilb_{X/Y}` over `T`, a point `t` of
`T` and an index `i ∈ I`, the integer `χ T z t i` stands for the Euler characteristic
`χ(X_t, E_{i,t} ⊗^𝐋 (i_*𝒪_{Z})_t)` of the source, for the perfect object `E i ∈ D(𝒪_X)` the
source fixes.  The invariants are data rather than a construction because that Euler
characteristic cannot be constructed in this development; the single field `χ_baseChange` is the
fibrewise compatibility the source's condition has, namely that the invariant at a point of a
base change is the invariant of the original family at the image point. -/
structure HilbertEulerData (f : X ⟶ Y) (I : Type v) where
  /-- The invariant of index `i` of the family `z` at the point `t` of the test scheme. -/
  χ : ∀ T : SchemesOverPresheaf B S hS Y, HilbertFamily f T →
    ((BigFppfOver.toScheme B S hS).obj T.left) → I → ℤ
  /-- The invariants are fibrewise: the invariant of a base change at a point is the invariant of
  the original family at the image point. -/
  χ_baseChange : ∀ {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (z : HilbertFamily f T)
    (t : (BigFppfOver.toScheme B S hS).obj T'.left) (i : I),
    χ T' (z.baseChange g) t i = χ T z (((BigFppfOver.toScheme B S hS).map g.left).base t) i

namespace HilbertEulerData

variable {f : X ⟶ Y} {I : Type v} (χd : HilbertEulerData f I) (P : I → ℤ)

/-- **Stacks 0DPG, the membership condition.**  A family `z` classified by `Hilb_{X/Y}` over a
test scheme `T` lies in `Hilb^P_{X/Y}(T)` exactly when each of its invariants is the prescribed
one at every point of `T`, that is, when `χ(X_t, E_{i,t} ⊗^𝐋 (i_*𝒪_Z)_t) = P i` for all `i` and
all `t ∈ T`. -/
def IsPrescribed {T : SchemesOverPresheaf B S hS Y} (z : HilbertFamily f T) : Prop :=
  ∀ (t : (BigFppfOver.toScheme B S hS).obj T.left) (i : I), χd.χ T z t i = P i

/-- The membership condition is stable under base change: the invariants of the base change of a
family are the invariants of the family at the image points, so prescribing them is a condition
on the family that its base changes inherit.  This is what makes `Hilb^P_{X/Y}` a subfunctor of
`Hilb_{X/Y}`. -/
theorem isPrescribed_baseChange {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T)
    (z : HilbertFamily f T) (h : χd.IsPrescribed P z) :
    χd.IsPrescribed P (z.baseChange g) :=
  fun t i => (χd.χ_baseChange g z t i).trans (h _ i)

/-- **Stacks 0DPG.** The functor `Hilb^P_{X/Y}`: it sends a test scheme `T` over `Y` to the set
of families classified by `Hilb_{X/Y}` over `T` whose fibrewise invariants are the prescribed
`P`, and a morphism of test schemes to base change of those families, which is well defined by
`AlgebraicGeometry.Space.HilbertEulerData.isPrescribed_baseChange`.

This is the source's `Hilb^P_{X/Y} = Quot^P_{𝒪_X/X/Y}`, formed directly as the subfunctor of the
Hilbert functor that the fibre product of Remark 0DP6 computes; that fibre product itself is not
available here, since `Coh^P_{X/Y}` is not constructed in this development. -/
@[stacks 0DPG "the definition of `Hilb^P_{X/Y}`, as the subfunctor of `Hilb_{X/Y}` of families \
whose fibrewise invariants are the prescribed ones; the fibre product \
`Quot_{𝒪_X/X/Y} ×_{Coh_{X/Y}} Coh^P_{X/Y}` of Remark 0DP6 and the identification \
`Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` of Lemma 0D00 are not available in this development"]
def numericalHilbertFunctor : (SchemesOverPresheaf B S hS Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := { z : HilbertFamily f T.unop // χd.IsPrescribed P z }
  map g := ↾fun z => ⟨z.1.baseChange g.unop, χd.isPrescribed_baseChange P g.unop z.1 z.2⟩
  map_id T := ConcreteCategory.hom_ext _ _ fun z => Subtype.ext (z.1.baseChange_id T.unop)
  map_comp g h := ConcreteCategory.hom_ext _ _ fun z =>
    Subtype.ext (z.1.baseChange_comp g.unop h.unop).symm

/-- The value of `Hilb^P_{X/Y}` at a test scheme is the set of families there whose invariants
are the prescribed ones. -/
theorem numericalHilbertFunctor_obj (T : SchemesOverPresheaf B S hS Y) :
    (χd.numericalHilbertFunctor P).obj (Opposite.op T) =
      { z : HilbertFamily f T // χd.IsPrescribed P z } :=
  rfl

/-- **Stacks 0DPG.** The morphism `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}`: a family with the prescribed
invariants is in particular a family.  The source asserts that this morphism is a flat closed
immersion, and an open and closed immersion in three listed cases; neither assertion is proved
here, both resting on Lemmas 0DND and 0DNE, which are absent.  What is proved is that it is a
monomorphism, `AlgebraicGeometry.Space.HilbertEulerData.mono_numericalHilbertInclusion`. -/
@[stacks 0DPG "the morphism `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}`, proved to be a monomorphism; that it \
is a flat closed immersion, and an open and closed immersion for `I` finite, `Y` locally \
Noetherian, or `I = ℤ` with `E i = L^{⊗ i}`, rests on Lemmas 0DND and 0DNE and is not proved"]
def numericalHilbertInclusion : χd.numericalHilbertFunctor P ⟶ hilbertFunctor f where
  app _ := ↾fun z => z.1
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ => rfl

/-- The morphism `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` forgets the prescription of the invariants. -/
@[simp]
theorem numericalHilbertInclusion_app_apply (T : (SchemesOverPresheaf B S hS Y)ᵒᵖ)
    (z : (χd.numericalHilbertFunctor P).obj T) :
    (χd.numericalHilbertInclusion P).app T z = z.1 :=
  rfl

/-- Each component of `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` is injective: a family determines the subtype
element carrying it, the prescription of the invariants being a proposition. -/
theorem injective_numericalHilbertInclusion_app (T : (SchemesOverPresheaf B S hS Y)ᵒᵖ) :
    Function.Injective ((χd.numericalHilbertInclusion P).app T) :=
  fun _ _ h => Subtype.ext h

/-- **The morphism `Hilb^P_{X/Y} ⟶ Hilb_{X/Y}` is a monomorphism.**  This is the part of the
source's "flat closed immersion" that a subfunctor inclusion carries unconditionally; closedness,
flatness and the openness of the three listed cases are not proved here. -/
theorem mono_numericalHilbertInclusion : Mono (χd.numericalHilbertInclusion P) := by
  have : ∀ T, Mono ((χd.numericalHilbertInclusion P).app T) := fun T =>
    (mono_iff_injective _).2 (χd.injective_numericalHilbertInclusion_app P T)
  exact NatTrans.mono_of_mono_app _

/-- **Distinct prescribed invariants cut out subfunctors with no family in common**, over a test
scheme that has a point: the invariants of a family at a point determine the prescription they
satisfy.  This is the disjointness underlying the source's decomposition of `Hilb_{X/Y}` into the
`Hilb^P_{X/Y}`; the decomposition itself is not proved here, resting on Stacks 0DN4. -/
theorem not_isPrescribed_of_ne {P P' : I → ℤ} (hP : P ≠ P')
    {T : SchemesOverPresheaf B S hS Y} (t : (BigFppfOver.toScheme B S hS).obj T.left)
    (z : HilbertFamily f T) (h : χd.IsPrescribed P z) (h' : χd.IsPrescribed P' z) : False :=
  hP (funext fun i => (h t i).symm.trans (h' t i))

end HilbertEulerData

end AlgebraicGeometry.Space

end
