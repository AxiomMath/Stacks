module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective

/-!
# Stacks Tag 07RM: a quasi-projective morphism is an open subscheme of a projective one

Stacks Tag 07RM (Morphisms, Lemma 29.43.12) says that a quasi-projective morphism `f : X ⟶ S`
with `S` quasi-compact and quasi-separated factors as `X ⟶ X' ⟶ S` with `X ⟶ X'` an open
immersion and `X' ⟶ S` projective. The source argument has two halves:

1. **Produce an immersion over `S` into something projective over `S`.** Twist the relatively
   ample module until it is relatively very ample ([Stacks, Tag 01VU], (1) ⟹ (2)), push it
   forward to a quasi-coherent module on `S` ([Stacks, Tag 01LC]), write that as a directed
   colimit of finite-type quasi-coherent modules ([Stacks, Tag 01PK]), and choose a stage of the
   colimit large enough that the resulting map to `𝐏(E)` restricts, over each member of a finite
   affine cover of `S`, to the immersion into `𝐏ⁿ` given by generating sections
   ([Stacks, Tag 02NP]).
2. **Turn that immersion into an open immersion onto a closed subscheme.** The immersion is
   quasi-compact because `f` is and `𝐏(E) ⟶ S` is separated ([Stacks, Tag 03GI]), so
   [Stacks, Tag 01RG] factors it as an open immersion into a closed subscheme `X' ⊆ 𝐏(E)`, and
   `X' ⟶ S` is projective by definition.

**Half 2 is proved here in full, with no hypothesis**, for any projectivity predicate with the
two properties the argument uses. Half 1 is the condition
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`, which is a theorem at
Definition 01W8's `AlgebraicGeometry.IsProjective`:
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective` in
`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`, where the tag is
registered on `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`.

## Where the source's inputs are

* **Tag 01RG** is Mathlib's `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`.
* **Tag 07RK**, used in the source only to conclude that the first factor of an immersion is an
  immersion, is Mathlib's `AlgebraicGeometry.IsImmersion.of_comp`.
* **Tag 03GI**, used only to cancel the separated structure morphism out of a quasi-compact
  composite, is Mathlib's `AlgebraicGeometry.QuasiCompact.of_comp` together with
  `AlgebraicGeometry.IsSeparated.instQuasiSeparated`; it is recorded below as
  `Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated`.
* The inputs of half 1 — a relatively ample module has a power with generating sections defining
  immersions into projective spaces over a finite affine covering ([Stacks, Tag 01VU]), finitely
  many sections of `f_*L` factor through a quasi-coherent module of finite type
  ([Stacks, Tag 01PK]), and the morphism to `𝐏(ℰ)` of the resulting surjection — are assembled in
  `Projective.lean`; see its module documentation.

## Why projectivity is a parameter here

Half 2 is stated for a `CategoryTheory.MorphismProperty` parameter `P` together with the only two
properties of it the source argument uses: a `P`-morphism is separated, and precomposing a
`P`-morphism with a closed immersion gives a `P`-morphism. Both hold for Tag 01W8's
`AlgebraicGeometry.IsProjective` (`AlgebraicGeometry.IsProjective.isSeparated` and
`Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion`) and for the
H-projectivity `Stacks.HProjective.IsHProjective`, so the same statement serves both.

## Main definitions

* `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`: half 1 of the argument, as a
  condition on a projectivity predicate.

## Main results

* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isClosedImmersion`: Tag 01RG in
  the shape used here.
* `Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated`: the use made of Tag
  03GI.
* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`: half 2, the
  factorisation of the immersion of half 1 through the closure of its image, for a projectivity
  predicate with the two properties used.
* `Stacks.QuasiProjectiveCompactification.immersionIntoProjective_top`: the condition is
  satisfiable for the trivial predicate.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.QuasiProjectiveCompactification

/-! ### Tag 01RG: factoring a quasi-compact immersion -/

/-- **Stacks Tag 01RG**: a quasi-compact immersion factors as an open immersion followed by a
closed immersion.

This is Mathlib's `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact`, with
its two instance arguments taken as explicit hypotheses, which is the shape the argument below
needs them in: the immersion comes out of an existential and so cannot be an instance. -/
theorem exists_isOpenImmersion_isClosedImmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hg : IsImmersion g) (hgc : QuasiCompact g) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (c : X' ⟶ Y),
      IsOpenImmersion j ∧ IsClosedImmersion c ∧ j ≫ c = g := by
  have := hg
  have := hgc
  exact (IsImmersion.isImmersion_iff_exists_of_quasiCompact (f := g)).mp hg

/-! ### Tag 03GI: quasi-compactness of the immersion -/

/-- **The use the proof of Tag 07RM makes of Stacks Tag 03GI**: an immersion into a scheme that
is separated over the base is quasi-compact as soon as the composite is. Separatedness enters
only through `AlgebraicGeometry.IsSeparated.instQuasiSeparated`. -/
theorem quasiCompact_of_comp_isSeparated {X Y S : Scheme.{u}} (g : X ⟶ Y) (q : Y ⟶ S)
    (hq : IsSeparated q) (hgq : QuasiCompact (g ≫ q)) : QuasiCompact g := by
  have := hq
  have := hgq
  exact QuasiCompact.of_comp g q

/-! ### Half 1, as a condition on the projectivity predicate -/

/-- **Half 1 of the proof of Stacks Tag 07RM, as a condition on a projectivity predicate.** Every
quasi-projective morphism with quasi-compact quasi-separated base admits an immersion over the
base into a scheme that is `P`-projective over the base.

At Definition 01W8's `AlgebraicGeometry.IsProjective` this is a theorem,
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`: the intermediate
scheme is the projective bundle `𝐏(ℰ)` of a quasi-coherent module of finite type, as in the
source. -/
def ImmersionIntoProjective (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), CompactSpace S → QuasiSeparatedSpace S →
    Stacks.HProjective.IsQuasiProjective f →
      ∃ (Y : Scheme.{u}) (g : X ⟶ Y) (q : Y ⟶ S), IsImmersion g ∧ P q ∧ g ≫ q = f

/-- The condition is satisfiable: taking every morphism to be `P`-projective makes it true, with
the identity as the immersion. Recorded so that
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` is visibly not an
implication from a false hypothesis.

This witness does not satisfy the separatedness hypothesis of that theorem; for a witness of the
*conclusion* at the axiom-clean projectivity predicate, which does, see
`QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective_of_isHQuasiProjective` in
`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/HProjective.lean`. -/
theorem immersionIntoProjective_top : ImmersionIntoProjective.{u} ⊤ :=
  fun X _ f _ _ _ => ⟨X, 𝟙 X, f, inferInstance, trivial, Category.id_comp f⟩

/-! ### Half 2 of Tag 07RM -/

/-- **Half 2 of the proof of Stacks Tag 07RM**: given half 1, a quasi-projective morphism over a
quasi-compact quasi-separated base factors as an open immersion followed by a `P`-projective
morphism. At Definition 01W8's projectivity this is
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`, which carries
the tag.

Projectivity is the parameter `P`, constrained by exactly the two properties the source argument
uses of `𝐏(E) ⟶ S`:

* `hsep` — a `P`-morphism is separated. This is where the source cites
  [Stacks, Tag 03GI]; it is used only to see that the immersion of half 1 is quasi-compact.
* `hcomp` — a closed immersion into a `P`-scheme over `S` is `P` over `S`. This is the "and
  `X' ⟶ S` is projective by definition" at the end of the source proof.

See the module documentation for why this is a parameter.

Note that no property of the quasi-projectivity datum is used here beyond quasi-compactness of
`f`: the relatively ample module is consumed entirely inside `hgap`. -/
theorem exists_isOpenImmersion_isProjective {P : MorphismProperty Scheme.{u}}
    (hsep : ∀ {Y S : Scheme.{u}} (q : Y ⟶ S), P q → IsSeparated q)
    (hcomp : ∀ {X' Y S : Scheme.{u}} (c : X' ⟶ Y) (q : Y ⟶ S), IsClosedImmersion c → P q →
      P (c ≫ q))
    (hgap : ImmersionIntoProjective P) {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ P p ∧ i ≫ p = f := by
  obtain ⟨Y, g, q, hg, hq, hgq⟩ := hgap X S f ‹CompactSpace S› ‹QuasiSeparatedSpace S› hf
  have hgc : QuasiCompact g :=
    quasiCompact_of_comp_isSeparated g q (hsep q hq) (hgq ▸ hf.quasiCompact)
  obtain ⟨X', j, c, hj, hc, hjc⟩ := exists_isOpenImmersion_isClosedImmersion g hg hgc
  refine ⟨X', j, c ≫ q, hj, hcomp c q hc hq, ?_⟩
  rw [← Category.assoc, hjc, hgq]

end Stacks.QuasiProjectiveCompactification

end
