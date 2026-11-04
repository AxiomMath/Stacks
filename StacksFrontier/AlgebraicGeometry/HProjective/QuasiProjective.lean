module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic

/-!
# Stacks Tag 087S part (2): quasi-projective implies H-quasi-projective

Part (2) of Stacks Tag 087S is discharged in the source by a single sentence — "Hence Lemma
29.44.12 applies and we see that (1) implies (2)" — standing on Morphisms Lemma 29.44.12
([Stacks, Tag 07RM]), which factors a quasi-projective morphism with quasi-compact
quasi-separated base as an open immersion followed by a projective morphism. This file states
quasi-projectivity over the repository's objects, names that one sentence as a hypothesis,
and proves part (2) from it.

## What is named, and what it contains

`Stacks.HProjective.ProjectiveCompactification` is the hypothesis. **It is not Tag 07RM alone**: it
asks for the second factor to be *H*-projective, which is Tag 07RM followed by part (1) of this
very tag, and it asks for it over every base, with neither the quasi-compactness and
quasi-separatedness of Tag 07RM nor the ample module of part (1). Tag 07RM itself is proved, at
Definition 01W8's projectivity, as
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`, and part (1)
over a base carrying an ample module as `AlgebraicGeometry.isProjectiveMorphism_of_isProjective`;
neither discharges this hypothesis, whose quantifier is wider. The docstring of the definition
records exactly which of the source's two ingredients each half is.

Everything else in part (2) is proved here with no hypothesis:

* the composite of the open immersion with the closed immersion into `ℙⁿ_S` is an immersion;
* it is quasi-compact, by cancelling the structure morphism of `ℙⁿ_S` against the
  quasi-compactness of `f`, which is available because
  `Stacks.HProjective.isSeparated_over` makes `ℙⁿ_S ⟶ S` separated and hence quasi-separated.

## Main definitions

* `Stacks.HProjective.IsQuasiProjective`: **Stacks Tag 01VW**, quasi-projectivity — finite type
  together with a relatively ample invertible module. This is Tag 01VW's quasi-projectivity with
  Tag 01VH's relative ampleness spelled as `Stacks.RelativeAmple.IsRelativelyAmple`, the Tag
  01VH declaration of the library, and the invertibility class taken to be the one that
  declaration binds; see the implementation notes on which of the repository's two Tag 01CS
  classes that is.
* `Stacks.HProjective.ProjectiveCompactification`: the named hypothesis, Tag 07RM composed with
  part (1) of Tag 087S.

## Main results

* `Stacks.HProjective.IsQuasiProjective.quasiCompact`,
  `Stacks.HProjective.IsQuasiProjective.locallyOfFiniteType`: the finite-type conjuncts, so that no
  consumer unfolds the definition.
* `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective`: **part (2) of Stacks Tag 087S**
  from `Stacks.HProjective.ProjectiveCompactification`.
* `Stacks.HProjective.projectiveCompactification_conclusion_of_isHProjective`: the hypothesis'
  conclusion holds, with the open immersion the identity, for any morphism that is already
  H-projective. Recorded so that the hypothesis is visibly not vacuous.
* `Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom`: **Stacks Tag 0B3H**, a quasi-affine
  morphism of finite type is quasi-projective, with `𝒪_X` as the relatively ample module.

## Implementation notes

**Ampleness of a sheaf on `S` is nowhere used.** The source states both parts under a chosen ample
invertible sheaf on the base, and the theorem below does not carry that hypothesis: the
argument's use of ampleness is entirely inside Properties Proposition 28.27.13
([Stacks, Tag 01Q3], clause (7)) and Properties Lemma 28.27.11 ([Stacks, Tag 01Q1]), both of
which sit on the far side of the named hypothesis. Dropping an unused hypothesis strengthens the
statement; the source's form follows from this one by discarding it.

**Which Tag 01CS class the invertibility binder is.** The repository carries two classes with
the Tag 01CS attribute, `Stacks.SheafOfModules.IsInvertible`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`) and
`AlgebraicGeometry.SheafOfModules.IsInvertible`
(`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`), with textually identical definitions
in different namespaces. `Stacks.Ample.IsInvertibleModule X L` abbreviates the *second* of them,
because `StacksFrontier/AlgebraicGeometry/AmpleWire/Basic.lean` opens
`AlgebraicGeometry.SheafOfModules` before stating it, and that is the class
`Stacks.RelativeAmple.IsRelativelyAmple` binds — so it is the one used here.

The two are **not** definitionally equal: a term of
`Stacks.Ample.IsInvertibleModule X L` is rejected where
`Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L` is expected. They are
equivalent, by `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`,
so a consumer holding the other flavour converts rather than being stuck; but the conversion is
a rewrite and not an identity, and a statement that mixes the two will not elaborate.

**The relative ampleness datum of `Stacks.HProjective.IsQuasiProjective` is never destructured.**
The only consequence of quasi-projectivity the argument consumes is quasi-compactness of `f`, which
is the second half of the finite-type conjunct. This is worth saying because it means part (2)
needs nothing from the ample module on `X` either; the whole of its geometric content is in Tag
07RM.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 0B3H](https://stacks.math.columbia.edu/tag/0B3H)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
* [EGA II, Proposition 5.3.4 (i)]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.HProjective

/-! ### Quasi-projectivity -/

/-- **Stacks Tag 01VW, quasi-projectivity**: a morphism of finite type admitting a relatively
ample invertible module. Finite type is the conjunction of local finite type and
quasi-compactness, as in Tag 01T1. This is Tag 01VW's quasi-projectivity with its folded
definitions spelled by their library names. -/
def IsQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  (LocallyOfFiniteType f ∧ QuasiCompact f) ∧
    ∃ L : X.Modules, ∃ hL : Stacks.Ample.IsInvertibleModule X L,
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L

/-- A quasi-projective morphism is quasi-compact. -/
theorem IsQuasiProjective.quasiCompact {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsQuasiProjective f) : QuasiCompact f := hf.1.2

/-- A quasi-projective morphism is locally of finite type. -/
theorem IsQuasiProjective.locallyOfFiniteType {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsQuasiProjective f) : LocallyOfFiniteType f := hf.1.1

/-! ### The named hypothesis -/

/-- **Stacks Tag 07RM composed with part (1) of Stacks Tag 087S, as a named hypothesis.** Every
quasi-projective morphism factors as an open immersion followed by an H-projective morphism.

The two ingredients, and which of them owes what:

* **Tag 07RM** (Morphisms, Lemma 29.44.12) supplies the factorisation `X → X' → S` with `X → X'`
  an open immersion and `X' → S` *projective*, over a quasi-compact quasi-separated base. It is
  proved as `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`,
  from [Stacks, Tag 01VU] (1) ⟹ (3), the finite-type lift of finitely many sections
  (`Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`) and the morphism to
  `𝐏(ℰ)` that the sections define.
* **Part (1) of Tag 087S** upgrades "projective" to "H-projective". By
  `Stacks.HProjective.isHProjective_iff_hasHProjectiveClosedImmersion` that is exactly
  H-projectivity of `𝐏(E) ⟶ S`, which needs an ample invertible module on `S`; over such a base it
  is `AlgebraicGeometry.isProjectiveMorphism_of_isProjective`.

The hypothesis is stated with H-projectivity rather than projectivity because H-projectivity is
what part (2) concludes; Tag 07RM's own conclusion, at Tag 01W8's `AlgebraicGeometry.IsProjective`,
is written down and proved in
`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`. -/
def ProjectiveCompactification : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsQuasiProjective f →
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ j ≫ p = f ∧ IsHProjective p

/-- The conclusion of `Stacks.HProjective.ProjectiveCompactification` holds for an H-projective
morphism, with the identity as the open immersion. Recorded so that the hypothesis is visibly
satisfiable rather than vacuous. -/
theorem projectiveCompactification_conclusion_of_isHProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ j ≫ p = f ∧ IsHProjective p :=
  ⟨X, 𝟙 X, f, inferInstance, Category.id_comp f, hf⟩

/-! ### Part (2) -/

/-- **Stacks Tag 087S, part (2): a quasi-projective morphism is H-quasi-projective**, from
`Stacks.HProjective.ProjectiveCompactification`.

The factorisation is `f = j ≫ p` with `j` an open immersion and `p` H-projective;
`Stacks.HProjective.isHQuasiProjective_comp_of_isHProjective` composes `j` with the closed
immersion of `p` into `ℙⁿ_S` and cancels the structure morphism against quasi-compactness of `f`.

No ample invertible sheaf on `S` appears: see the implementation notes of this file. -/
theorem isHQuasiProjective_of_isQuasiProjective (hgap : ProjectiveCompactification.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : IsQuasiProjective f) : IsHQuasiProjective f := by
  obtain ⟨X', j, p, hj, hjp, hp⟩ := hgap X S f hf
  have := hj
  have hqc : QuasiCompact (j ≫ p) := by rw [hjp]; exact hf.quasiCompact
  exact hjp ▸ isHQuasiProjective_comp_of_isHProjective j hp hqc

/-! ### Quasi-affine morphisms of finite type -/

/-- **Stacks Tag 0B3H.** A quasi-affine morphism of finite type is quasi-projective: the
structure sheaf `𝒪_X` is ample relative to a quasi-affine morphism by [Stacks, Tag 0891].

Finite type is the conjunction of local finite type and quasi-compactness, as in Tag 01T1, and
quasi-compactness is already a consequence of quasi-affineness, so only the local finite type
half is a hypothesis. -/
@[stacks 0B3H, ega "II 5.3.4" "(i)"]
theorem isQuasiProjective_of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] (hf : LocallyOfFiniteType f) : IsQuasiProjective f :=
  ⟨⟨hf, quasiCompact_of_isQuasiAffineHom f⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X,
    (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr
      fun V hV => IsQuasiAffineHom.isQuasiAffine_preimage V hV⟩

end Stacks.HProjective

end
