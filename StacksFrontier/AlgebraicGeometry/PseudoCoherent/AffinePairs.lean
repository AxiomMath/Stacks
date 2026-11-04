module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTfae
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Relative

/-!
# Relative pseudo-coherence on all compatible pairs of affine opens

Stacks 09UI defines relative `m`-pseudo-coherence of an object `E` of `D(𝒪_X)` for a morphism
`f : X ⟶ S` locally of finite type by the *existence* of an affine open cover `V` of `S` and,
over each member, an affine open cover `U` of `f ⁻¹ᵁ V i` on which the local condition holds.
Stacks 09UJ says that this is equivalent to the local condition holding on *every* compatible
pair of affine opens `U ⊆ f ⁻¹ᵁ V`, and that relative `m`-pseudo-coherence then restricts to
open subschemes.

This file names the per-pair condition, proves the direction of the equivalence that needs none
of the content of Stacks 09UJ — all pairs implies some cover — and records the equivalence itself
as a single named condition, so that the consumer in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PseudoCoherentTfae.lean` and the proof agree on its
shape. That condition is discharged in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairLocality.lean`, where Stacks 09UJ is
proved as `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair`: the local condition of
  Stacks 09UI at one compatible pair of affine opens, which is the first of the equivalent
  conditions of Stacks 09VC for the pair `(U ⟶ V, E|_U)`.
* `AlgebraicGeometry.AffinePairComparison`: the equivalence of Stacks 09UJ, as a `Prop`.
* `AlgebraicGeometry.AffinePairStructureSheafComparison`: the per-pair content of Stacks 09VF at
  the structure sheaf, as a `Prop`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`: **the implication
  (2) ⟹ (1) of Stacks 09UJ.** If the local condition holds on every compatible pair of affine
  opens then `E` is relatively `m`-pseudo-coherent, because the affine opens of `S` cover `S` and
  the affine opens of `X` contained in `f ⁻¹ᵁ V` cover `f ⁻¹ᵁ V`.
* `AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair`: the hypothesis
  `AlgebraicGeometry.RelativeStructureSheafComparison`, from which the remaining clause of
  Stacks 067Y follows by `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`, splits
  into the equivalence of Stacks 09UJ at the structure sheaf and a condition at one pair of
  affine opens at a time.

## Implementation notes

**What is proved here and what is proved elsewhere.** `AffinePairComparison` and
`AffinePairStructureSheafComparison` are named conditions, and no declaration in this file carries
a `stacks` attribute. Of Stacks 09UJ only the implication (2) ⟹ (1) is proved here, and like
the corresponding implication of `AlgebraicGeometry.pseudoCoherent_tfae` and of
`AlgebraicGeometry.exists_affineCover_derivedSectionsPseudoCoherentOn` it uses no
pseudo-coherence at all — it is the choice of cover. The implication (1) ⟹ (2), and with it
`AffinePairComparison` itself, is proved in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairLocality.lean`, which is where the tag
sits. The other theorem here,
`AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair`, is a reduction between
conditions and asserts no instance of any tag.

The implication (1) ⟹ (2) is the content of the tag, and the source proves it from two lemmas:

* Stacks 09VD, that the local condition for `(X ⟶ V, E)` with `V` a standard open of an affine
  `S` implies it for `(U ⟶ S, E|_U)` with `U` an affine open of `X`. Both paragraphs of its proof
  are proved: the first, which enlarges the base from `V` to `S`, as
  `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen`,
  and the second, which replaces `𝔸ⁿ⁺¹_S` by the standard open `D(g')` on which `U` is cut out,
  as
  `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen` in
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/RestrictTarget.lean`; the two are composed there
  as `exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen`. Both carry the side
  condition of Stacks 09VA on the pushforward of the structure sheaf, and both use only the
  *forward* half of Stacks 09VA itself, which is proved as
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`. What
  these results do not give is Stacks 09VD at an *arbitrary* affine open of `X`: the
  source's proof, like the formalization, produces the conclusion only at a standard open, and
  the passage to an arbitrary affine open is Stacks 09VE.
* Stacks 09VE, that for a finite-type morphism of affine schemes the local condition holds for
  `(X ⟶ S, E)` exactly when it holds for every member of a standard affine open cover of `X`.
  The part of it that does not involve pseudo-coherence is already proved, in
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/BasicOpenLocal.lean`. Its direction (2) ⟹ (1) is
  Stacks 09VD. Its direction (1) ⟹ (2) is **not** a consequence of the forward half of
  Stacks 09VA: the source's argument covers the intermediate scheme
  `T = Spec R[xᵢ, yᵢ, zᵢ]/(∑ yᵢzᵢ - 1)` by the opens `D(y_{i₀})` and must then recognise the
  closed immersion `U_{i₀} ⟶ D(y_{i₀}) ∩ T` as one of the immersions the local condition at
  `U_{i₀}` speaks about. Since the local condition is stated in the ∃-form, that recognition is
  Stacks 09VC, which needs the *reverse* half of Stacks 09VA — the reverse half is what turns
  pseudo-coherence of a pushforward back into pseudo-coherence of the object, and no composition
  of forward implications does that. Note also that `D(y_{i₀}) ∩ T` is a localization of a
  polynomial ring at one variable and so is *not* an affine space over `S`, contrary to the
  parenthetical remark at the end of the source's proof; it is a quotient of a polynomial ring by
  one non-zerodivisor, which is what makes the side condition of Stacks 09VA hold for it.

**Shape of the per-pair condition.** It is written with `U : X.affineOpens` and
`V : S.affineOpens` rather than with an open plus a proof that it is affine, so that it is
syntactically the body of `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` and the two
conditions can be compared without reindexing. The closed immersions it asks for do exist, by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, so the condition is not vacuous
on any pair.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these definitions makes
the same declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The local condition of Stacks 09UI at a single compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`: the restriction of `E` to `U` becomes `m`-pseudo-coherent after derived
pushforward along some closed immersion `U ⟶ 𝔸ⁿ_V` over `V` through which `f` restricted to `U`
factors.

This is the first of the equivalent conditions of Stacks 09VC for the pair `(U ⟶ V, E|_U)`, and
it is the condition that `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` asks for at each
member of its covers; condition (2) of Stacks 09UJ asks for it at *every* such pair. -/
public abbrev Scheme.Hom.IsPseudoCoherentFromOnAffinePair [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) (U : X.affineOpens) (V : S.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) : Prop :=
  ∃ (n : ℕ) (i : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme),
    IsClosedImmersion i ∧
      i ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom = f.resLE V.1 U.1 hUV ∧
      Scheme.Modules.IsPseudoCoherentFromAfterPushforward i
        ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E) m

/-- **Stacks 09UJ, the implication (2) ⟹ (1).** If the local condition of Stacks 09UI holds at
every compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, then `E` is relatively `m`-pseudo-coherent
in the sense of Stacks 09UI: take the cover of `S` by all of its affine opens, and over each of
them the cover of its inverse image by all the affine opens of `X` contained in it.

This is the direction of Stacks 09UJ that needs none of its content, exactly as for the
corresponding implications of `AlgebraicGeometry.pseudoCoherent_tfae` and of
`AlgebraicGeometry.exists_affineCover_derivedSectionsPseudoCoherentOn`. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∀ (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
      f.IsPseudoCoherentFromOnAffinePair E m U V hUV) :
    Scheme.Hom.IsPseudoCoherentFrom f E m :=
  ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V ↦
    ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U ↦ U.1,
      iSup_affineOpens_subtype_eq _, fun U ↦ ⟨U.2, h U.1 V U.2⟩⟩⟩

/-- **The statement of Stacks 09UJ.** For `f : X ⟶ S` locally of finite type, `E` an object of
the derived category of `𝒪_X`-modules and `m` an integer, the following are equivalent:

1. `E` is relatively `m`-pseudo-coherent, which is
   `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`;
2. the local condition
   `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair` holds at every compatible
   pair of affine opens `U ⊆ f ⁻¹ᵁ V`.

This is a `Prop`, not a theorem, so that this file can state it before the machinery its proof
needs is available; it carries no `stacks` attribute. The implication (2) ⟹ (1) is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair` below, and the
equivalence is proved as
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair` in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairLocality.lean`, which also carries the
tag. The final assertion of the source — that relative `m`-pseudo-coherence restricts to
compatible open subschemes — is not stated here, since the source derives it from this
equivalence; it is
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.resLE` in the same file. -/
public abbrev AffinePairComparison [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (m : ℤ) : Prop :=
  Scheme.Hom.IsPseudoCoherentFrom f E m ↔
    ∀ (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
      f.IsPseudoCoherentFromOnAffinePair E m U V hUV

/-- **The per-pair content of Stacks 09VF at the structure sheaf.** At one compatible pair of
affine opens `U ⊆ f ⁻¹ᵁ V`, the local condition of Stacks 09UI for `𝒪_X` is equivalent to
`Γ(X, U)` being `m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`.

This is what remains of `AlgebraicGeometry.RelativeStructureSheafComparison` once the equivalence
of Stacks 09UJ has turned its covers into all compatible pairs; it is stated as an abbreviation
so that `AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair` and a future proof of
Stacks 09VF agree on its shape. The source proves it from Stacks 08E7, both directions of which
are proved, together with the identification of `RΓ(U, E)` for affine `U` with the object of
`D(Γ(X, U))` corresponding to `E|_U` — the remaining content of Stacks 06Z0, isolated as
`Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`. It carries no `stacks` attribute; it is proved, with
no hypotheses, as `AlgebraicGeometry.affinePairStructureSheafComparison` in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairStructureSheaf.lean`. -/
public abbrev AffinePairStructureSheafComparison : Prop :=
  ∀ (hft : LocallyOfFiniteType f) (m : ℤ) (U : X.Opens) (hU : IsAffineOpen U)
      (V : S.Opens) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
    letI := hft
    f.IsPseudoCoherentFromOnAffinePair
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
        m ⟨U, hU⟩ ⟨V, hV⟩ e ↔
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
      PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom (R := Γ(S, V)) (A := Γ(X, U))
        Γ(X, U) m

/-- **The hypothesis of Stacks 067Y's remaining clause splits into Stacks 09UJ and the per-pair
content of Stacks 09VF.** `AlgebraicGeometry.RelativeStructureSheafComparison`, the hypothesis
from which `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison` derives the
three-condition form of Stacks 067Y, follows from the equivalence of Stacks 09UJ at the structure
sheaf together with `AlgebraicGeometry.AffinePairStructureSheafComparison`.

Both sides of the hypothesis are then about all compatible pairs of affine opens, so no choice of
cover intervenes and the proof is the composition of the two equivalences. The only bookkeeping
is that `RelativeStructureSheafComparison` quantifies over an open together with a proof that it
is affine, while the local condition of Stacks 09UI is indexed by `X.affineOpens`.

The point of the statement is that it replaces one opaque hypothesis by two whose mathematical
content is separated: the first is purely about covers of a scheme and is the subject of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/BasicOpenLocal.lean`, while the second is local on
both schemes and is where Stacks 08E7 and Stacks 06Z0 enter. -/
public theorem relativeStructureSheafComparison_of_affinePair
    (hUJ : ∀ (hft : LocallyOfFiniteType f) (m : ℤ),
      letI := hft
      AffinePairComparison f ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) m)
    (hVF : AffinePairStructureSheafComparison f) :
    RelativeStructureSheafComparison f := by
  intro hft m
  exact (hUJ hft m).trans
    ⟨fun h U hU V hV e ↦ (hVF hft m U hU V hV e).1 (h ⟨U, hU⟩ ⟨V, hV⟩ e),
      fun h U V hUV ↦ (hVF hft m U.1 U.2 V.1 V.2 hUV).2 (h U.1 U.2 V.1 V.2 hUV)⟩

end AlgebraicGeometry

end
