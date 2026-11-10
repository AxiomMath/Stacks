module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic

/-!
# Stacks Tags 0C4K and 0C4L: relative ampleness along a composition

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and let `L` be an invertible
`𝒪_X`-module.

* **Stacks Tag 0C4L** (permanence) says that if `L` is `g ∘ f`-ample and `f` is quasi-compact
  then `L` is `f`-ample.
* **Stacks Tag 0C4K** (composition) says that if `S` is quasi-compact, `L` is `f`-ample and `M`
  is a `g`-ample invertible `𝒪_Y`-module, then `L ⊗ f^* M ^⊗ a` is `g ∘ f`-ample for `a ≫ 0`.

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple`, Stacks Tag 01VH, which asks that
the morphism be quasi-compact and that the restriction of the module to the preimage of **every**
affine open of the base be ample.

## Main definitions

* `Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase`: **Stacks Tag 01VJ, clause (3)
  implies clause (1)** — relative ampleness may be checked on an affine open covering of the base
  rather than on every affine open. This is the one residue of Tag 0C4L, and one of the two
  residues of Tag 0C4K; it is a hypothesis neither tag's statement has, so neither tag is attached
  here.

## Main results

* `Stacks.RelativeAmpleComposition.isAmple_restrict_of_le`: **the instance of Stacks Tag 0B3E
  this cluster runs on, unconditionally.** If the restriction of `L` to an open `Z ⊆ X` is ample
  and `W ≤ Z` is an open with quasi-compact underlying space, then the restriction of `L` to `W`
  is ample.
* `Stacks.RelativeAmpleComposition.isAmple_preimage_of_le_preimage`: the same statement in the
  shape Tag 01VH consumes — ampleness on `f⁻¹V` from ampleness on `(g ∘ f)⁻¹U`, whenever
  `V ≤ g⁻¹U`.
* `Stacks.RelativeAmpleComposition.isRelativelyAmple_of_comp_of_forall_exists_affine`:
  **Stacks Tag 0C4L whenever every affine open of `Y` maps into an affine open of `S`**, with no
  premise.
* `Stacks.RelativeAmpleComposition.isRelativelyAmple_of_comp_of_isAffine`: **Stacks Tag 0C4L over
  an affine base, with no premise.** The special case `U = ⊤` of the above.
* `Stacks.RelativeAmpleComposition.exists_threshold_isRelativelyAmple_comp_of_isAffine`:
  **Stacks Tag 0C4K over an affine base**, on the single premise
  `Stacks.AmplePullbackPart1.EventualAffineDatum` — the residue of part (1) of Stacks Tag 0892
  that is already named in the tree. No new premise is introduced for Tag 0C4K over an affine
  base, and in particular the base-locality premise is not needed there.
* `Stacks.RelativeAmpleComposition.isRelativelyAmple_tensorPullbackPowModule_of_isAffine_base`:
  the same conclusion read through
  `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`, recording that over an affine
  base Tag 0C4K *is* part (1) of Tag 0892 and nothing more.

## The route

**Tag 0B3E is unconditional, and that is the fact this file is built on.** The two files that
state the relative-ampleness frontier — `../RelativeAmple/Basic.lean` ("Tag 01VJ ... is not here,
and it is what Tag 0C4K needs") and `StacksFrontier/AlgebraicGeometry/AmplePullback/Basic.lean`
("the general case is still conditional") — both predate
`Stacks.SectionExtension.isAmple_pullbackModule`, which proves Tag 0B3E in general with **no
premise**, by discharging `Stacks.SectionExtension.IsSectionRatio` from ampleness itself. So the
step "ampleness restricts to a quasi-compact open" — the only geometric input of Tag 0C4L — is
available, and `Stacks.RelativeAmpleComposition.isAmple_restrict_of_le` is it, using the
*second* of Tag 0B3E's four hypotheses (an immersion with quasi-compact source), which is the
cheap one here: `f⁻¹V` is quasi-compact because `f` is and `V` is affine, and no hypothesis on the
open immersion itself is needed.

Given that, the source's proof of Tag 0C4L goes through verbatim except for its last step. For an
affine open `V ⊆ Y` with `g(V)` inside an affine open `U ⊆ S`, the open `f⁻¹V` sits inside
`(g ∘ f)⁻¹U`, where `L` is ample by hypothesis, and `isAmple_restrict_of_le` concludes. What the
source then does, and what this file cannot, is handle an affine `V` whose image lies in **no**
single affine open of `S`: it covers `V` by affine opens that do, gets ampleness on each piece,
and quotes Tag 01VJ to assemble. That assembly is `RelativeAmpleLocalOnBase` and nothing else, and
once it is available the local step above is the whole of Tag 0C4L — which is why the finished,
unconditional tag lives downstream in `../RelativeAmple/CompositionPermanence.lean`, where
`Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase` is in scope.

Over an affine base the obstruction disappears, because `U = ⊤` works for every `V`.

## Implementation notes

**The open immersion of a smaller open.** `AlgebraicGeometry.Scheme.homOfLE` is the morphism of
open subschemes induced by `W ≤ Z`, and `AlgebraicGeometry.Scheme.homOfLE_ι` says it composes with
`Z.ι` to `W.ι`. Module pullback is pseudofunctorial, not functorial, so
`Stacks.RelativeAmpleComposition.restrictLeIso` composes
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` with the `eqToIso` of that composition law,
exactly as `Stacks.RelativeAmpleAffineBase.modulePullbackCompIdIso` does for an isomorphism;
ampleness is then
moved along it by `Stacks.RelativeVeryAmple.isAmple_congr`.

**`(g ∘ f)⁻¹U = f⁻¹(g⁻¹U)` holds on the nose**, so no transport is needed between the two
descriptions of the big open.

## What is not done

**Neither Stacks Tag 0C4K nor Stacks Tag 0C4L is attached, and neither label is closed.**

*Tag 0C4L.* Its single assertion is the implication for an arbitrary base, and what this file
proves of it restricts the base: `isRelativelyAmple_of_comp_of_isAffine` and
`isRelativelyAmple_of_comp_of_forall_exists_affine`. By the covering-set rule the label is
withheld here; it is attached to
`Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp` in
`../RelativeAmple/CompositionPermanence.lean`, which has no extra binder. The residue is exactly
one named statement — Stacks Tag 01VJ, clause (3) implies
clause (1) — and it is not a hypothesis that can be dropped by a better argument: the hypothesis
of Tag 0C4L gives ampleness of `L` on `f⁻¹V` only for those affine `V ⊆ Y` lying inside some
`g⁻¹U`, and those form a *basis* of `Y`, whereas Tag 01VH asks for every affine open. Bridging a
basis to every affine open is base-locality.

*Tag 0C4K.* Over an affine base it is part (1) of Stacks Tag 0892 exactly, and that part is
unproved in this repository:
`StacksFrontier/AlgebraicGeometry/AmpleQuasiAffinePullback/Basic.lean` records its four missing
ingredients and
`../AmplePullbackPart1/Basic.lean` names the single residue
`Stacks.AmplePullbackPart1.EventualAffineDatum`, the module-valued form of Stacks Tag 01PW. So
`exists_threshold_isRelativelyAmple_comp_of_isAffine` carries that premise. Over a general base
Tag 0C4K needs, in addition, `RelativeAmpleLocalOnBase` **and** the compatibility of the tensor
product and the pullback with restriction of the base to an open, which is not stated here: the
restriction of `L ⊗ f^* M ^⊗ a` to `(g ∘ f)⁻¹V` has to be identified with
`L| ⊗ (f|)^* (M|) ^⊗ a`, a Beck–Chevalley comparison for the open-immersion square. That is the
one piece of this cluster that is neither proved nor reduced here.

**`Stacks.RelativeAmple.IsRelativelyAmple` is not shown to restrict to an open of the base**
either, for the same reason: without the comparison above it cannot be stated for a module built
by tensoring and pulling back.

## References

* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 0C4L](https://stacks.math.columbia.edu/tag/0C4L)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeAmpleComposition

/-! ### Restriction of a module to a smaller open -/

section Restrict

variable {X : Scheme.{u}}

/-- **The restriction of `L` to `W` is the restriction along `W ≤ Z` of its restriction to `Z`.**

Module pullback is pseudofunctorial rather than functorial, so the two sides are isomorphic and
not equal: `Stacks.PullbackPseudofunctor.modulePullbackCompIso` compares the pullback along a
composite with the composite of the pullbacks, and
`AlgebraicGeometry.Scheme.homOfLE_ι` identifies `W.ι` with the composite
`W ⟶ Z ⟶ X`. -/
def restrictLeIso {W Z : X.Opens} (e : W ≤ Z) (L : X.Modules) :
    Stacks.AmpleLocallyClosed.pullbackModule W.ι L ≅
      Stacks.AmpleLocallyClosed.pullbackModule (X.homOfLE e)
        (Stacks.AmpleLocallyClosed.pullbackModule Z.ι L) :=
  eqToIso (congrArg (fun m : W.toScheme ⟶ X =>
      Stacks.AmpleLocallyClosed.pullbackModule m L) (X.homOfLE_ι e).symm) ≪≫
    (Stacks.PullbackPseudofunctor.modulePullbackCompIso Z.ι.toLRSHom.toShHom
      (X.homOfLE e).toLRSHom.toShHom).app L

/-- **Stacks Tag 0B3E, in the one instance this cluster needs, with no premise.** If the
restriction of an invertible `L` to an open `Z` of `X` is ample, and `W ≤ Z` is an open whose
underlying space is quasi-compact, then the restriction of `L` to `W` is ample.

`AlgebraicGeometry.Scheme.homOfLE` is an open immersion, hence an immersion, so the second of the
four hypotheses of Stacks Tag 0B3E — an immersion with quasi-compact source — is met by
`CompactSpace W`, and `Stacks.SectionExtension.isAmple_pullbackModule` applies with no premise.
`Stacks.RelativeAmpleComposition.restrictLeIso` then moves the conclusion onto the restriction of
`L` to `W` itself. -/
theorem isAmple_restrict_of_le {W Z : X.Opens} (e : W ≤ Z) (L : X.Modules)
    [IsInvertibleModule X L] (hZ : IsAmple Z.toScheme (Stacks.AmpleLocallyClosed.pullbackModule
      Z.ι L)) (hW : CompactSpace W.toScheme) :
    IsAmple W.toScheme (Stacks.AmpleLocallyClosed.pullbackModule W.ι L) :=
  (Stacks.RelativeVeryAmple.isAmple_congr _ _ (restrictLeIso e L)).mpr
    (Stacks.SectionExtension.isAmple_pullbackModule (X.homOfLE e) _ hZ
      (Or.inr (Or.inl ⟨hW, inferInstance⟩)))

end Restrict

/-! ### The preimage of an affine open is quasi-compact -/

/-- The preimage of a quasi-compact open under a quasi-compact morphism has quasi-compact
underlying space. `AlgebraicGeometry.Scheme.Hom.isCompact_preimage` gives compactness of the
preimage as a set; `isCompact_iff_compactSpace` turns it into the instance that
`Stacks.RelativeAmpleComposition.isAmple_restrict_of_le` asks for. -/
theorem compactSpace_preimage_of_isCompact {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (V : S.Opens) (hV : IsCompact (V : Set S)) : CompactSpace (f ⁻¹ᵁ V).toScheme := by
  have h := f.isCompact_preimage hV
  rwa [isCompact_iff_compactSpace] at h

/-! ### Stacks Tag 0C4L -/

section Permanence

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **Ampleness on `f⁻¹V` from ampleness on `(g ∘ f)⁻¹U`.** If `V` is an open of `Y` with
`V ≤ g⁻¹U`, `f` is quasi-compact and `V` is quasi-compact, then ampleness of the restriction of
`L` to `(g ∘ f)⁻¹U` — which is what `Stacks.RelativeAmple.IsRelativelyAmple` for `g ∘ f` asserts
when `U` is affine — gives ampleness of the restriction of `L` to `f⁻¹V`.

`(g ∘ f)⁻¹U = f⁻¹(g⁻¹U)` holds on the nose, so `f⁻¹V ≤ (g ∘ f)⁻¹U` is the monotonicity of
preimage, and `Stacks.RelativeAmpleComposition.isAmple_restrict_of_le` concludes. -/
theorem isAmple_preimage_of_le_preimage [QuasiCompact f] {V : Y.Opens} {U : S.Opens}
    (hVU : V ≤ g ⁻¹ᵁ U) (hV : IsCompact (V : Set Y))
    (hU : IsAmple ((f ≫ g) ⁻¹ᵁ U).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule ((f ≫ g) ⁻¹ᵁ U).ι L)) :
    IsAmple (f ⁻¹ᵁ V).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L) :=
  isAmple_restrict_of_le (Z := (f ≫ g) ⁻¹ᵁ U)
    (fun _ hx => hVU hx) L hU (compactSpace_preimage_of_isCompact f V hV)

/-- **Stacks Tag 0C4L whenever every affine open of `Y` lies over an affine open of `S`, with no
premise.** If `L` is ample relative to `g ∘ f`, `f` is quasi-compact, and every affine open of `Y`
is contained in the preimage of some affine open of `S`, then `L` is ample relative to `f`.

The hypothesis is exactly the step the source performs by choosing, for an affine `V ⊆ Y`, an
affine `U ⊆ S` with `g(V) ⊆ U`. On each such `V` the conclusion is
`Stacks.RelativeAmpleComposition.isAmple_preimage_of_le_preimage`. -/
theorem isRelativelyAmple_of_comp_of_forall_exists_affine
    (hL : Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g) L) (hf : QuasiCompact f)
    (hga : ∀ V : Y.Opens, IsAffineOpen V → ∃ U : S.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine ⟨hf, fun V hV => ?_⟩
  obtain ⟨U, hU, hVU⟩ := hga V hV
  have := hf
  exact isAmple_preimage_of_le_preimage f g L hVU hV.isCompact (hL.2 U hU)

/-- **Stacks Tag 0C4L over an affine base, with no premise.** For `S` affine the open `U = ⊤` is
affine and contains the image of every open of `Y`, so
`Stacks.RelativeAmpleComposition.isRelativelyAmple_of_comp_of_forall_exists_affine` applies with
no condition on `g` at all. -/
theorem isRelativelyAmple_of_comp_of_isAffine [IsAffine S]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g) L) (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_comp_of_forall_exists_affine f g L hL hf
    fun _ _ => ⟨⊤, isAffineOpen_top S, le_top⟩

end Permanence

/-! ### Stacks Tag 01VJ, clause (3) implies clause (1): the residue -/

/-- **Stacks Tag 01VJ, clause (3) implies clause (1): relative ampleness is local on the base.**
A quasi-compact morphism `f : X ⟶ S` and an invertible `L` for which *some* affine open covering
`S = ⋃ V_i` has every restriction `L|_{f⁻¹V_i}` ample, has `L` ample relative to `f` — that is,
`L|_{f⁻¹V}` is ample for **every** affine open `V ⊆ S`.

The covering is written pointwise: through every point of `S` there is an affine open on whose
preimage the restriction is ample.

This is the one residue of Stacks Tag 0C4L and one of the two residues of Stacks Tag 0C4K. It is
unproved in this repository — `../RelativeAmple/Basic.lean` records that its proof in the source
goes through relative `Proj` — and it is carried as a hypothesis rather than assumed silently. -/
def RelativeAmpleLocalOnBase : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) (L : X.Modules) (_ : IsInvertibleModule X L),
    QuasiCompact f →
    (∀ x : S, ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsAmple (f ⁻¹ᵁ V).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L)) →
    Stacks.RelativeAmple.IsRelativelyAmple f L

/-! ### Stacks Tag 0C4K over an affine base -/

section Composition

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules) (M : Y.Modules)
  [IsInvertibleModule X L] [IsInvertibleModule Y M]

/-- **Over an affine base, Stacks Tag 0C4K is part (1) of Stacks Tag 0892 and nothing more.** For
`S` affine, `L ⊗ f^* M ^⊗ a` is ample relative to `g ∘ f` if and only if it is ample on `X`.

This is `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple` at the module
`Stacks.AmplePullbackPart1.tensorPullbackPowModule`, recorded so that the reduction is visible
rather than buried in the proof below. -/
theorem isRelativelyAmple_tensorPullbackPowModule_of_isAffine_base [IsAffine S] (a : ℕ) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g)
        (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) ↔
      IsAmple X (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) :=
  Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (f ≫ g) _

/-- **Stacks Tag 0C4K over an affine base, on the single premise
`Stacks.AmplePullbackPart1.EventualAffineDatum`.** For `S` affine, `L` ample relative to `f` and
`M` ample relative to `g`, there is a threshold beyond which `L ⊗ f^* M ^⊗ a` is ample relative to
`g ∘ f`.

No new premise is introduced. `Stacks.AmplePullbackPart1.EventualAffineDatum` is the residue of
part (1) of Stacks Tag 0892 already named in this repository — the module-valued form of Stacks
Tag 01PW — and `Stacks.AmplePullbackPart1.exists_threshold_isAmple` is the deduction from it.
What this adds is the two translations at either end:
`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`
turns `g`-relative ampleness of `M` over an affine base into ampleness of `M` on `Y`, which is
what part (1) consumes, and turns the ampleness it produces on `X` back into
`g ∘ f`-relative ampleness. In particular the base-locality premise
`Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase` is **not** needed over an affine
base. -/
theorem exists_threshold_isRelativelyAmple_comp_of_isAffine [IsAffine S]
    (hdat : Stacks.AmplePullbackPart1.EventualAffineDatum f L M)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a → Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g)
      (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) := by
  have hMa : IsAmple Y M :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple g M).mp hM
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackPart1.exists_threshold_isAmple f L M
    (Stacks.AmplePullbackPart1.compactSpace_of_isAmple f L M hL hMa) hdat
  exact ⟨n, fun a ha =>
    (isRelativelyAmple_tensorPullbackPowModule_of_isAffine_base f g L M a).mpr (hn a ha)⟩

end Composition

/-! ### Faithfulness against the tagged statements

Each of the two tagged statements has a single unlabelled assertion. The `example`s below restate
what is proved above **in the statement's own binder order**, in the library vocabulary, so that
the exact distance between statement and theorem is one visible binder in each case. No `@[stacks]`
attribute is attached to anything in this file; by the covering-set rule the extra binder withholds
both labels. Tag 0C4L's own statement is met with no extra binder at all, downstream in
`../RelativeAmple/CompositionPermanence.lean`, which is where its label sits. -/

section Faithfulness

/-- **Stacks Tag 0C4L**, in the statement's binder order, with the one extra binder `[IsAffine S]`.
Unconditional. -/
example {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine S] (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g) L)
    (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_comp_of_isAffine f g L hL hf

/-- **Stacks Tag 0C4K**, in the statement's binder order, with the two extra binders `[IsAffine S]`
and `Stacks.AmplePullbackPart1.EventualAffineDatum`. The statement's own `[CompactSpace S]` is
retained
even though `[IsAffine S]` supplies it, so that nothing the statement asks for is dropped. -/
example {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [CompactSpace S] [IsAffine S]
    (L : X.Modules) (M : Y.Modules) [IsInvertibleModule X L] [IsInvertibleModule Y M]
    (hdat : Stacks.AmplePullbackPart1.EventualAffineDatum f L M)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g)
      (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M n) :=
  exists_threshold_isRelativelyAmple_comp_of_isAffine f g L M hdat hL hM

end Faithfulness

end Stacks.RelativeAmpleComposition

end
