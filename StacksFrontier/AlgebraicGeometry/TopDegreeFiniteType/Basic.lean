module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type of the top higher direct image

Let `f : X ⟶ Y` be a proper morphism all of whose fibres have dimension at most `d`, and let `F`
be a quasi-coherent `𝒪_X`-module of finite type. [Stacks, Tag 0EX4] asserts that `R ᵈ f_* F` is
quasi-coherent of finite type. The quasi-coherence is
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived_of_isProper`, which
holds in every degree and needs only that `f` be quasi-compact and quasi-separated. This file is
about the finite-type conclusion.

Two things are proved. The first is the opening move of the source's proof — the question is
local on `Y`, so it suffices to bound the sections over each affine open — isolated as a
criterion for a quasi-coherent module to be of finite type. The second is the case `d = 0` of the
tag, in full and unconditionally: a proper morphism whose fibres all have dimension at most `0`
is **finite** (Zariski's main theorem), the zeroth right derived functor of the pushforward is
the pushforward, and the pushforward of a quasi-coherent module of finite type along a finite
morphism is of finite type — which is proved here, with no hypothesis on `Y` at all.

The case `d > 0` is **not** proved; see the implementation notes for what it needs.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections`: a
  quasi-coherent module whose sections over every affine open form a finite module is of finite
  type. No hypothesis on the scheme.
* `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_pushforward_of_isFinite`: the
  pushforward of a quasi-coherent module of finite type along a finite morphism is of finite
  type.
* `AlgebraicGeometry.locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero` and
  `AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero`: a
  morphism locally of finite type whose fibres all have dimension at most `0` is locally
  quasi-finite, and a proper such morphism is finite.
* `rightDerived_pushforward_isFiniteType_of_isProper_of_forall_moduleFinite_sections`, in the
  same namespace: the finite-type conclusion of [Stacks, Tag 0EX4] reduced to the finiteness of
  the modules of sections of `R ᵈ f_* F` over the affine opens of `Y`.
* `rightDerived_pushforward_isFiniteType_of_isProper_of_fiber_dimension_le_zero`, in the same
  namespace: the finite-type conclusion of [Stacks, Tag 0EX4] in the case `d = 0`.

## Implementation notes

**No `@[stacks 0EX4]` attribute is attached to anything here.** The tag asserts the finite-type
conclusion for every `d`, and what is proved is the case `d = 0` together with a reduction of the
general case. The quasi-coherence clause of the tag already carries its own `@[stacks 0EX4]` in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageQcqs/Qcqs.lean`.

**What the case `d > 0` needs.** The source's route is: reduce to `Y = Spec R` affine, where the
conclusion is that `H ᵈ (X, F)` is a finite `R`-module ([Stacks, Tag 01XK] identifies it with the
global sections of `R ᵈ f_* F`); write `X` as a cofiltered limit of schemes proper and of finite
presentation over `Y` ([Stacks, Tag 09ZR]) with the fibre bound preserved at some stage
([Stacks, Tag 05M5]) to reduce to `f` of finite presentation; present `F` as a quotient of a
finitely presented module ([Stacks, Tag 086M]), the surjectivity on `H ᵈ` coming from the
vanishing of `H ᵈ ⁺ ¹` of the kernel ([Stacks, Tag 0E7D]); write `Y` as a cofiltered limit of
spectra of Noetherian rings and descend the whole situation to a finite stage
([Stacks, Tags 01ZM, 081F, 01ZR]); and finally invoke top-degree base change
([Stacks, Tag 0EX3]) to write `H ᵈ (X, F) = H ᵈ (X₀, F₀) ⊗_{R₀} R`, which is finite because
`H ᵈ (X₀, F₀)` is — **the finiteness theorem for the cohomology of a proper morphism over a
Noetherian base, [Stacks, Tag 02O6]**. That last input is the hard core: it is the same core as
[Stacks, Tag 02O5], it is proved by dévissage over Chow's lemma, and that proof is
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, which carries no hypothesis.
Of the other inputs, [Stacks, Tag 0E7D] and [Stacks, Tag 0EX3] have their reductions
formalized in `StacksDraft/AlgebraicGeometry/F3b/TopDegreeBaseChange/`, each with its own affine case
carried as a hypothesis, and [Stacks, Tags 09ZR, 086M, 081F] are absent.

**Why the sections criterion has no Noetherian hypothesis.** Condition (4) of
[Stacks, Tag 01XZ] implies condition (2) by
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn`, which assumes
nothing about the scheme; it is only the implications *into* coherence that need local
Noetherianness, and those are in
`StacksFrontier/AlgebraicGeometry/CoherenceCriteria/Basic.lean`. So the finite-type half of
[Stacks, Tag 01Y6] — the pushforward along a finite morphism — holds without any hypothesis on
the target, where the coherence half proved in
`StacksFrontier/AlgebraicGeometry/FiniteDirectImageCoherent/Basic.lean` needs
`IsLocallyNoetherian`.

**`AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType` is not proved here.** It
lives in `StacksFrontier/AlgebraicGeometry/Variety/Defs/Fibre.lean`, next to the instance
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField` that supplies its
only input, in a module whose import closure is three Mathlib files. It carries the hypothesis
in its name because the unqualified `AlgebraicGeometry.isLocallyNoetherian_fiber`
(`Morphisms/CohenMacaulay/FibreStalk.lean:313`) is a *different* statement, asking for
`IsLocallyNoetherian X` and no finiteness of `f`.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

/-! ### Fibres of dimension zero -/

/-- **A morphism locally of finite type all of whose fibres have dimension at most `0` is
locally quasi-finite.** Each fibre is locally Noetherian, hence locally Artinian by its
dimension bound, hence discrete. -/
theorem locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro y
  have := isLocallyNoetherian_fiber_of_locallyOfFiniteType f y
  have : IsLocallyArtinian (f.fiber y) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (by simpa using hdim y)
  exact _root_.isDiscrete_iff_discreteTopology.mpr
    ((f.fiberHomeo y).discreteTopology_iff.mp inferInstance)

/-- **A proper morphism all of whose fibres have dimension at most `0` is finite.** This is
Zariski's main theorem, [Stacks, Tag 02OH], in Mathlib's form
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`. -/
@[ega "III 4.4.5" "special case", ega "IV 18.12.4"]
theorem isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    IsFinite f :=
  have : LocallyQuasiFinite f :=
    locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero f hdim
  IsFinite.of_isProper_of_locallyQuasiFinite f

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

/-! ### Finite type from the sections over the affine opens -/

/-- **A quasi-coherent module whose sections over every affine open form a finite module is of
finite type.** This is (4) ⇒ (2) of [Stacks, Tag 01XZ], which needs no hypothesis on the scheme:
the affine opens cover, and over each of them the module is the sheaf associated with a finite
module. -/
theorem isFiniteType_of_forall_moduleFinite_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (h : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(F, U.1)) :
    F.IsFiniteType :=
  (isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F
    (exists_affineOpenCover_isFiniteTildeOn F fun U hU =>
      FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections F ⟨U, hU⟩
        (h ⟨U, hU⟩))).2

/-- **The finite-type half of [Stacks, Tag 01Y6].** The pushforward of a quasi-coherent module of
finite type along a finite morphism is of finite type. No hypothesis on the target is used: the
sections over an affine open `V` form a finite module by
`…FiniteDirectImageCoherent.moduleFinite_sections_pushforward_of_isFinite`, and finite type is
read off those by `isFiniteType_of_forall_moduleFinite_sections`.

The coherence half, `…FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`, does need
`IsLocallyNoetherian` on the target. -/
theorem isFiniteType_pushforward_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  isFiniteType_of_forall_moduleFinite_sections _ fun V =>
    FiniteDirectImageCoherent.moduleFinite_sections_pushforward_of_isFinite f F V

/-! ### The finite-type conclusion of Tag 0EX4 -/

/-- **The finite-type conclusion of [Stacks, Tag 0EX4], reduced to an affine base.** The source's
proof opens by saying that the question is local on `Y`, so that one may assume `Y = Spec R` and
prove that `H ᵈ (X, F)` is a finite `R`-module. That reduction is this statement: granted that
the sections of `R ᵈ f_* F` over every affine open of `Y` form a finite module, the module is of
finite type. Quasi-coherence, which the criterion needs, is the already-proved quasi-coherence
clause of the tag.

Properness is used only through that quasi-coherence, so the hypothesis could be weakened to
quasi-compact and quasi-separated; it is kept as the tag states it. -/
theorem rightDerived_pushforward_isFiniteType_of_isProper_of_forall_moduleFinite_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ) (F : X.Modules) [F.IsQuasicoherent]
    (h : ∀ V : Y.affineOpens,
      Module.Finite Γ(Y, V.1) Γ(((Scheme.Modules.pushforward f).rightDerived d).obj F, V.1)) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_of_forall_moduleFinite_sections _ h

/-- **[Stacks, Tag 0EX4] in the case `d = 0`, in full.** For a proper morphism all of whose
fibres have dimension at most `0`, the zeroth higher direct image of a quasi-coherent module of
finite type is of finite type.

Such a morphism is finite by Zariski's main theorem ([Stacks, Tag 02OH]), the zeroth right
derived functor of the pushforward is the pushforward
(`…DerivedPushforward.isFiniteType_rightDerived_zero_iff`), and the pushforward along a finite
morphism preserves finite type. No hypothesis on `Y` is needed.

**No `@[stacks 0EX4]` attribute is attached**: the tag asserts the conclusion for every `d`. -/
theorem rightDerived_pushforward_isFiniteType_of_isProper_of_fiber_dimension_le_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).IsFiniteType :=
  have : IsFinite f := isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero f hdim
  (DerivedPushforward.isFiniteType_rightDerived_zero_iff f F).2
    (isFiniteType_pushforward_of_isFinite f F)

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
