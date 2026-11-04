module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products and sheaf-homs of coherent modules

Let `X` be a locally Noetherian scheme and let `ℱ`, `𝒢` be coherent `𝒪_X`-modules.
[Stacks, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2) asserts that both
`ℱ ⊗_{𝒪_X} 𝒢` and `SheafHom_{𝒪_X}(ℱ, 𝒢)` are coherent.

Neither clause needs the scheme, nor the Noetherian hypothesis: the source's own proof is a
reference to the two permanence statements for coherent modules on a *ringed space*, namely
Tag 01CE (6) for the tensor product and Tag 01CQ (2) for the sheaf-hom, the latter applied to
`ℱ` through Tag 01BW (1), a coherent module is of finite presentation. So both clauses are
proved here at ringed-space generality and then specialized back to the source's statement.

The tensor clause was already in the library, at ringed-space generality, as
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`; it carries the `01Y2` attribute
there. What this file adds is the sheaf-hom clause, which completes the tag's covering set, and
the two scheme-level restatements that are the source's own statement.

## Main results

* `Stacks.AlgebraicGeometry.TensorHomCoherent.isCoherent_sheafInternalHom_of_isCoherent`:
  **the sheaf-hom clause of [Stacks, Tag 01Y2]**, on a ringed space. For coherent `ℱ` and `𝒢`,
  `SheafHom(ℱ, 𝒢)` is coherent. This declaration carries the tag; together with
  `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`, which carries it for the tensor
  clause, the covering set of `01Y2` is complete.
* `Stacks.AlgebraicGeometry.TensorHomCoherent.stacksIsCoherent_sheafInternalHom_of_isCoherent`:
  the same conclusion for the second coherence predicate of this branch. It is untagged because
  it restates a clause already registered rather than adding one, not because a tag may appear
  only once: a tag belongs on every declaration needed to state it.
* `Stacks.AlgebraicGeometry.TensorHomCoherent.isCoherent_sheafHom` and
  `Stacks.AlgebraicGeometry.TensorHomCoherent.isCoherent_tensorObj`: **the two clauses of
  [Stacks, Tag 01Y2] as the source states them**, for `ℱ`, `𝒢 : X.Modules` on a locally
  Noetherian scheme `X`, and as instances. These two carry the tag as well, because they are the
  only pair that states both of its conclusions about *one* `X` and *one* pair `ℱ`, `𝒢`: the two
  ringed-space statements above are each strictly more general, but they are indexed by two
  different spellings of the ringed space — `spaceRingedSite O` and
  `Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing X` — which instance search does
  not identify, so neither of them, nor the two together, literally state the source's lemma.
* `Stacks.AlgebraicGeometry.TensorHomCoherent.isCoherent_sheafHom_witness` and
  `Stacks.AlgebraicGeometry.TensorHomCoherent.isCoherent_tensorObj_witness`: both clauses with
  every binder instantiated, at `X = Spec ℤ` and `ℱ = 𝒢 = 𝒪_X`, by terms that assume nothing.
  They are the machine-checked record that the tag's content is not reached by the object being
  zero or the hypotheses being unsatisfiable.

## Implementation notes

**Why the scheme-level restatements are not redundant.** `AlgebraicGeometry.Scheme.Modules` is
a plain `def`, not an `abbrev`, so `X.Modules` and `SheafOfModules.{u} X.ringCatSheaf` — which
*are* interchangeable at the transparency elaboration uses — are not interchangeable for
instance search, which is syntactic; and `X.ringCatSheaf` is a third spelling again from the
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing X.toRingedSpace` that
`tensorSheaf_isCoherent` states its modules over. Concretely:
`tensorSheaf_isCoherent X.toRingedSpace F G` applied to `F G : X.Modules` fails to synthesize
`SheafOfModules.IsCoherent F` even with that very instance in scope, and the coherence
hypotheses have to be passed positionally. `isCoherent_tensorObj` does that once, so that no
consumer has to.

**`IsLocallyNoetherian` on the scheme-level statements.** It is the source's hypothesis and is
kept there, even though the proofs do not use it, so that those two declarations state Tag 01Y2
and nothing else. It is an instance binder, so it costs their use as instances nothing. The
unconditional statements are the ringed-space ones above them.

**The sheaf-hom at `𝒢 = 𝒪_X`** — the dual `ℱ^∨`, which is what the reflexivity theory of
Tags 0AY3/0EBH consumes — is already available unconditionally and as an instance, as
`Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_dualSheaf` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/HullInstances.lean`, by the route through the
first clause of Tag 01CQ. It is a special case of the clause proved here and is left alone.

## References

* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.InternalHom

universe u

namespace Stacks.AlgebraicGeometry.TensorHomCoherent

/-! ### The sheaf-hom clause, on a ringed space -/

/-- **The sheaf-hom clause of [Stacks, Tag 01Y2].** On a ringed space, the sheaf-hom
`SheafHom(ℱ, 𝒢)` between two coherent modules is coherent.

A coherent module is of finite presentation ([Stacks, Tag 01BW] (1)), and the sheaf-hom from a
module of finite presentation into a coherent module is coherent ([Stacks, Tag 01CQ] (2)). The
source states this for a locally Noetherian scheme; see `isCoherent_sheafHom` below for that
statement. -/
@[stacks 01Y2 "sheaf-hom", ega "I 9.1.1" "more general"]
theorem isCoherent_sheafInternalHom_of_isCoherent {Y : Type u} [TopologicalSpace Y]
    (O : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent (sheafInternalHom (spaceRingedSite O) F G) :=
  have := _root_.isFinitePresentation_of_isCoherent F
  isCoherent_sheafInternalHom' O F G

/-- `isCoherent_sheafInternalHom_of_isCoherent` for the coherence predicate of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, over which the coherence-closure
theory and the reflexive-hull development are stated. The two predicates agree by
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_iff`; this is the same statement as the one
above, so it adds no clause to the tag's covering set and is left untagged. -/
theorem stacksIsCoherent_sheafInternalHom_of_isCoherent {Y : Type u} [TopologicalSpace Y]
    (O : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite O).O))
    [_root_.Stacks.SheafOfModules.IsCoherent F] [_root_.Stacks.SheafOfModules.IsCoherent G] :
    _root_.Stacks.SheafOfModules.IsCoherent (sheafInternalHom (spaceRingedSite O) F G) :=
  have := _root_.Stacks.AlgebraicGeometry.ProperMapping.isCoherent_of_stacks
    (inferInstance : _root_.Stacks.SheafOfModules.IsCoherent F)
  have := _root_.Stacks.AlgebraicGeometry.ProperMapping.isCoherent_of_stacks
    (inferInstance : _root_.Stacks.SheafOfModules.IsCoherent G)
  _root_.Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
    (isCoherent_sheafInternalHom_of_isCoherent O F G)

/-! ### Stacks 01Y2 as the source states it -/

/-- **[Stacks, Tag 01Y2], the sheaf-hom clause.** Let `X` be a locally Noetherian scheme and let
`ℱ`, `𝒢` be coherent `𝒪_X`-modules. Then `SheafHom_{𝒪_X}(ℱ, 𝒢)` is coherent.

This is `isCoherent_sheafInternalHom_of_isCoherent` at the site of opens of `X` with its
structure sheaf; the Noetherian condition is the source's and is not used. -/
@[stacks 01Y2 "sheaf-hom, as the source states it: locally Noetherian scheme"]
instance isCoherent_sheafHom (X : Scheme.{u}) [IsLocallyNoetherian X] (F G : X.Modules)
    [hF : _root_.SheafOfModules.IsCoherent F] [hG : _root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent (sheafInternalHom (spaceRingedSite X.sheaf) F G) :=
  @isCoherent_sheafInternalHom_of_isCoherent _ _ X.sheaf F G hF hG

/-- **[Stacks, Tag 01Y2], the tensor-product clause.** Let `X` be a locally Noetherian scheme and
let `ℱ`, `𝒢` be coherent `𝒪_X`-modules. Then `ℱ ⊗_{𝒪_X} 𝒢` is coherent.

This is `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`, which carries the tag, read at
the `AlgebraicGeometry.Scheme.Modules.tensorObj` spelling of the tensor product; the Noetherian
condition is the source's and is not used. -/
@[stacks 01Y2 "tensor product, as the source states it: locally Noetherian scheme"]
instance isCoherent_tensorObj (X : Scheme.{u}) [IsLocallyNoetherian X] (F G : X.Modules)
    [hF : _root_.SheafOfModules.IsCoherent F] [hG : _root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent (Scheme.Modules.tensorObj F G) :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG

/-! ### A non-degenerate witness for both clauses -/

/-- The witness scheme for Tag 01Y2: `Spec ℤ`. It is locally Noetherian because `ℤ` is a
Noetherian ring, and it is not degenerate — it is non-empty, irreducible and one-dimensional,
and its structure sheaf has `ℤ` for global sections, so neither clause of the tag is being
reached here by the object being zero. -/
abbrev witnessScheme : Scheme.{0} := Spec (CommRingCat.of ℤ)

/-- The structure sheaf of `Spec ℤ`, the witness module for both clauses of Tag 01Y2. -/
abbrev witnessModule : witnessScheme.Modules := SheafOfModules.unit witnessScheme.ringCatSheaf

/-- The witness module is coherent, with nothing assumed: `Spec ℤ` is locally Noetherian and the
structure sheaf of a locally Noetherian scheme is coherent ([Stacks, Tag 01XZ]). -/
theorem isCoherent_witnessModule : _root_.SheafOfModules.IsCoherent witnessModule :=
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := witnessScheme)

/-- **The sheaf-hom clause of [Stacks, Tag 01Y2] is not vacuous**: every binder of
`isCoherent_sheafHom` is instantiated here by a term that assumes nothing, at a scheme and a
module that are not degenerate. Compare `isCoherent_sheafHom` itself, whose conclusion is *not*
available without the two coherence hypotheses — dropping either one leaves
`SheafOfModules.IsCoherent (sheafInternalHom (spaceRingedSite O) F G)` unsynthesizable, as it
must, since `SheafHom(𝒪_X, 𝒢) ≅ 𝒢` and `SheafHom(⊕_ℕ 𝒪_X, 𝒪_X) ≅ ∏_ℕ 𝒪_X`. -/
theorem isCoherent_sheafHom_witness :
    _root_.SheafOfModules.IsCoherent
      (sheafInternalHom (spaceRingedSite witnessScheme.sheaf) witnessModule witnessModule) :=
  have := isCoherent_witnessModule
  isCoherent_sheafHom witnessScheme witnessModule witnessModule

/-- **The tensor clause of [Stacks, Tag 01Y2] is not vacuous**, by the same witness. -/
theorem isCoherent_tensorObj_witness :
    _root_.SheafOfModules.IsCoherent
      (Scheme.Modules.tensorObj witnessModule witnessModule) :=
  have := isCoherent_witnessModule
  isCoherent_tensorObj witnessScheme witnessModule witnessModule

end Stacks.AlgebraicGeometry.TensorHomCoherent

end
