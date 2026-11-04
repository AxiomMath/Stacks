module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration

/-!
# The initial dévissage criterion for properties of coherent modules

[Stacks, Tag 01YG] checks a property `P` of coherent modules on a Noetherian scheme `X` on a
single family of test objects: the direct images `i_* I` of quasi-coherent ideals
`I ⊆ 𝒪_Z` along the closed immersions `i : Z ⟶ X` of integral closed subschemes. If `P` holds
on those, holds on the zero module, and is stable under extensions, then `P` holds on every
coherent module.

The proof combines two ingredients.
`Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration` is [Stacks, Tag 01YF]: every
coherent module carries a finite filtration by coherent submodules whose successive quotients are
such direct images. The induction along such a filtration is
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealFiltration`, which takes
the existence of these filtrations as a hypothesis; Tag 01YF supplies it.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent`: a property `P` of coherent
  modules on a Noetherian scheme holds on every coherent module as soon as it holds on the zero
  module and on the direct images `i_* I`, and is stable under extensions.

## Implementation notes

**The hypothesis on the zero module is not redundant.** The source lists only extension
stability and the test family, but with those two alone the lemma is false: on
`Spec` of the zero ring — a Noetherian scheme — there is no integral closed subscheme at all,
since an integral scheme is irreducible and hence nonempty, so the test family is empty and the
extension hypothesis is vacuous, while the zero module is coherent. Taking `P` to be
`fun _ => False` satisfies both hypotheses and fails the conclusion. The hypothesis
`P (⊤_ X.Modules)` is what the source's own induction starts from — its filtration begins at
`0 = F_0` — and it is the form the project's statement of this tag uses. It is also the only
thing the two-out-of-three variants [Stacks, Tag 01YH] and [Stacks, Tag 01YL] have to supply
before they can call this criterion: their stronger exactness hypothesis implies it.

**`_root_.SheafOfModules.IsCoherent` is written out.** Coherence has two declarations, and
inside the `Stacks.` namespace an unqualified spelling can resolve to
`Stacks.SheafOfModules.IsCoherent`. The dévissage engine is stated against the root constant, so
a relative name would state a different theorem.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

/-- Let `X` be a Noetherian scheme and let `P` be a property of
coherent `𝒪_X`-modules which holds on the zero module, is stable under extensions of coherent
modules, and holds on the direct image `i_* I` of every quasi-coherent ideal `I ⊆ 𝒪_Z` along
the closed immersion of every integral closed subscheme `i : Z ⟶ X`. Then `P` holds on every
coherent `𝒪_X`-module.

Every coherent module is filtered by such direct images ([Stacks, Tag 01YF]), and extension
stability propagates `P` along the filtration. -/
@[stacks 01YG]
public theorem property_of_isCoherent (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop) (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F :=
  property_of_forall_hasIdealFiltration P
    (fun F hF => @hasIdealFiltration X _ F hF) hzero hext hideal

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
