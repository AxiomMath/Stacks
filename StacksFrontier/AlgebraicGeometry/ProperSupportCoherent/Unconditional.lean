module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic

/-!
# Higher direct images of a module with proper support are coherent

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type — *not*
proper — and let `F` be a coherent `𝒪_X`-module whose support is proper over `S` in the sense of
[Stacks, Tag 0CYM]. Then `R ᵖ f_* F` is a coherent `𝒪_S`-module for every `p`, and so is
`f_* F`. This is [Stacks, Tag 08DS].

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_higherDirectImage_of_properSupp`:
  **[Stacks, Tag 08DS]** — `R ᵖ f_* F` is coherent in every degree `p : ℤ`.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_directImage_of_properSupp`: the
  same for the ordinary direct image `f_* F`, which is `R ⁰ f_* F`.

## Implementation notes

The hypotheses on `F` are quasi-coherence together with finite type rather than coherence: `X`
is locally Noetherian, being locally of finite type over a locally Noetherian base, and on a
locally Noetherian scheme the two conditions agree ([Stacks, Tag 01XZ]).

The degrees here are all of `ℤ`, where the source states `p ≥ 0`; in negative degrees the higher
direct image vanishes and the conclusion is the coherence of a zero object.

## References

* [Stacks Project, Tag 08DS](https://stacks.math.columbia.edu/tag/08DS)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

-- The statements below have to spell out `R ᵖ f_* F`, so they have to be elaborated at the same
-- derived category as the reduction in
-- `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Basic.lean`, namely
-- `CategoryTheory.HasDerivedCategory.standard`. The import cone of Chow's lemma contributes a
-- competing `HasDerivedCategory` instance, so the precedence is raised here.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type and let `F` be a
quasi-coherent `𝒪_X`-module of finite type whose support is proper over `S`. Then the higher
direct image `R ᵖ f_* F` is a coherent `𝒪_S`-module in every degree. -/
@[stacks 08DS]
theorem isCoherent_higherDirectImage_of_properSupp
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩) (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent :=
  isCoherent_rightDerivedPlus_of_isProperOver_supp f F hF
    (fun Z g hg G hG q =>
      _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent
        Z S g ‹_› hg G hG q) p

/-- Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type and let `F` be a
quasi-coherent `𝒪_X`-module of finite type whose support is proper over `S`. Then the direct
image `f_* F` is a coherent `𝒪_S`-module. -/
theorem isCoherent_directImage_of_properSupp
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩) :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  isCoherent_pushforward_of_isProperOver_supp f F hF
    (fun Z g hg G hG q =>
      _root_.AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent
        Z S g ‹_› hg G hG q)

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
