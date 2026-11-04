module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekProperQCoh

/-!
# Sheafy duality for a proper morphism, for Nagata compactifications

In Situation [Stacks, Tag 0AU4], for the upper shriek functors of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`), let `f : X ⟶ Y` be a proper morphism of schemes of finite
type over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`. Then
`Rf_* R𝓗om(L, ω_X^•) ≅ R𝓗om(Rf_* L, ω_Y^•)` for every `L` in `D_QCoh(𝒪_X)`, the second
isomorphism of [Stacks, Tag 0B6X].

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.sheafHomDualizingIsoNagata`: [Stacks, Tag 0B6X], the second
  isomorphism.

## References

* [Stacks Project, Tag 0B6X](https://stacks.math.columbia.edu/tag/0B6X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom push qcoh)

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0B6X], the second isomorphism.** In Situation 0AU4, for a proper `f : X ⟶ Y` of
schemes of finite type over `S`, the dualizing complexes `ω_X^•`, `ω_Y^•` normalized relative to
`ω_S^•` and every `L` in `D_QCoh(𝒪_X)`, `Rf_* R𝓗om(L, ω_X^•) ≅ R𝓗om(Rf_* L, ω_Y^•)`: the sheafy
trace map at `ω_Y^•` composed with `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]). -/
@[stacks 0B6X]
def sheafHomDualizingIsoNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (L : Std X) (hL : qcoh X L) :
    (push f).obj (((sheafHom X).obj (op L)).obj (stdComplex nagataCompactification 𝒦X)) ≅
      ((sheafHom Y).obj (op ((push f).obj L))).obj (stdComplex nagataCompactification 𝒦Y) :=
  sheafHomDualizingIsoOfQCoh nagataCompactification hpe hωS 𝒦X 𝒦Y L hL

end NormalizedOnOpens

end Stacks.Duality
