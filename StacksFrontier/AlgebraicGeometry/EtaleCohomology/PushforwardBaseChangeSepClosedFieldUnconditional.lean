module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedField

/-!
# Base change for pushforward over a separably closed field, with no residual hypothesis

Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite type.
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeSepClosedField.lean` proves
the covering condition of Tag 0EZX for `f` and deduces the finite-type case of Tag 0EZY with the
chain of identifications of sections of the first paragraph of the proof of Tag 0EZX left as the
hypothesis `hlocal`. That chain is
`Stacks.EtaleCohomology.local_baseChange_compatible`, proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeUnconditional.lean`, so the
canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` of a cartesian square over `f` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T` with no further hypothesis.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType` —
  base change for pushforward over a separably closed field in the case of `X` locally of finite
  type, which contains the finite-type case the source's proof of Tag 0EZY reduces to. It puts no
  hypothesis on `g`.

## Implementation notes

Stacks Tag 0EZY itself, for an arbitrary `X` over the separably closed field, is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeSepClosedFieldGeneral.lean`,
proved stalkwise rather than through the source's reduction to the finite-type case. The
finite-type case is kept here because it needs no hypothesis on `g` and no restriction on the
universe of the coefficients. The hypothesis `[LocallyOfFiniteType f]` is what the covering
condition of Tag 0EZX needs in this argument: without some finiteness on `f` an affine open of
an étale `X`-scheme need not be locally connected, and the covering is built out of connected
components of such opens.

## References

* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section SepClosedField

variable {X Y T : Scheme.{u}}

/-- **Base change for pushforward over a separably closed field, `X` locally of finite type.**
Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite type. Then in
a cartesian square over `f` the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T`, with no hypothesis on
`g`. The covering condition of Tag 0EZX holds because an affine open of an étale `X`-scheme is
Noetherian, hence locally connected (Tag 04MF), and over a separably closed field a connected
scheme is geometrically connected (Tag 0363); the bijectivity on sections over the covering is
`Stacks.EtaleCohomology.local_baseChange_compatible`. Stacks Tag 0EZY for an arbitrary `X` is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact`. -/
theorem isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType (k : Type u) [Field k]
    [IsSepClosed k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ Spec (.of k)) (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  have : Flat f := inferInstance
  exact isIso_smallEtaleSetBaseChange_of_etaleLocalFactorizationCover.{u, v} f h e g sq F
    (fun U => exists_etaleLocalFactorization_of_isSepClosed k f U)

end SepClosedField

end Stacks.EtaleCohomology

end
