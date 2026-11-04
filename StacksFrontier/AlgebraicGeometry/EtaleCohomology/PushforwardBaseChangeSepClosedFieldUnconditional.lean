module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeSepClosedField

/-!
# Base change for pushforward over a separably closed field, with no residual hypothesis

Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite type.
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeSepClosedField.lean` proves
the covering condition of Tag 0EZX for `f` and deduces Tag 0EZY with the chain of
identifications of sections of the first paragraph of the proof of Tag 0EZX left as the
hypothesis `hlocal`. That chain is
`Stacks.EtaleCohomology.local_baseChange_compatible`, proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeUnconditional.lean`, so the
canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` of a cartesian square over `f` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T` with nothing assumed.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType` —
  **Tag 0EZY** in the case of `X` locally of finite type over the separably closed field, which
  contains the source's finite-type case.

## Implementation notes

The source reduces the general case to the finite-type case in two steps, and neither is
available here, so only the finite-type case is asserted. The hypothesis `[LocallyOfFiniteType f]`
is accordingly more than the source's own statement assumes, and it is the first step that needs
it: without some finiteness on `f` an affine open of an étale `X`-scheme need not be locally
connected, and the covering is built out of connected components of such opens.

The first step is "we may work locally on `X`", which reduces an arbitrary `X` to an affine one.
That is Tag 0EZR clause (1), proved as
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_of_isIso_local` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/OrdinaryLocalityCriterion.lean`,
but about a different map: `Stacks.EtaleCohomology.smallEtaleSetsBaseChange`, the mate of the
composite of the two composition isomorphisms of direct images, where
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` is the mate of the corresponding two-square of
sheaf pushforwards. Nothing in the library identifies them, so the locality criterion cannot be
applied to this square as it stands.

The second step writes an affine `X` as a cofiltered limit of affine schemes of finite type over
`Spec k` and appeals to the compatibility of the base change map with such limits, Tag 0EZT part
(1). Tag 0EZT is carried only in part (2), for abelian coefficients and the higher direct images;
part (1) — sheaves of sets and the underived direct image — is not, and it would rest on the
set-valued form of the colimit assertion of Tag 0EYM, which has no carrier either.

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

/-- **Stacks Project, Tag 0EZY**, in the case of `X` locally of finite type over the separably
closed field. Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite
type. Then in a cartesian square over `f` the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F`
is an isomorphism for every sheaf of sets `F` on the small étale site of `T`. -/
@[stacks 0EZY "the case of `X` of finite type over the separably closed field, stated for `X`
locally of finite type. What is proved unconditionally is the covering condition of Tag 0EZX:
an affine open of an étale `X`-scheme is Noetherian, hence locally connected by Tag 04MF, so
the connected component of any of its points is an open quasi-compact subscheme, and over a
separably closed field a connected scheme is geometrically connected by Tag 0363; flatness of
`f` is automatic over a field. The chain of identifications of sections on which Tag 0EZX feeds
is supplied too, by `local_baseChange_compatible`, exactly as in Tags 0EZX, 0EYS and 0EZZ. What
is not asserted is the source's reduction of the general case to this one, which takes two steps.
Working locally on `X` to reduce to an affine `X` is Tag 0EZR clause (1), and that clause is now
proved, as `isIso_smallEtaleSetsBaseChange_of_isIso_local`; but it is proved about
`smallEtaleSetsBaseChange`, a second set-valued base change map built in
`BaseChangeHigher/OrdinaryLocality.lean` from the composition isomorphisms of direct images,
which no result identifies with the `smallEtaleSetBaseChange` of this square. The second step
writes an affine `X` as a cofiltered limit of affine finite-type `Spec k`-schemes and uses the
compatibility of the base change map with such limits, which is Tag 0EZT part (1); the two 0EZT
carriers give the cartesian square on the limits and part (2), for abelian coefficients and the
higher direct images, and part (1) -- sheaves of sets and the underived direct image, the form
this map takes -- has no carrier, nor has the set-valued colimit assertion of Tag 0EYM it would
be built from. The hypothesis that `f` be locally of finite type is therefore still needed, and
is more than the source's statement assumes."]
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
