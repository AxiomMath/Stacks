module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Projective
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Basic

/-!
# The projective chart of an affine scheme, and Chow's lemma modulo Segre

`StacksFrontier/AlgebraicGeometry/ChowNoetherian/Basic.lean` proves Chow's lemma over a
Noetherian base (Stacks 0200) from two hypotheses on the base, each a single tag of Stacks
chapter 29: `AlgebraicGeometry.HasAffineProjectiveChart`, which is Stacks 01VS for the structure
sheaf, and `AlgebraicGeometry.HasSegreEmbedding`, which is Stacks 01WD.

This file **discharges the first of them, for every base scheme**. An affine scheme is
quasi-affine, so `AlgebraicGeometry.exists_immersion_projectiveSpace` applies directly, and the
hypothesis holds with no assumption on the base at all. Chow's lemma over a Noetherian base is
therefore conditional on the Segre embedding alone.

## Main results

* `AlgebraicGeometry.hasAffineProjectiveChart`: **every scheme has affine projective charts**, so
  the hypothesis `AlgebraicGeometry.HasAffineProjectiveChart` is now a theorem.
* `AlgebraicGeometry.hasDenseChowModification_of_hasSegreEmbedding`: **Chow's lemma over a
  Noetherian base (Stacks 0200), granted only the Segre embedding over the base.**
* `AlgebraicGeometry.hasChowModification_of_hasSegreEmbedding`: the same in the form the proof of
  Chow's lemma over a quasi-compact quasi-separated base (Stacks 0202) consumes.

## Implementation notes

`AlgebraicGeometry.HasAffineProjectiveChart` quantifies over affine schemes `U` with a morphism
`U ⟶ S` locally of finite type, and asks for an immersion of `U` into a projective space over `S`
over `S` — no identification of the pullback of the twisting sheaf, which is why the hypothesis
is weaker than Stacks 01VS itself and why it is discharged here while that tag is not claimed.
See the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffineSpaceImmersion/Projective.lean`.

The tag `@[stacks 0200]` is still **not** attached to anything: the statements below remain
conditional on `AlgebraicGeometry.HasSegreEmbedding`, and 0200 asserts its conclusion outright.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Every scheme has affine projective charts.** An affine scheme locally of finite type over
`S` admits an immersion into a projective space over `S`, over `S`.

This is `AlgebraicGeometry.exists_immersion_projectiveSpace` for an affine source, affine
schemes being quasi-affine. -/
theorem hasAffineProjectiveChart (S : Scheme.{u}) : HasAffineProjectiveChart S :=
  fun _ _ g _ => AlgebraicGeometry.exists_immersion_projectiveSpace g

/-- **Chow's lemma over a Noetherian base (Stacks 0200), granted the Segre embedding over the
base.** A separated morphism of finite type over a Noetherian base admits a proper surjective
modification immersed in a projective space over the base, which is an isomorphism over a dense
open subscheme of the source. -/
theorem hasDenseChowModification_of_hasSegreEmbedding (hsegre : HasSegreEmbedding S) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasDenseChowModification f :=
  hasDenseChowModification_of_hasAffineProjectiveChart (hasAffineProjectiveChart S) hsegre f

/-- **Chow's lemma over a Noetherian base (Stacks 0200), granted the Segre embedding over the
base, in the form consumed by the proof of Chow's lemma over a quasi-compact quasi-separated base
(Stacks 0202).** -/
theorem hasChowModification_of_hasSegreEmbedding (hsegre : HasSegreEmbedding S) (f : X ⟶ S)
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasChowModification f :=
  (hasDenseChowModification_of_hasSegreEmbedding hsegre f).hasChowModification

end AlgebraicGeometry

end
