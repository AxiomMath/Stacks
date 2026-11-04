module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chow's lemma over an affine Noetherian base

Chow's lemma over a Noetherian base was proved in
`StacksFrontier/AlgebraicGeometry/Limits/ChowLemmaNoetherian.lean` from one named condition on the
base, `AlgebraicGeometry.AffineImmersionIntoProjectiveSpace`: that every affine scheme locally of
finite type over the base admits an immersion into a projective space over the base, over the
base. This file discharges that condition over an **affine** base, so that Chow's lemma over an
affine Noetherian base is unconditional.

The discharge is immediate from
`AlgebraicGeometry.exists_isImmersion_projectiveSpaceOver_of_isAffine`: the coordinate ring of an
affine scheme of finite type over an affine base is a quotient of a polynomial ring over the
coordinate ring of the base, so the scheme closed-immerses into an affine space over the base,
and an affine space over the base is a standard chart of a projective space over the base.

## Main results

* `AlgebraicGeometry.affineImmersionIntoProjectiveSpace_of_isAffine`: the condition holds over
  any affine base — no Noetherian hypothesis is needed for it.
* `AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_isAffine`: **Chow's lemma over an
  affine Noetherian base**, unconditionally, with the dense open over which the modification is
  an isomorphism.
* `AlgebraicGeometry.hasChowModification_of_isAffine`: the same without the dense open, which is
  the form `AlgebraicGeometry.HasChowModification` records.

## Implementation notes

No `@[stacks 0200]` attribute is attached. Tag 0200 is Chow's lemma over an arbitrary Noetherian
base, and what is proved here is its affine-base case. The general case is not obtained by
proving `AffineImmersionIntoProjectiveSpace` for a general Noetherian base: that condition asks
for an immersion into a projective space over the *whole* base, which for an affine scheme of
finite type over a base that is not affine is the assertion that it is quasi-projective over the
base, and the construction of Chow's lemma does not supply it. The general case instead has to
localise the choice of charts over an affine open covering of the base.

The affine-base case is nevertheless the case the theory of coherent higher direct images
consumes, since
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase` reduces
coherence of the higher direct images of a proper morphism to an affine base.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- **Every affine scheme locally of finite type over an affine base immerses into a projective
space over that base.** This discharges the one input of Chow's lemma over a Noetherian base,
`AlgebraicGeometry.AffineImmersionIntoProjectiveSpace`, whenever the base is affine; the
Noetherian hypothesis plays no part. -/
theorem affineImmersionIntoProjectiveSpace_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    AffineImmersionIntoProjectiveSpace S := by
  intro Y g hY hg
  have := hY
  have := hg
  exact exists_isImmersion_projectiveSpaceOver_of_isAffine g

/-- **Chow's lemma over an affine Noetherian base.** A separated morphism of finite type
`f : X ⟶ S` with `S` affine and Noetherian admits a proper surjective `π : Y ⟶ X` and an
immersion `Y ⟶ ℙⁿ_S` over `S`, with `π` an isomorphism above a dense open subscheme of `X`.

This is `AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_affineImmersion` with its
hypothesis discharged by `affineImmersionIntoProjectiveSpace_of_isAffine`. -/
@[ega "II 5.6.1" "(i), special case, (ii)"]
theorem hasChowModificationIsoOnDenseOpen_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasChowModificationIsoOnDenseOpen f :=
  hasChowModificationIsoOnDenseOpen_of_affineImmersion f
    (affineImmersionIntoProjectiveSpace_of_isAffine S)

/-- **Chow's lemma over an affine Noetherian base**, in the form without the dense open. -/
theorem hasChowModification_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    HasChowModification f :=
  (hasChowModificationIsoOnDenseOpen_of_isAffine f).hasChowModification

/-- **Chow's lemma for a proper morphism to an affine Noetherian base.** A proper morphism is
separated, locally of finite type and quasi-compact, so this is a special case of
`hasChowModification_of_isAffine`.

This is the shape the consumers of Chow's lemma in this development ask for — see the
hypothesis `hchow` of
`AlgebraicGeometry.exists_standardPHCovering_refinement_bind_of_chowLemma` and of
`AlgebraicGeometry.isPHCovering_bind_of_chowLemma` — except that those quantify over an
arbitrary affine target, where [Stacks, Tag 0202] holds with no Noetherian hypothesis. -/
theorem hasChowModification_of_isAffine_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    [IsNoetherian S] [IsProper f] : HasChowModification f :=
  hasChowModification_of_isAffine f

end AlgebraicGeometry

end
