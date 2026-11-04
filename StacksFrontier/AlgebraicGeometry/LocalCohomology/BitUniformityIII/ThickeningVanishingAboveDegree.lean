module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceTwistBound.Basic

/-!
# Vanishing of the cohomology of the thickening twists above a fixed degree

Let `A` be a commutative Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of
`Spec(A)` in `I`. This file discharges two of the eleven fields of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`, the Situation of [Stacks, Tag 0GA6] read
on `X`:

* the integer `d`, and
* `base_vanishing_gt`, the vanishing `Hⁱ(X, 𝒪_Y(q)) = 0` for `i > d` and **every** `q`.

They are discharged together, as they must be: `base_vanishing_gt` is a property of the data
field `d`, so neither can become a theorem while the other is a field. What replaces the two is
the single existential
`Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH_thickeningTwist`.

## Why this is not Grothendieck vanishing

The Stacks proof of Tag 0GA7 takes `d = d(S)` to be the maximum of the dimensions of the fibres
of `p : X → Spec(A)` and quotes vanishing above the fibre dimension ([Stacks, Tag 02V7]). That
route is not available here: 02V7 is formalized in this library only at fibre dimension zero.

It is also not needed. Nothing in Tag 0GA7 uses that `d` *is* the fibre dimension — the four
clauses quantify over `i` against `d` and never compute with it — so any `d` with the vanishing
property serves, and a `d` with that property exists for a much softer reason: `X` is
quasi-compact and quasi-separated, so a *finite* affine open cover of `X` exists and Čech
cohomology for it vanishes above the cover's cardinality ([Stacks, Tag 071L], in the form
`AlgebraicGeometry.exists_isZero_hgroup_top`). That bound is uniform in the sheaf, which is why
the theorem below is stated for every quasi-coherent sheaf at once and then specialised, and in
particular it is uniform in `q` — which is exactly what the field asks for, the vanishing above
`d` carrying no threshold on `q`.

The two hypotheses on `X` are available: `CompactSpace` from
`Stacks.Blowup.instIsProperToSpec`, and quasi-separatedness from
`Stacks.Blowup.instIsSeparatedToSpec` over the affine base, which needs no finiteness at all.

## Main results

* `Stacks.LocalCohomology.UniformityIII.quasiSeparatedSpace_blowupScheme`: `X` is
  quasi-separated, because it is separated over the affine `Spec(A)`.
* `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_blowupTwist`,
  `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_thickeningTwist`: `𝒪_X(q)` and
  `𝒪_{Yₙ}(q)` are quasi-coherent.
* `Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH`: a vanishing degree
  for `X` uniform in the quasi-coherent sheaf.
* `Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH_thickeningTwist`:
  **the two fields**, `∃ d, Hⁱ(X, 𝒪_{Yₙ}(q)) = 0` for all `n`, all `q` and every `i > d`.

## References

* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The blowup is quasi-separated.** It is separated over `Spec(A)`
(`Stacks.Blowup.instIsSeparatedToSpec`), hence quasi-separated over it, and the base is affine
and so quasi-separated itself. No Noetherian hypothesis is needed. -/
instance quasiSeparatedSpace_blowupScheme : QuasiSeparatedSpace (blowupScheme I) :=
  (quasiSeparated_iff_quasiSeparatedSpace (Stacks.Blowup.toSpec I)).mp inferInstance

/-- **`𝒪_X(q)` is quasi-coherent**, at the `(blowupScheme I).Modules` spelling of the category.
This is Tag 01MB for the twisting sheaves of a `Proj`, which instance search does not reach
across the `def` `AlgebraicGeometry.Scheme.Modules`. -/
instance isQuasicoherent_blowupTwist (q : ℕ) : (blowupTwist I q).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf
    (Stacks.Blowup.reesGrading I) (q : ℤ)

/-- **`𝒪_{Yₙ}(q)` is quasi-coherent**: it is the tensor product of the quasi-coherent
`𝒪_{Yₙ} = ι_* 𝒪_{Yₙ}`, the direct image of a structure sheaf along a closed immersion, with the
quasi-coherent `𝒪_X(q)`, and the tensor product of quasi-coherent modules is quasi-coherent
([Stacks, Tag 01CE]). -/
instance isQuasicoherent_thickeningTwist (n q : ℕ) : (thickeningTwist I n q).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj (X := blowupScheme I)
    (thickeningSheaf I n) (blowupTwist I q) inferInstance inferInstance

/-- **A vanishing degree for the cohomology of the blowup, uniform in the sheaf.** There is a
`d` with `Hⁱ(X, ℱ) = 0` for every quasi-coherent `ℱ` and every `i > d`.

This is `AlgebraicGeometry.exists_isZero_hgroup_top` — [Stacks, Tag 071L] for a finite affine
open cover — at `X`, which is quasi-compact (`Stacks.Blowup.instIsProperToSpec`) and
quasi-separated (`quasiSeparatedSpace_blowupScheme`). -/
theorem exists_forall_subsingleton_blowupH [IsNoetherianRing A] :
    ∃ d : ℕ, ∀ F : (blowupScheme I).Modules, F.IsQuasicoherent → ∀ i : ℕ, d < i →
      Subsingleton (blowupH I i F) :=
  (AlgebraicGeometry.exists_isZero_hgroup_top (blowupScheme I)).imp
    fun _ hd F hF i hi => AddCommGrpCat.subsingleton_of_isZero (hd F hF i hi.le)

/-- **The fields `d` and `base_vanishing_gt` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`, discharged together.** There is a `d`
such that `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0` for every thickening `Yₙ` of the exceptional divisor, every
twist `q` and every `i > d`.

The field asks for this at `n = 1` only, and with no threshold on `q`; both are met, the latter
because the degree produced by `exists_forall_subsingleton_blowupH` depends on `X` alone and not
on the sheaf. The vanishing for `n ≥ 2` is free for the same reason and is not the induction of
the Stacks proof — that induction is
`Stacks.LocalCohomology.UniformityIII.subsingleton_thickeningH`, which carries the vanishing in
the range `1 ≤ i ≤ d` up the thickenings and still needs the first short exact sequence. -/
theorem exists_forall_subsingleton_blowupH_thickeningTwist [IsNoetherianRing A] :
    ∃ d : ℕ, ∀ n i q : ℕ, d < i → Subsingleton (blowupH I i (thickeningTwist I n q)) :=
  (exists_forall_subsingleton_blowupH I).imp
    fun _ hd n i q hi => hd (thickeningTwist I n q) inferInstance i hi

end Stacks.LocalCohomology.UniformityIII

end
