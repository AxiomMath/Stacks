module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of the twisting sheaves on `Proj`

The dévissage of [Stacks, Tag 02O6] is applied on projective space with the family `𝒯` taken to
be the twists `𝒪(d)`, and every form of it asks for the members of `𝒯` to be coherent. This file
supplies that, for `Proj` of a Noetherian graded ring generated in degree one.

The argument is two steps and uses no tensor product. A twisting sheaf of a graded ring
generated in degree one is invertible, and `Proj` of a Noetherian graded ring is a Noetherian
scheme; an invertible module on a locally Noetherian scheme is coherent. Both inputs are proved
and public.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistingSheaf`: the twisting sheaves of
  a Noetherian graded ring generated in degree one are coherent.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistingSheaf_polyGrading`: the same on
  `Proj R[T₀, …, Tₙ]` for a Noetherian coefficient ring, which is the model the Čech machinery
  of [Stacks, Tag 01XT] lives on.
* `AlgebraicGeometry.isCoherent_pullback_projectiveSpaceAtUniverseTwistingSheaf`: the same two
  steps on the *library* model `projectiveSpaceOverRing n R`, so the statement holds on both
  models of projective space and not only on the one carrying the Čech machinery.
* `forall_finiteDimensional_cohomologyOverField_projModel_twistingSheaf`, in
  `Stacks.ProjectiveCohomology`: the dévissage of [Stacks, Tag 02O6] on `Proj k[T₀, …, Tₙ]`
  with the coherence hypothesis of the family discharged at the twists.

## Implementation notes

**No attribute is attached.** Coherence of an invertible module on a locally Noetherian scheme
is Tag 01XZ and is carried by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible`. Everything here is a
specialisation of that theorem to a particular module on a particular scheme, so attaching the
tag again would put one tag on three constants — the same hazard as for the two
`SheafOfModules.IsCoherent` classes, which both carry 01BY.

**The route does not go through a tensor product, and an earlier pricing said it had to.** The
nearest neighbour,
`AlgebraicGeometry.isCoherent_projectiveTwist`, is about `ℱ ⊗ π^*𝒪(d)` for an already-coherent
`ℱ`, and reaching `𝒪(d)` from it at `ℱ = 𝒪` would need the left unitor `𝒪 ⊗ 𝒪(d) ≅ 𝒪(d)` at the
`Scheme.Modules` spelling. None of that is used: `isCoherent_of_isInvertible` takes the
invertible module directly.

**Which hypotheses do work.** Dropping `[IsNoetherianRing S]` makes
`IsLocallyNoetherian (AlgebraicGeometry.Proj 𝒮)` unsynthesizable, and dropping the invertibility
of the twisting sheaf — which is where `hgen` is used — makes the coherence criterion
inapplicable.

**Satisfiability.** `isCoherent_twistingSheaf_polyGrading` discharges every hypothesis of
`isCoherent_twistingSheaf` with no assumption beyond Noetherianness of the coefficient ring, so
the hypothesis set is not vacuous.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.ProjectiveCohomology (polyGrading projModelToSpec)

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An invertible module, in the `AlgebraicGeometry` sense, on a locally Noetherian scheme is
coherent. -/
private theorem isCoherent_of_algebraicGeometry_isInvertible (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F) :
    _root_.SheafOfModules.IsCoherent F :=
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr h
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X F

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

/-- **The twisting sheaves of a Noetherian graded ring generated in degree one are coherent.**
They are invertible, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.algebraicGeometry_isInvertible_twistingSheaf`, and
`AlgebraicGeometry.Proj` of a Noetherian graded ring is a Noetherian scheme by [Stacks, Tag
0B5Q], so an invertible module on it is coherent by [Stacks, Tag 01XZ]. -/
@[ega "III 2.3.4" "partial"]
public theorem isCoherent_twistingSheaf {S : Type u} {σ : Type w} [CommRing S]
    [IsNoetherianRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (n : ℤ) :
    _root_.SheafOfModules.IsCoherent (twistingSheaf 𝒮 n) :=
  isCoherent_of_algebraicGeometry_isInvertible (AlgebraicGeometry.Proj 𝒮) _
    (algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen n)

/-- **The twisting sheaves on `Proj R[T₀, …, Tₙ]` are coherent** for a Noetherian coefficient
ring: a polynomial ring is generated in degree one and is Noetherian. -/
public theorem isCoherent_twistingSheaf_polyGrading (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ) (d : ℤ) :
    _root_.SheafOfModules.IsCoherent (twistingSheaf (polyGrading R n) d) :=
  isCoherent_twistingSheaf (polyGrading R n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R) d

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace AlgebraicGeometry

/-- **The twists on the library model of projective space are coherent.** `𝒪(d)` on
`projectiveSpaceOverRing n R` — presented, as everywhere on this import surface, as the pullback
of the twisting sheaf of the integral model — is invertible by
`AlgebraicGeometry.isInvertible_pullback_projectiveSpaceAtUniverseTwistingSheaf` and the model is
locally Noetherian by `AlgebraicGeometry.projectiveSpaceOver_isLocallyNoetherian`, so [Stacks,
Tag 01XZ] applies exactly as it does on the `Proj` model.

The two models of projective space are not identified here and nothing below needs them to be:
this is the same two-step argument run a second time, not a transport. -/
public theorem isCoherent_pullback_projectiveSpaceAtUniverseTwistingSheaf (R : Type u)
    [CommRing R] [IsNoetherianRing R] (n : ℕ) (d : ℤ) :
    _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback
        (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
        (projectiveSpaceAtUniverseTwistingSheaf n d)) :=
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (.of R)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of R))
  isCoherent_of_algebraicGeometry_isInvertible (projectiveSpaceOverRing n (.of R)) _
    (isInvertible_pullback_projectiveSpaceAtUniverseTwistingSheaf (R := R) n d)

end AlgebraicGeometry

namespace Stacks.ProjectiveCohomology

-- `open AlgebraicGeometry` inside a `Stacks.*` namespace resolves to `Stacks.AlgebraicGeometry`,
-- which exists and does not contain these names; the `_root_.` prefix is load-bearing.
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj
  (twistingSheaf isCoherent_twistingSheaf_polyGrading)

/-- **The dévissage of [Stacks, Tag 02O6] on `Proj k[T₀, …, Tₙ]` at the family of twists.**
`forall_finiteDimensional_cohomologyOverField_projModel_of_epi_biprodPow`, of
`Stacks.ProjectiveCohomology`, asks of its family that each member be coherent, that the
cohomology of each member be finite-dimensional in the degrees `0, …, n`, and that every
coherent module be a quotient of a power of a member. At the twists `𝒪(-d)` the first of
those is discharged here, leaving the Čech computation of [Stacks, Tag 01XT] and clause (1)
of [Stacks, Tag 01YS].

The twists are fed into the family slot by bare term application, with no bridging lemma and no
model comparison. -/
public theorem forall_finiteDimensional_cohomologyOverField_projModel_twistingSheaf
    (k : Type u) [Field k] (n : ℕ)
    (hTle : ∀ d : ℕ, ∀ q ≤ n, FiniteDimensional k
      (cohomologyOverField k (projModelToSpec k n)
        (twistingSheaf (polyGrading k n) (-(d : ℤ))) q))
    (hgen : ∀ G : (AlgebraicGeometry.Proj (polyGrading k n)).Modules,
      _root_.SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : Scheme.Modules.biprodPow
        (X := AlgebraicGeometry.Proj (polyGrading k n))
        (twistingSheaf (polyGrading k n) (-(d : ℤ))) r ⟶ G, Epi φ) :
    ∀ G : (AlgebraicGeometry.Proj (polyGrading k n)).Modules,
      _root_.SheafOfModules.IsCoherent G →
      ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) G q) :=
  forall_finiteDimensional_cohomologyOverField_projModel_of_epi_biprodPow k n
    (fun d => twistingSheaf (polyGrading k n) (-(d : ℤ)))
    (fun d => isCoherent_twistingSheaf_polyGrading k n (-(d : ℤ))) hTle hgen

end Stacks.ProjectiveCohomology

end
