module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.ModuleFinite

/-!
# The sheaf associated with a finite graded module on `Proj` of a Noetherian graded ring is
coherent

Let `A` be a graded ring which is Noetherian as a ring, let `M` be a finite graded `A`-module and
let `X = Proj A`. This file proves that the quasi-coherent `𝒪_X`-module `M̃` is **coherent**.

Everything the proof needs was already in the library, in two separate places, and the only thing
missing was that neither was stated for a general graded module:

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_associatedModuleSheaf` — `M̃` is of
  finite type as soon as `A` is a finite type algebra over `A₀`, which for `A` Noetherian is
  `Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`. Its local input is Tag 07Z2 (2),
  the finiteness of the degree-zero localization `M₍f₎` over `A₍f₎`.
* `Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType` —
  (2) ⇒ (1) of [Stacks, Tag 01XZ]: on a locally Noetherian scheme a quasi-coherent module of
  finite type is coherent. `Proj A` is Noetherian by
  `Stacks.AlgebraicGeometry.Proj.isNoetherian_proj` (Tag 0B5Q), and `M̃` is quasi-coherent by
  `AlgebraicGeometry.associatedModuleSheaf_isQuasicoherent` (Tag 01MB).

The statement is given for both of the library's coherence predicates, which are the same two
conditions under two names: `Stacks.SheafOfModules.IsCoherent` of Tag 01BV and
`SheafOfModules.IsCoherent` of Tag 01BW.

## Why this is wanted

It is the hypothesis every finiteness statement about `Proj` is phrased against. [Stacks, Tag
0B5R] opens its proof of part (2) with "Because `M` is a finite `A`-module we see that `M̃` is a
finite type `𝒪_X`-module, i.e., a coherent `𝒪_X`-module", and [Stacks, Tag 0AG7] opens the same
way; both then feed `M̃` to a result about coherent sheaves. Tag 02O6, the finiteness of
`Hⁱ(X, ℱ)` over a Noetherian affine base, also takes a coherent sheaf, and `Proj A → Spec A₀` is
proper for `A` Noetherian, so this is what lets 02O6 be applied to `M̃(n)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheaf`, for the
  coherence predicate of [Stacks, Tag 01BW].
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.stacksIsCoherent_associatedModuleSheaf`, for the
  coherence predicate of [Stacks, Tag 01BV].
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheafFunctor_obj` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.stacksIsCoherent_associatedModuleSheafFunctor_obj`:
  the same two for a bundled graded module, which is the form the associated-sheaf functor of
  [Stacks, Tag 01M7] presents its values in.

## Implementation notes

No `stacks` attribute is attached. The assertion is a sentence inside the proofs of Tags 0AG7 and
0B5R rather than a numbered statement of either, and the tags whose statements it is a case of —
01XZ and 07Z2 — are registered on the general results used here.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 07Z2](https://stacks.math.columbia.edu/tag/07Z2)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped Stacks.GradedLocalization

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w t

variable {A M : Type u} {σ : Type w} {τ : Type t}
  [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- **The sheaf associated with a finite graded module over a Noetherian graded ring is
coherent**, for the coherence predicate of [Stacks, Tag 01BV]. -/
public theorem stacksIsCoherent_associatedModuleSheaf :
    Stacks.SheafOfModules.IsCoherent
      (associatedModuleSheaf 𝒜 𝒨 : (AlgebraicGeometry.Proj 𝒜).Modules) := by
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  have hqc : SheafOfModules.IsQuasicoherent.{u, u, u} (associatedModuleSheaf 𝒜 𝒨) := inferInstance
  let F : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  let _ : F.IsQuasicoherent := hqc
  have : SheafOfModules.IsFiniteType.{u, u, u} F := isFiniteType_associatedModuleSheaf 𝒜 𝒨
  exact Stacks.AlgebraicGeometry.CoherentTFAE.stacksIsCoherent_of_isQuasicoherent_of_isFiniteType F

/-- **The sheaf associated with a finite graded module over a Noetherian graded ring is
coherent**, for the coherence predicate of [Stacks, Tag 01BW] — the spelling the finiteness
results about twisted global sections are stated against.

`Proj A` is a Noetherian scheme, `M̃` is quasi-coherent, and `M̃` is of finite type because the
degree-zero localization `M₍f₎` is a finite `A₍f₎`-module on each standard open; on a locally
Noetherian scheme those three facts are coherence.

Finite type of `A` over `A₀` is *derived* here from `A` being Noetherian
(`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`) rather than assumed, so no
`Algebra.FiniteType (𝒜 0) A` binder appears and a consumer that only knows `A` Noetherian can
apply this directly. -/
public theorem isCoherent_associatedModuleSheaf :
    _root_.SheafOfModules.IsCoherent
      (associatedModuleSheaf 𝒜 𝒨 : (AlgebraicGeometry.Proj 𝒜).Modules) := by
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  have hqc : SheafOfModules.IsQuasicoherent.{u, u, u} (associatedModuleSheaf 𝒜 𝒨) := inferInstance
  let F : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  let _ : F.IsQuasicoherent := hqc
  have : SheafOfModules.IsFiniteType.{u, u, u} F := isFiniteType_associatedModuleSheaf 𝒜 𝒨
  exact Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType F

/-- **The associated-sheaf functor of [Stacks, Tag 01M7] sends a bundled graded module with
finite carrier to a coherent module**, over a Noetherian graded ring. This is
`isCoherent_associatedModuleSheaf` at the grading the object carries, the functor's value being
that associated sheaf by
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_obj`. -/
public theorem isCoherent_associatedModuleSheafFunctor_obj
    (X : Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.{u, u, w} 𝒜)
    [Module.Finite A X.carrier] :
    _root_.SheafOfModules.IsCoherent
      ((Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor 𝒜).obj X) :=
  isCoherent_associatedModuleSheaf 𝒜 X.grade

/-- **The associated-sheaf functor sends a bundled graded module with finite carrier to a
coherent module**, for the coherence predicate of [Stacks, Tag 01BV]. -/
public theorem stacksIsCoherent_associatedModuleSheafFunctor_obj
    (X : Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat.{u, u, w} 𝒜)
    [Module.Finite A X.carrier] :
    Stacks.SheafOfModules.IsCoherent
      ((Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor 𝒜).obj X) :=
  stacksIsCoherent_associatedModuleSheaf 𝒜 X.grade

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
