module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# The cohomology sheaves of a dualizing complex are coherent

A dualizing complex `K` on a locally Noetherian scheme `X` is, over every affine open `U`, the
associated sheaf of a dualizing complex `ω` over `Γ(X, U)` ([Stacks, Tag 0A87], here
`Stacks.Duality.IsDualizingComplex`). Restriction along `U ⟶ X` and the associated-sheaf functor
are exact, so both commute with taking cohomology in the derived category; hence `H^i(K)|_U` is
the associated sheaf of the `Γ(X, U)`-module `H^i(ω)`, and that module is *finite*, because
finiteness of the cohomology modules is the second condition in the definition of a dualizing
complex over a Noetherian ring ([Stacks, Tag 0A7B]).

So every cohomology sheaf of `K` satisfies condition (5) of [Stacks, Tag 01XZ] on the covering of
`X` by its affine opens; it is therefore quasi-coherent and of finite type, hence coherent by the
implication (2) ⇒ (1) of that tag. This is the finiteness statement used inside the proofs of
[Stacks, Tag 0AWI] and [Stacks, Tag 0AWK].

## Main results

* `Stacks.Duality.isFiniteTildeOn_homology_of_hasDualizingModelOn` — a dualizing model at an
  affine open exhibits every cohomology sheaf as the associated sheaf of a finite module there.
* `Stacks.Duality.isCoherent_homology_of_isDualizingComplex` — **the cohomology sheaves of a
  dualizing complex on a locally Noetherian scheme are coherent.**
* `Stacks.Duality.stacksIsCoherent_homology_of_isDualizingComplex` — the same for the other
  coherence predicate of this branch.

## Implementation notes

Both exact functors are handled by one lemma, `Dualizing.mapDerivedCategoryHomologyIso`, which
for an exact `F` supplies `H^i ∘ F^der ≅ F ∘ H^i`; it is used on
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` and on the composite
`AlgebraicGeometry.tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom`. Both
need `Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits`: the first two are
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive`,
`restrictFunctor_preservesFiniteLimits` and `AlgebraicGeometry.tilde.preservesFiniteLimits`, and
colimits are preserved because both functors are left adjoints.

`D(𝒪_X)` is an instance argument throughout, inherited from
`Stacks.Duality.IsDualizingComplex`, so these results hold at whatever model the caller uses.
The two derived categories of `isFiniteTildeOn_homology_of_hasDualizingModelOn`'s proof that do
*not* appear in its statement — `D(𝒪_U)` and `D(Γ(X, U))`, both depending on the affine open
`U` — are introduced at `HasDerivedCategory.standard` by two `let`s, matching the choice sealed
inside the body of `Stacks.Duality.HasDualizingModelOn`.

`Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn` is phrased with
`AlgebraicGeometry.Scheme.Modules.pullback` where `Stacks.Duality.HasDualizingModelOn` uses
`restrictFunctor`; `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` converts between
them.

The coherence predicate is written `_root_.SheafOfModules.IsCoherent`, which inside the `Stacks.`
namespace is not the same constant as the unqualified name — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure`. [Stacks, Tag 0AWI] writes
`(ω_X).IsCoherent`, which is this one; the other predicate is supplied as a second statement.

**No `@[stacks]` attribute is placed.** None of these is the statement of a tag.
`isCoherent_homology_of_isDualizingComplex` is the globalisation of condition (2) of
[Stacks, Tag 0A7B]; it supplies the coherence of `ω_X` in
`Stacks.Duality.isDualizingModuleOf_relativeDualizingModule`, which proves [Stacks, Tag 0AWI]
and carries that tag.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.CoherentOfFiniteType

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **A dualizing model at an affine open exhibits every cohomology sheaf as a finite `tilde`.**
If `K|_U` is the associated sheaf of a dualizing complex `ω` over `Γ(X, U)`, then `H^i(K)|_U` is
the associated sheaf of the finite `Γ(X, U)`-module `H^i(ω)`. This is condition (5) of
[Stacks, Tag 01XZ] for `H^i(K)` at `U`. -/
theorem isFiniteTildeOn_homology_of_hasDualizingModelOn {K : DerivedCategory X.Modules}
    {U : X.Opens} {hU : IsAffineOpen U} (h : HasDualizingModelOn K U hU) (i : ℤ) :
    IsFiniteTildeOn ((DerivedCategory.homologyFunctor X.Modules i).obj K) U hU := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  refine ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω,
    hω.finiteCohomology i, ⟨?_⟩⟩
  exact ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _

/-- **The cohomology sheaves of a dualizing complex on a locally Noetherian scheme are
coherent.** The affine opens cover `X`, and on each of them the cohomology sheaf is the
associated sheaf of a finite module, so it is quasi-coherent and of finite type; on a locally
Noetherian scheme that is coherence, by [Stacks, Tag 01XZ] (2) ⇒ (1). -/
theorem isCoherent_homology_of_isDualizingComplex {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (i : ℤ) :
    _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
  set F := (DerivedCategory.homologyFunctor X.Modules i).obj K with hF
  have hcov : TopologicalSpace.IsOpenCover (fun V : X.affineOpens => V.1) :=
    iSup_affineOpens_eq_top X
  have hfin : ∀ V : X.affineOpens, IsFiniteTildeOn F V.1 V.2 := fun V =>
    isFiniteTildeOn_homology_of_hasDualizingModelOn (hK V.1 V.2) i
  have _ : F.IsQuasicoherent :=
    isQuasicoherent_of_cover_isFiniteTildeOn F _ hcov (fun V => V.2) hfin
  have _ : F.IsFiniteType :=
    isFiniteType_of_cover_isFiniteTildeOn F _ hcov (fun V => V.2) hfin
  exact isCoherent_of_isQuasicoherent_of_isFiniteType F

/-- `Stacks.Duality.isCoherent_homology_of_isDualizingComplex` for the second coherence predicate
of this branch, `Stacks.SheafOfModules.IsCoherent`. -/
theorem stacksIsCoherent_homology_of_isDualizingComplex {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (i : ℤ) :
    Stacks.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
  Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
    (isCoherent_homology_of_isDualizingComplex hK i)

end Stacks.Duality

end
