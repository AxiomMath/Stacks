module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardPreservesComparison
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Cohomology over a coherent base ring

Let `R` be a coherent ring, let `X` be a scheme of finite presentation over `R` and let `G` be an
`𝒪_X`-module of finite presentation, flat over `R`, with support proper over `R`. Then every
cohomology module `Hⁱ(X, G)` is a coherent `R`-module. This is [Stacks, Tag 0EX6].

The source proves it by combining [Stacks, Tag 0A1H] — for a morphism of finite presentation, a
perfect `E` and a bounded complex of finitely presented modules flat over the base with support
proper over the base, `Rf_*(E ⊗^𝐋 𝒢^•)` is perfect — with the two algebra lemmas
[Stacks, Tag 0658] and [Stacks, Tag 0EWZ], both of which this library has. Tag 0A1H is not in this
library: its proof is Noetherian approximation of the whole situation, and the Noetherian case
that is available here, `isPerfect_derivedGlobalSections` of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSections.lean` ([Stacks, Tag 07VK] (1)),
does not apply, since a coherent ring need not be Noetherian and a
morphism of finite presentation with properly supported module need not be proper. Perfectness of
`RΓ(X, G)` over `R` is therefore carried here as an explicit hypothesis; see the implementation
notes.

## Main definitions

No new objects are introduced: `RΓ(X, G)` as an object of `D(R)` is
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.derivedGlobalSectionsOverBase`.

## Main results

* `…CoherentBaseCohomology.isCoherent_homology_of_isPerfect`: over a coherent ring, every
  cohomology module of a perfect object of `D(R)` is coherent. This is [Stacks, Tag 0658] followed
  by [Stacks, Tag 0EWZ], and is unconditional.
* `…CoherentBaseCohomology.cohomologyIso`: the degree-`i` cohomology of `RΓ(X, G)`, read over the
  base ring, is `Hⁱ(X, G)` with its `R`-action restricted along `R ⟶ Γ(X, 𝒪_X)`.
* `…CoherentBaseCohomology.isCoherent_cohomology_of_isPerfect_derivedGlobalSections`:
  **[Stacks, Tag 0EX6]**, with perfectness of `RΓ(X, G)` as an explicit hypothesis.

## Implementation notes

**The carried hypothesis.** `isCoherent_cohomology_of_isPerfect_derivedGlobalSections` takes
`StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f G)`: the object `RΓ(X, G)` of
`D(R)` is perfect. That is [Stacks, Tag 0A1H] for `E = 𝒪_X` and the one-term complex `G`, read over
the affine base `Spec R` — the geometric input the source's proof cites, and the only part of the
source's proof that this library cannot supply. It is a statement about a complex, not about the
module `Hⁱ(X, G)` the conclusion is about, and it is proved by an argument (Noetherian
approximation, [Stacks, Tag 0A1H]) entirely different from the algebra that turns it into the
conclusion here. All of the source's own hypotheses are kept, so the statement is the source's
statement with one upstream lemma assumed; when Tag 0A1H lands the hypothesis discharges by
application and the conclusion does not change.

**Everything else is proved.** The two algebra lemmas the source combines with Tag 0A1H are
`StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension` ([Stacks, Tag 0658]) and
`StacksDraft.PseudoCoherence.pseudoCoherentFrom_iff_finite_and_coherent_homology`
([Stacks, Tag 0EWZ]); `isCoherent_homology_of_isPerfect` is their composite and uses no hypothesis
beyond coherence of `R`. The identification of the cohomology of `RΓ(X, G)` with `Hⁱ(X, G)` is
`cohomologyIso`, and needs no cover: restriction of scalars along `R ⟶ Γ(X, 𝒪_X)` is exact, so it
commutes with the cohomology functors of the derived categories
(`StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`), and the cohomology of
the bounded below derived global sections in degree `i` is the classical `i`-th right derived
functor of `AlgebraicGeometry.moduleGlobalSections`
(`Stacks.DerivedIndexing.rightDerivedIso`).

**The source's other hypotheses.** Flatness of `G` over `R` and properness of its support are
kept, because they are the source's statement, but they are not used by the argument below: they
are exactly what Tag 0A1H consumes, and Tag 0A1H is the carried hypothesis. They are therefore
named `_hflat` and `_hsupp`.

**The derived-category model.** Everything here runs under
`CategoryTheory.HasDerivedCategory.standard`, which is the model `derivedGlobalSectionsOverBase`
and `StacksDraft.Perfect.IsPerfect` are stated at. The exactness and injectivity instances that
`derivedGlobalSectionsOverBase` was elaborated with are
the named ones of `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatGlobalSections.lean`,
reactivated below as local instances so that the terms match on the nose.

## References

* [Stacks Project, Tag 0EX6](https://stacks.math.columbia.edu/tag/0EX6)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 0EWZ](https://stacks.math.columbia.edu/tag/0EWZ)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.CoherentBaseCohomology

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesFiniteLimits_baseRestriction
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesFiniteColimits_baseRestriction
  Stacks.AlgebraicGeometry.ProperFlatGlobalSections.preservesHomology_baseRestriction

/-- **Over a coherent ring every cohomology module of a perfect complex is coherent.** This is
[Stacks, Tag 0658] — a perfect object of `D(R)` is pseudo-coherent — followed by
[Stacks, Tag 0EWZ] — over a coherent ring a bounded above object of `D(R)` is pseudo-coherent
exactly when all its cohomology modules are coherent. The boundedness above that Tag 0EWZ needs
comes from a bounded finite-projective representative, which perfectness provides. -/
theorem isCoherent_homology_of_isPerfect {R : Type u} [CommRing R] [IsCoherentRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : StacksDraft.Perfect.IsPerfect K) (i : ℤ) :
    Module.IsCoherent R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  have hPseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u} K).1.mp hK).1
  obtain ⟨P, a, b, hGE, hLE, hfinite, hprojective, ⟨e⟩⟩ := hK
  have hBound : ∃ c : ℤ, ∀ j : ℤ, c < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj K) := by
    refine ⟨b, fun j hj => ?_⟩
    have hzP : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj
        (DerivedCategory.Q.obj P)) :=
      (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc j)
        (P.isZero_of_isStrictlyLE b j hj)).of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).app P)
    exact hzP.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso e)
  exact ((StacksDraft.PseudoCoherence.pseudoCoherentFrom_iff_finite_and_coherent_homology.{u, u}
    K hBound 0).2.2).mp hPseudo i

/-- **The cohomology of `RΓ(X, F)` over the base is `Hⁱ(X, F)` over the base.** Restriction of
scalars along `R ⟶ Γ(X, 𝒪_X)` is exact, hence commutes with the cohomology functors of the
derived categories, and the degree-`i` cohomology of the bounded below derived global sections is
the classical `i`-th right derived functor of `AlgebraicGeometry.moduleGlobalSections`.

No cover and no hypothesis on `f` or `F` is involved. -/
def cohomologyIso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (F : X.Modules) (i : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i : ℤ)).obj
        (derivedGlobalSectionsOverBase f F) ≅
      (ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived i).obj F) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom) (i : ℤ)).app
      (derivedGlobalSections F) ≪≫
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (AlgebraicGeometry.moduleGlobalSections X) i).app
          F).symm

/-- **[Stacks, Tag 0EX6].** Let `R` be a coherent ring, let `f : X ⟶ Spec R` be of finite
presentation ([Stacks, Tag 01TP] (3), spelled out as its three constituent properties) and let `G`
be an `𝒪_X`-module of finite presentation, flat over `R`, whose support is proper over `R`. Then
`Hⁱ(X, G)`, with its `R`-action restricted along `R ⟶ Γ(X, 𝒪_X)`, is a coherent `R`-module in
every degree.

The proof is the source's: `RΓ(X, G)` is a perfect object of `D(R)` ([Stacks, Tag 0A1H] for
`E = 𝒪_X` and the one-term complex `G`, carried here as the hypothesis `hperf`), a perfect object
is pseudo-coherent ([Stacks, Tag 0658]), and over a coherent ring the cohomology modules of a
bounded above pseudo-coherent object are coherent ([Stacks, Tag 0EWZ]); `cohomologyIso` identifies
the cohomology of `RΓ(X, G)` with `Hⁱ(X, G)`.

**Carried hypothesis.** `hperf : StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f G)`
is Tag 0A1H over the affine base, the one input of the source's proof that this library does not
prove. It is a statement about the complex `RΓ(X, G)`, proved by Noetherian approximation, and not
the conclusion — which is coherence of the single module `Hⁱ(X, G)` — restated. The source's own
hypotheses are all present; when Tag 0A1H lands, `hperf` discharges by application. -/
@[stacks 0EX6 "carrying as an explicit hypothesis Tag 0A1H: RΓ(X, G) is perfect over the base"]
theorem isCoherent_cohomology_of_isPerfect_derivedGlobalSections
    {R : Type u} [CommRing R] [IsCoherentRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : X.Modules) [G.IsFinitePresentation]
    (_hflat : IsFlatOver f.toLRSHom.toShHom G)
    (_hsupp : ∃ Z : TopologicalSpace.Closeds X,
      (Z : Set X) = SheafOfModules.supp G ∧ IsProperOver f Z)
    (hperf : StacksDraft.Perfect.IsPerfect (derivedGlobalSectionsOverBase f G))
    (i : ℕ) :
    Module.IsCoherent R
      ((ModuleCat.restrictScalars (Stacks.Cech.globalRingHom f).hom).obj
        (((AlgebraicGeometry.moduleGlobalSections X).rightDerived i).obj G)) := by
  have hco : Module.IsCoherent R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i : ℤ)).obj
        (derivedGlobalSectionsOverBase f G)) :=
    isCoherent_homology_of_isPerfect _ hperf (i : ℤ)
  exact Module.IsCoherent.of_equiv (cohomologyIso f G i).toLinearEquiv

end Stacks.AlgebraicGeometry.CoherentBaseCohomology

end
