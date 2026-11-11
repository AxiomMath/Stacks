module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineBaseTorDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.ChartRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation

/-!
# The derived direct image along a perfect morphism of affine schemes has finite Tor dimension

`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap` proves the affine case
of the Tor-dimension half of [Stacks, Tag 08EV] for a morphism of the form `Spec φ`. An affine
scheme is not a spectrum on the nose, so that statement does not apply to a morphism `h : Z ⟶ W`
of affine schemes as it stands. This file transports it along
`AlgebraicGeometry.Scheme.isoSpec`, and so proves: for `h : Z ⟶ W` a perfect morphism of affine
schemes and `B` an object of `D(𝒪_Z)` with quasi-coherent cohomology and finite Tor dimension,
`Rh_*B` has finite Tor dimension on `W`.

## Main results

* `AlgebraicGeometry.exists_tildeComplex_iso`: **[Stacks, Tag 06Z0] read at a complex of
  modules.** An object of `D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent is the
  degreewise sheafification of a complex of `R`-modules.
* `AlgebraicGeometry.hasTorAmplitude_restrictFunctor_iso_iff`: Tor amplitude transports along an
  isomorphism of schemes, with restriction of modules written as
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.
* `AlgebraicGeometry.isPullback_isoSpec`: a morphism of affine schemes is the morphism of spectra
  it induces on sections, in the sense that the square built from the two copies of
  `AlgebraicGeometry.Scheme.isoSpec` is Cartesian.
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine`: **the affine
  base case at a morphism of affine schemes.**

## Implementation notes

The three transports along `isoSpec` that the reduction needs are all available:

* on the *functor*, [Stacks, Tag 08FE] in the scheme spelling
  (`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpenIso`), which asks only that the two
  vertical edges of the Cartesian square be open immersions, and an isomorphism is one;
* on the *predicate*,
  `Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_scheme_iff`, combined with
  `AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor` to turn the derived
  pullback of that statement into the restriction functor the first transport produces;
* on the *hypothesis `hA`*, [Stacks, Tag 06Z0], in the counit form
  `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`. Only existence of *some*
  complex of modules sheafifying to `B` is needed, not that it is `RΓ`, because the Tor-amplitude
  interval of the complex is read back from the sheaf side by [Stacks, Tag 08E9]; this is why the
  clause of [Stacks, Tag 06Z0] identifying the complex with derived global sections, which that
  statement declines to assert, plays no part.

The ring map of the transported statement is `h.appLE ⊤ ⊤`, not `h.appTop`, because that is the
spelling perfectness of a morphism of schemes is read at
(`AlgebraicGeometry.HasRingHomProperty.appLE`); the two agree by
`Stacks.AffineAlgebraEquivalence.appLE_top_top`, which is where
`AlgebraicGeometry.Scheme.toSpecΓ_naturality` is read.

No `@[stacks]` attribute is placed: this is the affine case of the Tor-dimension half of
[Stacks, Tag 08EV], already registered where it is proved, moved to a morphism of affine schemes.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 0687](https://stacks.math.columbia.edu/tag/0687)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.TorAmplitude
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### [Stacks, Tag 06Z0] at a complex of modules -/

/-- **[Stacks, Tag 06Z0] read at a complex of modules.** An object `A` of `D(𝒪_{Spec R})` all of
whose cohomology sheaves are quasi-coherent is isomorphic to the degreewise sheafification of a
complex of `R`-modules.

This is the counit clause of [Stacks, Tag 06Z0],
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`, which exhibits `A` as the
derived sheafification of its derived global sections, followed by a passage from the object of
`D(R)` to a representing complex. The complex produced is a representative of `RΓ(Spec R, A)`, but
nothing of that is asserted: only existence is, which is all the Tor-amplitude estimate of
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap` consumes. -/
theorem exists_tildeComplex_iso (R : CommRingCat.{u}) (A : DerivedCategory (Spec R).Modules)
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj A).IsQuasicoherent) :
    ∃ M : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (A ≅
      DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) := by
  have hiso : IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app A) :=
    derivedTildeGlobalSectionsAdjunction_counit_isIso R ⟨A, hqc⟩
  set M : DerivedCategory (ModuleCat.{u} R) := (derivedGlobalSectionsOver (𝟙 (Spec R))).obj A
  have e1 : (tilde.functor R).mapDerivedCategory.obj M ≅ A :=
    ((derivedTildeCompι R).app M).symm ≪≫ @asIso _ _ _ _ _ hiso
  refine ⟨DerivedCategory.Q.objPreimage M, ⟨e1.symm ≪≫ ?_⟩⟩
  exact (tilde.functor R).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    (tilde.functor R).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-! ### Transport of Tor amplitude along an isomorphism of schemes -/

/-- **Tor amplitude transports along an isomorphism of schemes**, with restriction of modules in
Mathlib's spelling. For `e : A ≅ B` an isomorphism of schemes, an object of `D(𝒪_B)` has Tor
amplitude in `[a, b]` exactly when its restriction along `e.hom` does.

This is `Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_scheme_iff`, which is
stated at the derived pullback, read through
`AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor`: for an isomorphism the
derived pullback is the restriction functor. -/
theorem hasTorAmplitude_restrictFunctor_iso_iff {A B : Scheme.{u}} (e : A ≅ B)
    (T : DerivedCategory (StrictlyPerfect.OXMod.{u, u} B.toRingedSpace)) (a b : ℤ) :
    HasTorAmplitude A.toRingedSpace
        ((Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory.obj T) a b ↔
      HasTorAmplitude B.toRingedSpace T a b := by
  rw [← Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_scheme_iff e T a b]
  have i := Scheme.Modules.derivedPullbackObjIsoRestrictFunctor e.hom T
  exact ⟨fun h => FlatOpcycles.hasTorAmplitude_of_iso (X := A.toRingedSpace) h i,
    fun h => FlatOpcycles.hasTorAmplitude_of_iso (X := A.toRingedSpace) h i.symm⟩

/-! ### A morphism of affine schemes as a morphism of spectra -/

/-- **A morphism of affine schemes is the morphism of spectra of its map on sections.** For
`h : Z ⟶ W` with `Z` and `W` affine the square
```
Spec Γ(Z, ⊤) --Spec (h.appLE ⊤ ⊤)--> Spec Γ(W, ⊤)
     |                                    |
 isoSpec.inv                         isoSpec.inv
     v                                    v
     Z -------------h---------------->    W
```
is Cartesian: it commutes by `AlgebraicGeometry.Scheme.toSpecΓ_naturality`, and both vertical
edges are isomorphisms. It is the square at which [Stacks, Tag 08FE] carries the affine base case
from a morphism of spectra to a morphism of affine schemes. -/
theorem isPullback_isoSpec {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (h : Z ⟶ W)
    (hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤) :
    IsPullback Z.isoSpec.inv (Spec.map (h.appLE ⊤ ⊤ hle)) h W.isoSpec.inv := by
  rw [Stacks.AffineAlgebraEquivalence.appLE_top_top h hle]
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  have hn : Z.isoSpec.hom ≫ Spec.map h.appTop = h ≫ W.isoSpec.hom :=
    (Scheme.toSpecΓ_naturality h).symm
  rw [Iso.inv_comp_eq, ← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The Tor clause of perfectness, for a perfect morphism of affine schemes.** For `h : Z ⟶ W`
perfect with `Z` and `W` affine, the ring `Γ(Z, ⊤)` has finite Tor dimension over `Γ(W, ⊤)` along
`h.appLE ⊤ ⊤`.

This is the Tor half of perfectness (`Algebra.Perfect.moduleHasFiniteTorDimension`) for the
chart ring map at the pair of affine opens `⊤ ⊆ Z`, `⊤ ⊆ W`, read at the canonical derived tensor
product by `StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff`. It is the
hypothesis `hφ` of `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap`. -/
theorem perfectTorAmplitude_appLE_top {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (h : Z ⟶ W)
    [AlgebraicGeometry.Perfect h] (hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤) :
    letI : Algebra Γ(W, ⊤) Γ(Z, ⊤) := (h.appLE ⊤ ⊤ hle).hom.toAlgebra
    ∃ c d : ℤ, HasTorAmplitudeCanonical Γ(W, ⊤)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(W, ⊤)) 0).obj
        ((ModuleCat.restrictScalars (algebraMap Γ(W, ⊤) Γ(Z, ⊤))).obj
          (ModuleCat.of Γ(Z, ⊤) Γ(Z, ⊤)))) c d := by
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := (h.appLE ⊤ ⊤ hle).hom.toAlgebra
  have : Algebra.Perfect Γ(W, ⊤) Γ(Z, ⊤) := RingHom.perfect_algebraMap.mp
    (HasRingHomProperty.appLE @Perfect h ‹_› ⟨⊤, isAffineOpen_top W⟩ ⟨⊤, isAffineOpen_top Z⟩
      hle)
  let D := canonicalCertifiedDerivedTensoring Γ(W, ⊤)
  obtain ⟨c, d, hcd⟩ :=
    Algebra.Perfect.moduleHasFiniteTorDimension (B := Γ(Z, ⊤)) D.comparison D.isLeftDerived
  exact ⟨c, d, (hasTorAmplitudeIn_canonicalCertified_iff Γ(W, ⊤) _ c d).mp hcd⟩

/-! ### The affine base case at a morphism of affine schemes -/

/-- **The affine base case of the Tor-dimension half of [Stacks, Tag 08EV], at a morphism of
affine schemes.** Let `h : Z ⟶ W` be a perfect morphism of affine schemes and let `B` be an object
of `D(𝒪_Z)` whose cohomology sheaves are quasi-coherent and which has finite Tor dimension on `Z`.
Then `Rh_*B` has finite Tor dimension on `W`.

This is `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap`, which proves
it for a morphism `Spec φ`, carried across the Cartesian square of
`AlgebraicGeometry.isPullback_isoSpec` by [Stacks, Tag 08FE] on the functor and by
`AlgebraicGeometry.hasTorAmplitude_restrictFunctor_iso_iff` on the Tor-amplitude predicate. Its
hypothesis `hφ` is `AlgebraicGeometry.perfectTorAmplitude_appLE_top`, that is, perfectness of `h`;
its hypothesis `hA` is `AlgebraicGeometry.exists_tildeComplex_iso`, that is, quasi-coherence of the
cohomology of `B`. -/
@[sga "5 III 6.3" "special case"]
theorem hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine
    {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W] (h : Z ⟶ W) [AlgebraicGeometry.Perfect h]
    (B : DerivedCategory Z.Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj B).IsQuasicoherent)
    (hTor : HasFiniteTorDimension Z.toRingedSpace B) :
    HasFiniteTorDimension W.toRingedSpace ((schemeDerivedPushforward h).obj B) := by
  have hle : (⊤ : Z.Opens) ≤ h ⁻¹ᵁ ⊤ := by simp
  have hAtor : HasFiniteTorDimension (Spec Γ(Z, ⊤)).toRingedSpace
      ((Scheme.Modules.restrictFunctor Z.isoSpec.inv).mapDerivedCategory.obj B) := by
    obtain ⟨a, b, hab⟩ := hTor
    exact ⟨a, b, (hasTorAmplitude_restrictFunctor_iso_iff Z.isoSpec.symm B a b).2 hab⟩
  obtain ⟨a, b, hab⟩ := hasFiniteTorDimension_schemeDerivedPushforward_specMap
    (h.appLE ⊤ ⊤ hle) (perfectTorAmplitude_appLE_top h hle) _
    (exists_tildeComplex_iso Γ(Z, ⊤) _
      (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory Z.isoSpec.inv hqc)) hAtor
  exact ⟨a, b, (hasTorAmplitude_restrictFunctor_iso_iff W.isoSpec.symm _ a b).1
    (FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec Γ(W, ⊤)).toRingedSpace) hab
      (schemeDerivedPushforwardRestrictOpenIso h W.isoSpec.inv (Spec.map (h.appLE ⊤ ⊤ hle))
        Z.isoSpec.inv (isPullback_isoSpec h hle) B))⟩

end AlgebraicGeometry

end
