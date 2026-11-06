module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasicoherentKFlatModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# A K-flat representative with quasi-coherent terms, on an arbitrary affine scheme

`AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model` writes every object of
`D_QCoh(𝒪_{Spec R})` as the class of a K-flat complex of quasi-coherent modules.  Its proof goes
through the affine dictionary of [Stacks, Tag 06Z0], which is stated on a *spectrum*.  A general
affine scheme is only *isomorphic* to a spectrum, and that is what the localization half of
[Stacks, Tag 08I9] produces: restricting a morphism to an affine open of the base leaves a
morphism over an affine *scheme*.  This file transports the statement along
`AlgebraicGeometry.Scheme.isoSpec`.

Nothing here is new mathematics.  The object `K` on `U` is carried to `Spec Γ(U, ⊤)` by
restriction along `isoSpec.inv`, where the spectrum statement produces a complex `C`; the
representative on `U` is the *degreewise pullback* of `C` along `isoSpec.hom`.  Each of the three
things that has to be checked of it is a transport already in the library.

* *The terms are quasi-coherent.*  The degreewise pullback along a morphism of ringed spaces
  preserves quasi-coherence — [Stacks, Tag 01BG],
  `AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent`.
* *The complex is K-flat.*  The degreewise pullback of a K-flat complex along *any* morphism of
  ringed spaces is K-flat — [Stacks, Tag 06YC],
  `Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional`.  Both of these are
  unconditional, which is why the pullback and not the restriction is the complex taken.
* *Its class in `D(𝒪_U)` is `K`.*  Here the restriction is what is convenient: it is exact, so
  its action on derived categories is the degreewise one, and restricting along `isoSpec.inv` and
  then along `isoSpec.hom` is the identity.  This is the device of
  `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedTilde_derivedSectionsSpec`.  The two
  descriptions of the representative are identified by Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`: restriction along an open
  immersion *is* the degreewise pullback.

Quasi-coherence of the cohomology sheaves of the transported object is
`AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoSpecCancel`: restricting along the inverse
  of an isomorphism of schemes and then along the isomorphism is the identity.
* `AlgebraicGeometry.exists_kFlat_isQuasicoherent_model_of_isAffine`: **every object of
  `D_QCoh(𝒪_U)`, for `U` an affine scheme, is the class of a K-flat cochain complex of
  quasi-coherent `𝒪_U`-modules.**

## Implementation notes

*`HasDerivedCategory.standard` is installed at priority `10000`*, as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/QuasicoherentKFlatModel.lean`; see the implementation
notes there.

*The reducibility attributes* collapse the library's spellings of the category of
`𝒪_X`-modules: `AlgebraicGeometry.Scheme.Modules X`, in which Mathlib's restriction and pullback
functors are stated, and `SheafOfModules.{u} (structureSheafRing X.toRingedSpace)`, in which
K-flatness and the ringed-space pullback are.  They are equal by `rfl` but not at the
transparency instance search runs at.

Nothing is tagged: [Stacks, Tag 06Z0] asserts the affine equivalence and [Stacks, Tag 06YS] the
existence of a K-flat resolution, and the statement below is a corollary of the two which the
Stacks project does not state as a result of its own.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-! ### Restriction along an isomorphism of schemes and its inverse -/

namespace Scheme.Modules

/-- **Restricting along the inverse of an isomorphism of schemes and then along the isomorphism
is the identity.**  The three steps are the compatibility of restriction with composition, with
equal morphisms and with the identity; no coherence obligation of an equivalence is needed, and
only this one composite is used below. -/
def restrictFunctorIsoSpecCancel {X Y : Scheme.{u}} (e : X ≅ Y) :
    restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
    restrictFunctorId

end Scheme.Modules

/-! ### The K-flat quasi-coherent model over an affine scheme -/

section

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules structureSheafRing
  TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **A K-flat representative with quasi-coherent terms, on an arbitrary affine scheme.**  Let `U`
be an affine scheme and let `K` be an object of `D(𝒪_U)` all of whose cohomology sheaves are
quasi-coherent.  Then `K` is the class of a cochain complex of `𝒪_U`-modules which is K-flat and
all of whose terms are quasi-coherent.

This is `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model`, which is available
over a spectrum only, transported along `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem exists_kFlat_isQuasicoherent_model_of_isAffine (U : Scheme.{u}) [IsAffine U]
    (K : DerivedCategory U.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor U.Modules n).obj K).IsQuasicoherent) :
    ∃ C : CochainComplex U.Modules ℤ,
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace C ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K) := by
  obtain ⟨C, hCq, -, hCk, ⟨eC⟩⟩ :=
    AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model Γ(U, ⊤)
      ((Scheme.Modules.restrictFunctor U.isoSpec.inv).mapDerivedCategory.obj K)
      (fun n => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory U.isoSpec.inv hK n)
  refine ⟨((modulePullback U.isoSpec.hom.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C, fun n => ?_, ?_, ⟨?_⟩⟩
  · exact have := hCq n
      AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
        U.isoSpec.hom.toLRSHom.toShHom (C.X n)
  · exact Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional
      U.isoSpec.hom.toLRSHom.toShHom C hCk
  · refine DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Scheme.Modules.restrictFunctorIsoPullback U.isoSpec.hom)
        (ComplexShape.up ℤ)).app C).symm ≪≫
      ((Scheme.Modules.restrictFunctor U.isoSpec.hom).mapDerivedCategoryFactors.app C).symm ≪≫
      (Scheme.Modules.restrictFunctor U.isoSpec.hom).mapDerivedCategory.mapIso eC ≪≫ ?_
    exact (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Scheme.Modules.restrictFunctorIsoSpecCancel U.isoSpec) ≪≫
      Functor.mapDerivedCategoryId U.Modules).app K

end

end AlgebraicGeometry

end
