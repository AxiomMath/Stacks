module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RestrictionToAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Tor amplitude on a ringed space is local on the base

Let `X` be a ringed space and `E` an object of `D(O_X)`. Tor amplitude in `[a, b]`
([Stacks, Tag 08CG]) is a condition on the derived tensor product of `E` with every
`O_X`-module, so it is not visibly a local condition: Tag 08CI turns it into a *single global*
complex of flat modules concentrated in `[a, b]`. This file proves that it is local anyway — if
every point of `X` has an open neighbourhood on which the restriction of `E` has Tor amplitude
in `[a, b]`, then `E` has Tor amplitude in `[a, b]`, with the *same* interval.

That is the reduction `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` exists in
place of. That predicate quantifies the interval existentially on each member of the covering,
so it cannot carry a bound from the members to the whole space; the statement below does.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlat_representative`: every object
  of `D(O_X)` is the class of a K-flat complex.
* `Stacks.Cohomology.TorAmplitude.derivedTensorRestrictIsoOfKFlatLeft`: restriction to an open
  subspace carries the derived tensor product of a K-flat complex with an arbitrary complex to
  the derived tensor product of the restrictions.
* `Stacks.Cohomology.TorAmplitude.restrictSingleComplexIso`: the restriction of a module placed
  in degree zero is its restriction placed in degree zero.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`: **Tor amplitude in `[a, b]`
  is local on an open covering.**

## Implementation notes

The hypothesis is only needed for *one* complex: the proof chooses a K-flat complex `K` with
`Q(K) ≅ E` (Tag 06YS on a ringed space,
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution`, applied to a
complex representing `E`), and then for an `O_X`-module `F` computes
`E ⊗^L F[0]` as `Q(Tot(K ⊗ F[0]))`. This uses the `comparisonLeft` field of the derived tensor
product, which asks K-flatness of the *left* argument only — so `F[0]` needs no resolution, and
`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`, which asks it of both, is
not what is applied here.

Restriction to an open subspace then commutes with everything in sight:
with the total tensor complex unconditionally
(`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`), with the localization functor
(`AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`), with the degree-zero single
functor (`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, restriction being exact) and
with the cohomology sheaf functors
(`StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`). The restriction of `K`
stays K-flat, by Tag 06YC at the open immersion. So each cohomology sheaf of `E ⊗^L F[0]`
restricts to a cohomology sheaf of `E|_U ⊗^L (F|_U)[0]`, which the hypothesis kills; and a sheaf
of modules whose restrictions to an open covering all vanish is zero
(`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules`).

No bound on the interval is used, and `a ≤ b` is not assumed: unlike Tag 08CI, which needs it to
place a truncation, the argument here is degreewise and says nothing about the shape of
`Set.Icc a b`.

Restriction is taken in the `AlgebraicGeometry.RingedSpace.restrictModules` spelling, which is
the one `AlgebraicGeometry.RingedSpace.derivedRestrictModules` and
`AlgebraicGeometry.RingedSpace.restrictComplex` are built from, and the one
`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules` is stated at. The tree carries a
second copy with a character-identical body in namespace
`AlgebraicGeometry.RingedSpace.PseudoCoherence`, which is the one
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` names. The two restriction functors
are equal by `rfl`, and so are the two `restrictComplex`, both verified by elaboration, so a
consumer holding either spelling may use this. The derived restrictions agree as well, but only
up to the `CategoryTheory.Limits.PreservesFiniteColimits` instance each is built from, which is
data rather than a proposition — hence the hypothesis is stated at
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the canonical name, as the module
docstring of `StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict` asks.

The derived categories of the open subspaces are the standard ones — that is what
`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat` reads them as, and
leaving the hom universe a parameter would put a metavariable in it at the two spellings of the
category of modules, which instance search does not cross. The derived category of `X` itself is
left arbitrary. All universes of the ringed space coincide, as they must for
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` to be stated; the index type of the covering is
unconstrained.

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u d

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- The image under the localization functor of a quasi-isomorphism of complexes of
`O_X`-modules, as an isomorphism of the derived category.

Hoisted into a declaration with the two complexes as free variables so that the complexes
produced by `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution`, whose
type is given at the `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules` spelling of
the category of `O_X`-modules, are unified with the `StrictlyPerfect.OXMod` spelling by term
elaboration at default transparency. Instance search does not cross the two: the two ring
sheaves are equal only by `rfl`. -/
private def qMapIsoOfQuasiIso {K G : CochainComplex (OXMod.{u, u} X) ℤ} (f : K ⟶ G)
    (hf : QuasiIso f) : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj G :=
  letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (OXMod.{u, u} X) f).2 hf
  asIso (DerivedCategory.Q.map f)

/-- **Every object of `D(O_X)` on a ringed space is the class of a K-flat complex.**

Tag 06YS resolves a *complex* by a K-flat one
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution`); the localization
functor is essentially surjective, so applying it to a complex representing the given object and
composing the two isomorphisms gives the statement for an object. -/
theorem exists_kFlat_representative (E : DerivedCategory (OXMod.{u, u} X)) :
    ∃ K : CochainComplex (OXMod.{u, u} X) ℤ,
      KFlat X K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨K, p, hK, -, hqp, -⟩ :=
    exists_kFlatResolution X ((DerivedCategory.Q (C := OXMod.{u, u} X)).objPreimage E)
  exact ⟨K, hK,
    ⟨qMapIsoOfQuasiIso p hqp ≪≫ (DerivedCategory.Q (C := OXMod.{u, u} X)).objObjPreimageIso E⟩⟩

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude

universe u d

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)
  [HasDerivedCategory.{d} (OXMod.{u, u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Restriction to an open subspace commutes with the derived tensor product when the left
argument is K-flat.**

`(K ⊗^L L)|_U ≅ K|_U ⊗^L L|_U` for `K` K-flat and `L` arbitrary.

The derived tensor product is the total tensor complex as soon as one argument is K-flat
(the `comparisonLeft` field of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`),
restriction commutes with the total tensor complex unconditionally
(`Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso`), and the restriction of a
K-flat complex is K-flat (Tag 06YC at the open immersion), so `comparisonLeft` applies again on
`U`.

This differs from `Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat` in two
ways: K-flatness is asked of the left argument only, and the left-hand side is the derived
tensor product on `X` rather than the localization of a total tensor complex. Both matter for a
consumer tensoring with a module placed in degree zero, which is not K-flat unless the module is
flat. -/
def derivedTensorRestrictIsoOfKFlatLeft (K L : CochainComplex (OXMod.{u, u} X) ℤ)
    (hK : KFlat X K) :
    (AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj
        (((derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj
          (DerivedCategory.Q.obj L)) ≅
      ((derTensor (X.restrict U.isOpenEmbedding)).tensor.obj
          (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex K U))).obj
        (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex L U)) :=
  (AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).mapIso
      ((derTensor X).comparisonLeft K L hK) ≪≫
    AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X U _ ≪≫
    DerivedCategory.Q.mapIso (Stacks.Cohomology.RestrictionTensor.restrictComplexTensorIso
      X U K L) ≪≫
    ((derTensor (X.restrict U.isOpenEmbedding)).comparisonLeft _ _
      (kFlat_restrictComplex U K hK)).symm

/-- **The restriction of a module placed in degree zero is its restriction placed in degree
zero.**

Restriction to an open subspace is exact, so it commutes with the degree-zero single functor
into the derived category (`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`); this is
that isomorphism with the left-hand side written as the localization of the restricted single
complex, which is the spelling
`Stacks.Cohomology.TorAmplitude.derivedTensorRestrictIsoOfKFlatLeft` produces. -/
def restrictSingleComplexIso (F : OXMod.{u, u} X) :
    DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex
        ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F) U) ≅
      (DerivedCategory.singleFunctor
          (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        ((AlgebraicGeometry.RingedSpace.restrictModules X U).obj F) :=
  (AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X U _).symm ≪≫
    ((AlgebraicGeometry.RingedSpace.restrictModules X U).mapDerivedCategorySingleFunctor 0).app F

/-- **Tor amplitude in `[a, b]` is local on an open covering.** If the restriction of an object
of `D(O_X)` to each member of an open covering of `X` has Tor amplitude in `[a, b]`, then the
object has Tor amplitude in `[a, b]`.

The interval is carried unchanged, which is what
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` cannot do: it quantifies the
interval existentially on each member of the covering.

No relation between `a` and `b` is assumed, and no bound on the interval is used. -/
theorem hasTorAmplitude_of_iSup_eq_top (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ)
    {ι : Type*} (V : ι → Opens X.carrier) (hV : iSup V = ⊤)
    (h : ∀ i : ι, HasTorAmplitude (X.restrict (V i).isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X (V i)).obj E) a b) :
    HasTorAmplitude X E a b := by
  classical
  have hcover : ∀ x : X.carrier, ∃ i, x ∈ V i := fun x =>
    TopologicalSpace.Opens.mem_iSup.mp (show x ∈ iSup V from by rw [hV]; trivial)
  obtain ⟨K, hKflat, ⟨eK⟩⟩ := exists_kFlat_representative (X := X) E
  intro F n hn
  let SF := (HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F
  let Z : DerivedCategory (OXMod.{u, u} X) :=
    ((derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj SF)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).mapIso
    (((derTensor X).tensor.mapIso eK.symm).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj
        (((derTensor X).tensor.obj E).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) n).obj Z)
  refine AlgebraicGeometry.RingedSpace.isZero_of_restrictModules X _ V hcover fun i => ?_
  refine IsZero.of_iso ?_
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (AlgebraicGeometry.RingedSpace.restrictModules X (V i)) n).app Z).symm
  refine IsZero.of_iso (h i ((AlgebraicGeometry.RingedSpace.restrictModules X (V i)).obj F) n hn)
    ((DerivedCategory.homologyFunctor _ n).mapIso ?_)
  exact derivedTensorRestrictIsoOfKFlatLeft X (V i) K SF hKflat ≪≫
    ((derTensor (X.restrict (V i).isOpenEmbedding)).tensor.mapIso
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X (V i) K).symm ≪≫
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules X (V i)).mapIso eK)).app _ ≪≫
      ((derTensor (X.restrict (V i).isOpenEmbedding)).tensor.obj _).mapIso
        (restrictSingleComplexIso X (V i) F)

end Stacks.Cohomology.TorAmplitude

end
