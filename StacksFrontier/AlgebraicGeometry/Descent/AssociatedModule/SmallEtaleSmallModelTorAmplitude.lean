module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison

/-!
# The derived pullback along `ε`, read on the `Type u`-presented model

`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom` is the morphism `ε` of Stacks 08H7 read
through the `Type u`-presented model of the small étale ringed topos, so that both its source
and its target are `AlgebraicGeometry.RingedTopos.{u, u, u}`.  This file records that the whole
Stacks 06YY / 05VD / 07A4 / 08H5 chain applies to it, which is what the model was built for.

Nothing here is new mathematics: each statement below is one library theorem instantiated at
`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom` and
`AlgebraicGeometry.SmallEtale.isMorphismOfSites_toZariskiSmallModelHom_u`.  What the file
establishes is that the instantiation *goes through* — every typeclass hypothesis of those
theorems is satisfied by the model with no new assumption, the three that cost work on the small
étale site itself (sheafification of abelian groups, local bijectivity, sheafification of sets)
being unconditional instances on a genuinely small site.

## Main results

* `AlgebraicGeometry.SmallEtale.hasLeftDerivedFunctor_toZariskiSmallModel`: the derived pullback
  `Lε^*` exists on the model, Stacks 06YY's existence assertion.
* `AlgebraicGeometry.SmallEtale.derivedPullbackSmallModel`: `Lε^*` on the model, named so that
  the statement of Stacks 07A4 elaborates.
* `AlgebraicGeometry.SmallEtale.isTriangulated_derivedPullback_toZariskiSmallModel`: it is
  exact, Stacks 06YY's exactness assertion.
* `AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_toZariskiSmallModel`:
  **Stacks 08H5 for `ε` read on the model** — `Lε^*` preserves Tor amplitude in a fixed
  interval, for *any* derived tensor product datum on either side.
* `AlgebraicGeometry.SmallEtale.hasFiniteTorDimension_derivedPullback_toZariskiSmallModel`: the
  same for finite Tor dimension.
* `AlgebraicGeometry.SmallEtale.derivedPullbackTensorIsoSmallModel`: **Stacks 07A4 for `ε` read
  on the model** — the bifunctorial isomorphism `Lε^*(K ⊗^L L) ≅ Lε^*K ⊗^L Lε^*L`, the derived
  flat base change for `ε`.

## Implementation notes

**Why the existence of `Lε^*` is declared as an instance.**  Every clause of Stacks 06YY, and
hence Stacks 08H5 and Stacks 07A4, is stated in a binder context carrying
`(pullbackOnHomotopy f).HasLeftDerivedFunctor _` as an instance argument — the functor `Lf^*`
cannot be written down without it.  The witness is unconditional for a morphism of ringed topoi
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`), and
it is a `Prop` class, so by proof irrelevance nothing depends on which witness is supplied.
Registering it as an instance at `ε` read on the model is what lets the statements below be
written without a hypothesis.

**The derived categories are the standard ones.**  `HasDerivedCategory.standard` is introduced
as a local instance, as in each of the files these statements come from; the hom universe
of `D(𝒪)` is therefore the one that construction provides and is not a free parameter.

**Stacks 08HF, and what is still missing for Stacks 05VD on the small étale site itself.**
Stacks 08HF is now carried, as an `iff`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleTorAmplitudeComparison.lean`;
the converse half needs Stacks 08H8 for `ε` read on the model, which
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSmallModelPullbackExact.lean`
supplies.  What remains open is a different statement: Stacks 05VD for `ε` on the
`RingedTopos.{u, u + 1, u}` presentation rather than on the model.  Two
of the three transports that needs are available:
`AlgebraicGeometry.SmallEtale.smallModelModulesEquiv` and
`AlgebraicGeometry.SmallEtale.isFlat_iff_smallModelModuleRestriction` transport sheaves of
modules and flatness, and
`AlgebraicGeometry.SmallEtale.isFlat_pullbackModulesToEtale_obj` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSmallModelAbstractHom.lean`
proves Stacks 05VD for `ε` up to a single natural isomorphism, namely
`pullbackModulesToEtale ≅ smallModelModuleRestriction`.  That isomorphism, and the derived-category
transport, are what remain; see the implementation notes of that file.

## References

* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.SheafOfModules Stacks.SheafOfModules.DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06YY, existence, for `ε` read on the model.**  Degreewise pullback along `ε_model`
followed by localization has an everywhere-defined left derived functor, so `Lε^*` is defined on
the whole of `D(𝒪_S)`.

This is registered as an instance because it is the instance argument every clause of
Stacks 06YY, 07A4 and 08H5 carries. -/
public instance hasLeftDerivedFunctor_toZariskiSmallModel :
    (pullbackOnHomotopy (toZariskiSmallModelHom B S hS)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (toZariskiSmallModelHom B S hS)
    (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)

/-- `Lε^*` on the model, named.

The two ringed topoi are passed explicitly and the result type is left to be inferred.  Both are
needed: `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` takes them as
implicit arguments which the elaborator solves *before* the morphism, so leaving them out
defaults its universe parameter to `0`; and writing the result type out in the
`Stacks.DerivedTensor.RingedSite.DerivedModules` spelling that Stacks 07A4 uses does not help,
since that abbreviation is not unfolded far enough to constrain the universe either.  With the
functor named this way, the statement of Stacks 07A4 below elaborates. -/
public noncomputable abbrev derivedPullbackSmallModel :=
  derivedPullback (X := smallModelRingedTopos B S hS) (Y := S.zariskiRingedTopos)
    (toZariskiSmallModelHom B S hS)

/-- **Stacks 06YY, exactness, for `ε` read on the model.**  The derived pullback along `ε_model`
is an exact functor of triangulated categories. -/
public theorem isTriangulated_derivedPullback_toZariskiSmallModel :
    (derivedPullback (X := smallModelRingedTopos B S hS) (Y := S.zariskiRingedTopos)
      (toZariskiSmallModelHom B S hS)).IsTriangulated :=
  isTriangulated_derivedPullback (toZariskiSmallModelHom B S hS)
    (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)

/-- **Stacks 08H5 for `ε` read on the model.**  If an object `E` of `D(𝒪_S)` has Tor amplitude in
`[a, b]` for a derived tensor product datum `T` on the small Zariski ringed site of `S`, then
`Lε^*E` has Tor amplitude in `[a, b]` for *any* derived tensor product datum `T'` on the model.

The arbitrariness of `T'` is inherited from Stacks 08H5: the direction of Stacks 08G1 that it
uses — a bounded complex of flat modules has Tor amplitude in its support interval — takes no
input about the datum. -/
public theorem hasTorAmplitude_derivedPullback_toZariskiSmallModel
    (T : @Stacks.SheafOfModules.DerivedTensorProduct S.zariskiRingedTopos.toRingedSite
      inferInstance inferInstance inferInstance
      (Stacks.SheafOfModules.Tensor.sheafTensor_additive S.zariskiRingedTopos.toRingedSite.O)
      (fun moduleSheaf => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
        S.zariskiRingedTopos.toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance))
    (T' : @Stacks.SheafOfModules.DerivedTensorProduct (smallModelRingedTopos B S hS).toRingedSite
      inferInstance inferInstance inferInstance
      (Stacks.SheafOfModules.Tensor.sheafTensor_additive
        (smallModelRingedTopos B S hS).toRingedSite.O)
      (fun moduleSheaf => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
        (smallModelRingedTopos B S hS).toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance))
    (E : RingedSite.DerivedModules S.zariskiRingedTopos.toRingedSite) (a b : ℤ)
    (hamp : @HasTorAmplitude S.zariskiRingedTopos.toRingedSite
      inferInstance inferInstance inferInstance
      (Tensor.sheafTensor_additive.{u, u, u, u, u} S.zariskiRingedTopos.toRingedSite.O)
      (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
        S.zariskiRingedTopos.toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance) T E a b) :
    @HasTorAmplitude (smallModelRingedTopos B S hS).toRingedSite
      inferInstance inferInstance inferInstance
      (Tensor.sheafTensor_additive.{u, u, u, u, u} (smallModelRingedTopos B S hS).toRingedSite.O)
      (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
        (smallModelRingedTopos B S hS).toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance)
      T' ((derivedPullback (X := smallModelRingedTopos B S hS) (Y := S.zariskiRingedTopos)
      (toZariskiSmallModelHom B S hS)).obj E) a b :=
  @hasTorAmplitude_derivedPullback (smallModelRingedTopos B S hS) S.zariskiRingedTopos
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Tensor.sheafTensor_additive.{u, u, u, u, u} (smallModelRingedTopos B S hS).O)
    (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (smallModelRingedTopos B S hS).O moduleSheaf)
    (fun _ _ _ => inferInstance)
    (Tensor.sheafTensor_additive.{u, u, u, u, u} S.zariskiRingedTopos.O)
    (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      S.zariskiRingedTopos.O moduleSheaf)
    (fun _ _ _ => inferInstance)
    (toZariskiSmallModelHom B S hS) (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
    (hasLeftDerivedFunctor_toZariskiSmallModel B S hS) T T' E a b hamp

/-- **Stacks 08H5 for the predicate of Stacks 08FZ (2), for `ε` read on the model.**  Finite Tor
dimension is preserved by the derived pullback along `ε_model`: an interval containing the Tor
amplitude of `E` contains that of `Lε^*E`. -/
public theorem hasFiniteTorDimension_derivedPullback_toZariskiSmallModel
    (T : @Stacks.SheafOfModules.DerivedTensorProduct S.zariskiRingedTopos.toRingedSite
      inferInstance inferInstance inferInstance
      (Stacks.SheafOfModules.Tensor.sheafTensor_additive S.zariskiRingedTopos.toRingedSite.O)
      (fun moduleSheaf => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
        S.zariskiRingedTopos.toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance))
    (T' : @Stacks.SheafOfModules.DerivedTensorProduct (smallModelRingedTopos B S hS).toRingedSite
      inferInstance inferInstance inferInstance
      (Stacks.SheafOfModules.Tensor.sheafTensor_additive
        (smallModelRingedTopos B S hS).toRingedSite.O)
      (fun moduleSheaf => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive
        (smallModelRingedTopos B S hS).toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance))
    (E : RingedSite.DerivedModules S.zariskiRingedTopos.toRingedSite)
    (h : @HasFiniteTorDimension S.zariskiRingedTopos.toRingedSite
      inferInstance inferInstance inferInstance
      (Tensor.sheafTensor_additive.{u, u, u, u, u} S.zariskiRingedTopos.toRingedSite.O)
      (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
        S.zariskiRingedTopos.toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance) T E) :
    @HasFiniteTorDimension (smallModelRingedTopos B S hS).toRingedSite
      inferInstance inferInstance inferInstance
      (Tensor.sheafTensor_additive.{u, u, u, u, u} (smallModelRingedTopos B S hS).toRingedSite.O)
      (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
        (smallModelRingedTopos B S hS).toRingedSite.O moduleSheaf)
      (fun _ _ _ => inferInstance)
      T' ((derivedPullback (X := smallModelRingedTopos B S hS) (Y := S.zariskiRingedTopos)
      (toZariskiSmallModelHom B S hS)).obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b,
    hasTorAmplitude_derivedPullback_toZariskiSmallModel B S hS T T' E a b hamp⟩

/-- **Stacks 07A4 for `ε` read on the model.**  The canonical bifunctorial isomorphism

`Lε^*(K ⊗^L_{𝒪_S} L) ≅ Lε^*K ⊗^L_{𝒪} Lε^*L`,

stated between the two uncurried bifunctors on `D(𝒪_S) × D(𝒪_S)` so that naturality in both
variables is part of its type.

This is the derived flat base change for `ε`, stated for
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`.  It is the isomorphism the
*source's* proof of the converse half of Stacks 08HF goes through, together with the
zero-reflection assertion of Stacks 08H8; the converse half as this tree carries it
(`AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_hasTorAmplitude`) takes a
different route — a computation on K-flat representatives — and so does not use this
isomorphism, which is why it is available for an arbitrary derived tensor product datum. -/
public def derivedPullbackTensorIsoSmallModel :
    Functor.uncurry.obj
          (@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            S.zariskiRingedTopos.C S.zariskiRingedTopos.category
            S.zariskiRingedTopos.J S.zariskiRingedTopos.O
            inferInstance inferInstance inferInstance
            (Tensor.sheafTensor_additive.{u, u, u, u, u} S.zariskiRingedTopos.O)
            (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
              S.zariskiRingedTopos.O moduleSheaf)
            (fun _ _ _ => inferInstance)) ⋙
        derivedPullbackSmallModel B S hS ≅
      (derivedPullbackSmallModel B S hS).prod (derivedPullbackSmallModel B S hS) ⋙
        Functor.uncurry.obj
          (@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (smallModelRingedTopos B S hS).C (smallModelRingedTopos B S hS).category
            (smallModelRingedTopos B S hS).J (smallModelRingedTopos B S hS).O
            inferInstance inferInstance inferInstance
            (Tensor.sheafTensor_additive.{u, u, u, u, u} (smallModelRingedTopos B S hS).O)
            (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
              (smallModelRingedTopos B S hS).O moduleSheaf)
            (fun _ _ _ => inferInstance)) :=
  @Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso
    (smallModelRingedTopos B S hS) S.zariskiRingedTopos
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Tensor.sheafTensor_additive.{u, u, u, u, u} (smallModelRingedTopos B S hS).O)
    (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (smallModelRingedTopos B S hS).O moduleSheaf)
    (Tensor.sheafTensor_additive.{u, u, u, u, u} S.zariskiRingedTopos.O)
    (fun moduleSheaf => Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      S.zariskiRingedTopos.O moduleSheaf)
    (fun _ _ _ => inferInstance)
    (fun _ _ _ => inferInstance)
    (toZariskiSmallModelHom B S hS) (hasLeftDerivedFunctor_toZariskiSmallModel B S hS)
    (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)

end AlgebraicGeometry.SmallEtale

end
