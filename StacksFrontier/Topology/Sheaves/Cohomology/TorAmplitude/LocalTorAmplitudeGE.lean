module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude in `[a, ∞)` is local, and does not depend on the derived tensor product

Let `X` be a ringed space and `E` an object of `D(𝒪_X)`. This file proves two facts about Tor
amplitude in `[a, ∞)` ([Stacks, Tag 08CG]) which [Stacks, Tag 0E2N] consumes.

* It is local on `X`: if the restriction of `E` to every member of an open covering of `X` has
  Tor amplitude in `[a, ∞)`, then so does `E`, with the same `a`. This is
  `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_iSup_eq_top`, the half-infinite companion
  of `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`, proved the same way; in
  particular the hypothesis `Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE` implies
  `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE`
  (`hasTorAmplitudeGE_of_locallyHasTorAmplitudeGE`).
* On the ringed site of opens it does not depend on which derived tensor product of
  [Stacks, Tag 06YU] it is measured with: two inhabitants of
  `Stacks.SheafOfModules.DerivedTensorProduct` both compute `E ⊗^L F[0]` as the class of
  `Tot(A ⊗ F[0])` for a K-flat model `A` of `E`
  (`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_transfer`).

## Implementation notes

The import of `LocalTorAmplitude` brings the locally small derived category of sheaves of
modules into scope as a global instance, next to `HasDerivedCategory.standard`. The transfer
lemma is stated at the standard instance, which is the one the derived tensor products and the
diagonal of [Stacks, Tag 0BYS] are elaborated with, so the standard instance is given priority in
that section. The locality statement keeps the derived category of `X` a parameter and names the
standard derived categories of the open subspaces explicitly, as
`Stacks.Cohomology.TorAmplitude.derivedTensorRestrictIsoOfKFlatLeft` reads them.

## References

* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude

universe u d

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **Tor amplitude in `[a, ∞)` is local on an open covering.** If the restriction of an object
of `D(𝒪_X)` to each member of an open covering of `X` has Tor amplitude in `[a, ∞)`, then the
object has Tor amplitude in `[a, ∞)`.

The proof is that of `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`: represent
the object by a K-flat complex, compute its derived tensor product with a module in degree zero
as a total tensor complex, and test vanishing of a cohomology sheaf on the covering. -/
@[sga "6 I 5.5" "partial"]
theorem hasTorAmplitudeGE_of_iSup_eq_top (E : DerivedCategory (OXMod.{u, u} X)) (a : ℤ)
    {ι : Type*} (V : ι → Opens X.carrier) (hV : iSup V = ⊤)
    (h : ∀ i : ι, @HasTorAmplitudeGE (X.restrict (V i).isOpenEmbedding)
      (HasDerivedCategory.standard _)
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X (V i)).obj E) a) :
    HasTorAmplitudeGE X E a := by
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

/-- **Local Tor amplitude in `[a, ∞)` is Tor amplitude in `[a, ∞)`.** The hypothesis
`LocallyHasTorAmplitudeGE` of [Stacks, Tag 0E2N], with the standard derived categories on the
members of the covering, implies the global condition with the same bound. -/
theorem hasTorAmplitudeGE_of_locallyHasTorAmplitudeGE (E : DerivedCategory (OXMod.{u, u} X))
    (a : ℤ) (h : @LocallyHasTorAmplitudeGE X _ (fun _ => HasDerivedCategory.standard _) E a) :
    HasTorAmplitudeGE X E a := by
  obtain ⟨I, U, hU, hI⟩ := h
  exact hasTorAmplitudeGE_of_iSup_eq_top E a U hU hI

end Stacks.Cohomology.TorAmplitude

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe v

attribute [local instance 2000] HasDerivedCategory.standard

/-- For any derived tensor product on the ringed site of opens of a ringed space, the derived
tensor product of `E` with a module placed in degree zero is the class of the total tensor
complex of the chosen K-flat model of `E` with that module: the `comparisonLeft` field at the
model. -/
def tensorSingleModelIso {W : RingedSpace.{v, v}}
    (T : Stacks.SheafOfModules.DerivedTensorProduct (Stacks.SheafOfModules.ringedSite W.sheaf))
    (E : DerivedCategory (SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite W.sheaf).O)))
    (F : SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite W.sheaf).O)) :
    (T.tensor.obj E).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex W.sheaf).obj
        ((Stacks.SheafOfModules.ringedSite W.sheaf).kFlatModel E)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) :=
  (T.tensor.mapIso ((Stacks.SheafOfModules.ringedSite W.sheaf).kFlatModelIso E).symm).app _ ≪≫
    (T.tensor.obj _).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
    T.comparisonLeft _ _ ((Stacks.SheafOfModules.ringedSite W.sheaf).isKFlat_kFlatModel E)

/-- **Tor amplitude in `[a, ∞)` does not depend on the chosen derived tensor product.** Two
derived tensor products on the ringed site of opens of a ringed space agree, at a K-flat model
of the first argument, with the same total tensor complex, so the cohomology sheaves whose
vanishing defines Tor amplitude in `[a, ∞)` are isomorphic. -/
theorem hasTorAmplitudeGE_transfer {W : RingedSpace.{v, v}}
    (T T' : Stacks.SheafOfModules.DerivedTensorProduct (Stacks.SheafOfModules.ringedSite W.sheaf))
    {E : DerivedCategory (SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite W.sheaf).O))}
    {a : ℤ} (h : T.HasTorAmplitudeGE E a) : T'.HasTorAmplitudeGE E a := fun F n hn =>
  IsZero.of_iso (h F n hn) ((DerivedCategory.homologyFunctor _ n).mapIso
    (tensorSingleModelIso T' E F ≪≫ (tensorSingleModelIso T E F).symm))

end Stacks.SheafOfModules.DerivedTensorProduct

end
