module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution

/-!
# Tor amplitude does not depend on the derived tensor product

Let `(C, O)` be a ringed site. Tor amplitude, finite Tor dimension and local finite Tor dimension
(Stacks 08FZ) are stated in this development against a datum
`Stacks.SheafOfModules.DerivedTensorProduct`, a derived tensor bifunctor on `D(O)` together with
its comparisons with the ordinary total tensor product on K-flat complexes. This file proves that
the three notions do not depend on that datum: any two derived tensor products give the same
answer. Together with the existence of a derived tensor product,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` (Stacks 06YU), this makes the three notions
intrinsic to `E`, as they are in the source, where `- ⊗^L_O -` is *the* derived tensor product.

The comparison is the one implicit in the source's definition of `⊗^L`. Represent `E` by a
K-flat complex `P` (Stacks 06YS); then each derived tensor product sends `(E, F[0])` to the total
tensor complex `Tot(P ⊗_O F)`, through its left K-flat comparison, so the two values are
isomorphic and so are their cohomology sheaves.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.nonempty_tensorSingleIso`: two derived tensor
  products agree, up to isomorphism, on `E ⊗^L F[0]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_congr`,
  `Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_congr` and
  `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_congr`: Tor amplitude
  in an interval, finite Tor dimension and local finite Tor dimension are the same for any two
  derived tensor products (on every slice, for the last).

## Implementation notes

The site is an `AlgebraicGeometry.RingedSite.{c, u, u}`: its objects live in an arbitrary universe
`c`, while its morphisms and the sections of its structure sheaf and of its modules live in `u`.
That is the generality in which K-flat resolutions,
`Stacks.SheafOfModules.exists_kFlat_quasiIso`, are available, and it covers the small étale site
of an algebraic space, an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, together with all of its
slices.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe c u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

section Global

variable {X : RingedSite.{c, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Two derived tensor products agree on `E ⊗^L F[0]`.** Representing `E` by a K-flat complex
`P`, Stacks 06YS, both send `(E, F[0])` to the total tensor complex `Tot(P ⊗_O F)` through their
left K-flat comparisons. -/
theorem nonempty_tensorSingleIso (T T' : DerivedTensorProduct.{c, u, u, d} X)
    (E : RingedSite.DerivedModules.{c, u, u, d} X) (F : RingedSite.Modules.{c, u, u} X) :
    Nonempty ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj F) ≅
      (T'.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{c, u, u} X) 0).obj F)) := by
  obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso X (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := p)).2 hp
  let e : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let s := (DerivedCategory.singleFunctorIsoCompQ (RingedSite.Modules.{c, u, u} X) 0).app F
  exact ⟨(T.tensor.mapIso e.symm).app _ ≪≫ (T.tensor.obj _).mapIso s ≪≫
    T.comparisonLeft _ _ hP ≪≫ (T'.comparisonLeft _ _ hP).symm ≪≫
    (T'.tensor.obj _).mapIso s.symm ≪≫ (T'.tensor.mapIso e).app _⟩

/-- **Tor amplitude does not depend on the derived tensor product.** -/
theorem hasTorAmplitude_congr (T T' : DerivedTensorProduct.{c, u, u, d} X)
    (E : RingedSite.DerivedModules.{c, u, u, d} X) (a b : ℤ) :
    HasTorAmplitude T E a b ↔ HasTorAmplitude T' E a b := by
  suffices key : ∀ T T' : DerivedTensorProduct.{c, u, u, d} X,
      HasTorAmplitude T E a b → HasTorAmplitude T' E a b from ⟨key T T', key T' T⟩
  intro T T' h F i hi
  obtain ⟨e⟩ := nonempty_tensorSingleIso T T' E F
  exact (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{c, u, u} X) i).mapIso e).symm

/-- **Finite Tor dimension does not depend on the derived tensor product.** -/
theorem hasFiniteTorDimension_congr (T T' : DerivedTensorProduct.{c, u, u, d} X)
    (E : RingedSite.DerivedModules.{c, u, u, d} X) :
    HasFiniteTorDimension T E ↔ HasFiniteTorDimension T' E :=
  exists₂_congr fun a b => hasTorAmplitude_congr T T' E a b

end Global

section Local

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{c, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [∀ U : X.C, HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance] sliceDerived

variable
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Local finite Tor dimension does not depend on the derived tensor products** chosen on the
slices of the site. -/
theorem locallyHasFiniteTorDimension_congr
    (T T' : ∀ U : X.C, DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{c, u, u, d} X) :
    LocallyHasFiniteTorDimension T E ↔ LocallyHasFiniteTorDimension T' E :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    forall_congr' fun V => forall_congr' fun _ => forall_congr' fun _ =>
      hasFiniteTorDimension_congr (T V) (T' V) _

end Local

end Stacks.SheafOfModules.DerivedTensorProduct

end
