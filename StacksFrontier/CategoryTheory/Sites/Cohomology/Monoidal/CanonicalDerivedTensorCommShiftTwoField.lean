module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo

/-!
# The shift datum of the canonical derived tensor product is the transported one

Let `(C, O)` be a ringed site.  The bifunctor
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R` of [Stacks, Tag 06YU] carries two
`CategoryTheory.Functor.CommShift₂Int` data: the structure field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂` of the canonical derived tensor
product, and `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, transported
from `CochainComplex.KFlatBifunctor.derivedBifunctor` along
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`.  This file proves that they are equal.

## Main results

* `CategoryTheory.Functor.CommShift.ofIso_eq`: if `e : F ≅ G` is compatible with the shifts for
  a structure `d` on `G`, then the structure transported along `e` is `d`.
* `CategoryTheory.Functor.CommShift₂.ofIso_eq`: the two-variable analogue.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq`: **the
  two shift data of the canonical derived tensor product agree.**
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso_commShift₂`: the comparison with
  `CochainComplex.KFlatBifunctor.derivedBifunctor` is compatible with the shifts.

## Implementation notes

A `CategoryTheory.Functor.CommShift` structure is determined by its commutation isomorphisms, and
a shift-compatible isomorphism `e` determines these on its target from those on its source; this
is the uniqueness half of `CategoryTheory.Functor.CommShift.ofIso`.  For the derived tensor
product, the canonical derived tensor product is the construction
(`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_eq`), whose bifunctor and shift
datum are those of `CochainComplex.KFlatBifunctor.derivedBifunctor`, and at the construction the
comparison `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso` is the identity: on
K-flat pairs it is a K-flat comparison followed by its own inverse.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor

namespace Functor.CommShift

variable {C D : Type*} [Category* C] [Category* D] {A : Type*} [AddMonoid A] [HasShift C A]
  [HasShift D A]

/-- A `CategoryTheory.Functor.CommShift` structure is determined by its commutation
isomorphisms. -/
theorem ext_of_commShiftIso {F : C ⥤ D} {d d' : F.CommShift A}
    (h : ∀ a : A, @commShiftIso _ _ _ _ F A _ _ _ d a = @commShiftIso _ _ _ _ F A _ _ _ d' a) :
    d = d' := by
  cases d
  cases d'
  obtain rfl : _ = _ := funext h
  rfl

/-- **Uniqueness of the transported shift structure.**  If `e : F ≅ G` is compatible with the
shifts for a structure `d` on `G`, then `d` is the structure
`CategoryTheory.Functor.CommShift.ofIso` transported along `e`. -/
theorem ofIso_eq {F G : C ⥤ D} (e : F ≅ G) [F.CommShift A] (d : G.CommShift A)
    (he : @NatTrans.CommShift _ _ _ _ F G e.hom A _ _ _ _ d) :
    ofIso e A = d := by
  refine ext_of_commShiftIso fun a => Iso.ext (NatTrans.ext (funext fun X => ?_))
  have hX := @NatTrans.shift_app_comm _ _ _ _ F G e.hom A _ _ _ _ d he a X
  rw [ofIso_commShiftIso_hom_app]
  rw [hX, Iso.inv_hom_id_app_assoc]

end Functor.CommShift

namespace Functor.CommShift₂

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]

/-- A `CategoryTheory.Functor.CommShift₂` structure is determined by its two families of
one-variable shift structures. -/
theorem ext_of_commShiftObj {G : C₁ ⥤ C₂ ⥤ D} {h : CommShift₂Setup D M} {d d' : G.CommShift₂ h}
    (h₁ : ∀ X₁, commShiftObj (self := d) h X₁ = commShiftObj (self := d') h X₁)
    (h₂ : ∀ X₂, commShiftFlipObj (self := d) h X₂ = commShiftFlipObj (self := d') h X₂) :
    d = d' := by
  cases d
  cases d'
  obtain rfl : _ = _ := funext h₁
  obtain rfl : _ = _ := funext h₂
  rfl

/-- **Uniqueness of the transported two-variable shift structure.**  If `e : G ≅ G'` is
compatible with the shifts in both variables for a structure `d` on `G'`, then `d` is the
structure `CategoryTheory.Functor.CommShift₂.ofIso` transported along `e`. -/
theorem ofIso_eq {G G' : C₁ ⥤ C₂ ⥤ D} (e : G ≅ G') (h : CommShift₂Setup D M) [G.CommShift₂ h]
    (d : G'.CommShift₂ h) (he : @NatTrans.CommShift₂ _ _ _ _ _ _ M _ _ _ _ G G' e.hom h _ d) :
    ofIso e h = d :=
  ext_of_commShiftObj (fun X₁ => CommShift.ofIso_eq (e.app X₁) _ (he.commShift_app X₁))
    (fun X₂ => CommShift.ofIso_eq ((flipIso e).app X₂) _ (he.commShift_flipApp X₂))

end Functor.CommShift₂

end CategoryTheory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- At the construction of the derived tensor product, the comparison with
`CochainComplex.KFlatBifunctor.derivedBifunctor` is the identity: on a pair of K-flat complexes
it is a K-flat comparison followed by its own inverse. -/
theorem derivedBifunctorTensorIso_construction_hom :
    (derivedBifunctorTensorIso R
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductConstruction R)).hom = 𝟙 _ :=
  Localization.natTrans₂_ext (kFlatComplexQ R) (kFlatComplexQ R)
    (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R) fun X₁ X₂ =>
      (derivedBifunctorTensorIso_hom_app_app R _ X₁.1 X₂.1 X₁.2 X₂.2).trans (Iso.hom_inv_id _)

/-- **The two shift data of the canonical derived tensor product agree**: the structure field
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.commShift₂` of the canonical derived tensor
product of [Stacks, Tag 06YU] is the datum
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int` transported from
`CochainComplex.KFlatBifunctor.derivedBifunctor`. -/
theorem canonicalDerivedTensorProduct_commShift₂_eq :
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).commShift₂ =
      canonicalTensor_commShift₂Int R := by
  have key : ∀ T, T = Stacks.DerivedTensor.RingedSite.derivedTensorProductConstruction R →
      T.commShift₂ = Functor.CommShift₂.ofIsoInt (derivedBifunctorTensorIso R T) := by
    rintro T rfl
    refine (Functor.CommShift₂.ofIso_eq _ _ _ ?_).symm
    rw [derivedBifunctorTensorIso_construction_hom]
    exact (inferInstance : NatTrans.CommShift₂ (𝟙 (derivedBifunctor (curriedTensor (Mod R))))
      CommShift₂Setup.int)
  exact key _ (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_eq R)

/-- **The comparison of the two derived tensor bifunctors is compatible with the shifts in both
variables**, for the shift datum of the canonical derived tensor product, its structure field.
For the transported datum `canonicalTensor_commShift₂Int` this holds by construction
(`CategoryTheory.Functor.CommShift₂.ofIsoInt_commShift₂`), and
`canonicalDerivedTensorProduct_commShift₂_eq` identifies the two data.  Every statement about the
shifts of `CochainComplex.KFlatBifunctor.derivedBifunctor` can therefore be moved to
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` along this isomorphism. -/
theorem canonicalTensorIso_commShift₂ :
    NatTrans.CommShift₂Int (canonicalTensorIso R).hom :=
  (canonicalDerivedTensorProduct_commShift₂_eq R).symm ▸
    Functor.CommShift₂.ofIsoInt_commShift₂ (canonicalTensorIso R)

end Stacks.SheafOfModules.DerivedMonoidal

end
