module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison

/-!
# The two derived tensor products of a ringed site are isomorphic

A ringed site `(C, O)` carries two independently defined derived tensor products on `D(Mod(O))`:
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, stated for a bundled ringed site, and
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, stated for the structure sheaf.
The first is the construction `derivedTensorProductOfExact` and the second the construction
`derivedTensorProductConstruction`, both opaque to the kernel (`irreducible_def`).  They are
different terms, so the constructions built on them cannot be composed directly: the derived
internal hom and its tensor–internal-hom bijection use the first, while the derived
pullback–tensor comparison, the relative Künneth morphism and the symmetric monoidal structure on
`D(Mod(O))` use the second.

This file identifies their bifunctors. Both are characterized by the same data — the K-flat
comparison and its naturality — so each descends the total tensor product of K-flat complexes
along `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ` in both variables, and the
comparison is the resulting isomorphism of descents.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceDerivedBifunctorTensorIso`: the bifunctor of
  an arbitrary `Stacks.SheafOfModules.DerivedTensorProduct` is
  `CochainComplex.KFlatBifunctor.derivedBifunctor`.
* `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`: the two canonical derived
  tensor products agree.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceDerivedBifunctorTensorIso_hom_app_app`: on a
  pair of K-flat complexes the comparison is the one-sided K-flat comparison of
  `derivedBifunctor` followed by the inverse of the K-flat comparison of the given derived
  tensor product.

## Implementation notes

The argument is `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso` with the
other of the two `DerivedTensorProduct` structures in the lifting datum; the localization of
the K-flat complexes, the common source bifunctor and the second descent are reused verbatim
from the neighbouring file.

K-flatness is spelled `Stacks.SheafOfModules.IsKFlat` by the structure used here and
`Stacks.SheafOfModules.KFlat.KFlat` by the one used there. Both are the condition that
`Tot(F ⊗_O K)` be acyclic for acyclic `F`, so no conversion appears below.

Nothing here carries a project tag. Tag 06YU already sits on both developments, the
`Stacks.DerivedTensor.RingedSite` one and the one in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Existence.lean`; this file is the
comparison between the two, not a third account of the tag.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod X.O)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- `Mod(O)` is monoidal, with the three universe arguments of
`SheafOfModules.monoidalCategorySheafTensor` pinned at this file's single universe `u`.

The sections universe of that structure is `max u v w` for a free `w`, so unifying it against
the `u` of `Mod X.O` leaves `w` undetermined; the whiskerings below cannot reduce through a
monoidal structure on `Comp(Mod(O))` synthesized from one whose universe is still a
metavariable.  Pinning it costs no generality: this file's ringed site is
`RingedSite.{u, u, u}`. -/
local instance monoidalCategoryModRingedSite : MonoidalCategory (Mod X.O) :=
  SheafOfModules.monoidalCategorySheafTensor.{u, u} X.O

variable (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)

/-! ### Reading the merged naturality one variable at a time -/

private theorem comp_id_comp_eq {D : Type*} [Category D] {A B Z : D} {a : A ⟶ B}
    {b : B ⟶ B} {c : B ⟶ Z} {e : A ⟶ Z} (h : a ≫ b ≫ c = e) (hb : b = 𝟙 B) : a ≫ c = e := by
  rw [hb, Category.id_comp] at h
  exact h

private theorem id_comp_comp_eq {D : Type*} [Category D] {A B Z : D} {a : A ⟶ A}
    {b : A ⟶ B} {c : B ⟶ Z} {e : A ⟶ Z} (h : a ≫ b ≫ c = e) (ha : a = 𝟙 A) : b ≫ c = e := by
  rw [ha, Category.id_comp] at h
  exact h

/-- Naturality of the K-flat comparison in the first variable alone, in the monoidal spelling
of the total tensor product. -/
theorem interfaceComparison_naturality_left {K K' L : Complexes X.O} (f : K ⟶ K')
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hK' : Stacks.SheafOfModules.IsKFlat X.O K')
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (T.comparison K' L hK' hL).hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (f ▷ L) :=
  comp_id_comp_eq (T.comparison_naturality f (𝟙 L) hK hK' hL hL)
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id])

/-- Naturality of the K-flat comparison in the second variable alone. -/
theorem interfaceComparison_naturality_right (K : Complexes X.O) {L L' : Complexes X.O}
    (g : L ⟶ L') (hK : Stacks.SheafOfModules.IsKFlat X.O K)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L)
    (hL' : Stacks.SheafOfModules.IsKFlat X.O L') :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (T.comparison K L' hK hL').hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (K ◁ g) :=
  id_comp_comp_eq (T.comparison_naturality (𝟙 K) g hK hK hL hL')
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app])

/-! ### The descent -/

/-- **The bifunctor of a `Stacks.SheafOfModules.DerivedTensorProduct` descends the total tensor
product of K-flat complexes.** The lifting isomorphism is the `comparison` field, and its two
naturality squares are the merged naturality field read one variable at a time. -/
@[instance_reducible]
def interfaceTensorLifting :
    Localization.Lifting₂ (kFlatComplexQ X.O) (kFlatComplexQ X.O)
      (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
      (kFlatTensorSource X.O) T.tensor where
  iso := NatIso.ofComponents
    (fun A ↦ NatIso.ofComponents (fun B ↦ T.comparison A.1 B.1 A.2 B.2)
      (fun g ↦ interfaceComparison_naturality_right X T _ g.hom _ _ _))
    (fun f ↦ by ext B; exact interfaceComparison_naturality_left X T f.hom _ _ _)

attribute [local instance] interfaceTensorLifting derivedBifunctorLifting

/-! ### The comparison -/

/-- **The derived tensor bifunctor of `CochainComplex.KFlatBifunctor` is the bifunctor of any
`Stacks.SheafOfModules.DerivedTensorProduct`.** Both descend the total tensor product of K-flat
complexes along `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ` in each variable, so the
comparison is `CategoryTheory.Localization.lift₂NatIso` of the identity. -/
def interfaceDerivedBifunctorTensorIso :
    derivedBifunctor (curriedTensor (Mod X.O)) ≅ T.tensor :=
  Localization.lift₂NatIso (kFlatComplexQ X.O) (kFlatComplexQ X.O)
    (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
    (kFlatTensorSource X.O) (kFlatTensorSource X.O)
    (derivedBifunctor (curriedTensor (Mod X.O))) T.tensor (Iso.refl _)

/-- **The comparison, computed on a pair of K-flat complexes**: the one-sided K-flat comparison
of `derivedBifunctor` followed by the inverse of the K-flat comparison of the given derived
tensor product. -/
theorem interfaceDerivedBifunctorTensorIso_hom_app_app (K L : Complexes X.O)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    ((interfaceDerivedBifunctorTensorIso X T).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (comparisonRight (curriedTensor (Mod X.O)) K L hL).hom ≫ (T.comparison K L hK hL).inv := by
  refine (Localization.lift₂NatTrans_app_app (kFlatComplexQ X.O) (kFlatComplexQ X.O)
    (kFlatComplexQuasiIso X.O) (kFlatComplexQuasiIso X.O)
    (kFlatTensorSource X.O) (kFlatTensorSource X.O)
    (derivedBifunctor (curriedTensor (Mod X.O))) T.tensor (Iso.refl _).hom
    (⟨K, hK⟩ : (KFlatComplexes X.O).FullSubcategory)
    (⟨L, hL⟩ : (KFlatComplexes X.O).FullSubcategory)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- **The two canonical derived tensor products of a ringed site agree**: the bifunctor of
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which the derived internal hom is stated
over, is isomorphic to `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, which the
derived pullback–tensor comparison and the symmetric monoidal structure are stated over. -/
def interfaceTensorCanonicalIso :
    Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X ≅
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O :=
  (interfaceDerivedBifunctorTensorIso X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X)).symm ≪≫
    canonicalTensorIso X.O

end Stacks.SheafOfModules.DerivedMonoidal

end
