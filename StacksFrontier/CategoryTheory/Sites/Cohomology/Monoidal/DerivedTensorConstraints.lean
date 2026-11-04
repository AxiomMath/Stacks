module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.KFlatComplexesInTheDerivedCategory

/-!
# The constraints of the symmetric monoidal derived category of a ringed site

For a ringed site `(C, O)` the derived category `D(Mod(O))` is a symmetric monoidal category
whose tensor product is the derived tensor product.  This file supplies the remaining clause of
that statement: its associativity and commutativity constraints are, through the comparison with
the total tensor product on K-flat complexes, the constraints of `Comp(Mod(O))`, whose braiding
is the Koszul symmetry.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison`: the comparison
  `Q(K) ⊗ Q(L) ≅ Q(Tot(K ⊗_O L))` for K-flat complexes `K` and `L`, namely the tensorator of
  the braided monoidal functor `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ`.
* `Stacks.SheafOfModules.DerivedMonoidal.SymmetricMonoidalDerivedTensor`: a symmetric monoidal
  structure on `D(Mod(O))` with the derived tensor product as its tensor product, the structure
  sheaf in degree zero as its unit, and those constraints.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_naturality`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_associator`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatComparison_braiding`: the comparison is natural in
  both complexes and carries the associator and the braiding of `D(Mod(O))` to those of
  `Comp(Mod(O))`.
* `Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerivedTensor`: the whole structure.

## Implementation notes

No coherence diagram is checked.  The K-flat complexes are a full monoidal subcategory of
`Comp(Mod(O))`, and the composite from them to `D(Mod(O))` is a braided monoidal functor
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/MonoidalLocalizationFunctors.lean`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/KFlatComplexesMonoidalSubcategory.lean`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/KFlatComplexesInTheDerivedCategory.lean`).
Its tensorator *is* the comparison, and the three results above are its `μ_natural`,
`associativity` and `braided` fields.

The tensor product is identified with the derived tensor product of Tag 06YU as an isomorphism
of bifunctors, by `Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso`; the
sharper statement that a re-seating of this structure has that bifunctor as its tensor product
*on the nose* is `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

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

/- The pinned-universe monoidal structures of `CanonicalDerivedTensorComparison`, back in
scope.  `SheafOfModules.monoidalCategorySheafTensor` has sections in `max u v w` for a `w`
that the `u` of `Mod R` does not determine, and the constraints below cannot be reduced
through a structure whose universe is still a metavariable. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal
  CochainComplex.KFlatMonoidal.homotopyBraided
  kFlatQ_isLocalization derivedMonoidal derivedSymmetric

attribute [local instance] homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided
  kFlatQuotientMonoidal kFlatQuotientLaxBraided kFlatComplexQMonoidal kFlatComplexQLaxBraided

/-! ### The comparison on K-flat complexes -/

/-- **For K-flat complexes the tensor product of `D(Mod(O))` is the image of the total tensor
product of complexes.**  This is the tensorator of `kFlatComplexQ`. -/
abbrev kFlatComparison {K L : Complexes R} (hK : KFlat R K) (hL : KFlat R L) :
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L) :=
  Functor.Monoidal.μIso (kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩

/-- **The commutativity constraint of `D(Mod(O))` is the Koszul symmetry of complexes**: the
comparison on K-flat complexes carries the braiding of `D(Mod(O))` to that of
`Comp(Mod(O))`. -/
theorem kFlatComparison_braiding {K L : Complexes R} (hK : KFlat R K) (hL : KFlat R L) :
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (kFlatComparison R hL hK).hom =
      (kFlatComparison R hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom :=
  (Functor.LaxBraided.braided (F := kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩).symm

/-- **The associativity constraint of `D(Mod(O))` is the associator of the total tensor product
of complexes**: the comparison on K-flat complexes carries the associator of `D(Mod(O))` to
that of `Comp(Mod(O))`. -/
theorem kFlatComparison_associator {K L M : Complexes R} (hK : KFlat R K) (hL : KFlat R L)
    (hM : KFlat R M) :
    (kFlatComparison R hK hL).hom ▷ DerivedCategory.Q.obj M ≫
        (kFlatComparison R (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hM).hom ≫
        DerivedCategory.Q.map (α_ K L M).hom =
      (α_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).hom ≫
        DerivedCategory.Q.obj K ◁ (kFlatComparison R hL hM).hom ≫
        (kFlatComparison R hK (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hM)).hom :=
  Functor.LaxMonoidal.associativity (kFlatComplexQ R) ⟨K, hK⟩ ⟨L, hL⟩ ⟨M, hM⟩

/-- **The comparison is natural in both complexes.** -/
theorem kFlatComparison_naturality {K K' L L' : Complexes R} (f : K ⟶ K') (g : L ⟶ L')
    (hK : KFlat R K) (hK' : KFlat R K') (hL : KFlat R L) (hL' : KFlat R L') :
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫ (kFlatComparison R hK' hL').hom =
      (kFlatComparison R hK hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural (F := kFlatComplexQ R)
    (X := ⟨K, hK⟩) (Y := ⟨K', hK'⟩) (X' := ⟨L, hL⟩) (Y' := ⟨L', hL'⟩)
    (ObjectProperty.homMk f) (ObjectProperty.homMk g)

/-! ### The field types of `SymmetricMonoidalDerivedTensor` -/

/-- The tensor product of `D(Mod(O))` is the derived tensor product of Tag 06YU. -/
abbrev TensorIsoDerived [Monoidal R] :=
  curriedTensor (DerivedModules R) ≅
    Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R

/-- A comparison, on K-flat complexes, of the tensor product of `D(Mod(O))` with the total
tensor product of complexes. -/
abbrev KFlatComparisonData [Monoidal R] :=
  ∀ (K L : Complexes R), KFlat R K → KFlat R L →
    (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L))

/-- The comparison is natural in both complexes. -/
abbrev ComparisonNatural [Monoidal R] (c : KFlatComparisonData R) : Prop :=
  ∀ (K K' L L' : Complexes R) (f : K ⟶ K') (g : L ⟶ L')
    (hK : KFlat R K) (hK' : KFlat R K') (hL : KFlat R L) (hL' : KFlat R L'),
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫ (c K' L' hK' hL').hom =
      (c K L hK hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g)

/-- The comparison carries the associator of `D(Mod(O))` to that of `Comp(Mod(O))`. -/
abbrev ComparisonAssociator [Monoidal R] (c : KFlatComparisonData R) : Prop :=
  ∀ (K L M : Complexes R) (hK : KFlat R K) (hL : KFlat R L) (hM : KFlat R M),
    (c K L hK hL).hom ▷ DerivedCategory.Q.obj M ≫
        (c (K ⊗ L) M (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hK hL) hM).hom ≫
        DerivedCategory.Q.map (α_ K L M).hom =
      (α_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).hom ≫
        DerivedCategory.Q.obj K ◁ (c L M hL hM).hom ≫
        (c K (L ⊗ M) hK (CochainComplex.KFlatMonoidal.kFlat_tensor (Mod R) hL hM)).hom

/-- The comparison carries the braiding of `D(Mod(O))` to the Koszul braiding of
`Comp(Mod(O))`. -/
abbrev ComparisonBraiding [Monoidal R] [Symmetric R] (c : KFlatComparisonData R) : Prop :=
  ∀ (K L : Complexes R) (hK : KFlat R K) (hL : KFlat R L),
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫ (c L K hL hK).hom =
      (c K L hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom

/-! ### The statement -/

/-- A symmetric monoidal structure on the derived category of modules on a ringed site whose
tensor product is the derived tensor product, whose unit is the structure sheaf in degree zero,
and whose associativity and commutativity constraints are, through the comparison on K-flat
complexes, the usual constraints of the total tensor product of complexes. -/
public structure SymmetricMonoidalDerivedTensor where
  /-- The monoidal category structure on `D(Mod(O))`. -/
  monoidal : Monoidal R
  /-- The symmetry of the monoidal structure on `D(Mod(O))`. -/
  symmetric : Symmetric R
  /-- The tensor product of `D(Mod(O))` is isomorphic to the derived tensor product. -/
  tensorIso : TensorIsoDerived R
  /-- The unit of `D(Mod(O))` is isomorphic to the structure sheaf in degree zero. -/
  unitIso : UnitIso R
  /-- The comparison `Q(K) ⊗ Q(L) ≅ Q(K ⊗ L)` for K-flat complexes `K` and `L`. -/
  comparison : KFlatComparisonData R
  /-- The comparison is natural in both complexes. -/
  comparison_naturality : ComparisonNatural R comparison
  /-- The comparison carries the associator of `D(Mod(O))` to that of `Comp(Mod(O))`. -/
  comparison_associator : ComparisonAssociator R comparison
  /-- The comparison carries the braiding of `D(Mod(O))` to the Koszul braiding of
  `Comp(Mod(O))`. -/
  comparison_braiding : ComparisonBraiding R comparison

/-- **The derived category of modules on a ringed site is a symmetric monoidal category with
tensor product the derived tensor product and the usual associativity and commutativity
constraints**, the latter being those of the total tensor product of complexes with the Koszul
sign convention. -/
@[stacks 0FPT]
public def symmetricMonoidalDerivedTensor : SymmetricMonoidalDerivedTensor R where
  monoidal := derivedMonoidal R
  symmetric := derivedSymmetric R
  tensorIso := monoidalTensorCanonicalIso R
  unitIso := CochainComplex.KFlatMonoidal.derivedUnitIso (Mod R) (exists_kFlat_resolution R)
  comparison _ _ hK hL := kFlatComparison R hK hL
  comparison_naturality _ _ _ _ f g hK hK' hL hL' :=
    kFlatComparison_naturality R f g hK hK' hL hL'
  comparison_associator _ _ _ hK hL hM := kFlatComparison_associator R hK hL hM
  comparison_braiding _ _ hK hL := kFlatComparison_braiding R hK hL

end Stacks.SheafOfModules.DerivedMonoidal

end
