module

public import StacksFrontier.Homology.DerivedCategory.DerivedTensorPairwiseComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
public import StacksFrontier.Homology.KFlat.BifunctorComplexLocalization
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft

/-!
# The canonical derived tensor product of `D(R)` is the K-flat derived bifunctor

Over a commutative ring `R`, the canonical derived tensor product
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` and the derived bifunctor
`CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried tensor product are isomorphic
bifunctors on `D(R)`. Both are liftings of the single bifunctor `(K, L) ↦ Q(K ⊗_R L)` on K-flat
complexes along the localization functor `CochainComplex.KFlatBifunctor.kFlatComplexQ` in each
variable, so `CategoryTheory.Localization.lift₂NatIso` compares them.

Everything is stated for an arbitrary model of `D(R)`, except
`CochainComplex.DerivedTensor.monoidalTensorObjIsoDerivedBifunctorObj`, which is read at the
standard model, the one at which the symmetric monoidal structure on `D(R)` is constructed.

## Main definitions

* `CochainComplex.DerivedTensor.kFlatTensorSource`: the bifunctor on K-flat complexes that both
  sides descend, namely `(K, L) ↦ Q(K ⊗_R L)`.
* `CochainComplex.DerivedTensor.canonicalTensorLifting`,
  `CochainComplex.DerivedTensor.derivedBifunctorLifting`: the two
  `CategoryTheory.Localization.Lifting₂` data exhibiting each bifunctor as a descent of
  `kFlatTensorSource`.
* `CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso`: the resulting isomorphism
  of bifunctors.
* `CochainComplex.DerivedTensor.monoidalTensorObjIsoDerivedBifunctorObj`: the tensor product of
  the symmetric monoidal structure on `D(R)` is isomorphic to `derivedBifunctor` at every pair of
  objects.

## Main results

* `CochainComplex.DerivedTensor.exists_kFlat_iso`: every object of `D(R)` is isomorphic to the
  image of a K-flat complex.
* `CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso_hom_app_app`: the comparison,
  on the image of a pair of K-flat complexes, is the one-sided K-flat comparison of the descent
  followed by the inverse of the two-sided K-flat comparison of the canonical derived tensor
  product.
* `CochainComplex.DerivedTensor.nonempty_canonicalTensorObj_iso_derivedBifunctorObj`: the two
  bifunctors agree at every pair of objects up to isomorphism.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.DerivedTensor

section

variable (R : Type u) [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]

/-- Every object of `D(R)` is isomorphic to the image under `DerivedCategory.Q` of a K-flat
complex. -/
theorem exists_kFlat_iso (Z : DerivedCategory (ModuleCat.{u} R)) :
    ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
      CochainComplex.KFlat.{u, u} K ∧ Nonempty (DerivedCategory.Q.obj K ≅ Z) := by
  obtain ⟨K, f, hK, -, hf, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
      ((DerivedCategory.Q (C := ModuleCat.{u} R)).objPreimage Z)
  have : QuasiIso f := hf
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso Z⟩⟩

/-! ### The bifunctor on K-flat complexes that both sides descend -/

/-- The bifunctor `(K, L) ↦ Q(K ⊗_R L)` on K-flat complexes of `R`-modules: the total tensor
complex, pushed into `D(R)`. -/
abbrev kFlatTensorSource :
    (KFlatBifunctor.kFlatComplexes (curriedTensor (ModuleCat.{u} R))).FullSubcategory ⥤
      (KFlatBifunctor.kFlatComplexes (curriedTensor (ModuleCat.{u} R))).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (((Functor.whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj
      (KFlatBifunctor.kFlatComplexes (curriedTensor (ModuleCat.{u} R))).ι).obj
      (KFlatBifunctor.kFlatComplexes (curriedTensor (ModuleCat.{u} R))).ι).obj
    (curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)

/-! ### The two descents -/

/-- Naturality of the two-sided K-flat comparison of the canonical derived tensor product in its
first variable alone. -/
theorem canonicalComparison_naturality_left
    {K K' L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K')
    (hK : CochainComplex.KFlat.{u, u} K) (hK' : CochainComplex.KFlat.{u, u} K')
    (hL : CochainComplex.KFlat.{u, u} L) :
    ((canonicalDerivedTensorProduct R).tensor.map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorProduct R).comparison K' L hK' hL).hom =
      ((canonicalDerivedTensorProduct R).comparison K L hK hL).hom ≫
        DerivedCategory.Q.map (f ▷ L) := by
  have h := (canonicalDerivedTensorProduct R).comparison_naturality f (𝟙 L) hK hK' hL hL
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- Naturality of the two-sided K-flat comparison of the canonical derived tensor product in its
second variable alone. -/
theorem canonicalComparison_naturality_right (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L')
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L)
    (hL' : CochainComplex.KFlat.{u, u} L') :
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        ((canonicalDerivedTensorProduct R).comparison K L' hK hL').hom =
      ((canonicalDerivedTensorProduct R).comparison K L hK hL).hom ≫
        DerivedCategory.Q.map (K ◁ g) := by
  have h := (canonicalDerivedTensorProduct R).comparison_naturality (𝟙 K) g hK hK hL hL'
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the left complex. No
K-flatness is assumed on the left. -/
theorem derivedComparison_naturality_left
    {K K' L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ K')
    (hL : CochainComplex.KFlat.{u, u} L) :
    ((KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R))).map
          (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) K' L hL).hom =
      (KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) K L hL).hom ≫
        DerivedCategory.Q.map (f ▷ L) :=
  KFlatBifunctor.comparisonRight_naturality_left (curriedTensor (ModuleCat.{u} R)) f L hL

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the K-flat right
complex. -/
theorem derivedComparison_naturality_right (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L')
    (hL : CochainComplex.KFlat.{u, u} L) (hL' : CochainComplex.KFlat.{u, u} L') :
    ((KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R))).obj
          (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) K L' hL').hom =
      (KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) K L hL).hom ≫
        DerivedCategory.Q.map (K ◁ g) :=
  KFlatBifunctor.comparisonRight_naturality_right (curriedTensor (ModuleCat.{u} R)) K g hL hL'

/-- The canonical derived tensor product is a lifting of
`CochainComplex.DerivedTensor.kFlatTensorSource` along `kFlatComplexQ` in each variable, with
lifting isomorphism its two-sided K-flat comparison. -/
@[instance_reducible]
def canonicalTensorLifting :
    Localization.Lifting₂
      (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
      (kFlatTensorSource R) (canonicalDerivedTensorProduct R).tensor where
  iso := NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ (canonicalDerivedTensorProduct R).comparison X.1 Y.1 X.2 Y.2)
      (fun g ↦ canonicalComparison_naturality_right R _ g.hom _ _ _))
    (fun f ↦ by ext Y; exact canonicalComparison_naturality_left R f.hom _ _ _)

/-- `CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried tensor product is a lifting
of `CochainComplex.DerivedTensor.kFlatTensorSource` along `kFlatComplexQ` in each variable, with
lifting isomorphism the one-sided comparison `CochainComplex.KFlatBifunctor.comparisonRight`. -/
@[instance_reducible]
def derivedBifunctorLifting :
    Localization.Lifting₂
      (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
      (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
      (kFlatTensorSource R)
      (KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R))) where
  iso := NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) X.1 Y.1 Y.2)
      (fun g ↦ derivedComparison_naturality_right R _ g.hom _ _))
    (fun f ↦ by ext Y; exact derivedComparison_naturality_left R f.hom _)

attribute [local instance] canonicalTensorLifting derivedBifunctorLifting

/-! ### The comparison -/

/-- The derived bifunctor `CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried tensor
product is isomorphic to the canonical derived tensor product, as bifunctors on `D(R)`. -/
def derivedBifunctorCanonicalTensorIso :
    KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R)) ≅
      (canonicalDerivedTensorProduct R).tensor :=
  Localization.lift₂NatIso
    (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
    (kFlatTensorSource R) (kFlatTensorSource R)
    (KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R)))
    (canonicalDerivedTensorProduct R).tensor (Iso.refl _)

/-- On the images of K-flat complexes `K` and `L`, the component of
`CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso` is the one-sided K-flat
comparison of `derivedBifunctor` followed by the inverse of the two-sided K-flat comparison of
the canonical derived tensor product. -/
theorem derivedBifunctorCanonicalTensorIso_hom_app_app
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L) :
    ((derivedBifunctorCanonicalTensorIso R).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (KFlatBifunctor.comparisonRight (curriedTensor (ModuleCat.{u} R)) K L hL).hom ≫
        ((canonicalDerivedTensorProduct R).comparison K L hK hL).inv := by
  refine (Localization.lift₂NatTrans_app_app
    (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQ (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
    (KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (ModuleCat.{u} R)))
    (kFlatTensorSource R) (kFlatTensorSource R)
    (KFlatBifunctor.derivedBifunctor (curriedTensor (ModuleCat.{u} R)))
    (canonicalDerivedTensorProduct R).tensor (Iso.refl _).hom
    (⟨K, hK⟩ : (KFlatBifunctor.kFlatComplexes
      (curriedTensor (ModuleCat.{u} R))).FullSubcategory)
    (⟨L, hL⟩ : (KFlatBifunctor.kFlatComplexes
      (curriedTensor (ModuleCat.{u} R))).FullSubcategory)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- The canonical derived tensor product and the derived bifunctor
`CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried tensor product are isomorphic at
every pair of objects of `D(R)`. -/
theorem nonempty_canonicalTensorObj_iso_derivedBifunctorObj
    (Z₁ Z₂ : DerivedCategory (ModuleCat.{u} R)) :
    Nonempty ((((canonicalDerivedTensorProduct R).tensor).obj Z₁).obj Z₂ ≅
      ((KFlatBifunctor.derivedBifunctor
        (curriedTensor (ModuleCat.{u} R))).obj Z₁).obj Z₂) :=
  ⟨(((derivedBifunctorCanonicalTensorIso R).app Z₁).app Z₂).symm⟩

end

section Monoidal

-- `DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory` is stated for the
-- standard model of `D(R)`.
attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- For the symmetric monoidal structure
`DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory` on `D(R)`, the tensor
product `Z₁ ⊗ Z₂` is isomorphic to `CochainComplex.KFlatBifunctor.derivedBifunctor` of the curried
tensor product at `(Z₁, Z₂)`. -/
def monoidalTensorObjIsoDerivedBifunctorObj
    (Z₁ Z₂ : DerivedCategory (ModuleCat.{u} R)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    Z₁ ⊗ Z₂ ≅ ((KFlatBifunctor.derivedBifunctor
      (curriedTensor (ModuleCat.{u} R))).obj Z₁).obj Z₂ :=
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    R).choose_spec.choose_spec.choose
  ((e.app Z₁).app Z₂) ≪≫ (nonempty_canonicalTensorObj_iso_derivedBifunctorObj R Z₁ Z₂).some

end Monoidal

end CochainComplex.DerivedTensor

end
