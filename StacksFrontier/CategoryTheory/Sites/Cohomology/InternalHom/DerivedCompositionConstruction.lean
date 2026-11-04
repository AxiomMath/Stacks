module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluation
import StacksCore.Tactic.StacksAttribute

/-! # The composition morphism of derived internal Hom on a ringed site

Let `(C, O)` be a ringed site. This file assembles the data Stacks 0A98 records about the
composition morphism of derived internal Homs

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`,

whose construction and functoriality are
`StacksDraft.Ch21.Sec34.DerivedCompositionOnASite`: the morphism itself, its computation on a
K-flat resolution of the second internal Hom complex, and its three functorialities — covariant
in the target, contravariant in the source, and dinatural in the intermediate object.

The only piece not already in `DerivedCompositionOnASite` is the K-flat computation. It is the
statement that, after replacing the second tensor factor `RSheafHom(K, L)` by the class of a
K-flat complex `H` mapping to `SheafHom(K, L)`, derived composition becomes the class of the
composition morphism of internal Hom complexes of Stacks 0A91. No quasi-isomorphism hypothesis
on that map is needed: the identity holds for *every* morphism `H ⟶ SheafHom(K, L)`, because
the canonical map `toTensor` of Stacks 0FPH out of which derived composition is built is
natural in both factors without any hypothesis, and the K-flatness of `H` enters only to make
the source comparison of Stacks 0A97 an isomorphism.

## Main definitions

* `AlgebraicGeometry.RingedSite.DerivedSheafHomComposition`: the data recorded by Stacks 0A98.
* `AlgebraicGeometry.RingedSite.derivedSheafHomCompositionConstruction`: **Stacks 0A98**.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomComposition_kFlatModel`: the K-flat computation.

## Implementation notes

The four lemmas `derivedTensorMap_id_left`, `derivedTensorMap_id_right`,
`derivedSheafHomMap_id_left` and `derivedSheafHomMap_id_right` record that the two-variable
induced maps of `StacksDraft.Ch21.Sec34.DerivedCompositionOnASite` specialise, at an identity in
one variable, to the one-variable maps of the underlying functors. They are what lets the fields
below be stated in the one-variable form, which is the form in which Stacks 0A98 asks for them,
while the proofs use the two-variable lemmas.

The `comparison` field is stated without the isomorphism
`RSheafHom(L, M) ⟶ SheafHom(L, M)` prefixed to both sides, which is how Stacks 0A98 records it;
the prefixed form follows by composing on the left and is strictly weaker.

## References

* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section HomSpecialisations

variable
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (Hd : DerivedInternalHom.{u, d} X)
  {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- At the identity in the source, the two-variable induced map on a derived internal Hom is the
map induced by the target alone. -/
lemma derivedSheafHomMap_id_left
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b : B ⟶ B') :
    derivedSheafHomMap X Hd (𝟙 A) b = (Hd.hom.obj (op A)).map b := by
  simp [derivedSheafHomMap]

/-- At the identity in the target, the two-variable induced map on a derived internal Hom is the
map induced by the source alone. -/
lemma derivedSheafHomMap_id_right (a : A' ⟶ A)
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomMap X Hd a (𝟙 B) = (Hd.hom.map a.op).app B := by
  simp [derivedSheafHomMap]

end HomSpecialisations

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (Hd : DerivedInternalHom.{u, d} X)

section TensorSpecialisations

variable
  {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- At the identity in the left tensor factor, the two-variable induced map on a derived tensor
product is the map induced by the right factor alone. -/
lemma derivedTensorMap_id_left
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b : B ⟶ B') :
    derivedTensorMap X T (𝟙 A) b = (T.tensor.obj A).map b := by
  simp [derivedTensorMap]

/-- At the identity in the right tensor factor, the two-variable induced map on a derived tensor
product is the map induced by the left factor alone. -/
lemma derivedTensorMap_id_right (a : A ⟶ A')
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorMap X T a (𝟙 B) = (T.tensor.map a).app B := by
  simp [derivedTensorMap]

end TensorSpecialisations

/-- **Derived composition on a K-flat model of the second internal Hom complex.** For complexes
`K`, `J`, `I` with `J` and `I` K-injective, a K-flat complex `H` and *any* morphism
`f : H ⟶ SheafHom(K, J)`, derived composition read on `H` through the source comparison of
Stacks 0A97 is the class of the composition morphism of internal Hom complexes of Stacks
0A91. -/
theorem derivedSheafHomComposition_kFlatModel
    (K J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective]
    (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (f : H ⟶ (sheafHomComplex X K J).obj) :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
            (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map f ≫ (Hd.homComparison K J).inv) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) ≫
        (Hd.homComparison K I).hom =
      (derivedEvaluationSourceComparison X T Hd H J I hH).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        DerivedCategory.Q.map (compositionMap X K J I) := by
  have hkey : DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 (sheafHomComplex X J I).obj) f
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map
          ((tensorTotalIsoTensorComplex X (sheafHomComplex X J I).obj
            (sheafHomComplex X K J).obj).inv ≫ compositionMap X K J I) =
      DerivedCategory.Q.map
          (tensorTotalIsoTensorComplex X (sheafHomComplex X J I).obj H).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        DerivedCategory.Q.map (compositionMap X K J I) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (mapBifunctorMap_comp_tensorTotalIso_inv X (𝟙 (sheafHomComplex X J I).obj) f
        (compositionMap X K J I))
  have hnat := T.toTensor_naturality (𝟙 (sheafHomComplex X J I).obj) f
  rw [CategoryTheory.Functor.map_id] at hnat
  have hA : derivedTensorMap X T (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
            (DerivedCategory.Q.obj I)))
          (DerivedCategory.Q.map f ≫ (Hd.homComparison K J).inv) ≫
        derivedTensorMap X T (Hd.homComparison J I).hom (Hd.homComparison K J).hom =
      derivedTensorMap X T (Hd.homComparison J I).hom
          (𝟙 (DerivedCategory.Q.obj H)) ≫
        derivedTensorMap X T
          (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X J I).obj))
          (DerivedCategory.Q.map f) := by
    rw [derivedTensorMap_comp, derivedTensorMap_comp]
    simp
  have hB : derivedTensorMap X T
            (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X J I).obj))
            (DerivedCategory.Q.map f) ≫
          homComplexDerivedComposition X T K J I =
        T.toTensor (sheafHomComplex X J I).obj H ≫
          DerivedCategory.Q.map
              (tensorTotalIsoTensorComplex X (sheafHomComplex X J I).obj H).inv ≫
            DerivedCategory.Q.map
              (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
            DerivedCategory.Q.map (compositionMap X K J I) := by
    dsimp only [homComplexDerivedComposition, derivedTensorMap]
    simp only [Category.assoc]
    -- The reassociated naturality of `toTensor` leaves the left-hand side bracketed as
    -- `(a ≫ b) ≫ c`, and the two spellings of the total tensor product agree only
    -- definitionally, so `hkey` is applied in term position rather than by rewriting.
    rw [reassoc_of% hnat]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun z ↦ T.toTensor (sheafHomComplex X J I).obj H ≫ z) hkey)
  rw [← derivedTensorMap_id_left, derivedSheafHomComposition_eq_onKInjectiveModel,
    derivedEvaluationSourceComparison_hom]
  dsimp only [derivedCompositionOnKInjectiveModel]
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Data recorded by Stacks 0A98: the composition morphism of derived internal Homs, its value
on a K-flat model of the second internal Hom complex, and its three functorialities. -/
structure DerivedSheafHomComposition where
  /-- The canonical composition morphism
  `RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`. -/
  comp (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj ((Hd.hom.obj (op L)).obj M)).obj ((Hd.hom.obj (op K)).obj L) ⟶
      (Hd.hom.obj (op K)).obj M
  /-- On a K-flat model of the second internal Hom complex, derived composition is induced by
  the composition morphism of internal Hom complexes. -/
  comparison
      (K J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      [J.IsKInjective] [I.IsKInjective]
      (hH : Stacks.SheafOfModules.IsKFlat X.O H)
      (f : H ⟶ (sheafHomComplex X K J).obj) :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
            (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map f ≫ (Hd.homComparison K J).inv) ≫
        comp (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj J)
          (DerivedCategory.Q.obj I) ≫
        (Hd.homComparison K I).hom =
      (derivedEvaluationSourceComparison X T Hd H J I hH).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        DerivedCategory.Q.map (compositionMap X K J I)
  /-- Contravariant naturality in the source object. -/
  natural_source
      {K K' L M :
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
      (k : K' ⟶ K) :
    comp K L M ≫ (Hd.hom.map k.op).app M =
      (T.tensor.obj ((Hd.hom.obj (op L)).obj M)).map ((Hd.hom.map k.op).app L) ≫
        comp K' L M
  /-- Covariant naturality in the target object. -/
  natural_target
      {K L M M' :
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
      (m : M ⟶ M') :
    comp K L M ≫ (Hd.hom.obj (op K)).map m =
      (T.tensor.map ((Hd.hom.obj (op L)).map m)).app ((Hd.hom.obj (op K)).obj L) ≫
        comp K L M'
  /-- Dinaturality in the intermediate object: a morphism may be absorbed either covariantly
  into the right-hand tensor factor or contravariantly into the left-hand one. -/
  dinatural_middle
      {K L L' M :
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
      (l : L ⟶ L') :
    (T.tensor.obj ((Hd.hom.obj (op L')).obj M)).map ((Hd.hom.obj (op K)).map l) ≫
        comp K L' M =
      (T.tensor.map ((Hd.hom.map l.op).app M)).app ((Hd.hom.obj (op K)).obj L) ≫
        comp K L M

/-- **Stacks 0A98: the composition morphism of derived internal Homs.** For arbitrary objects
`K`, `L`, `M` of `D(Mod(O))` there is a canonical morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`,

which on a K-flat model of the second internal Hom complex is the composition morphism of
internal Hom complexes of Stacks 0A91, and which is contravariant in the source, covariant in
the target and dinatural in the intermediate object. -/
@[stacks 0A98]
def derivedSheafHomCompositionConstruction : DerivedSheafHomComposition X T Hd where
  comp := derivedSheafHomComposition X T Hd
  comparison := fun K J I H _ _ hH f =>
    derivedSheafHomComposition_kFlatModel X T Hd K J I H hH f
  natural_source := fun {_ _ L M} k => by
    rw [← derivedSheafHomMap_id_right, ← derivedSheafHomMap_id_right,
      ← derivedTensorMap_id_left]
    exact derivedSheafHomComposition_natural_source X T Hd k L M
  natural_target := fun {K L _ _} m => by
    rw [← derivedSheafHomMap_id_left, ← derivedSheafHomMap_id_left,
      ← derivedTensorMap_id_right]
    exact derivedSheafHomComposition_natural_target X T Hd K L m
  dinatural_middle := fun {K _ _ M} l => by
    rw [← derivedSheafHomMap_id_left, ← derivedTensorMap_id_left,
      ← derivedSheafHomMap_id_right, ← derivedTensorMap_id_right]
    exact derivedSheafHomComposition_dinatural_middle X T Hd K l M

end AlgebraicGeometry.RingedSite

end
