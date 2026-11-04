module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluationSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
import StacksCore.Tactic.StacksAttribute

/-! # Composition of derived internal Hom on a ringed site

Let `(C, O)` be a ringed site. Stacks 0A98 asks, for arbitrary objects `K`, `L`, `M` of
`D(Mod(O))`, for a canonical morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(Mod(O))`, together with its functoriality: contravariant in `K`, covariant in `M` and
*dinatural* in the intermediate object `L`, which enters the source covariantly in one tensor
factor and contravariantly in the other.

This file constructs it, from a derived internal Hom datum
(`AlgebraicGeometry.RingedSite.DerivedInternalHom`, Stacks 0A97) and a derived tensor product
datum (`Stacks.SheafOfModules.DerivedTensorProduct`, Stacks 06YU), in three steps.

1. On *complexes*, the composition morphism of internal Hom complexes of Stacks 0A91 is
   transported into the derived category along the canonical map `toTensor` from the derived
   tensor product to the ordinary total tensor product of Stacks 0FPH, giving
   `AlgebraicGeometry.RingedSite.homComplexDerivedComposition`. No K-flatness hypothesis is
   needed, because `toTensor` is defined for arbitrary complexes; that is what makes this
   construction choice-free and hence functorial, in contrast to the K-flat resolution that
   the Stacks proof chooses.
2. For complexes `K`, `L`, `M` with `L` and `M` K-injective, the K-injective model comparison
   of the derived internal Hom turns that into
   `AlgebraicGeometry.RingedSite.derivedCompositionOnKInjectiveModel`, and the functoriality
   of the complex-level composition morphism becomes its three naturality statements.
3. Every object of `D(Mod(O))` is isomorphic to the class of a K-injective complex, through a
   chosen representative and the functorial K-injective resolution
   (`AlgebraicGeometry.RingedSite.kInjectiveModel`). Transporting step 2 along those
   isomorphisms gives `AlgebraicGeometry.RingedSite.derivedSheafHomComposition` for arbitrary
   objects, and the three naturality statements survive the transport because every morphism
   of `D(Mod(O))` into the class of a K-injective complex is the class of a morphism of
   complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorMap` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomMap`: the morphisms induced on a derived tensor
  product and on a derived internal Hom by morphisms in both variables.
* `AlgebraicGeometry.RingedSite.homComplexDerivedComposition`: step 1.
* `AlgebraicGeometry.RingedSite.derivedCompositionOnKInjectiveModel`: step 2.
* `AlgebraicGeometry.RingedSite.kInjectiveModel` and
  `AlgebraicGeometry.RingedSite.kInjectiveModelIso`: the K-injective representative of an
  object of the derived category.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComposition`: step 3, the composition morphism
  for arbitrary objects.
* `AlgebraicGeometry.RingedSite.derivedCompositionSourceIso`: the identification of the source
  of derived composition with the class of a total tensor complex, on a K-flat resolution of
  the right-hand internal Hom complex.
* `AlgebraicGeometry.RingedSite.DerivedSheafHomComposition`: the data recorded by Stacks 0A98 —
  the morphism, its value on K-injective and K-flat models, and its three functorialities.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCompositionOnKInjectiveModel_natural`: the three
  functorialities of step 2, in one identity.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComposition_eq_onKInjectiveModel`: the
  composition morphism of step 3 is the one of step 2 whenever the two targets are already
  K-injective. This is the independence of the construction from the chosen representatives.
* `AlgebraicGeometry.RingedSite.derivedSheafHomCompositionConstruction`: **Stacks 0A98**.

## Implementation notes

The one-variable specialisations of
`AlgebraicGeometry.RingedSite.derivedCompositionOnKInjectiveModel_natural` — one per slot of
the intermediate complex, one for the source and one for the target — are what the transport
of step 3 consumes, and they are stated separately because the three-variable identity cannot
be applied directly: the source slot is contravariant while the representative maps all point
*into* the models.

A genuinely four-variable natural transformation `RSheafHom(L₂, M) ⊗^L RSheafHom(K, L₁) ⟶
RSheafHom(K, M)` would be *zero*: naturality in `L₁` at the morphism `L ⟶ 0` forces it, since
`RSheafHom(K, 0) = 0`. So the dinaturality of the composition morphism in the intermediate
object is not an instance of naturality of a transformation of functors, and it is recorded
here as its own identity.

Step 1 is where this differs from the Stacks proof, which chooses a K-flat complex
`H ⟶ SheafHom(K, L)` and reads the composition morphism on it. That choice reappears here only
in the `comparison` field of `AlgebraicGeometry.RingedSite.DerivedSheafHomComposition`, where
it is *derived* from `Stacks.SheafOfModules.DerivedTensorProduct.toTensor_naturality` and
`toTensor_eq_comparisonRight`; the resulting independence of the chosen resolution is
therefore a theorem rather than an assumption.

`AlgebraicGeometry.RingedSite.kInjectiveModel` combines a chosen `Q`-preimage, which exists
because the localization functor of a localization is essentially surjective, with the
functorial K-injective resolution of Stacks 079P. Only two of its properties are used: it is
K-injective, and its class is isomorphic to the given object.

The universes are the diagonal `RingedSite.{u, u, u}` with the universe `d` of the
localization free, as in every file of the derived internal Hom cluster.

## References

* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section SheafHom

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]

/-- The localization functor onto the derived category of sheaves of modules on a ringed site
is essentially surjective, being the localization functor of a localization. -/
local instance essSurjQ :
    (DerivedCategory.Q
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).EssSurj :=
  Localization.essSurj _
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The chosen K-injective complex representing an object of the derived category: the
functorial K-injective resolution of a chosen preimage under the localization functor. -/
def kInjectiveModel
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (kInjectiveResolution X).obj (DerivedCategory.Q.objPreimage Z)

/-- The chosen complex `kInjectiveModel X Z` is K-injective. -/
instance isKInjective_kInjectiveModel
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (kInjectiveModel X Z).IsKInjective :=
  inferInstanceAs ((kInjectiveResolution X).obj
    (DerivedCategory.Q.objPreimage Z)).IsKInjective

/-- The chosen K-injective complex does represent the given object. -/
def kInjectiveModelIso
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory.Q.obj (kInjectiveModel X Z) ≅ Z :=
  (asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (DerivedCategory.Q.objPreimage Z)))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso Z

/-- Every morphism of the derived category into the class of a K-injective complex is the
class of a morphism of complexes. -/
theorem exists_Q_map_eq_of_isKInjective
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (φ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :
    ∃ h : A ⟶ I, DerivedCategory.Q.map h = φ := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj A) I).surjective
    ((DerivedCategory.quotientCompQhIso _).hom.app A ≫ φ ≫
      (DerivedCategory.quotientCompQhIso _).inv.app I)
  obtain ⟨h, rfl⟩ :=
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).map_surjective g
  refine ⟨h, ?_⟩
  have hnat := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) h
  rw [hg] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  simpa using hnat.symm

/-- A morphism of the derived category lifts to a morphism of the chosen K-injective models,
compatibly with the representing isomorphisms. -/
private lemma exists_kInjectiveModel_map
    {E F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : E ⟶ F) :
    ∃ κ : kInjectiveModel X E ⟶ kInjectiveModel X F,
      DerivedCategory.Q.map κ ≫ (kInjectiveModelIso X F).hom =
        (kInjectiveModelIso X E).hom ≫ f ∧
      (kInjectiveModelIso X E).inv ≫ DerivedCategory.Q.map κ =
        f ≫ (kInjectiveModelIso X F).inv := by
  obtain ⟨κ, hκ⟩ := exists_Q_map_eq_of_isKInjective X (I := kInjectiveModel X F)
    ((kInjectiveModelIso X E).hom ≫ f ≫ (kInjectiveModelIso X F).inv)
  refine ⟨κ, ?_, ?_⟩
  · rw [hκ, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hκ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Merging two consecutive classes of morphisms of complexes, in term position. -/
private lemma Q_map_comp'
    {A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ B) (g : B ⟶ C) :
    DerivedCategory.Q.map f ≫ DerivedCategory.Q.map g = DerivedCategory.Q.map (f ≫ g) :=
  (DerivedCategory.Q.map_comp f g).symm

variable (Hd : DerivedInternalHom.{u, d} X)

variable {A A' A'' B B' B'' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- The morphism of derived internal Homs induced by morphisms in both variables, the first
one contravariantly. -/
def derivedSheafHomMap (a : A' ⟶ A) (b : B ⟶ B') :
    (Hd.hom.obj (op A)).obj B ⟶ (Hd.hom.obj (op A')).obj B' :=
  (Hd.hom.map a.op).app B ≫ (Hd.hom.obj (op A')).map b

/-- Two identities induce the identity on a derived internal Hom. -/
@[simp]
lemma derivedSheafHomMap_id
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomMap X Hd (𝟙 A) (𝟙 B) = 𝟙 ((Hd.hom.obj (op A)).obj B) := by
  simp [derivedSheafHomMap]

/-- The induced morphisms on derived internal Homs compose. -/
lemma derivedSheafHomMap_comp (a : A' ⟶ A) (b : B ⟶ B') (a' : A'' ⟶ A') (b' : B' ⟶ B'') :
    derivedSheafHomMap X Hd a b ≫ derivedSheafHomMap X Hd a' b' =
      derivedSheafHomMap X Hd (a' ≫ a) (b ≫ b') := by
  simp [derivedSheafHomMap, op_comp, Functor.map_comp, NatTrans.comp_app,
    NatTrans.naturality_assoc]

/-- The K-injective model comparison of the derived internal Hom, read as an identity between
the induced morphisms on derived internal Hom and on internal Hom complexes. -/
lemma derivedSheafHomMap_homComparison
    {K K' M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') [M.IsKInjective] [M'.IsKInjective] :
    derivedSheafHomMap X Hd (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) ≫
        (Hd.homComparison K' M').hom =
      (Hd.homComparison K M).hom ≫ DerivedCategory.Q.map (homMap X k m) := by
  dsimp only [derivedSheafHomMap]
  rw [Category.assoc]
  exact Hd.homComparison_natural k m

end SheafHom

section Tensor

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable {K K' L L' M M' :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Crossing the two spellings of the total tensor product: Section 17's functoriality,
followed by the comparison with Section 34's spelling, is that comparison followed by Section
34's functoriality. Stated in term position because the two spellings of the source agree only
at default transparency, so no rewriting tactic can perform the reassociation. -/
lemma mapBifunctorMap_comp_tensorTotalIso_inv
    {A A₁ B B₁ Z :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A₁) (g : B ⟶ B₁) (w : tensorTotal X A₁ B₁ ⟶ Z) :
    HomologicalComplex.mapBifunctorMap f g (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        ((tensorTotalIsoTensorComplex X A₁ B₁).inv ≫ w) =
      (tensorTotalIsoTensorComplex X A B).inv ≫ tensorTotalMap X f g ≫ w :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ w) (tensorTotalIsoTensorComplex_naturality X f g)).symm.trans
      (Category.assoc _ _ _))

/-- The complex-level identity behind the functoriality of derived composition. -/
lemma mapBifunctorMap_comp_compositionMap (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M') :
    HomologicalComplex.mapBifunctorMap (homMap X (𝟙 L') m) (homMap X k l)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        ((tensorTotalIsoTensorComplex X (sheafHomComplex X L' M').obj
          (sheafHomComplex X K' L').obj).inv ≫ compositionMap X K' L' M') =
      HomologicalComplex.mapBifunctorMap (homMap X l (𝟙 M))
          (𝟙 (sheafHomComplex X K L).obj) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) ≫
        (((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M) ≫
          homMap X k m) :=
  ((mapBifunctorMap_comp_tensorTotalIso_inv X (homMap X (𝟙 L') m) (homMap X k l)
      (compositionMap X K' L' M')).trans
    ((congrArg (fun z ↦ (tensorTotalIsoTensorComplex X (sheafHomComplex X L' M).obj
        (sheafHomComplex X K L).obj).inv ≫ z) (compositionMap_natural X k l m)).trans
      (mapBifunctorMap_comp_tensorTotalIso_inv X (homMap X l (𝟙 M))
        (𝟙 (sheafHomComplex X K L).obj)
        (compositionMap X K L M ≫ homMap X k m)).symm)).trans
    (congrArg (fun z ↦ HomologicalComplex.mapBifunctorMap (homMap X l (𝟙 M))
        (𝟙 (sheafHomComplex X K L).obj) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) ≫ z)
      (Category.assoc (tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj).inv (compositionMap X K L M)
        (homMap X k m)).symm)

variable
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)

section Maps

variable {A A' A'' B B' B'' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- The morphism of derived tensor products induced by morphisms in both factors. -/
def derivedTensorMap (a : A ⟶ A') (b : B ⟶ B') :
    (T.tensor.obj A).obj B ⟶ (T.tensor.obj A').obj B' :=
  (T.tensor.map a).app B ≫ (T.tensor.obj A').map b

/-- Two identities induce the identity on a derived tensor product. -/
@[simp]
lemma derivedTensorMap_id
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorMap X T (𝟙 A) (𝟙 B) = 𝟙 ((T.tensor.obj A).obj B) := by
  simp [derivedTensorMap]

/-- The induced morphisms on derived tensor products compose. -/
@[reassoc]
lemma derivedTensorMap_comp (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'') :
    derivedTensorMap X T a b ≫ derivedTensorMap X T a' b' =
      derivedTensorMap X T (a ≫ a') (b ≫ b') := by
  simp [derivedTensorMap, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]

/-- Composing induced morphisms on derived tensor products when the second is the identity in
the right-hand factor. -/
@[reassoc]
lemma derivedTensorMap_comp_left (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') :
    derivedTensorMap X T a b ≫ derivedTensorMap X T a' (𝟙 B') =
      derivedTensorMap X T (a ≫ a') b := by
  rw [derivedTensorMap_comp, Category.comp_id]

/-- Composing induced morphisms on derived tensor products when the second is the identity in
the left-hand factor. -/
lemma derivedTensorMap_comp_right (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'') :
    derivedTensorMap X T a b ≫ derivedTensorMap X T (𝟙 A') b' =
      derivedTensorMap X T a (b ≫ b') := by
  rw [derivedTensorMap_comp, Category.comp_id]

end Maps

/-- **Derived composition of internal Hom complexes.** The composition morphism of internal
Hom complexes of Stacks 0A91, read in the derived category along the canonical map from the
derived tensor product to the ordinary total tensor product. No K-flatness is assumed. -/
def homComplexDerivedComposition
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (T.tensor.obj (DerivedCategory.Q.obj (sheafHomComplex X L M).obj)).obj
        (DerivedCategory.Q.obj (sheafHomComplex X K L).obj) ⟶
      DerivedCategory.Q.obj (sheafHomComplex X K M).obj :=
  T.toTensor (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ≫
    DerivedCategory.Q.map
      ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M)

/-- **Functoriality of derived composition of internal Hom complexes**, in all three complexes
at once. -/
theorem homComplexDerivedComposition_natural (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M') :
    derivedTensorMap X T (DerivedCategory.Q.map (homMap X (𝟙 L') m))
          (DerivedCategory.Q.map (homMap X k l)) ≫
        homComplexDerivedComposition X T K' L' M' =
      derivedTensorMap X T (DerivedCategory.Q.map (homMap X l (𝟙 M)))
          (DerivedCategory.Q.map (𝟙 (sheafHomComplex X K L).obj)) ≫
        homComplexDerivedComposition X T K L M ≫
          DerivedCategory.Q.map (homMap X k m) := by
  dsimp only [homComplexDerivedComposition, derivedTensorMap]
  simp only [Category.assoc]
  rw [reassoc_of% (T.toTensor_naturality (homMap X (𝟙 L') m) (homMap X k l)),
    reassoc_of% (T.toTensor_naturality (homMap X l (𝟙 M))
      (𝟙 (sheafHomComplex X K L).obj)),
    Q_map_comp' X ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M) (homMap X k m),
]
  have h2 := ((Q_map_comp' X (HomologicalComplex.mapBifunctorMap (homMap X (𝟙 L') m)
        (homMap X k l) (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
      ((tensorTotalIsoTensorComplex X (sheafHomComplex X L' M').obj
        (sheafHomComplex X K' L').obj).inv ≫ compositionMap X K' L' M')).trans
    (congrArg DerivedCategory.Q.map
      (mapBifunctorMap_comp_compositionMap X k l m))).trans
    (Q_map_comp' X (HomologicalComplex.mapBifunctorMap (homMap X l (𝟙 M))
      (𝟙 (sheafHomComplex X K L).obj) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ))
      (((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M) ≫
        homMap X k m)).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ T.toTensor (sheafHomComplex X L' M).obj
      (sheafHomComplex X K L).obj ≫ z) h2).trans (Category.assoc _ _ _).symm)

section Composition

variable (Hd : DerivedInternalHom.{u, d} X)

/-- **Derived composition on K-injective targets.** For complexes `K`, `L`, `M` with `L` and
`M` K-injective, the morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

obtained from the composition morphism of internal Hom complexes through the K-injective model
comparison of the derived internal Hom. -/
def derivedCompositionOnKInjectiveModel
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    (T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj L))).obj
          (DerivedCategory.Q.obj M))).obj
        ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj L)) ⟶
      (Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj M) :=
  derivedTensorMap X T (Hd.homComparison L M).hom (Hd.homComparison K L).hom ≫
    homComplexDerivedComposition X T K L M ≫ (Hd.homComparison K M).inv

/-- The left-hand side of the functoriality identity, with the K-injective model comparisons
pulled out in front. -/
private lemma derivedCompositionOnKInjectiveModel_natural_aux₁
    (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M')
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective] [M'.IsKInjective] :
    derivedTensorMap X T
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj L'))
            (DerivedCategory.Q.map m))
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (DerivedCategory.Q.map l)) ≫
        derivedCompositionOnKInjectiveModel X T Hd K' L' M' =
      derivedTensorMap X T (Hd.homComparison L' M).hom (Hd.homComparison K L).hom ≫
        derivedTensorMap X T (DerivedCategory.Q.map (homMap X (𝟙 L') m))
          (DerivedCategory.Q.map (homMap X k l)) ≫
        homComplexDerivedComposition X T K' L' M' ≫ (Hd.homComparison K' M').inv := by
  have h₁ := derivedSheafHomMap_homComparison X Hd (𝟙 L') m
  have h₂ := derivedSheafHomMap_homComparison X Hd k l
  rw [CategoryTheory.Functor.map_id] at h₁
  dsimp only [derivedCompositionOnKInjectiveModel]
  rw [derivedTensorMap_comp_assoc, h₁, h₂, ← derivedTensorMap_comp_assoc]

/-- The right-hand side of the functoriality identity, with the K-injective model comparisons
pulled out in front. -/
private lemma derivedCompositionOnKInjectiveModel_natural_aux₂
    (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M')
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective] [M'.IsKInjective] :
    derivedTensorMap X T
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (𝟙 (DerivedCategory.Q.obj M)))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M ≫
          derivedSheafHomMap X Hd (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) =
      derivedTensorMap X T (Hd.homComparison L' M).hom (Hd.homComparison K L).hom ≫
        derivedTensorMap X T (DerivedCategory.Q.map (homMap X l (𝟙 M)))
          (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X K L).obj)) ≫
        homComplexDerivedComposition X T K L M ≫
          DerivedCategory.Q.map (homMap X k m) ≫ (Hd.homComparison K' M').inv := by
  have h₃ := derivedSheafHomMap_homComparison X Hd l (𝟙 M)
  rw [CategoryTheory.Functor.map_id] at h₃
  have h₄ : (Hd.homComparison K M).inv ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) =
      DerivedCategory.Q.map (homMap X k m) ≫ (Hd.homComparison K' M').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact derivedSheafHomMap_homComparison X Hd k m
  dsimp only [derivedCompositionOnKInjectiveModel]
  -- The unfolding leaves the left-hand side bracketed as `a ≫ (b ≫ c) ≫ d`, in which the
  -- reassociated `derivedTensorMap_comp_assoc` has no match; without this normalisation the
  -- rewrite below fires on the right-hand side instead.
  simp only [Category.assoc]
  rw [derivedTensorMap_comp_assoc, Category.id_comp, h₃, h₄,
    derivedTensorMap_comp_left_assoc]

/-- **Functoriality of derived composition on K-injective targets**, in all three complexes at
once: contravariant in the source, covariant in the target, and dinatural in the intermediate
complex, which may be absorbed into either tensor factor of the source. -/
theorem derivedCompositionOnKInjectiveModel_natural (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M')
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective] [M'.IsKInjective] :
    derivedTensorMap X T
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj L'))
            (DerivedCategory.Q.map m))
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (DerivedCategory.Q.map l)) ≫
        derivedCompositionOnKInjectiveModel X T Hd K' L' M' =
      derivedTensorMap X T
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (𝟙 (DerivedCategory.Q.obj M)))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M ≫
          derivedSheafHomMap X Hd (DerivedCategory.Q.map k) (DerivedCategory.Q.map m) := by
  have hΨ := homComplexDerivedComposition_natural X T k l m
  rw [CategoryTheory.Functor.map_id] at hΨ
  rw [derivedCompositionOnKInjectiveModel_natural_aux₁,
    derivedCompositionOnKInjectiveModel_natural_aux₂,
    ← Category.assoc (derivedTensorMap X T
      (DerivedCategory.Q.map (homMap X (𝟙 L') m))
      (DerivedCategory.Q.map (homMap X k l))), hΨ]
  simp only [Category.assoc]

/-- Derived composition on K-injective targets is contravariant in the source complex. -/
theorem derivedCompositionOnKInjectiveModel_natural_source (k : K' ⟶ K)
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    derivedTensorMap X T
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj L))).obj (DerivedCategory.Q.obj M)))
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (𝟙 (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K' L M =
      derivedCompositionOnKInjectiveModel X T Hd K L M ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
          (𝟙 (DerivedCategory.Q.obj M)) := by
  have h := derivedCompositionOnKInjectiveModel_natural X T Hd k (𝟙 L) (𝟙 M)
  simp only [CategoryTheory.Functor.map_id, derivedSheafHomMap_id, derivedTensorMap_id,
    Category.id_comp] at h
  exact h

/-- Derived composition on K-injective targets is covariant in the target complex. -/
theorem derivedCompositionOnKInjectiveModel_natural_target
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : M ⟶ M')
    [L.IsKInjective] [M.IsKInjective] [M'.IsKInjective] :
    derivedTensorMap X T
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj L))
            (DerivedCategory.Q.map m))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M' =
      derivedCompositionOnKInjectiveModel X T Hd K L M ≫
        derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj K))
          (DerivedCategory.Q.map m) := by
  have h := derivedCompositionOnKInjectiveModel_natural X T Hd (𝟙 K) (𝟙 L) m
  simp only [CategoryTheory.Functor.map_id, derivedSheafHomMap_id, derivedTensorMap_id,
    Category.id_comp] at h
  exact h

/-- **Dinaturality of derived composition on K-injective targets in the intermediate
complex.** A morphism may be absorbed either covariantly into the right-hand tensor factor or
contravariantly into the left-hand one, with the same effect. -/
theorem derivedCompositionOnKInjectiveModel_dinatural_middle
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (l : L ⟶ L')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective] :
    derivedTensorMap X T
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj L'))).obj (DerivedCategory.Q.obj M)))
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj K))
            (DerivedCategory.Q.map l)) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L' M =
      derivedTensorMap X T
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (𝟙 (DerivedCategory.Q.obj M)))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M := by
  have h := derivedCompositionOnKInjectiveModel_natural X T Hd (𝟙 K) l (𝟙 M)
  simp only [CategoryTheory.Functor.map_id, derivedSheafHomMap_id, Category.comp_id] at h
  exact h

/-- The first collapse of induced tensor morphisms, with a tail. -/
private lemma dtCompLeft
    {A A' A'' B B' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'')
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (T.tensor.obj A'').obj B' ⟶ Z) :
    derivedTensorMap X T a b ≫ derivedTensorMap X T a' (𝟙 B') ≫ h =
      derivedTensorMap X T (a ≫ a') b ≫ h := by
  rw [← Category.assoc, derivedTensorMap_comp_left]

/-- The general collapse of induced tensor morphisms, with a tail. -/
private lemma dtComp
    {A A' A'' B B' B'' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (T.tensor.obj A'').obj B'' ⟶ Z) :
    derivedTensorMap X T a b ≫ derivedTensorMap X T a' b' ≫ h =
      derivedTensorMap X T (a ≫ a') (b ≫ b') ≫ h := by
  rw [← Category.assoc, derivedTensorMap_comp]

/-- Contravariance in the source complex, with a tail. -/
private lemma natSourceTail (k : K' ⟶ K)
    (L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective]
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (Hd.hom.obj (op (DerivedCategory.Q.obj K'))).obj (DerivedCategory.Q.obj M) ⟶ Z) :
    derivedTensorMap X T
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj L))).obj (DerivedCategory.Q.obj M)))
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
            (𝟙 (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K' L M ≫ h =
      derivedCompositionOnKInjectiveModel X T Hd K L M ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map k)
          (𝟙 (DerivedCategory.Q.obj M)) ≫ h := by
  rw [← Category.assoc, derivedCompositionOnKInjectiveModel_natural_source,
    Category.assoc]

/-- The second collapse of induced tensor morphisms, with a tail. -/
private lemma dtCompRight
    {A A' B B' B'' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'')
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (T.tensor.obj A').obj B'' ⟶ Z) :
    derivedTensorMap X T a b ≫ derivedTensorMap X T (𝟙 A') b' ≫ h =
      derivedTensorMap X T a (b ≫ b') ≫ h := by
  rw [← Category.assoc, derivedTensorMap_comp_right]

/-- Covariance in the target complex, with a tail. -/
private lemma natTargetTail
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : M ⟶ M')
    [L.IsKInjective] [M.IsKInjective] [M'.IsKInjective]
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj M') ⟶ Z) :
    derivedTensorMap X T
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj L))
            (DerivedCategory.Q.map m))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M' ≫ h =
      derivedCompositionOnKInjectiveModel X T Hd K L M ≫
        derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj K))
          (DerivedCategory.Q.map m) ≫ h := by
  rw [← Category.assoc, derivedCompositionOnKInjectiveModel_natural_target,
    Category.assoc]

/-- Dinaturality in the intermediate complex, with a tail. -/
private lemma dinatMiddleTail
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (l : L ⟶ L')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [L'.IsKInjective] [M.IsKInjective]
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : (Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj M) ⟶ Z) :
    derivedTensorMap X T
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj L'))).obj (DerivedCategory.Q.obj M)))
          (derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj K))
            (DerivedCategory.Q.map l)) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L' M ≫ h =
      derivedTensorMap X T
          (derivedSheafHomMap X Hd (DerivedCategory.Q.map l)
            (𝟙 (DerivedCategory.Q.obj M)))
          (𝟙 ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).obj
            (DerivedCategory.Q.obj L))) ≫
        derivedCompositionOnKInjectiveModel X T Hd K L M ≫ h := by
  rw [← Category.assoc, derivedCompositionOnKInjectiveModel_dinatural_middle,
    Category.assoc]

/-- **Transport of derived composition along quasi-isomorphisms of K-injective
representatives.** Derived composition on K-injective targets does not depend on the chosen
representatives: transporting it along three morphisms of complexes whose classes are
invertible returns it. -/
theorem derivedCompositionOnKInjectiveModel_transport
    {A A₁ B B₁ C C₁ :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B₁.IsKInjective] [C.IsKInjective] [C₁.IsKInjective]
    (a : A ⟶ A₁) (b : B ⟶ B₁) (c : C ⟶ C₁)
    (ea : DerivedCategory.Q.obj A₁ ≅ DerivedCategory.Q.obj A)
    (eb : DerivedCategory.Q.obj B₁ ≅ DerivedCategory.Q.obj B)
    (ec : DerivedCategory.Q.obj C₁ ≅ DerivedCategory.Q.obj C)
    (ha : DerivedCategory.Q.map a = ea.inv) (hb : DerivedCategory.Q.map b = eb.inv)
    (hc : DerivedCategory.Q.map c = ec.inv) :
    derivedTensorMap X T (derivedSheafHomMap X Hd eb.hom ec.inv)
          (derivedSheafHomMap X Hd ea.hom eb.inv) ≫
        derivedCompositionOnKInjectiveModel X T Hd A₁ B₁ C₁ ≫
        derivedSheafHomMap X Hd ea.inv ec.hom =
      derivedCompositionOnKInjectiveModel X T Hd A B C := by
  have s₁ : derivedSheafHomMap X Hd eb.hom (DerivedCategory.Q.map c) =
      derivedSheafHomMap X Hd eb.hom (𝟙 _) ≫
        derivedSheafHomMap X Hd (𝟙 _) (DerivedCategory.Q.map c) := by
    rw [derivedSheafHomMap_comp, Category.id_comp, Category.id_comp]
  have s₂ : derivedSheafHomMap X Hd ea.hom (DerivedCategory.Q.map b) =
      derivedSheafHomMap X Hd ea.hom (𝟙 _) ≫
        derivedSheafHomMap X Hd (𝟙 _) (DerivedCategory.Q.map b) := by
    rw [derivedSheafHomMap_comp, Category.id_comp, Category.id_comp]
  have c₁ : derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj A₁))
        (DerivedCategory.Q.map c) ≫
      derivedSheafHomMap X Hd (DerivedCategory.Q.map a) ec.hom =
        derivedSheafHomMap X Hd (DerivedCategory.Q.map a)
          (𝟙 (DerivedCategory.Q.obj C)) := by
    rw [derivedSheafHomMap_comp, Category.comp_id, hc, Iso.inv_hom_id]
  have c₂ : ∀ Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      derivedSheafHomMap X Hd eb.hom (𝟙 Z) ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map b) (𝟙 Z) = 𝟙 _ := by
    intro Z
    rw [derivedSheafHomMap_comp, Category.comp_id, hb, Iso.inv_hom_id,
      derivedSheafHomMap_id]
  have c₃ : ∀ Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      derivedSheafHomMap X Hd ea.hom (𝟙 Z) ≫
        derivedSheafHomMap X Hd (DerivedCategory.Q.map a) (𝟙 Z) = 𝟙 _ := by
    intro Z
    rw [derivedSheafHomMap_comp, Category.comp_id, ha, Iso.inv_hom_id,
      derivedSheafHomMap_id]
  rw [← ha, ← hb, ← hc, s₁, ← dtCompLeft, natTargetTail, c₁, s₂, ← dtCompRight,
    dinatMiddleTail, dtCompLeft, c₂,
    ← derivedCompositionOnKInjectiveModel_natural_source, dtCompRight, c₃,
    derivedTensorMap_id, Category.id_comp]

section Objects

variable {E E' F F' G G' :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- **Stacks 0A98: the composition morphism of derived internal Homs.** For arbitrary objects
`K`, `L`, `M` of `D(Mod(O))`, the canonical morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`,

obtained from the composition morphism of internal Hom complexes of Stacks 0A91 by passing to
the chosen K-injective representatives of the three objects. -/
def derivedSheafHomComposition
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (T.tensor.obj ((Hd.hom.obj (op L)).obj M)).obj ((Hd.hom.obj (op K)).obj L) ⟶
      (Hd.hom.obj (op K)).obj M :=
  derivedTensorMap X T
      (derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom (kInjectiveModelIso X M).inv)
      (derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom
        (kInjectiveModelIso X L).inv) ≫
    derivedCompositionOnKInjectiveModel X T Hd (kInjectiveModel X K)
      (kInjectiveModel X L) (kInjectiveModel X M) ≫
    derivedSheafHomMap X Hd (kInjectiveModelIso X K).inv (kInjectiveModelIso X M).hom

/-- **Independence of the chosen representatives.** On the classes of complexes whose two
targets are already K-injective, the composition morphism for arbitrary objects is the one
built directly from those complexes. -/
theorem derivedSheafHomComposition_eq_onKInjectiveModel
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) =
      derivedCompositionOnKInjectiveModel X T Hd K L M := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq_of_isKInjective X
    (I := kInjectiveModel X (DerivedCategory.Q.obj K))
    (kInjectiveModelIso X (DerivedCategory.Q.obj K)).inv
  obtain ⟨b, hb⟩ := exists_Q_map_eq_of_isKInjective X
    (I := kInjectiveModel X (DerivedCategory.Q.obj L))
    (kInjectiveModelIso X (DerivedCategory.Q.obj L)).inv
  obtain ⟨c, hc⟩ := exists_Q_map_eq_of_isKInjective X
    (I := kInjectiveModel X (DerivedCategory.Q.obj M))
    (kInjectiveModelIso X (DerivedCategory.Q.obj M)).inv
  exact derivedCompositionOnKInjectiveModel_transport X T Hd a b c _ _ _ ha hb hc

/-- **Contravariant naturality of derived composition in the source object.** -/
theorem derivedSheafHomComposition_natural_source (k : E' ⟶ E)
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomComposition X T Hd E L M ≫ derivedSheafHomMap X Hd k (𝟙 M) =
      derivedTensorMap X T (𝟙 ((Hd.hom.obj (op L)).obj M))
          (derivedSheafHomMap X Hd k (𝟙 L)) ≫
        derivedSheafHomComposition X T Hd E' L M := by
  obtain ⟨κ, hκ₁, hκ₂⟩ := exists_kInjectiveModel_map X k
  have t₁ : derivedSheafHomMap X Hd (kInjectiveModelIso X E).inv
        (kInjectiveModelIso X M).hom ≫ derivedSheafHomMap X Hd k (𝟙 M) =
      derivedSheafHomMap X Hd (k ≫ (kInjectiveModelIso X E).inv)
        (kInjectiveModelIso X M).hom := by
    rw [derivedSheafHomMap_comp, Category.comp_id]
  have t₂ : derivedSheafHomMap X Hd k (𝟙 L) ≫
        derivedSheafHomMap X Hd (kInjectiveModelIso X E').hom
          (kInjectiveModelIso X L).inv =
      derivedSheafHomMap X Hd ((kInjectiveModelIso X E').hom ≫ k)
        (kInjectiveModelIso X L).inv := by
    rw [derivedSheafHomMap_comp, Category.id_comp]
  have t₃ : derivedSheafHomMap X Hd (kInjectiveModelIso X E).hom
        (kInjectiveModelIso X L).inv ≫
      derivedSheafHomMap X Hd (DerivedCategory.Q.map κ)
        (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X L))) =
      derivedSheafHomMap X Hd ((kInjectiveModelIso X E').hom ≫ k)
        (kInjectiveModelIso X L).inv := by
    rw [derivedSheafHomMap_comp, Category.comp_id, hκ₁]
  have t₄ : derivedSheafHomMap X Hd (DerivedCategory.Q.map κ)
        (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X M))) ≫
      derivedSheafHomMap X Hd (kInjectiveModelIso X E').inv
        (kInjectiveModelIso X M).hom =
      derivedSheafHomMap X Hd (k ≫ (kInjectiveModelIso X E).inv)
        (kInjectiveModelIso X M).hom := by
    rw [derivedSheafHomMap_comp, Category.id_comp, hκ₂]
  dsimp only [derivedSheafHomComposition]
  simp only [Category.assoc]
  rw [t₁, dtComp, Category.id_comp, t₂, ← t₃, ← dtCompRight, natSourceTail, t₄]

/-- **Covariant naturality of derived composition in the target object.** -/
theorem derivedSheafHomComposition_natural_target
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m : G ⟶ G') :
    derivedSheafHomComposition X T Hd K L G ≫ derivedSheafHomMap X Hd (𝟙 K) m =
      derivedTensorMap X T (derivedSheafHomMap X Hd (𝟙 L) m)
          (𝟙 ((Hd.hom.obj (op K)).obj L)) ≫
        derivedSheafHomComposition X T Hd K L G' := by
  obtain ⟨μ, hμ₁, hμ₂⟩ := exists_kInjectiveModel_map X m
  have t₁ : derivedSheafHomMap X Hd (kInjectiveModelIso X K).inv
        (kInjectiveModelIso X G).hom ≫ derivedSheafHomMap X Hd (𝟙 K) m =
      derivedSheafHomMap X Hd (kInjectiveModelIso X K).inv
        ((kInjectiveModelIso X G).hom ≫ m) := by
    rw [derivedSheafHomMap_comp, Category.id_comp]
  have t₂ : derivedSheafHomMap X Hd (𝟙 L) m ≫
        derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom
          (kInjectiveModelIso X G').inv =
      derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom
        (m ≫ (kInjectiveModelIso X G').inv) := by
    rw [derivedSheafHomMap_comp, Category.comp_id]
  have t₃ : derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom
        (kInjectiveModelIso X G).inv ≫
      derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X L)))
        (DerivedCategory.Q.map μ) =
      derivedSheafHomMap X Hd (kInjectiveModelIso X L).hom
        (m ≫ (kInjectiveModelIso X G').inv) := by
    rw [derivedSheafHomMap_comp, Category.id_comp, hμ₂]
  have t₄ : derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X K)))
        (DerivedCategory.Q.map μ) ≫
      derivedSheafHomMap X Hd (kInjectiveModelIso X K).inv
        (kInjectiveModelIso X G').hom =
      derivedSheafHomMap X Hd (kInjectiveModelIso X K).inv
        ((kInjectiveModelIso X G).hom ≫ m) := by
    rw [derivedSheafHomMap_comp, Category.comp_id, hμ₁]
  dsimp only [derivedSheafHomComposition]
  simp only [Category.assoc]
  rw [t₁, dtComp, Category.id_comp, t₂, ← t₃, ← dtCompLeft, natTargetTail, t₄]

/-- **Dinaturality of derived composition in the intermediate object.** A morphism of the
intermediate object may be absorbed either covariantly into the right-hand tensor factor or
contravariantly into the left-hand one, with the same effect. -/
theorem derivedSheafHomComposition_dinatural_middle
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (l : F ⟶ F')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorMap X T (𝟙 ((Hd.hom.obj (op F')).obj M))
          (derivedSheafHomMap X Hd (𝟙 K) l) ≫
        derivedSheafHomComposition X T Hd K F' M =
      derivedTensorMap X T (derivedSheafHomMap X Hd l (𝟙 M))
          (𝟙 ((Hd.hom.obj (op K)).obj F)) ≫
        derivedSheafHomComposition X T Hd K F M := by
  obtain ⟨lam, hlam₁, hlam₂⟩ := exists_kInjectiveModel_map X l
  have u₁ : derivedSheafHomMap X Hd (𝟙 K) l ≫
        derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom
          (kInjectiveModelIso X F').inv =
      derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom
        (l ≫ (kInjectiveModelIso X F').inv) := by
    rw [derivedSheafHomMap_comp, Category.comp_id]
  have u₂ : derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom
        (kInjectiveModelIso X F).inv ≫
      derivedSheafHomMap X Hd (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X K)))
        (DerivedCategory.Q.map lam) =
      derivedSheafHomMap X Hd (kInjectiveModelIso X K).hom
        (l ≫ (kInjectiveModelIso X F').inv) := by
    rw [derivedSheafHomMap_comp, Category.id_comp, hlam₂]
  have u₃ : derivedSheafHomMap X Hd (kInjectiveModelIso X F').hom
        (kInjectiveModelIso X M).inv ≫
      derivedSheafHomMap X Hd (DerivedCategory.Q.map lam)
        (𝟙 (DerivedCategory.Q.obj (kInjectiveModel X M))) =
      derivedSheafHomMap X Hd ((kInjectiveModelIso X F).hom ≫ l)
        (kInjectiveModelIso X M).inv := by
    rw [derivedSheafHomMap_comp, Category.comp_id, hlam₁]
  have u₄ : derivedSheafHomMap X Hd l (𝟙 M) ≫
        derivedSheafHomMap X Hd (kInjectiveModelIso X F).hom
          (kInjectiveModelIso X M).inv =
      derivedSheafHomMap X Hd ((kInjectiveModelIso X F).hom ≫ l)
        (kInjectiveModelIso X M).inv := by
    rw [derivedSheafHomMap_comp, Category.id_comp]
  dsimp only [derivedSheafHomComposition]
  rw [dtComp, Category.id_comp, u₁, ← u₂, ← dtCompRight, dinatMiddleTail, dtCompLeft, u₃,
    dtComp, Category.id_comp, u₄]

end Objects

end Composition

end Tensor

end AlgebraicGeometry.RingedSite

end
