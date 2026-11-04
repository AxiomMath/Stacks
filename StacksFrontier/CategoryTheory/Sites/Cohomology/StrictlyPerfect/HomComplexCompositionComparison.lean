module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality

/-!
# Composition is compatible with the comparison to derived internal Hom

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. There are two
composition products in play. On the naive internal Hom complexes of Stacks 0A8Z there is the
composition morphism of Stacks 0A91,

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`,

read in the derived category along the canonical map from the derived tensor product; and on the
derived internal Homs there is the composition morphism of Stacks 0A98,

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`.

This file proves that the canonical comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` carries the first to the second: the
square

```
Q(SheafHom(L, M)) ⊗^L Q(SheafHom(K, L))  ⟶  Q(SheafHom(K, M))
            |                                        |
            v                                        v
  RSheafHom(QL, QM) ⊗^L RSheafHom(QK, QL)  ⟶  RSheafHom(QK, QM)
```

commutes, with no hypothesis on `K`, `L` or `M`.

## The proof

The square is first proved for `L` and `M` K-injective. There the comparison is the inverse of
the model comparison of `AlgebraicGeometry.RingedSite.DerivedInternalHom` on the nose, and
derived composition is by construction the composition of internal Hom complexes conjugated by
that model comparison, so the two vertical maps cancel against the conjugation and nothing is
left to prove.

The two targets are then released one at a time, each along the K-injective augmentation of the
complex being released, and each time the released square is deduced from the already-known one
by three naturality statements: naturality of the comparison
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`), functoriality of the
naive composition (`AlgebraicGeometry.RingedSite.homComplexDerivedComposition_natural`) and the
matching functoriality of derived composition.

* Releasing the *target* `M` costs nothing: the morphism
  `RSheafHom(QK, QM) ⟶ RSheafHom(QK, QM')` induced by a K-injective augmentation `M ⟶ M'` is an
  isomorphism, because the augmentation is a quasi-isomorphism, so it may be cancelled from the
  right of the square.
* Releasing the *intermediate* complex `L` is the step that needs an input: the intermediate
  complex occurs contravariantly in one tensor factor, so the cancellation is on the *left*, and
  what has to be cancelled is the morphism `SheafHom(L', M) ⟶ SheafHom(L, M)` induced by the
  augmentation `L ⟶ L'`. That is a quasi-isomorphism by Stacks 0A95, which requires the target
  `M` to be K-injective — which is exactly the state the previous step leaves it in, so the two
  releases must be performed in this order.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition`: **the square
  commutes** for arbitrary `K`, `L`, `M`.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_of_isKInjective` and
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_of_isKInjective_target`:
  the two intermediate cases, the first a cancellation of the model comparison and the second
  the release of the intermediate complex.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_target` and
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_source`: the two
  one-variable specialisations of the naturality of the comparison.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section Comparison

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (Hd : DerivedInternalHom.{u, d} X)

/-- **Naturality of the comparison in the target alone.** This is the one-variable
specialisation of `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality` in
which the source is untouched. -/
lemma strictlyPerfectHomComparison_naturality_target
    (E F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (g : F ⟶ F') :
    DerivedCategory.Q.map (homMap X (𝟙 E) g) ≫ strictlyPerfectHomComparison X Hd E F' =
      strictlyPerfectHomComparison X Hd E F ≫
        (Hd.hom.obj (op (DerivedCategory.Q.obj E))).map (DerivedCategory.Q.map g) := by
  have h := strictlyPerfectHomComparison_naturality X Hd E E F F' (𝟙 E) g
  simp only [CategoryTheory.Functor.map_id, op_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- **Naturality of the comparison in the source alone.** This is the one-variable
specialisation of `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality` in
which the target is untouched. -/
lemma strictlyPerfectHomComparison_naturality_source
    (E E' F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : E' ⟶ E) :
    DerivedCategory.Q.map (homMap X e (𝟙 F)) ≫ strictlyPerfectHomComparison X Hd E' F =
      strictlyPerfectHomComparison X Hd E F ≫
        (Hd.hom.map (DerivedCategory.Q.map e).op).app (DerivedCategory.Q.obj F) := by
  have h := strictlyPerfectHomComparison_naturality X Hd E E' F F e (𝟙 F)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

end Comparison

/-- Every complex admits a quasi-isomorphism to its chosen K-injective resolution. -/
private theorem exists_quasiIso_to_kInjectiveResolution
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ j : K ⟶ (kInjectiveResolution X).obj K, QuasiIso j :=
  ⟨(kInjectiveAugmentation X).app K, inferInstance⟩

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

section Splittings

variable {A A' A'' B B' B'' :
  DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}

/-- A composite in the left-hand tensor factor splits off as an induced morphism which is the
identity in the right-hand factor. -/
lemma derivedTensorMap_split_left (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') :
    derivedTensorMap X T (a ≫ a') b =
      derivedTensorMap X T a (𝟙 B) ≫ derivedTensorMap X T a' b := by
  rw [derivedTensorMap_comp, Category.id_comp]

/-- A composite in the right-hand tensor factor splits off as an induced morphism which is the
identity in the left-hand factor. -/
lemma derivedTensorMap_split_right (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'') :
    derivedTensorMap X T a (b ≫ b') =
      derivedTensorMap X T (𝟙 A) b ≫ derivedTensorMap X T a b' := by
  rw [derivedTensorMap_comp, Category.id_comp]

/-- The morphism induced on derived tensor products by a pair of isomorphisms is an
isomorphism. -/
lemma isIso_derivedTensorMap (a : A ⟶ A') (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedTensorMap X T a b) :=
  ⟨⟨derivedTensorMap X T (inv a) (inv b), by
      rw [derivedTensorMap_comp, IsIso.hom_inv_id, IsIso.hom_inv_id, derivedTensorMap_id], by
      rw [derivedTensorMap_comp, IsIso.inv_hom_id, IsIso.inv_hom_id, derivedTensorMap_id]⟩⟩

end Splittings

section NaiveComposition

variable {L L' M M' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Dinaturality of the naive composition in the intermediate complex**, read in the derived
category: a morphism of the intermediate complex may be absorbed covariantly into the right-hand
tensor factor or contravariantly into the left-hand one, with the same effect. -/
lemma homComplexDerivedComposition_dinatural_middle
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (l : L ⟶ L')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedTensorMap X T (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X L' M).obj))
          (DerivedCategory.Q.map (homMap X (𝟙 K) l)) ≫
        homComplexDerivedComposition X T K L' M =
      derivedTensorMap X T (DerivedCategory.Q.map (homMap X l (𝟙 M)))
          (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X K L).obj)) ≫
        homComplexDerivedComposition X T K L M := by
  have h := homComplexDerivedComposition_natural X T (𝟙 K) l (𝟙 M)
  simp only [homMap_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- **Covariant naturality of the naive composition in the target complex**, read in the derived
category. -/
lemma homComplexDerivedComposition_natural_target
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : M ⟶ M') :
    derivedTensorMap X T (DerivedCategory.Q.map (homMap X (𝟙 L) m))
          (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X K L).obj)) ≫
        homComplexDerivedComposition X T K L M' =
      homComplexDerivedComposition X T K L M ≫
        DerivedCategory.Q.map (homMap X (𝟙 K) m) := by
  have h := homComplexDerivedComposition_natural X T (𝟙 K) (𝟙 L) m
  simp only [homMap_id, CategoryTheory.Functor.map_id, derivedTensorMap_id,
    Category.id_comp] at h
  exact h

end NaiveComposition

variable (Hd : DerivedInternalHom.{u, d} X)

/-- **The composition square at K-injective intermediate and target complexes.** For `L` and `M`
K-injective the comparison to derived internal Hom carries the naive composition morphism of
Stacks 0A91 to the derived composition morphism of Stacks 0A98.

At a K-injective target the comparison is the inverse of the model comparison of
`AlgebraicGeometry.RingedSite.DerivedInternalHom`, and derived composition at K-injective
intermediate and target complexes is the naive composition conjugated by that same model
comparison, so the identity is the cancellation of an isomorphism against its inverse in each of
the two tensor factors. -/
theorem strictlyPerfectHomComparison_composition_of_isKInjective
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    derivedTensorMap X T (strictlyPerfectHomComparison X Hd L M)
          (strictlyPerfectHomComparison X Hd K L) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      homComplexDerivedComposition X T K L M ≫ strictlyPerfectHomComparison X Hd K M := by
  rw [derivedSheafHomComposition_eq_onKInjectiveModel]
  dsimp only [derivedCompositionOnKInjectiveModel]
  rw [strictlyPerfectHomComparison_eq_homComparison_inv,
    strictlyPerfectHomComparison_eq_homComparison_inv,
    strictlyPerfectHomComparison_eq_homComparison_inv, ← Category.assoc,
    derivedTensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id, derivedTensorMap_id,
    Category.id_comp]

/-- **The composition square at a K-injective target.** The intermediate complex `L` is
arbitrary; only the target `M` is assumed K-injective.

The identity is deduced from the K-injective case at the chosen K-injective resolution `L'` of
`L` by cancelling, from the left, the morphism `SheafHom(L', M) ⟶ SheafHom(L, M)` induced by the
augmentation `L ⟶ L'`. That morphism is a quasi-isomorphism by Stacks 0A95, whose hypothesis is
exactly that the target `M` is K-injective, so this is the step that forces the target to be
released after the intermediate complex and not before. -/
theorem strictlyPerfectHomComparison_composition_of_isKInjective_target
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective] :
    derivedTensorMap X T (strictlyPerfectHomComparison X Hd L M)
          (strictlyPerfectHomComparison X Hd K L) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      homComplexDerivedComposition X T K L M ≫ strictlyPerfectHomComparison X Hd K M := by
  obtain ⟨j, hqi⟩ := exists_quasiIso_to_kInjectiveResolution X L
  have : IsIso (DerivedCategory.Q.map (homMap X j (𝟙 M))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (homMap_quasiIso X (𝟙 M) j)
  have := isIso_derivedTensorMap X T (DerivedCategory.Q.map (homMap X j (𝟙 M)))
    (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X K L).obj))
  rw [← cancel_epi (derivedTensorMap X T (DerivedCategory.Q.map (homMap X j (𝟙 M)))
    (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X K L).obj)))]
  conv_lhs =>
    rw [← Category.assoc, ← derivedTensorMap_split_left,
      strictlyPerfectHomComparison_naturality_source, ← derivedTensorMap_comp_left,
      Category.assoc, ← derivedSheafHomMap_id_right,
      ← derivedSheafHomComposition_dinatural_middle, ← Category.assoc,
      derivedTensorMap_comp_right, derivedSheafHomMap_id_left,
      ← strictlyPerfectHomComparison_naturality_target, derivedTensorMap_split_right,
      Category.assoc,
      strictlyPerfectHomComparison_composition_of_isKInjective X T Hd K
        ((kInjectiveResolution X).obj L) M]
  conv_rhs =>
    rw [← Category.assoc, ← homComplexDerivedComposition_dinatural_middle, Category.assoc]

/-- **The composition square, in general.** For arbitrary complexes `K`, `L`, `M` the canonical
comparison to derived internal Hom carries the composition morphism of internal Hom complexes of
Stacks 0A91 to the composition morphism of derived internal Homs of Stacks 0A98.

The target is released from the previous statement along its K-injective augmentation `M ⟶ M'`:
the induced morphism `RSheafHom(QK, QM) ⟶ RSheafHom(QK, QM')` is an isomorphism, because the
augmentation is a quasi-isomorphism, so it may be cancelled from the right. -/
theorem strictlyPerfectHomComparison_composition
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedTensorMap X T (strictlyPerfectHomComparison X Hd L M)
          (strictlyPerfectHomComparison X Hd K L) ≫
        derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      homComplexDerivedComposition X T K L M ≫ strictlyPerfectHomComparison X Hd K M := by
  obtain ⟨j, hqi⟩ := exists_quasiIso_to_kInjectiveResolution X M
  have : IsIso (DerivedCategory.Q.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqi
  rw [← cancel_mono ((Hd.hom.obj (op (DerivedCategory.Q.obj K))).map
    (DerivedCategory.Q.map j))]
  conv_lhs =>
    rw [Category.assoc, ← derivedSheafHomMap_id_left,
      derivedSheafHomComposition_natural_target, ← Category.assoc,
      derivedTensorMap_comp_left, derivedSheafHomMap_id_left,
      ← strictlyPerfectHomComparison_naturality_target, derivedTensorMap_split_left,
      Category.assoc,
      strictlyPerfectHomComparison_composition_of_isKInjective_target X T Hd K L
        ((kInjectiveResolution X).obj M)]
  conv_rhs =>
    rw [Category.assoc, ← strictlyPerfectHomComparison_naturality_target, ← Category.assoc,
      ← homComplexDerivedComposition_natural_target, Category.assoc]

end AlgebraicGeometry.RingedSite

end
