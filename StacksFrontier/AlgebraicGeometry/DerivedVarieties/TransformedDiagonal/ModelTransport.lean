module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormula
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorModelTransport
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The Hom groups of Tag 0G0A read at the standard model of the derived category

The complex of [Stacks, Tag 0G0A] lives in the locally small derived category
`DerivedCategory (pullback f g).Modules` of Tag 079Q, which is what instance search supplies:
`AlgebraicGeometry.perfectDerived`, `AlgebraicGeometry.DiagonalResolution.transformedTerm` and
`AlgebraicGeometry.derivedExternalTensorMap` take no model as a binder. The results its Künneth
input is to be read off — the Künneth formula for Ext of [Stacks, Tag 0FXZ], the global Künneth
formula of [Stacks, Tag 0FLQ], the identification of [Stacks, Tag 08DK] of a Hom group with the
global sections of a derived internal hom — are stated at `HasDerivedCategory.standard`, a
different choice of localization, so their Hom groups are different types. This file identifies
the Hom groups that matter, compatibly with the pure maps `a ⊠ c`, so that a statement about the
pure maps at one model is a statement about them at the other.

The comparison is `StacksDraft.DerivedModel.schemeModulesComparison`, which is the identity on
objects: an object of the locally small model *is* an object of the standard one, and only the
morphisms move.

## Main definitions

* `StacksDraft.DerivedModel.modelHomLinearEquiv`: the morphisms between two objects of `D(𝒪_X)` at
  the two models, as a `k`-linear equivalence.
* `AlgebraicGeometry.derivedExternalTensorMapAt`: the pure map `u ⊠ v` with the three models as
  binders; `AlgebraicGeometry.derivedExternalTensorStd` and
  `AlgebraicGeometry.derivedExternalTensorMapStd` are `⊠` and `u ⊠ v` at the standard model.
* `AlgebraicGeometry.derivedExternalTensorModelIso`: the comparison carries `K ⊠ L` at the
  standard model to `K ⊠ L` at the locally small model.
* `AlgebraicGeometry.derivedExternalTensorHomModelEquiv`: the resulting additive identification
  of the Hom groups between external tensor products.
* `AlgebraicGeometry.DiagonalResolution.transformedImagePairingStd`: the pairing
  `(a, c) ↦ a ⊠ c` of Tag 0G0A on `X ×_k Y` with every derived category at the standard model.

## Main results

* `StacksDraft.DerivedModel.additive_schemeModulesComparison_functor` and
  `StacksDraft.DerivedModel.linear_schemeModulesComparison_functor`: the comparison is additive
  and `k`-linear.
* `StacksDraft.DerivedModel.modelHomLinearEquiv_singleFunctor_map`: it carries `single(a)` to
  `single(a)`.
* `AlgebraicGeometry.derivedExternalTensorModelIso_naturality` and
  `AlgebraicGeometry.derivedExternalTensorHomModelEquiv_derivedExternalTensorMapStd`: the
  identification carries the pure map `u ⊠ v` at the standard model to the pure map of the
  images of `u` and `v`.
* `AlgebraicGeometry.IsTensorPairing.of_equiv`: a tensor pairing transports along a `k`-linear
  identification of its second factor and an additive identification of its target.
* `AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairing_iff_std`: **the
  Künneth input `himage` of Tag 0G0A holds if and only if it holds at the standard model.**

## Implementation notes

*Route.* The comparison is carried through each constituent of `⊠`: through the derived pullback
by the existing `StacksDraft.DerivedModel.derivedPullbackModelIso`, and through the derived tensor
product by `StacksDraft.DerivedModel.derivedTensorModelIso`, which compares two descents of the
total tensor product of K-flat complexes. The alternative — re-declaring the Künneth morphism
for Ext and its five theorem inputs with the model as a binder — would have meant restating the
development of `…KunnethMapForExt` and of every file it is built from, and is not needed: only
the Hom groups between the terms are compared, never the Künneth morphism itself.

*No object is transported.* `StacksDraft.DerivedModel.schemeModulesComparison` is
`ShrinkHoms.equivalence`, so its functor and inverse are the identity on objects by `rfl`; the
standard-model objects below, `AlgebraicGeometry.DiagonalResolution.firstFactorStd` and
`AlgebraicGeometry.DiagonalResolution.secondFactorImageStd`, are therefore the same objects as
the locally small `single(ℰᵢ)` and `F(𝒢ᵢ)`, and every isomorphism here is between morphism
types.

*The `k`-linear structures* are the canonical `DerivedCategory.instLinear` at either model,
induced from `[Linear k X.Modules]`, and on `AlgebraicGeometry.perfectDerived`
`CategoryTheory.Linear.fullSubcategory`, turned on as a local instance exactly as in
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Situation`, so that the
statement of `isTensorPairing_transformedImagePairing_iff_std` is literally the hypothesis
`himage` of `AlgebraicGeometry.exists_kunnethComplex_of_imagePairing`.

Nothing here carries a project tag: these are statements about two Lean choices of one
mathematical object.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ u

namespace StacksDraft.DerivedModel

/-! ### The comparison of the two models of `D(𝒪_X)` is additive and linear -/

section Comparison

variable (X : AlgebraicGeometry.Scheme.{u})

/-- **The comparison of the two models of `D(𝒪_X)` is additive.** Read along the localization
functor out of the homotopy category of the standard model it is the localization functor of the
locally small model (`StacksDraft.DerivedModel.shrinkComparisonQhIso`), which is additive, and
additivity of a functor out of a localization with a calculus of fractions is detected after
precomposing with the localization functor. -/
instance additive_schemeModulesComparison_functor :
    (schemeModulesComparison X).functor.Additive :=
  (Localization.functor_additive_iff
    (@DerivedCategory.Qh X.Modules _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (schemeModulesComparison X).functor).2
    (Functor.additive_of_iso (shrinkComparisonQhIso X.Modules))

/-- **The inverse comparison of the two models of `D(𝒪_X)` is additive.** -/
instance additive_schemeModulesComparison_inverse :
    (schemeModulesComparison X).inverse.Additive :=
  inferInstance

variable (k : Type*) [Ring k] [Linear k X.Modules]

/-- **The comparison of the two models of `D(𝒪_X)` is `k`-linear**, for the `k`-linear structures
of `DerivedCategory.instLinear` at the two models. It carries the localization functor of the
standard model to that of the locally small one, which is `k`-linear, and `k`-linearity of a
functor out of a localization is detected after precomposing with the localization functor. -/
instance linear_schemeModulesComparison_functor :
    (schemeModulesComparison X).functor.Linear k :=
  letI : Localization.Lifting
      (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := X.Modules)) (schemeModulesComparison X).functor :=
    ⟨Iso.refl _⟩
  (Localization.functor_linear_iff
    (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) k
    (DerivedCategory.Q (C := X.Modules)) (schemeModulesComparison X).functor).1 inferInstance

/-- **The bijection of morphism types between the two models of `D(𝒪_X)`, as a `k`-linear
equivalence.** An object of the locally small model is an object of the standard one (the inverse
comparison is the identity on objects), and a morphism of the locally small model is carried to
its preimage under the comparison. -/
def modelHomLinearEquiv (K L : DerivedCategory X.Modules) :
    (K ⟶ L) ≃ₗ[k] ((schemeModulesComparison X).inverse.obj K ⟶
      (schemeModulesComparison X).inverse.obj L) where
  toFun φ := (schemeModulesComparison X).fullyFaithfulFunctor.preimage φ
  map_add' φ ψ := (schemeModulesComparison X).functor.map_injective (by
    rw [Functor.map_add]
    exact ((schemeModulesComparison X).fullyFaithfulFunctor.map_preimage (φ + ψ)).trans
      (congrArg₂ (· + ·)
        ((schemeModulesComparison X).fullyFaithfulFunctor.map_preimage φ).symm
        ((schemeModulesComparison X).fullyFaithfulFunctor.map_preimage ψ).symm))
  map_smul' c φ := (schemeModulesComparison X).functor.map_injective (by
    rw [RingHom.id_apply, Functor.map_smul]
    exact ((schemeModulesComparison X).fullyFaithfulFunctor.map_preimage (c • φ)).trans
      (congrArg (c • ·)
        ((schemeModulesComparison X).fullyFaithfulFunctor.map_preimage φ).symm))
  invFun ψ := (schemeModulesComparison X).functor.map ψ
  left_inv φ := (schemeModulesComparison X).fullyFaithfulFunctor.map_preimage φ
  right_inv ψ := (schemeModulesComparison X).fullyFaithfulFunctor.preimage_map ψ

/-- The equivalence `modelHomLinearEquiv` sends a morphism `φ` of the locally small model to its
preimage under the comparison functor. -/
theorem modelHomLinearEquiv_apply {K L : DerivedCategory X.Modules} (φ : K ⟶ L) :
    modelHomLinearEquiv X k K L φ = (schemeModulesComparison X).fullyFaithfulFunctor.preimage φ :=
  rfl

/-- The inverse of `modelHomLinearEquiv` is the action on morphisms of the comparison functor. -/
@[simp]
theorem modelHomLinearEquiv_symm_apply {K L : DerivedCategory X.Modules}
    (ψ : (schemeModulesComparison X).inverse.obj K ⟶ (schemeModulesComparison X).inverse.obj L) :
    (modelHomLinearEquiv X k K L).symm ψ = (schemeModulesComparison X).functor.map ψ :=
  rfl

/-- **The bijection of morphism types carries the single functor to the single functor**: a
morphism `single(a)` of the locally small model goes to `single(a)` of the standard one. -/
@[simp]
theorem modelHomLinearEquiv_singleFunctor_map (n : ℤ) {M N : X.Modules} (a : M ⟶ N) :
    modelHomLinearEquiv X k _ _ ((DerivedCategory.singleFunctor X.Modules n).map a) =
      (@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).map a :=
  (schemeModulesComparison X).fullyFaithfulFunctor.preimage_map _

end Comparison

/-- **The comparison carries the single functor to the single functor**: on morphisms, the image
under the comparison of `single(a)` at the standard model is `single(a)` at the locally small
model. Both are the localization functors of the two models applied to the same morphism of
complexes, and the comparison matches the two localization functors on the nose. -/
theorem schemeModulesComparison_functor_map_singleFunctor_map (X : AlgebraicGeometry.Scheme.{u})
    (n : ℤ) {M N : X.Modules} (a : M ⟶ N) :
    (schemeModulesComparison X).functor.map
        ((@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).map a) =
      (DerivedCategory.singleFunctor X.Modules n).map a :=
  rfl

end StacksDraft.DerivedModel

namespace AlgebraicGeometry

open StacksDraft.DerivedModel

attribute [local instance] hasDerivedCategoryRingedSpace hasDerivedCategoryTensorSite

/-! ### The pure map of derived external tensor products, at any model -/

section Bifunctor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] (T : C₁ ⥤ C₂ ⥤ D)

/-- A naturality square for a composite of a comparison `ψ` with `bifunctorMap T α β`, assembled
from a square for `ψ` and one square for each of `α` and `β`. -/
theorem bifunctorMap_comparison_naturality {Z Z' : D} {K₀ K₀' : C₁} {L₀ L₀' : C₂}
    {K K' : C₁} {L L' : C₂} (a : Z ⟶ Z') (ψ : Z ⟶ (T.obj K₀).obj L₀)
    (ψ' : Z' ⟶ (T.obj K₀').obj L₀') (x : K₀ ⟶ K₀') (y : L₀ ⟶ L₀') (α : K₀ ⟶ K) (α' : K₀' ⟶ K')
    (β : L₀ ⟶ L) (β' : L₀' ⟶ L') (x' : K ⟶ K') (y' : L ⟶ L')
    (hT : a ≫ ψ' = ψ ≫ bifunctorMap T x y) (hp : x ≫ α' = α ≫ x') (hq : y ≫ β' = β ≫ y') :
    a ≫ ψ' ≫ bifunctorMap T α' β' = (ψ ≫ bifunctorMap T α β) ≫ bifunctorMap T x' y' := by
  rw [← Category.assoc, hT, Category.assoc, Category.assoc, bifunctorMap_comp, bifunctorMap_comp,
    hp, hq]

end Bifunctor

section DerivedExternalTensor

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The map `u ⊠ v : K ⊠ L ⟶ K' ⊠ L'` of derived external tensor products, with the three models
of the derived categories as binders, like `AlgebraicGeometry.derivedExternalTensor`. At the
locally small model it is `AlgebraicGeometry.derivedExternalTensorMap`
(`AlgebraicGeometry.derivedExternalTensorMapAt_eq`). -/
def derivedExternalTensorMapAt [HasDerivedCategory.{w₁} X.Modules]
    [HasDerivedCategory.{w₂} Y.Modules] [HasDerivedCategory.{w₃} (pullback f g).Modules]
    {K K' : DerivedCategory X.Modules} {L L' : DerivedCategory Y.Modules}
    (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorAt f g K L ⟶ derivedExternalTensorAt f g K' L' :=
  bifunctorMap (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (pullback f g).sheaf)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst f g).toLRSHom.toShHom).map u)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd f g).toLRSHom.toShHom).map v)

/-- At the locally small model the pure map is `AlgebraicGeometry.derivedExternalTensorMap`. -/
theorem derivedExternalTensorMapAt_eq {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorMapAt f g u v = derivedExternalTensorMap f g u v :=
  rfl

/-- `K ⊠ L` at the standard model of all three derived categories. -/
abbrev derivedExternalTensorStd
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _) :=
  @derivedExternalTensorAt X Y S f g (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) K L

/-- The pure map `u ⊠ v` at the standard model of all three derived categories. -/
abbrev derivedExternalTensorMapStd
    {K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {L L' : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorStd f g K L ⟶ derivedExternalTensorStd f g K' L' :=
  @derivedExternalTensorMapAt X Y S f g (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) K K' L L' u v

/-- **The derived external tensor product read at the two models.** The comparison carries
`K ⊠ L` taken at the standard model to `K ⊠ L` taken at the locally small model: the derived
tensor product is compared by `StacksDraft.DerivedModel.derivedTensorModelIsoApp` and the two
derived pullbacks by `StacksDraft.DerivedModel.derivedPullbackModelIso`. -/
def derivedExternalTensorModelIso
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    (schemeModulesComparison (pullback f g)).functor.obj (derivedExternalTensorStd f g K L) ≅
      derivedExternalTensor f g ((schemeModulesComparison X).functor.obj K)
        ((schemeModulesComparison Y).functor.obj L) :=
  derivedTensorModelIsoApp (pullback f g).sheaf (HasDerivedCategory.standard _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (schemeModulesComparison (pullback f g)).functor (Iso.refl _)
      (@Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _ _ _ _ _ _
        (HasDerivedCategory.standard _) _ _ _)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) _ _ ≪≫
    Functor.bifunctorMapIso
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (pullback f g).sheaf)
      ((derivedPullbackModelIso (pullback.fst f g).toLRSHom.toShHom).app K)
      ((derivedPullbackModelIso (pullback.snd f g).toLRSHom.toShHom).app L)

/-- The underlying morphism of `AlgebraicGeometry.derivedExternalTensorModelIso`. -/
theorem derivedExternalTensorModelIso_hom
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (L : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    (derivedExternalTensorModelIso f g K L).hom =
      (derivedTensorModelIsoApp (pullback f g).sheaf (HasDerivedCategory.standard _)
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
        (schemeModulesComparison (pullback f g)).functor (Iso.refl _)
        (@Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _ _ _ _ _ _
          (HasDerivedCategory.standard _) _ _ _)
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) _ _).hom ≫
      bifunctorMap (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _)
        ((derivedPullbackModelIso (pullback.fst f g).toLRSHom.toShHom).hom.app K)
        ((derivedPullbackModelIso (pullback.snd f g).toLRSHom.toShHom).hom.app L) :=
  rfl

/-- **Naturality of the comparison of the derived external tensor products**: the comparison
carries the pure map `u ⊠ v` at the standard model to the pure map of the images of `u` and `v`
at the locally small model. -/
theorem derivedExternalTensorModelIso_naturality
    {K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {L L' : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L') :
    (schemeModulesComparison (pullback f g)).functor.map (derivedExternalTensorMapStd f g u v) ≫
        (derivedExternalTensorModelIso f g K' L').hom =
      (derivedExternalTensorModelIso f g K L).hom ≫
        derivedExternalTensorMap f g ((schemeModulesComparison X).functor.map u)
          ((schemeModulesComparison Y).functor.map v) := by
  have hT := derivedTensorModelIsoApp_naturality (pullback f g).sheaf
    (HasDerivedCategory.standard _)
    (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
    (schemeModulesComparison (pullback f g)).functor (Iso.refl _)
    (@Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _ _ _ _ _ _
      (HasDerivedCategory.standard _) _ _ _)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _)
    ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _
      (pullback.fst f g).toLRSHom.toShHom (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) _).map u)
    ((@Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback _ _
      (pullback.snd f g).toLRSHom.toShHom (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) _).map v)
  have hp := (derivedPullbackModelIso (pullback.fst f g).toLRSHom.toShHom).hom.naturality u
  have hq := (derivedPullbackModelIso (pullback.snd f g).toLRSHom.toShHom).hom.naturality v
  exact bifunctorMap_comparison_naturality
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (pullback f g).sheaf) _ _ _ _ _ _ _
    _ _ _ _ hT hp hq

/-- **The Hom groups between derived external tensor products, read at the two models.** For
objects `K, K'` of `D(𝒪_X)` and `L, L'` of `D(𝒪_Y)` at the standard model, conjugating by the
comparisons of `AlgebraicGeometry.derivedExternalTensorModelIso` identifies the morphisms
`K ⊠ L ⟶ K' ⊠ L'` at the standard model with those at the locally small model, additively. -/
def derivedExternalTensorHomModelEquiv
    (K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (L L' : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)) :
    (derivedExternalTensorStd f g K L ⟶ derivedExternalTensorStd f g K' L') ≃+
      (derivedExternalTensor f g ((schemeModulesComparison X).functor.obj K)
          ((schemeModulesComparison Y).functor.obj L) ⟶
        derivedExternalTensor f g ((schemeModulesComparison X).functor.obj K')
          ((schemeModulesComparison Y).functor.obj L')) where
  toFun φ := (derivedExternalTensorModelIso f g K L).inv ≫
    (schemeModulesComparison (pullback f g)).functor.map φ ≫
      (derivedExternalTensorModelIso f g K' L').hom
  invFun ψ := (schemeModulesComparison (pullback f g)).fullyFaithfulFunctor.preimage
    ((derivedExternalTensorModelIso f g K L).hom ≫ ψ ≫
      (derivedExternalTensorModelIso f g K' L').inv)
  left_inv φ := by
    apply (schemeModulesComparison (pullback f g)).functor.map_injective
    rw [Functor.FullyFaithful.map_preimage]
    simp
  right_inv ψ := by
    dsimp only
    rw [Functor.FullyFaithful.map_preimage]
    simp
  map_add' φ φ' := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- **The identification of Hom groups carries pure maps to pure maps**: the pure map `u ⊠ v` at
the standard model goes to the pure map of the images of `u` and `v` at the locally small
model. This is `AlgebraicGeometry.derivedExternalTensorModelIso_naturality`. -/
theorem derivedExternalTensorHomModelEquiv_derivedExternalTensorMapStd
    {K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {L L' : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorHomModelEquiv f g K K' L L' (derivedExternalTensorMapStd f g u v) =
      derivedExternalTensorMap f g ((schemeModulesComparison X).functor.map u)
        ((schemeModulesComparison Y).functor.map v) := by
  change (derivedExternalTensorModelIso f g K L).inv ≫ _ ≫ _ = _
  rw [Iso.inv_comp_eq]
  exact derivedExternalTensorModelIso_naturality f g u v

end DerivedExternalTensor

/-! ### Transporting a tensor pairing along identifications of its factors and target -/

section TensorPairingEquiv

variable {k : Type*} [CommRing k] {M N N' P P' : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N'] [AddCommGroup P]
  [AddCommGroup P']

omit [AddCommGroup M] [Module k M] in
/-- Reindexing the second factor of the pairs by a `k`-linear equivalence and then by its
inverse does nothing. -/
theorem freeAbelianGroupMapRight_symm_apply (e : N ≃ₗ[k] N') (u : FreeAbelianGroup (M × N')) :
    freeAbelianGroupMapRight (e : N →ₗ[k] N')
        (freeAbelianGroupMapRight (e.symm : N' →ₗ[k] N) u) = u :=
  DFunLike.congr_fun (FreeAbelianGroup.lift_ext
    ((freeAbelianGroupMapRight (M := M) (e : N →ₗ[k] N')).comp
      (freeAbelianGroupMapRight (e.symm : N' →ₗ[k] N))) (AddMonoidHom.id _)
    fun _ => by simp) u

/-- **A tensor pairing transports along identifications of its second factor and its target.**
If `p` exhibits `P` as `M ⊗_k N`, `e : N' ≃ₗ[k] N` is `k`-linear, `ε : P' ≃+ P` is additive, and
`p'` matches `p` on generators through `e` and `ε`, then `p'` exhibits `P'` as `M ⊗_k N'`. -/
theorem IsTensorPairing.of_equiv {p : FreeAbelianGroup (M × N) →+ P}
    {p' : FreeAbelianGroup (M × N') →+ P'} (e : N' ≃ₗ[k] N) (ε : P' ≃+ P)
    (h : ∀ (m : M) (n : N'), ε (p' (FreeAbelianGroup.of (m, n))) =
      p (FreeAbelianGroup.of (m, e n)))
    (hp : IsTensorPairing k M N p) : IsTensorPairing k M N' p' := by
  have hcomp : ∀ u, ε (p' u) = p (freeAbelianGroupMapRight (e : N' →ₗ[k] N) u) :=
    DFunLike.congr_fun (FreeAbelianGroup.lift_ext (ε.toAddMonoidHom.comp p')
      (p.comp (freeAbelianGroupMapRight (e : N' →ₗ[k] N))) fun q => by simpa using h q.1 q.2)
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hp.surjective (ε y)
    refine ⟨freeAbelianGroupMapRight (e.symm : N →ₗ[k] N') z, ε.injective ?_⟩
    rw [hcomp, freeAbelianGroupMapRight_symm_apply, hz]
  · rw [ker_freeAbelianGroupToTensor_comap (M := M) e, ← hp.ker_eq]
    ext u
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, ← hcomp,
      AddEquiv.map_eq_zero_iff]

end TensorPairingEquiv

/-! ### The Künneth input on `X ×_k Y` of Tag 0G0A, read at the standard model -/

attribute [local instance] CategoryTheory.Linear.fullSubcategory

namespace DiagonalResolution

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [Linear k X.Modules] [Linear k Y.Modules]
  (R : DiagonalResolution f) (g : Y ⟶ Spec (.of k)) (F : perfectDerived X ⥤ perfectDerived Y)

/-- The image `F(𝒢ᵢ)` of the `i`-th second factor, as an object of the *standard* model of
`D(𝒪_Y)`. It is the same object as `(F.obj (R.secondFactor i)).obj`, the inverse comparison being
the identity on objects. -/
abbrev secondFactorImageStd (i : ℕ) :
    @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _) :=
  (schemeModulesComparison Y).inverse.obj (F.obj (R.secondFactor i)).obj

/-- The `i`-th first factor `ℰᵢ`, placed in degree zero of the *standard* model of `D(𝒪_X)`. -/
abbrev firstFactorStd (i : ℕ) : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _) :=
  (@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).obj (R.left i)

/-- A pair of a map of first factors and a map, at the standard model of `D(𝒪_Y)`, between the
images of the second factors. -/
abbrev ImagePairStd (i j : ℕ) : Type (u + 1) :=
  (R.left i ⟶ R.left j) × (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)

/-- **The pairing `(a, c) ↦ a ⊠ c` on `X ×_k Y`, at the standard model**, extended additively to
formal integral combinations of pairs: the counterpart of
`AlgebraicGeometry.DiagonalResolution.transformedImagePairing` with every derived category taken at
`HasDerivedCategory.standard`, which is the model at which the Künneth formula for Ext of
[Stacks, Tag 0FXZ] is stated. -/
def transformedImagePairingStd (i j : ℕ) :
    FreeAbelianGroup (R.ImagePairStd F i j) →+
      (derivedExternalTensorStd f g (R.firstFactorStd i) (R.secondFactorImageStd F i) ⟶
        derivedExternalTensorStd f g (R.firstFactorStd j) (R.secondFactorImageStd F j)) :=
  FreeAbelianGroup.lift fun p =>
    derivedExternalTensorMapStd f g
      ((@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).map p.1)
      p.2

omit [Linear k X.Modules] [Linear k Y.Modules] in
/-- The pairing `transformedImagePairingStd` sends a single pair `(a, c)` to `single(a) ⊠ c`. -/
@[simp]
theorem transformedImagePairingStd_of {i j : ℕ} (p : R.ImagePairStd F i j) :
    R.transformedImagePairingStd g F i j (FreeAbelianGroup.of p) =
      derivedExternalTensorMapStd f g
        ((@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).map p.1)
        p.2 :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The Hom groups between the images of the second factors, at the two models**, as a
`k`-linear equivalence: a morphism of `D_perf(𝒪_Y)` is a morphism of the locally small `D(𝒪_Y)`,
and that is carried to the standard model by `StacksDraft.DerivedModel.modelHomLinearEquiv`. -/
def secondFactorImageHomLinearEquiv (i j : ℕ) :
    (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j)) ≃ₗ[k]
      (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j) :=
  InducedCategory.homLinearEquiv (R := k) ≪≫ₗ modelHomLinearEquiv Y k _ _

omit [Linear k X.Modules] in
/-- The equivalence `secondFactorImageHomLinearEquiv` sends a morphism `c` to the preimage, under
the comparison functor, of its underlying morphism. -/
theorem secondFactorImageHomLinearEquiv_apply {i j : ℕ}
    (c : F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j)) :
    R.secondFactorImageHomLinearEquiv F i j c =
      (schemeModulesComparison Y).fullyFaithfulFunctor.preimage c.hom :=
  rfl

/-- **The Hom groups between the terms `ℰᵢ ⊠ F(𝒢ᵢ)` of Tag 0G0A, at the two models**: the Hom
group between the terms at the standard model is identified additively with the Hom group
between the terms `AlgebraicGeometry.DiagonalResolution.transformedTerm`, which are at the locally
small model. -/
def transformedTermHomModelEquiv (i j : ℕ) :
    (derivedExternalTensorStd f g (R.firstFactorStd i) (R.secondFactorImageStd F i) ⟶
        derivedExternalTensorStd f g (R.firstFactorStd j) (R.secondFactorImageStd F j)) ≃+
      (R.imageTerm g F i ⟶ R.imageTerm g F j) :=
  derivedExternalTensorHomModelEquiv f g (R.firstFactorStd i) (R.firstFactorStd j)
    (R.secondFactorImageStd F i) (R.secondFactorImageStd F j)

omit [Linear k X.Modules] in
/-- **The two identifications match the two pairings on generators**: the pure map
`single(a) ⊠ c` at the standard model goes to the pure map `single(a) ⊠ c` at the locally small
model. -/
theorem transformedTermHomModelEquiv_transformedImagePairingStd_of {i j : ℕ}
    (a : R.left i ⟶ R.left j) (c : F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j)) :
    R.transformedTermHomModelEquiv g F i j
        (R.transformedImagePairingStd g F i j
          (FreeAbelianGroup.of (a, R.secondFactorImageHomLinearEquiv F i j c))) =
      R.transformedImagePairing g F i j (FreeAbelianGroup.of (a, c)) := by
  rw [transformedImagePairingStd_of, transformedImagePairing_of]
  refine (derivedExternalTensorHomModelEquiv_derivedExternalTensorMapStd f g _ _).trans ?_
  congr 1
  dsimp only
  rw [secondFactorImageHomLinearEquiv_apply]
  exact (schemeModulesComparison Y).fullyFaithfulFunctor.map_preimage c.hom

/-- **The Künneth input `himage` of Tag 0G0A is the same statement at the standard model.** The
pairing `(a, c) ↦ a ⊠ c` exhibits the Hom group between the terms `ℰᵢ ⊠ F(𝒢ᵢ)` and `ℰⱼ ⊠ F(𝒢ⱼ)`
of the complex of [Stacks, Tag 0G0A] as `Hom(ℰᵢ, ℰⱼ) ⊗_k Hom(F(𝒢ᵢ), F(𝒢ⱼ))` exactly when the
same pairing does so with every derived category read at `HasDerivedCategory.standard` — the
model at which the Künneth formula for Ext of [Stacks, Tag 0FXZ], the derived internal hom of
[Stacks, Tag 08DK] and the global Künneth formula of [Stacks, Tag 0FLQ] are stated. -/
theorem isTensorPairing_transformedImagePairing_iff_std (i j : ℕ) :
    IsTensorPairing k (R.left i ⟶ R.left j)
        (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j))
        (R.transformedImagePairing g F i j) ↔
      IsTensorPairing k (R.left i ⟶ R.left j)
        (R.secondFactorImageStd F i ⟶ R.secondFactorImageStd F j)
        (R.transformedImagePairingStd g F i j) :=
  ⟨IsTensorPairing.of_equiv (R.secondFactorImageHomLinearEquiv F i j).symm
      (R.transformedTermHomModelEquiv g F i j) fun a c => by
        rw [← transformedTermHomModelEquiv_transformedImagePairingStd_of,
          LinearEquiv.apply_symm_apply],
    IsTensorPairing.of_equiv (R.secondFactorImageHomLinearEquiv F i j)
      (R.transformedTermHomModelEquiv g F i j).symm fun a c => by
        rw [← transformedTermHomModelEquiv_transformedImagePairingStd_of,
          AddEquiv.symm_apply_apply]⟩

end DiagonalResolution

end AlgebraicGeometry

end
