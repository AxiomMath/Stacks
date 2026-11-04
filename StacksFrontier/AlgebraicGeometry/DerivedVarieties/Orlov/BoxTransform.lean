module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal

/-!
# The integral transform of a derived external product

Let `X` and `Y` be schemes over `S`. For `E ∈ D(𝒪_X)` and `B ∈ D(𝒪_Y)` write
`E ⊠ B = L pr_1^* E ⊗^𝐋 L pr_2^* B` on `X ×_S Y`. For `𝓕 ∈ D(𝒪_X)` the integral transform of
`E ⊠ B` is

`R pr_{2,*}(L pr_1^* 𝓕 ⊗^𝐋 (E ⊠ B)) ≅ L g^* R f_*(𝓕 ⊗^𝐋 E) ⊗^𝐋 B`

as soon as `f` is quasi-compact, quasi-separated and flat and the three objects have
quasi-coherent cohomology: associativity of `⊗^𝐋`, the compatibility of derived pullback with the
derived tensor product ([Stacks, Tag 079U]), the projection formula along `pr_2`
([Stacks, Tag 08EU]) and flat base change ([Stacks, Tag 08IB]). The comparison is written as a
morphism from the right-hand side, natural in `E` and in `B`, which is how the computations of
[Stacks, Section 0G07] consume it.

## Main definitions

* `AlgebraicGeometry.derivedBox`: the derived external product `E ⊠ B` on `X ×_S Y`.
* `AlgebraicGeometry.boxTransformMap`: the comparison morphism
  `L g^* R f_*(𝓕 ⊗^𝐋 E) ⊗^𝐋 B ⟶ R pr_{2,*}(L pr_1^* 𝓕 ⊗^𝐋 (E ⊠ B))`.

## Main results

* `AlgebraicGeometry.boxTransformMap_naturality_left`,
  `AlgebraicGeometry.boxTransformMap_naturality_right`: naturality in `E` and in `B`.
* `AlgebraicGeometry.isIso_boxTransformMap`: the comparison is an isomorphism.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The derived external product** `E ⊠ B = L pr_1^* E ⊗^𝐋 L pr_2^* B` on `X ×_S Y`. -/
def derivedBox (E : DerivedCategory X.Modules) (B : DerivedCategory Y.Modules) :
    DerivedCategory (pullback f g).Modules :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
    ((fourierMukaiPullback f g).obj E)).obj ((dpull (pullback.snd f g)).obj B)

/-- The morphism of derived external products induced by a morphism in the first factor. -/
def derivedBoxMapLeft {E E' : DerivedCategory X.Modules} (a : E ⟶ E')
    (B : DerivedCategory Y.Modules) : derivedBox f g E B ⟶ derivedBox f g E' B :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
    ((fourierMukaiPullback f g).map a)).app ((dpull (pullback.snd f g)).obj B)

/-- The morphism of derived external products induced by a morphism in the second factor. -/
def derivedBoxMapRight (E : DerivedCategory X.Modules) {B B' : DerivedCategory Y.Modules}
    (b : B ⟶ B') : derivedBox f g E B ⟶ derivedBox f g E B' :=
  ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
    ((fourierMukaiPullback f g).obj E)).map ((dpull (pullback.snd f g)).map b)

/-- The integral transform `N ↦ R pr_{2,*}(L pr_1^* 𝓕 ⊗^𝐋 N)` with a fixed argument `𝓕`, as a
functor of the kernel `N`. -/
abbrev kernelIntegralTransform (𝓕 : DerivedCategory X.Modules) :
    DerivedCategory (pullback f g).Modules ⥤ DerivedCategory Y.Modules :=
  (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
    ((fourierMukaiPullback f g).obj 𝓕) ⋙ fourierMukaiPushforward f g

/-- The value `L g^* R f_*(𝓕 ⊗^𝐋 E) ⊗^𝐋 B` that the transform of `E ⊠ B` is compared with. -/
abbrev boxTransformTarget (𝓕 E : DerivedCategory X.Modules) (B : DerivedCategory Y.Modules) :
    DerivedCategory Y.Modules :=
  ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
    ((dpull g).obj ((dpush f).obj
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)))).obj B

/-- The square of ringed spaces underlying the cartesian square of `X ×_S Y`. -/
theorem pullback_condition_shHom :
    (pullback.fst f g).toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      (pullback.snd f g).toLRSHom.toShHom ≫ g.toLRSHom.toShHom :=
  shHom_comp_eq pullback.condition

/-- **The comparison morphism for the transform of a derived external product**:
`L g^* R f_*(𝓕 ⊗^𝐋 E) ⊗^𝐋 B ⟶ R pr_{2,*}(L pr_1^* 𝓕 ⊗^𝐋 (E ⊠ B))`, the composite of flat base
change, the projection formula along `pr_2`, the compatibility of `L pr_1^*` with `⊗^𝐋` and the
associator. -/
def boxTransformMap (𝓕 E : DerivedCategory X.Modules) (B : DerivedCategory Y.Modules) :
    boxTransformTarget f g 𝓕 E B ⟶ (kernelIntegralTransform f g 𝓕).obj (derivedBox f g E B) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).map
      ((dbaseChange (pullback.fst f g) (pullback.snd f g) f g (pullback_condition_shHom f g)).app
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E))).app B ≫
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      (pullback.snd f g).toLRSHom.toShHom
      ((fourierMukaiPullback f g).obj
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)) B ≫
    (fourierMukaiPushforward f g).map
      (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
            (pullback.fst f g).toLRSHom.toShHom).hom.app (𝓕, E))).app
          ((dpull (pullback.snd f g)).obj B)) ≫
    (fourierMukaiPushforward f g).map
        (α_ ((fourierMukaiPullback f g).obj 𝓕) ((fourierMukaiPullback f g).obj E)
          ((dpull (pullback.snd f g)).obj B)).hom

/-- The projection formula along `pr_2`, as a natural transformation in the second factor. -/
def projectionFormulaNatTransSnd (E₁ : DerivedCategory (pullback f g).Modules) :
    (derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((fourierMukaiPushforward f g).obj E₁) ⟶
      dpull (pullback.snd f g) ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj E₁ ⋙
          fourierMukaiPushforward f g where
  app B := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
    (pullback.snd f g).toLRSHom.toShHom E₁ B
  naturality _ _ b :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      (pullback.snd f g).toLRSHom.toShHom E₁ b

/-- The associator of the derived tensor product on `X ×_S Y`, as a natural transformation in
the third variable. -/
def derivedAssociatorNatTrans (A A' : DerivedCategory (pullback f g).Modules) :
    (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
        (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj A).obj A') ⟶
      (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj A' ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj A :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  { app := fun C => (α_ A A' C).hom
    naturality := fun _ _ c => associator_naturality_right A A' c }

/-- `boxTransformMap` as a natural transformation in the second factor. -/
def boxTransformNatTransRight (𝓕 E : DerivedCategory X.Modules) :
    (derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((dpull g).obj ((dpush f).obj
          (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E))) ⟶
      dpull (pullback.snd f g) ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
          ((fourierMukaiPullback f g).obj E) ⋙ kernelIntegralTransform f g 𝓕 :=
  (derivedTensorProductFunctor Y.toRingedSpace.sheaf).map
      ((dbaseChange (pullback.fst f g) (pullback.snd f g) f g (pullback_condition_shHom f g)).app
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)) ≫
    projectionFormulaNatTransSnd f g ((fourierMukaiPullback f g).obj
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)) ≫
    Functor.whiskerLeft (dpull (pullback.snd f g)) (Functor.whiskerRight
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).map
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
            (pullback.fst f g).toLRSHom.toShHom).hom.app (𝓕, E))) (fourierMukaiPushforward f g)) ≫
    Functor.whiskerLeft (dpull (pullback.snd f g)) (Functor.whiskerRight
        (derivedAssociatorNatTrans f g ((fourierMukaiPullback f g).obj 𝓕)
          ((fourierMukaiPullback f g).obj E)) (fourierMukaiPushforward f g))

/-- `boxTransformMap` is the component of `boxTransformNatTransRight`. -/
theorem boxTransformNatTransRight_app (𝓕 E : DerivedCategory X.Modules)
    (B : DerivedCategory Y.Modules) :
    (boxTransformNatTransRight f g 𝓕 E).app B = boxTransformMap f g 𝓕 E B :=
  rfl

/-- **Naturality of the comparison in the second factor.** -/
theorem boxTransformMap_naturality_right (𝓕 E : DerivedCategory X.Modules)
    {B B' : DerivedCategory Y.Modules} (b : B ⟶ B') :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((dpull g).obj ((dpush f).obj
          (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)))).map b ≫
      boxTransformMap f g 𝓕 E B' =
    boxTransformMap f g 𝓕 E B ≫ (kernelIntegralTransform f g 𝓕).map (derivedBoxMapRight f g E b) :=
  (boxTransformNatTransRight f g 𝓕 E).naturality b

/-- The projection formula along `pr_2`, as a natural transformation in the first factor. -/
def projectionFormulaNatTransFst (B : DerivedCategory Y.Modules) :
    fourierMukaiPushforward f g ⋙ (derivedTensorProductFunctor Y.toRingedSpace.sheaf).flip.obj B ⟶
      (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj
          ((dpull (pullback.snd f g)).obj B) ⋙ fourierMukaiPushforward f g where
  app E₁ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
    (pullback.snd f g).toLRSHom.toShHom E₁ B
  naturality _ _ e :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
      (pullback.snd f g).toLRSHom.toShHom e B

/-- The associator of the derived tensor product on `X ×_S Y`, as a natural transformation in
the middle variable. -/
def derivedAssociatorNatTransMid (A C : DerivedCategory (pullback f g).Modules) :
    (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj A ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj C ⟶
      (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj C ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj A :=
  letI := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  { app := fun E' => (α_ A E' C).hom
    naturality := fun _ _ e => associator_naturality_middle A e C }

/-- The uncurried bifunctor at a morphism whose first component is an identity. -/
theorem uncurry_obj_map_id_fst {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) (c : C) {d d' : D} (a : d ⟶ d') :
    (Functor.uncurry.obj T).map ((𝟙 c, a) : (c, d) ⟶ (c, d')) = (T.obj c).map a := by
  simp

/-- The same, after applying a functor to both arguments. -/
theorem prod_comp_uncurry_obj_map_id_fst {C C' E : Type*} [Category C] [Category C']
    [Category E] (G : C ⥤ C') (T : C' ⥤ C' ⥤ E) (c : C) {d d' : C} (a : d ⟶ d') :
    (G.prod G ⋙ Functor.uncurry.obj T).map ((𝟙 c, a) : (c, d) ⟶ (c, d')) =
      (T.obj (G.obj c)).map (G.map a) := by
  simp

/-- The compatibility of `L pr_1^*` with the derived tensor product ([Stacks, Tag 079U]), as a
natural transformation in the second variable. -/
def pullbackTensorNatTrans (𝓕 : DerivedCategory X.Modules) :
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕 ⋙ fourierMukaiPullback f g ⟶
      fourierMukaiPullback f g ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).obj
          ((fourierMukaiPullback f g).obj 𝓕) where
  app E := (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
    (pullback.fst f g).toLRSHom.toShHom).hom.app (𝓕, E)
  naturality E E' a := by
    have h := (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      (pullback.fst f g).toLRSHom.toShHom).hom.naturality (X := (𝓕, E)) (Y := (𝓕, E'))
        (𝟙 𝓕, a)
    exact (congrArg (· ≫ _) (congrArg (fourierMukaiPullback f g).map
        (uncurry_obj_map_id_fst
          (derivedTensorProductFunctor X.toRingedSpace.sheaf) 𝓕 a)).symm).trans
      (h.trans (congrArg (_ ≫ ·)
        (prod_comp_uncurry_obj_map_id_fst (fourierMukaiPullback f g)
          (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf) 𝓕 a)))

/-- `boxTransformMap` as a natural transformation in the first factor. -/
def boxTransformNatTransLeft (𝓕 : DerivedCategory X.Modules) (B : DerivedCategory Y.Modules) :
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕 ⋙ dpush f ⋙ dpull g ⋙
        (derivedTensorProductFunctor Y.toRingedSpace.sheaf).flip.obj B ⟶
      fourierMukaiPullback f g ⋙
        (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj
          ((dpull (pullback.snd f g)).obj B) ⋙ kernelIntegralTransform f g 𝓕 :=
  Functor.whiskerLeft ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕)
      (Functor.whiskerRight
        (dbaseChange (pullback.fst f g) (pullback.snd f g) f g (pullback_condition_shHom f g))
        ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).flip.obj B)) ≫
    Functor.whiskerLeft ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕 ⋙
        fourierMukaiPullback f g) (projectionFormulaNatTransFst f g B) ≫
    Functor.whiskerRight (pullbackTensorNatTrans f g 𝓕)
      ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj
          ((dpull (pullback.snd f g)).obj B) ⋙ fourierMukaiPushforward f g) ≫
    Functor.whiskerLeft (fourierMukaiPullback f g)
      (Functor.whiskerRight (derivedAssociatorNatTransMid f g ((fourierMukaiPullback f g).obj 𝓕)
        ((dpull (pullback.snd f g)).obj B)) (fourierMukaiPushforward f g))

/-- `boxTransformMap` is the component of `boxTransformNatTransLeft`. -/
theorem boxTransformNatTransLeft_app (𝓕 E : DerivedCategory X.Modules)
    (B : DerivedCategory Y.Modules) :
    (boxTransformNatTransLeft f g 𝓕 B).app E = boxTransformMap f g 𝓕 E B :=
  rfl

/-- **Naturality of the comparison in the first factor.** -/
theorem boxTransformMap_naturality_left (𝓕 : DerivedCategory X.Modules)
    {E E' : DerivedCategory X.Modules} (a : E ⟶ E') (B : DerivedCategory Y.Modules) :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).map
        ((dpull g).map ((dpush f).map
          (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).map a)))).app B ≫
      boxTransformMap f g 𝓕 E' B =
    boxTransformMap f g 𝓕 E B ≫
      (kernelIntegralTransform f g 𝓕).map (derivedBoxMapLeft f g a B) := by
  rw [← boxTransformNatTransLeft_app, ← boxTransformNatTransLeft_app]
  exact (boxTransformNatTransLeft f g 𝓕 B).naturality a

variable [QuasiCompact f] [QuasiSeparated f] [Flat f]

/-- Flat base change ([Stacks, Tag 08IB]) for the square of `X ×_S Y`. -/
theorem isIso_dbaseChange_app (M : DerivedCategory X.Modules) (hM : IsQCohAll M) :
    IsIso ((dbaseChange (pullback.fst f g) (pullback.snd f g) f g
      (pullback_condition_shHom f g)).app M) :=
  derivedBaseChangeIsIsoOnQuasicoherent _ _ f g (IsPullback.of_hasPullback f g)
    inferInstance inferInstance (torIndependent_of_flat f g) _ _ hM

/-- A bifunctor carries an isomorphism in its first variable to an isomorphism at every
object. -/
theorem isIso_app_map_of_isIso {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) {x y : C} (φ : x ⟶ y) [IsIso φ] (d : D) : IsIso ((T.map φ).app d) :=
  inferInstance

/-- Flat base change, tensored with a fixed object. -/
theorem isIso_tensor_dbaseChange_app (M : DerivedCategory X.Modules)
    (B : DerivedCategory Y.Modules) (hM : IsQCohAll M) :
    IsIso (((derivedTensorProductFunctor Y.toRingedSpace.sheaf).map
      ((dbaseChange (pullback.fst f g) (pullback.snd f g) f g
        (pullback_condition_shHom f g)).app M)).app B) := by
  have := isIso_dbaseChange_app f g M hM
  exact @isIso_app_map_of_isIso _ _ _ _ _ _ _ _ _ _ this B

omit [Flat f] in
/-- The projection formula ([Stacks, Tag 08EU]) along `pr_2`. -/
theorem isIso_projectionFormulaMap_snd (E₁ : DerivedCategory (pullback f g).Modules)
    (B : DerivedCategory Y.Modules) (hE₁ : IsQCohAll E₁) (hB : IsQCohAll B) :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      (pullback.snd f g).toLRSHom.toShHom E₁ B) :=
  projectionFormulaIsIsoOnQuasicoherent _ inferInstance inferInstance _ _ hE₁ hB

/-- **The transform of a derived external product**: for `f` quasi-compact, quasi-separated and
flat, and `𝓕`, `E`, `B` with quasi-coherent cohomology, the comparison
`L g^* R f_*(𝓕 ⊗^𝐋 E) ⊗^𝐋 B ⟶ R pr_{2,*}(L pr_1^* 𝓕 ⊗^𝐋 (E ⊠ B))` is an isomorphism. -/
theorem isIso_boxTransformMap (𝓕 E : DerivedCategory X.Modules) (B : DerivedCategory Y.Modules)
    (h𝓕 : IsQCohAll 𝓕) (hE : IsQCohAll E) (hB : IsQCohAll B) :
    IsIso (boxTransformMap f g 𝓕 E B) := by
  have hW : IsQCohAll (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E) :=
    isQCohAll_dtenR h𝓕 hE
  have h₁ := isIso_dbaseChange_app f g _ hW
  have h₂ := isIso_projectionFormulaMap_snd f g ((fourierMukaiPullback f g).obj
    (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E)) B
    (isQCohAll_dpull (pullback.fst f g) hW) hB
  let := Scheme.Modules.canonicalDerivedMonoidal (pullback f g)
  unfold boxTransformMap
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_))
  · exact isIso_tensor_dbaseChange_app f g _ B hW
  · exact ((fourierMukaiPushforward f g).mapIso
      (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).mapIso
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
            (pullback.fst f g).toLRSHom.toShHom).app (𝓕, E))).app
          ((dpull (pullback.snd f g)).obj B))).isIso_hom
  · exact ((fourierMukaiPushforward f g).mapIso
        (α_ ((fourierMukaiPullback f g).obj 𝓕) ((fourierMukaiPullback f g).obj E)
          ((dpull (pullback.snd f g)).obj B))).isIso_hom

end AlgebraicGeometry
