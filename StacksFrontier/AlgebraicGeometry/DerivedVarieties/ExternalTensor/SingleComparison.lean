module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Terms
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafStalk
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# The derived external tensor product of two modules placed in degree zero

Let `k` be a field, let `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` be schemes over `k` with
projections `p` and `q` from `W = X ×_k Y`, let `ℱ` be an `𝒪_X`-module and `𝒢` a quasi-coherent
`𝒪_Y`-module.  This file proves

`Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ≅ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]`,

that is, that the derived external tensor product of [Stacks, Tag 0G0A] of two modules placed in
degree zero is their external tensor product of [Stacks, Tag 0G46] placed in degree zero.  Over a
field no flatness hypothesis is needed beyond quasi-coherence of `𝒢`: every module on a scheme
over a field is flat over the base, which is what makes `G ↦ p^*G ⊗ q^*𝒢` exact.

## Main definitions

* `AlgebraicGeometry.derivedPullbackComplexIso` and
  `AlgebraicGeometry.derivedPullbackKFlatIso`: `Lh^*(QK) ≅ Q(h^*K)` for a complex on which the
  derived-pullback comparison of [Stacks, Tag 06YJ] is invertible, in particular for a K-flat
  complex.
* `AlgebraicGeometry.flatResQIso`: the chosen K-flat resolution of `ℱ[0]` is `ℱ[0]` in the
  derived category.
* `AlgebraicGeometry.derivedPullbackSingleIsoOfFlat`: `Lh^*(ℳ[0]) ≅ (h^*ℳ)[0]` for a flat
  morphism of schemes `h`.
* `AlgebraicGeometry.boxTensorFunctor`: the functor `G ↦ p^*G ⊗_{𝒪_W} N` from `𝒪_Z`-modules to
  `𝒪_W`-modules, for `p : W ⟶ Z` and `N` an `𝒪_W`-module.
* `AlgebraicGeometry.pulledBackFlatRes`: the chosen K-flat resolution of `ℱ[0]`, pulled back
  along `p`.

## Main results

* `AlgebraicGeometry.isFlatOver_of_field`: **every module on a scheme over a field is flat over
  the base**, the stalks of `Spec k` being fields.
* `AlgebraicGeometry.isFlat_of_flat` and
  `AlgebraicGeometry.quasiIso_mapHomologicalComplex_of_flat`: a flat morphism of schemes is flat
  as a morphism of ringed spaces, and its degreewise pullback carries quasi-isomorphisms to
  quasi-isomorphisms.
* `AlgebraicGeometry.kFlat_pulledBackFlatRes`: the pulled-back resolution is K-flat, by
  [Stacks, Tag 06YC].
* `AlgebraicGeometry.preservesHomology_boxTensorFunctor`: `G ↦ p^*G ⊗ N` preserves homology when
  `N` is flat over the target of `p`.  This is [Stacks, Tag 0GMU].
* `AlgebraicGeometry.boxTotalSingleIso`: `Tot(p^*K ⊗ N[0])` is `G ↦ p^*G ⊗ N` applied degreewise
  to `K`.
* `AlgebraicGeometry.derivedExternalTensorSingleIso`: **the comparison**,
  `Lp^*ℱ[0] ⊗^𝐋 Lq^*𝒢[0] ≅ (p^*ℱ ⊗ q^*𝒢)[0]`.

## Implementation notes

*The shape of the argument, which is the source's.*  Write `K` for the chosen K-flat resolution
of `ℱ[0]` on `X`, `N = q^*𝒢`, and `E` for the functor `G ↦ p^*G ⊗_{𝒪_W} N`.  Four steps:

1. `Lp^*ℱ[0] ≅ Q(p^*K)`, because `K` is K-flat and the pullback of a K-flat complex is K-flat;
2. `Lq^*𝒢[0] ≅ N[0]`, because `q` is flat — it is the base change of `f : X ⟶ Spec k`, and every
   morphism to the spectrum of a field is flat;
3. `Q(p^*K) ⊗^𝐋 N[0] ≅ Q(Tot(p^*K ⊗ N[0]))`, the one-sided K-flat comparison of
   [Stacks, Tag 06YU], which needs K-flatness only of the left factor;
4. `Tot(p^*K ⊗ N[0]) = E(K)` degreewise, and `E` preserves homology because `N` is flat over `X`
   relative to `p`, so the augmentation `K ⟶ ℱ[0]` is carried to a quasi-isomorphism
   `E(K) ⟶ E(ℱ[0]) = (p^*ℱ ⊗ N)[0]`.

Step 4 is where quasi-coherence of `𝒢` is used: it is the hypothesis of [Stacks, Tag 01U8] that
transports flatness of `𝒢` over `Spec k` to flatness of `q^*𝒢` over `X` along `p`, and that is
the hypothesis of [Stacks, Tag 0GMU].

*No tag is registered here.*  Every tag the argument uses — 06YJ, 06YS, 06YC, 06YU, 0GMU, 01U8 —
is registered where it is proved; what is here is their composite at two modules in degree zero,
a component result of the Künneth formula of [Stacks, Tag 0BEF] and of the external-tensor
computations of [Stacks, Tag 0G0E], and carries no tag of its own.

*The model of the derived categories is a binder.*  Every statement below that mentions a
derived category takes its model as a `[CategoryTheory.HasDerivedCategory.{w} _]` binder, so the
comparison is available both at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and at
`CategoryTheory.HasDerivedCategory.standard`, which is the model the Fourier-Mukai vocabulary
and [Stacks, Tag 0B54] are available at and hence the model a display of [Stacks, Tag 0G0E]
needs.  `HasDerivedCategory` carries the localized category as data, so two models are two
different types and no transport between them is possible; a free binder is the only crossing.
This is why `Stacks.Duality.derivedPullback` and `Stacks.Duality.derivedTensor` are not used:
neither declares a `HasDerivedCategory` binder, so instance search bakes the locally small model
into each of their types.  What is named instead is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the ringed-space functor
the first abbreviates, and
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the ringed-site bifunctor the
second abbreviates; both take their models as arguments.

*Why the spellings are named.*  The category of `𝒪_W`-modules has three spellings in play —
`AlgebraicGeometry.Scheme.Modules`, which is an opaque definition,
`CategoryTheory.SheafOfModules (structureSheafRing W.toRingedSpace)`, which the ringed-space
pullback is stated at, and `CategoryTheory.SheafOfModules
(Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)`, which the tensor bifunctor of
[Stacks, Tag 06YM] is stated at.  They are equal by `rfl`, so unification sees through them, but
the discrimination tree instance search is keyed into does not: an additivity instance proved at
one spelling is not retrieved at another.  `TensorModules` names the third, which everything
touching the tensor product is stated at, and the additivity and total-complex instances are
named rather than synthesized for the same reason.  For the same reason the model binder, which
is written at the `Scheme.Modules` spelling because that is the spelling of the statements, is
carried to the other two by the two `local instance` bridges below: a binder at one spelling is
not found at another, so without them the ringed-space pullback and the ringed-site tensor
product would each synthesize the locally small model afresh and the binder would be inert.

## References

* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe w w₁ w₂ w₃ u

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

namespace AlgebraicGeometry

/-- Modules on a scheme, at the spelling `Stacks.SheafOfModules.Tensor.ringSheaf` that the
tensor bifunctor of [Stacks, Tag 06YM] is stated at.  It is `W.Modules` by `rfl`. -/
abbrev TensorModules (W : Scheme.{u}) : Type (u + 1) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)

/-! ### Instances named rather than synthesized -/

-- The model binder, written at the `Scheme.Modules` spelling, carried to the ringed-space and
-- ringed-site spellings that the derived pullback and the derived tensor product are stated at.
-- Without these two instances a binder at one spelling is not found at another and the two
-- functors synthesize the locally small model afresh.
attribute [local instance 10000] hasDerivedCategoryRingedSpace hasDerivedCategoryTensorSite

/-- The tensor product of modules on a scheme is additive in its second variable. -/
local instance sheafTensorAdditiveScheme (W : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).Additive :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive W.sheaf

/-- Tensoring with a fixed module on a scheme is additive. -/
local instance sheafTensorObjAdditiveScheme (W : Scheme.{u}) (M : W.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj M).Additive :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive W.sheaf M

/-- Degreewise pullback of modules along a morphism of schemes is additive. -/
local instance modulePullbackAdditiveScheme {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (modulePullback h.toLRSHom.toShHom).Additive :=
  modulePullback_additive _

/-- The total tensor complexes on a scheme exist. -/
local instance hasMapBifunctorScheme (W : Scheme.{u})
    (K L : CochainComplex (TensorModules W) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology W) W.sheaf K L

/-- The tensor product is additive in its first variable. -/
local instance sheafTensorFlipObjAdditive (W : Scheme.{u}) (N : TensorModules W) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N).Additive where
  map_add {_ _ f g} := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).map (f + g)).app N = _
    rw [(Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).map_add]
    rfl

/-- The tensor product bifunctor preserves zero morphisms. -/
local instance sheafTensorPreservesZeroScheme (W : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)

/-! ### Flatness over a field -/

/-- **Every module on a scheme over a field is flat over the base.**  For `f : X ⟶ Spec k` with
`k` a field, every `𝒪_X`-module is flat over `Spec k` in the sense of [Stacks, Tag 08KT]: the
stalk of `Spec k` at the image of a point is a field, hence semisimple, so every module over it
is projective and therefore flat. -/
theorem isFlatOver_of_field (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) :
    AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F := by
  intro x
  let : Field ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) :=
    (isField_stalk_Spec_field k (f.base x)).toField
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x
  let : Module ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) M :=
    Module.compHom M (f.toLRSHom.toShHom.hom.stalkMap x).hom
  exact inferInstanceAs
    (Module.Flat ((Spec (CommRingCat.of k)).presheaf.stalk (f.base x)) M)

/-! ### The derived pullback of a complex -/

/-- **`Lh^*(QK) ≅ Q(h^*K)` for a complex on which the comparison of [Stacks, Tag 06YJ] is
invertible.**  The derived pullback of the image of a complex in the derived category is the
image of its degreewise pullback, as soon as the canonical comparison `Lh^* ⟶ h^*` is invertible
there; the other three factors are the identifications of the two localization functors and the
compatibility of degreewise pullback with the homotopy category, all invertible outright. -/
def derivedPullbackComplexIso {X Y : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules]
    [HasDerivedCategory.{w₂} Y.Modules] (h : X ⟶ Y) (K : CochainComplex Y.Modules ℤ)
    (hcomp : IsIso ((derivedPullbackComparison h.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj K))) :
    (derivedPullback h.toLRSHom.toShHom).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (derivedPullback h.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso Y.Modules).app K).symm ≪≫
    @asIso _ _ _ _ _ hcomp ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePullback h.toLRSHom.toShHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso X.Modules).app _

/-- **`Lh^*(QK) ≅ Q(h^*K)` for a K-flat complex**, unconditionally: the K-flat complexes are a
resolving datum for `h^*`, so the comparison of [Stacks, Tag 06YJ] is invertible on them. -/
def derivedPullbackKFlatIso {X Y : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules]
    [HasDerivedCategory.{w₂} Y.Modules] (h : X ⟶ Y) (K : CochainComplex Y.Modules ℤ)
    (hK : Stacks.Duality.KFlatComplex K) :
    (derivedPullback h.toLRSHom.toShHom).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  derivedPullbackComplexIso h K
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      h.toLRSHom.toShHom K hK)

/-- **The chosen K-flat resolution of `ℱ[0]` is `ℱ[0]` in the derived category**: its
augmentation is a quasi-isomorphism by [Stacks, Tag 06YS], hence invertible after `Q`. -/
def flatResQIso (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules] (F : X.Modules) :
    DerivedCategory.Q.obj (TorFormula.flatRes X F) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj F :=
  haveI : IsIso (DerivedCategory.Q.map (TorFormula.flatResHom X F)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := X.Modules) _).2 inferInstance
  asIso (DerivedCategory.Q.map (TorFormula.flatResHom X F)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F).symm

/-- A flat morphism of schemes is flat as a morphism of ringed spaces: both predicates are
flatness of every stalk map. -/
theorem isFlat_of_flat {X Y : Scheme.{u}} (h : X ⟶ Y) [Flat h] :
    AlgebraicGeometry.IsFlat h.toLRSHom.toShHom :=
  fun x => (Flat.iff_flat_stalkMap h).mp inferInstance x

/-- **Degreewise pullback along a flat morphism carries quasi-isomorphisms to
quasi-isomorphisms**, because it preserves homology. -/
theorem quasiIso_mapHomologicalComplex_of_flat {X Y : Scheme.{u}} (h : X ⟶ Y) [Flat h]
    {K L : CochainComplex Y.Modules ℤ} (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) :=
  @HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _
    φ (modulePullback h.toLRSHom.toShHom) (modulePullbackAdditiveScheme h)
    (preservesHomology_modulePullback_of_isFlat _ (isFlat_of_flat h)) _ _ _ _ inferInstance

/-- **`Lh^*(ℳ[0]) ≅ (h^*ℳ)[0]` for a flat morphism of schemes.**  The chosen K-flat resolution
of `ℳ[0]` computes the derived pullback, and its degreewise pullback is still a resolution of
`(h^*ℳ)[0]` because `h^*` is exact. -/
def derivedPullbackSingleIsoOfFlat {X Y : Scheme.{u}} [HasDerivedCategory.{w₁} X.Modules]
    [HasDerivedCategory.{w₂} Y.Modules] (h : X ⟶ Y) [Flat h] (M : Y.Modules) :
    (derivedPullback h.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj M) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback h).obj M) :=
  letI hq := quasiIso_mapHomologicalComplex_of_flat h (TorFormula.flatResHom Y M)
  (derivedPullback h.toLRSHom.toShHom).mapIso (flatResQIso Y M).symm ≪≫
    derivedPullbackKFlatIso h (TorFormula.flatRes Y M) (TorFormula.flatRes_kFlat Y M) ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map
      (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (TorFormula.flatResHom Y M)))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (C := X.Modules) _).2 hq) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback h.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm

/-! ### The functor `G ↦ p^*G ⊗ N` -/

/-- The functor `G ↦ p^*G ⊗_{𝒪_W} N` from `𝒪_Z`-modules to `𝒪_W`-modules, for `p : W ⟶ Z` and
`N` an `𝒪_W`-module.  Its source and target are spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, the spelling the tensor bifunctor of [Stacks, Tag
06YM] is stated at. -/
def boxTensorFunctor {W Z : Scheme.{u}} (p : W ⟶ Z) (N : TensorModules W) :
    TensorModules Z ⥤ TensorModules W :=
  modulePullback p.toLRSHom.toShHom ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N

/-- Degreewise pullback, at the `ringSheaf` spelling of the two categories of modules. -/
local instance modulePullbackAdditiveRingSheaf {W Z : Scheme.{u}} (p : W ⟶ Z) :
    (modulePullback p.toLRSHom.toShHom :
      TensorModules Z ⥤ TensorModules W).Additive :=
  modulePullback_additive _

/-- `G ↦ p^*G ⊗ N` is additive. -/
local instance boxTensorFunctorAdditive {W Z : Scheme.{u}} (p : W ⟶ Z) (N : TensorModules W) :
    (boxTensorFunctor p N).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _
    (modulePullback p.toLRSHom.toShHom : TensorModules Z ⥤ TensorModules W)
    (modulePullbackAdditiveRingSheaf p) _ _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).flip.obj N)
    (sheafTensorFlipObjAdditive W N)

/-- `G ↦ p^*G ⊗ N` is the functor of [Stacks, Tag 0GMU].

The two are the *same* functor: `Stacks.SheafOfModules.pullbackTensorFunctor` is defined as
`modulePullback ⋙ (Tensor.sheafTensor _).flip.obj N`, which is `boxTensorFunctor` on the nose,
so the comparison is the identity. -/
def boxTensorFunctorIso {W Z : Scheme.{u}} (p : W ⟶ Z) (N : TensorModules W) :
    boxTensorFunctor p N ≅ Stacks.SheafOfModules.pullbackTensorFunctor p.toLRSHom.toShHom N :=
  Iso.refl _

/-- `G ↦ p^*G ⊗ N` preserves homology when `N` is flat over `Z`. -/
theorem preservesHomology_boxTensorFunctor {W Z : Scheme.{u}} (p : W ⟶ Z)
    (N : TensorModules W)
    (hN : AlgebraicGeometry.IsFlatOver p.toLRSHom.toShHom N) :
    (boxTensorFunctor p N).PreservesHomology := by
  have hE := (exactFunctor_iff
      (Stacks.SheafOfModules.pullbackTensorFunctor p.toLRSHom.toShHom N)).mp
    (Stacks.SheafOfModules.pullbackTensorFunctor_exact p.toLRSHom.toShHom N hN)
  have h3 : PreservesFiniteLimits (boxTensorFunctor p N) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (boxTensorFunctorIso p N).symm hE.1
  have h4 : PreservesFiniteColimits (boxTensorFunctor p N) :=
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (boxTensorFunctorIso p N).symm hE.2
  exact @Functor.preservesHomologyOfExact _ _ _ _ _ _ (boxTensorFunctor p N) _ h3 h4

/-! ### The comparison -/

/-- The chosen K-flat resolution of `F[0]`, pulled back along `p`. -/
abbrev pulledBackFlatRes {W X : Scheme.{u}} (p : W ⟶ X) (F : X.Modules) :
    CochainComplex (TensorModules W) ℤ :=
  ((modulePullback p.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (TorFormula.flatRes X F)

/-- **The pulled-back resolution is K-flat**, by [Stacks, Tag 06YC]. -/
theorem kFlat_pulledBackFlatRes {W X : Scheme.{u}} (p : W ⟶ X) (F : X.Modules) :
    Stacks.Duality.KFlatComplex (pulledBackFlatRes p F) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional p.toLRSHom.toShHom _
    (TorFormula.flatRes_kFlat X F)

/-- **`Lp^*(ℱ[0]) ≅ Q(p^*K)` for the chosen K-flat resolution `K` of `ℱ[0]`**: the resolution
computes `ℱ[0]` in the derived category, and being K-flat it computes the derived pullback. -/
def derivedPullbackSingleFlatResIso {W X : Scheme.{u}} [HasDerivedCategory.{w₁} W.Modules]
    [HasDerivedCategory.{w₂} X.Modules] (p : W ⟶ X) (F : X.Modules) :
    (derivedPullback p.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      DerivedCategory.Q.obj (pulledBackFlatRes p F) :=
  (derivedPullback p.toLRSHom.toShHom).mapIso (flatResQIso X F).symm ≪≫
    derivedPullbackKFlatIso p (TorFormula.flatRes X F) (TorFormula.flatRes_kFlat X F)

/-- **`Tot(p^*K ⊗ N[0])` is `G ↦ p^*G ⊗ N` applied degreewise to `K`.**  The second factor is
concentrated in degree zero, so the total complex of the tensor double complex has one summand
in each degree. -/
def boxTotalSingleIso {W X : Scheme.{u}} (p : W ⟶ X) (F : X.Modules) (N : TensorModules W) :
    HomologicalComplex.mapBifunctor (pulledBackFlatRes p F)
        ((CochainComplex.singleFunctor (TensorModules W) 0).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (ComplexShape.up ℤ) ≅
      ((boxTensorFunctor p N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (TorFormula.flatRes X F) :=
  HomologicalComplex.mapBifunctorSingleRightIso
    (Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf) (pulledBackFlatRes p F) N

/-- **`Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ≅ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]`**, for two schemes over a field
and `𝒢` quasi-coherent: the derived external tensor product of two modules placed in degree zero
is their external tensor product placed in degree zero.

The four steps are the four isomorphisms of the module docstring: the K-flat resolution computes
`Lp^*`, flatness of `q` computes `Lq^*`, the one-sided K-flat comparison of [Stacks, Tag 06YU]
computes the derived tensor product, and the exactness of `G ↦ p^*G ⊗ q^*𝒢` — which is
[Stacks, Tag 0GMU], and which is where quasi-coherence of `𝒢` enters — turns the augmentation of
the resolution into a quasi-isomorphism after applying that functor. -/
def derivedExternalTensorSingleIso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} Y.Modules]
    [HasDerivedCategory.{w₃} (pullback f g).Modules] (F : X.Modules) (G : Y.Modules)
    [G.IsQuasicoherent] :
    derivedExternalTensorAt f g ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (DerivedCategory.singleFunctor (pullback f g).Modules 0).obj
        (externalTensorProduct f g F G) :=
  letI N : TensorModules (pullback f g) :=
    (Scheme.Modules.pullback (pullback.snd f g)).obj G
  letI hGqc : SheafOfModules.IsQuasicoherent
      (R := structureSheafRing Y.toRingedSpace) G :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G)
  letI hN : AlgebraicGeometry.IsFlatOver (pullback.fst f g).toLRSHom.toShHom N :=
    @modulePullback_isFlatOver _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback f g).flip G hGqc
      (isFlatOver_of_field k g G)
  letI hPH := preservesHomology_boxTensorFunctor (pullback.fst f g) N hN
  letI hq : QuasiIso (((boxTensorFunctor (pullback.fst f g) N).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (TorFormula.flatResHom X F)) :=
    @HomologicalComplex.quasiIso_map_of_preservesHomology _ _ _ _ _ _ _ _ _ _
      (TorFormula.flatResHom X F) (boxTensorFunctor (pullback.fst f g) N)
      (boxTensorFunctorAdditive (pullback.fst f g) N) hPH _ _ _ _ inferInstance
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (pullback f g).sheaf).mapIso
      (derivedPullbackSingleFlatResIso (pullback.fst f g) F)).app _ ≪≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (pullback f g).sheaf).obj _).mapIso
      (derivedPullbackSingleIsoOfFlat (pullback.snd f g) G ≪≫
        (DerivedCategory.singleFunctorIsoCompQ (pullback f g).Modules 0).app N) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (pullback f g).sheaf).comparisonLeft (pulledBackFlatRes (pullback.fst f g) F)
      ((CochainComplex.singleFunctor (TensorModules (pullback f g)) 0).obj N)
      (kFlat_pulledBackFlatRes (pullback.fst f g) F) ≪≫
    DerivedCategory.Q.mapIso (boxTotalSingleIso (pullback.fst f g) F N) ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map
        (((boxTensorFunctor (pullback.fst f g) N).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (TorFormula.flatResHom X F)))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso
        (C := TensorModules (pullback f g)) _).2 hq) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (boxTensorFunctor (pullback.fst f g) N) (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (pullback f g).Modules 0).app _).symm

end AlgebraicGeometry

end
