module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit

/-!
# The projection formula for higher direct images along an invertible module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝒢` be an `𝒪_X`-module
on the small étale site and let `ℳ` be an invertible `𝒪_Y`-module. Then

`R^q f_*(𝒢 ⊗_{𝒪_X} f^*ℳ) ≅ (R^q f_*𝒢) ⊗_{𝒪_Y} ℳ` for every `q`,

naturally in `𝒢`. This is the higher-direct-image clause of Stacks 01E8 for an invertible
module, on the small étale sites of algebraic spaces, at the module universe of the structure
rings. It is the projection formula the proof of Stacks 0EDJ applies, to the twists of `i_*𝒪_Z`
by the pulled-back invertible modules.

## Main definitions

* `Stacks.ProjectionFormula.adjunctionTensorRightNatTrans`: the abstract projection formula map
  `R G ⊗ H ⟶ R (G ⊗ L H)` of `CategoryTheory.adjunctionTensorMap`, as a natural transformation in
  `G`.
* `AlgebraicGeometry.Space.tensorRightModules`: tensoring an `𝒪_Z`-module on the right by a fixed
  module, as an endofunctor of the `𝒪_Z`-modules.
* `AlgebraicGeometry.Space.pushforwardTensorRightIso`: the projection formula in degree zero,
  `(- ⊗ f^*ℳ) ⋙ f_* ≅ f_* ⋙ (- ⊗ ℳ)`.
* `AlgebraicGeometry.Space.rightDerivedModulePushforwardTensorRightIso`: **the projection formula
  in every degree**, `R^q f_*(𝒢 ⊗ f^*ℳ) ≅ (R^q f_*𝒢) ⊗ ℳ`.

## Twists

The intersection number of Stacks 0EDF is the mixed finite difference of the Euler
characteristics of the twists `AlgebraicGeometry.Space.twistedModule` at the indicator functions
of the subsets `T ⊆ {1, …, d}`, where only the exponents `0` and `1` occur. For those twists:

* `AlgebraicGeometry.Space.rightDerivedTwistedModuleIndicatorIso`:
  `R^q f_*(𝒩 ⊗ ⨂_{j ∈ T} f^*L_j) ≅ R^q f_*𝒩 ⊗ ⨂_{j ∈ T} L_j`;
* `AlgebraicGeometry.Space.pushforwardTwistedModuleIndicatorIso`: the same for `f_*`;
* `AlgebraicGeometry.Space.twistedModuleCongrIndicatorIso`: such a twist depends on the family of
  invertible modules only up to isomorphism;
* `AlgebraicGeometry.Space.twistedModuleMapIso`: the bookkeeping behind both, that a functor
  carrying each twisting step carries the iterated twist.

## The route

This is the route of `StacksFrontier/AlgebraicGeometry/ProjectionFormula/HigherDirectImage.lean` for
schemes, run on the small étale ringed topoi. In degree zero the canonical map
`f_*𝒢 ⊗ ℳ ⟶ f_*(𝒢 ⊗ f^*ℳ)` is `CategoryTheory.adjunctionTensorMap` for the adjunction
`f^* ⊣ f_*` (`AlgebraicGeometry.Space.modulePullbackAdjunction`) and the comparison
`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` of Stacks 03EL (`Stacks.SheafOfModules.pullbackTensorIso`); it is an
isomorphism by the abstract projection formula
`Stacks.ProjectionFormula.isIso_adjunctionTensorMap`, because tensoring by `ℳ` and by `f^*ℳ`
are equivalences (Stacks 01CS; `f^*ℳ` is invertible by Stacks 0B8P). In higher degree an
equivalence is exact and preserves injective objects, so
`CategoryTheory.Functor.rightDerivedCompIsoOfPreservesInjectiveObjects`,
`CategoryTheory.Functor.rightDerivedIsoOfNatIso` and `CategoryTheory.Functor.rightDerivedCompIso`
carry the degree-zero isomorphism to every `R^q`.

## Implementation notes

The tensor product is that of the small étale ringed topos, which is the spelling
`Stacks.SheafOfModules.pullbackTensorIso` is stated in; it is definitionally the tensor product of
the small étale ringed site used by `AlgebraicGeometry.Space.twistStep`, and
`AlgebraicGeometry.Space.rightDerivedModulePushforwardSheafTensorIso` restates the result at that
spelling. The instances of finite products on the categories of modules are given explicitly:
instance search for them otherwise stops at an undetermined universe of a Grothendieck abelian
category of sheaves of modules.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0EDJ](https://stacks.math.columbia.edu/tag/0EDJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.ProjectionFormula

open scoped CategoryTheory.Prod

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract projection formula map as a natural transformation** in the object `G` of
`D`: its component at `G` is `CategoryTheory.adjunctionTensorMap`,
`A (R G, H) ⟶ R (B (G, L H))`, and its naturality is the naturality of that map in its first
argument, the identity of `H` being carried by `L` to the identity of `L H`. -/
def adjunctionTensorRightNatTrans (H : C) :
    R ⋙ tensorRightOf A H ⟶ tensorRightOf B (L.obj H) ⋙ R where
  app G := adjunctionTensorMap adj A B α G H
  naturality G G' g := by
    have h := adjunctionTensorMap_natural adj A B α g (𝟙 H)
    rw [L.map_id] at h
    exact h

/-- The components of the abstract projection formula transformation are isomorphisms under the
hypotheses of `Stacks.ProjectionFormula.isIso_adjunctionTensorMap`. -/
theorem isIso_adjunctionTensorRightNatTrans_app (H : C) (G : D)
    [(tensorRightOf A H).IsEquivalence] [(tensorRightOf B (L.obj H)).IsEquivalence]
    (hα : ∀ M : C, IsIso (α.app (M, H))) :
    IsIso ((adjunctionTensorRightNatTrans adj A B α H).app G) :=
  isIso_adjunctionTensorMap adj A B α G H hα

end Stacks.ProjectionFormula

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **Tensoring on the right by a fixed module**, `𝒢 ↦ 𝒢 ⊗_{𝒪_Z} ℳ`, as an endofunctor of the
`𝒪_Z`-modules on the small étale site of `Z`, for the tensor product of the small étale ringed
topos. -/
noncomputable abbrev tensorRightModules (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2 :=
  Stacks.ProjectionFormula.tensorRightOf
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS Z).O)) M

/-- **Tensoring on the right by an invertible module is an equivalence** (Stacks 01CS): this is
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible`, read through
`CategoryTheory.Functor.tensorRightOfUncurryIso`. -/
instance isEquivalence_tensorRightModules (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property M] :
    (tensorRightModules B S hS Z M).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _
    (Functor.tensorRightOfUncurryIso
      (Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Z.1 Z.2).O) M).symm
    (@Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible
      (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
      (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
      _ _ M hM)

/-- **Stacks 0B8P** at the spelling `Stacks.SheafOfModules.IsInvertible` of the twists: the inverse
image of an invertible `𝒪_Y`-module is invertible. This is
`AlgebraicGeometry.Space.isInvertible_modulePullback_obj`, stated for the other class, between the
two conversions `Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry` and
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`. -/
theorem stacksIsInvertible_modulePullback_obj (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property M] :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      ((modulePullback B S hS f).obj M) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_modulePullback_obj B S hS f M
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hM))

/-- **The projection formula map** `f_*𝒢 ⊗ ℳ ⟶ f_*(𝒢 ⊗ f^*ℳ)` of Stacks 0FZE, as a natural
transformation in `𝒢`: `Stacks.ProjectionFormula.adjunctionTensorRightNatTrans` for the
adjunction `f^* ⊣ f_*` and the comparison of Stacks 03EL. -/
noncomputable def pushforwardTensorRightNatTrans (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    modulePushforward B S hS f ⋙ tensorRightModules B S hS Y M ⟶
      tensorRightModules B S hS X ((modulePullback B S hS f).obj M) ⋙ modulePushforward B S hS f :=
  Stacks.ProjectionFormula.adjunctionTensorRightNatTrans (modulePullbackAdjunction B S hS f) _ _
    (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).hom M

/-- **The projection formula map is invertible for an invertible module**: tensoring by `ℳ` and
by `f^*ℳ` are equivalences and the comparison of Stacks 03EL is an isomorphism, so the abstract
projection formula `Stacks.ProjectionFormula.isIso_adjunctionTensorMap` applies. -/
theorem isIso_pushforwardTensorRightNatTrans_app (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property M]
    (G : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((pushforwardTensorRightNatTrans B S hS f M).app G) := by
  have := stacksIsInvertible_modulePullback_obj B S hS f M
  exact @Stacks.ProjectionFormula.isIso_adjunctionTensorRightNatTrans_app _ _ _ _ _ _
    (modulePullbackAdjunction B S hS f) _ _ _ M G
    (inferInstance : (tensorRightModules B S hS Y M).IsEquivalence)
    (inferInstance : (tensorRightModules B S hS X ((modulePullback B S hS f).obj M)).IsEquivalence)
    (fun T => Iso.isIso_hom ((Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS f)).app (T, M)))

/-- **The projection formula in degree zero for an invertible module**, naturally in the module on
the source: `(- ⊗ f^*ℳ) ⋙ f_* ≅ f_* ⋙ (- ⊗ ℳ)`. -/
noncomputable def pushforwardTensorRightIso (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property M] :
    tensorRightModules B S hS X ((modulePullback B S hS f).obj M) ⋙ modulePushforward B S hS f ≅
      modulePushforward B S hS f ⋙ tensorRightModules B S hS Y M :=
  haveI := isIso_pushforwardTensorRightNatTrans_app B S hS f M
  haveI := NatIso.isIso_of_isIso_app (pushforwardTensorRightNatTrans B S hS f M)
  (asIso (pushforwardTensorRightNatTrans B S hS f M)).symm

/-! ### Twists -/

section Twists

/-- A twisting step at exponent `1` is tensoring by the module itself: the first tensor power is
identified with the module by `Stacks.SheafOfModules.Invertible.tensorPowerOneIso`. -/
noncomputable def twistStepOneIso (Z : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS Z.1 Z.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property L]
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    twistStep B S hS Z.1 Z.2 L 1 M ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj
        M).obj L :=
  @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
    (structurePresheaf B S hS Z.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
    _ _ _ _ _ _ (Iso.refl M)
    (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
      (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
      _ _ L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL))

/-- **Carrying a twist along a functor which carries each twisting step.** If `Φ` takes the
twisting step by `L' j` at exponent `n j` to the twisting step by `L j`, for every index `j` and
every module, then it takes the twist `M ⊗ L'₁^{⊗ n₁} ⊗ ⋯` to the twist
`Φ M ⊗ L₁^{⊗ n₁} ⊗ ⋯`. -/
noncomputable def twistedModuleMapIso {d : ℕ}
    (Φ : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
    (L' : Fin d → Modules.{u, u} B S hS X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        (L' j)]
    (L : Fin d → Modules.{u, u} B S hS Y.1 Y.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
        (L j)]
    (n : Fin d → ℤ)
    (step : ∀ (j : Fin d) (N : Modules.{u, u} B S hS X.1 X.2),
      Φ.obj (twistStep B S hS X.1 X.2 (L' j) (n j) N) ≅
        twistStep B S hS Y.1 Y.2 (L j) (n j) (Φ.obj N))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    Φ.obj (twistedModule B S hS X.1 X.2 M L' n) ≅
      twistedModule B S hS Y.1 Y.2 (Φ.obj M) L n := by
  suffices h : ∀ (l : List (Fin d)) (M : Modules.{u, u} B S hS X.1 X.2),
      Nonempty (Φ.obj (l.foldl (fun N j => twistStep B S hS X.1 X.2 (L' j) (n j) N) M) ≅
        l.foldl (fun N j => twistStep B S hS Y.1 Y.2 (L j) (n j) N) (Φ.obj M)) from
    (h (List.finRange d) M).some
  intro l
  induction l with
  | nil => exact fun M => ⟨Iso.refl _⟩
  | cons j t ih =>
    exact fun M => ⟨(ih (twistStep B S hS X.1 X.2 (L' j) (n j) M)).some ≪≫
      foldlTwistStepIso B S hS Y.1 Y.2 L n t (step j M)⟩

/-- A twisting step at exponent `0` or `1` depends on the invertible module only up to
isomorphism. -/
noncomputable def twistStepCongrIndicatorIso (Z : AlgebraicSpaces B S hS)
    {L L' : Modules.{u, u} B S hS Z.1 Z.2}
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property L]
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property L']
    (e : L ≅ L') (b : Prop) [Decidable b] (N : Modules.{u, u} B S hS Z.1 Z.2) :
    twistStep B S hS Z.1 Z.2 L (if b then 1 else 0) N ≅
      twistStep B S hS Z.1 Z.2 L' (if b then 1 else 0) N := by
  by_cases h : b
  · simp only [if_pos h]
    exact twistStepOneIso B S hS Z L N ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj
        N).mapIso e ≪≫ (twistStepOneIso B S hS Z L' N).symm
  · simp only [if_neg h]
    exact twistStepZeroIso B S hS Z.1 Z.2 L N ≪≫ (twistStepZeroIso B S hS Z.1 Z.2 L' N).symm

/-- A twist at an indicator exponent depends on the family of invertible modules only up to
isomorphism. -/
noncomputable def twistedModuleCongrIndicatorIso {d : ℕ} (Z : AlgebraicSpaces B S hS)
    {L L' : Fin d → Modules.{u, u} B S hS Z.1 Z.2}
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
        (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
        (L' j)]
    (e : ∀ j, L j ≅ L' j) (T : Finset (Fin d)) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    twistedModule B S hS Z.1 Z.2 N L (fun j => if j ∈ T then 1 else 0) ≅
      twistedModule B S hS Z.1 Z.2 N L' (fun j => if j ∈ T then 1 else 0) :=
  twistedModuleMapIso B S hS (X := Z) (Y := Z) (𝟭 _) L L' _
    (fun j N => twistStepCongrIndicatorIso B S hS Z (e j) (j ∈ T) N) N

end Twists

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **Stacks 01E8, the higher direct image clause, for an invertible module on the small étale
sites of algebraic spaces.** For a morphism `f : X ⟶ Y` of algebraic spaces, an `𝒪_X`-module `𝒢`
and an invertible `𝒪_Y`-module `ℳ`,

`R^q f_*(𝒢 ⊗ f^*ℳ) ≅ (R^q f_*𝒢) ⊗ ℳ` for every `q`.

Tensoring by `f^*ℳ` is an exact equivalence, so it preserves injective objects and may be pulled
out of the right derived functors of `f_*` on the source side; tensoring by `ℳ` is exact, so it
may be pulled out on the target side; and in degree zero the two composites agree by
`AlgebraicGeometry.Space.pushforwardTensorRightIso`. -/
noncomputable def rightDerivedModulePushforwardTensorRightIso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property M]
    (G : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS f).rightDerived q).obj
        ((tensorRightModules B S hS X ((modulePullback B S hS f).obj M)).obj G) ≅
      (tensorRightModules B S hS Y M).obj
        (((modulePushforward B S hS f).rightDerived q).obj G) := by
  intro _
  haveI := stacksIsInvertible_modulePullback_obj B S hS f M (hM := hM)
  haveI : Limits.HasFiniteProducts (Modules.{u, u} B S hS X.1 X.2) := Abelian.has_finite_products
  haveI : Limits.HasFiniteProducts (Modules.{u, u} B S hS Y.1 Y.2) := Abelian.has_finite_products
  haveI : Limits.HasBinaryProducts (Modules.{u, u} B S hS X.1 X.2) :=
    Limits.hasLimitsOfShape_discrete (C := Modules.{u, u} B S hS X.1 X.2) Limits.WalkingPair
  haveI : Limits.HasBinaryProducts (Modules.{u, u} B S hS Y.1 Y.2) :=
    Limits.hasLimitsOfShape_discrete (C := Modules.{u, u} B S hS Y.1 Y.2) Limits.WalkingPair
  haveI : (tensorRightModules B S hS X ((modulePullback B S hS f).obj M)).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (tensorRightModules B S hS Y M).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI :
      (tensorRightModules B S hS X ((modulePullback B S hS f).obj M)).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_isEquivalence
  haveI : (tensorRightModules B S hS X ((modulePullback B S hS f).obj M)).PreservesHomology :=
    inferInstance
  haveI : (tensorRightModules B S hS Y M).PreservesHomology := inferInstance
  have e1 := (Functor.rightDerivedCompIsoOfPreservesInjectiveObjects
      (tensorRightModules B S hS X ((modulePullback B S hS f).obj M))
      (modulePushforward B S hS f) G q).symm
  have e2 :=
    (Functor.rightDerivedIsoOfNatIso (@pushforwardTensorRightIso B S hS _ _ f M hM) q).app G
  have e3 := (Functor.rightDerivedCompIso (modulePushforward B S hS f)
    (tensorRightModules B S hS Y M) q).app G
  exact e1 ≪≫ e2 ≪≫ e3

/-- **Stacks 01E8 for an invertible module, at the spelling of the twists.** The isomorphism
`AlgebraicGeometry.Space.rightDerivedModulePushforwardTensorRightIso`, with the tensor products
written as those of the small étale ringed sites, as in `AlgebraicGeometry.Space.twistStep`. -/
noncomputable def rightDerivedModulePushforwardSheafTensorIso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property M]
    (G : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS f).rightDerived q).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
          G).obj ((modulePullback B S hS f).obj M)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
          (((modulePushforward B S hS f).rightDerived q).obj G)).obj M :=
  rightDerivedModulePushforwardTensorRightIso B S hS f M G q

/-- **The projection formula for one twisting step at exponent `0` or `1`, in every degree.** -/
noncomputable def rightDerivedTwistStepIndicatorIso (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property L]
    (b : Prop) [Decidable b] (N : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    letI := stacksIsInvertible_modulePullback_obj B S hS f L (hM := hL)
    ((modulePushforward B S hS f).rightDerived q).obj
        (twistStep B S hS X.1 X.2 ((modulePullback B S hS f).obj L) (if b then 1 else 0) N) ≅
      twistStep B S hS Y.1 Y.2 L (if b then 1 else 0)
        (((modulePushforward B S hS f).rightDerived q).obj N) := by
  intro _
  haveI := stacksIsInvertible_modulePullback_obj B S hS f L (hM := hL)
  by_cases h : b
  · simp only [if_pos h]
    exact ((modulePushforward B S hS f).rightDerived q).mapIso
        (twistStepOneIso B S hS X ((modulePullback B S hS f).obj L) N) ≪≫
      @rightDerivedModulePushforwardSheafTensorIso B S hS _ _ f L hL N q ≪≫
      (twistStepOneIso B S hS Y L _).symm
  · simp only [if_neg h]
    exact ((modulePushforward B S hS f).rightDerived q).mapIso
        (twistStepZeroIso B S hS X.1 X.2 ((modulePullback B S hS f).obj L) N) ≪≫
      (twistStepZeroIso B S hS Y.1 Y.2 L _).symm

/-- **The projection formula for a twist at an indicator exponent, in every degree.** For a
morphism `f : X ⟶ Y`, invertible `𝒪_Y`-modules `L₁, …, L_d`, a subset `T ⊆ {1, …, d}` and an
`𝒪_X`-module `𝒩`,

`R^q f_*(𝒩 ⊗ ⨂_{j ∈ T} f^*L_j) ≅ R^q f_*𝒩 ⊗ ⨂_{j ∈ T} L_j`,

the twists being those of `AlgebraicGeometry.Space.twistedModule` at the indicator function of
`T`. These are the twists the intersection number of Stacks 0EDF is defined from. -/
noncomputable def rightDerivedTwistedModuleIndicatorIso {d : ℕ} (f : X ⟶ Y)
    (L : Fin d → Modules.{u, u} B S hS Y.1 Y.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
        (L j)]
    (T : Finset (Fin d)) (N : Modules.{u, u} B S hS X.1 X.2) (q : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    letI := fun j => stacksIsInvertible_modulePullback_obj B S hS f (L j) (hM := hL j)
    ((modulePushforward B S hS f).rightDerived q).obj
        (twistedModule B S hS X.1 X.2 N (fun j => (modulePullback B S hS f).obj (L j))
          fun j => if j ∈ T then 1 else 0) ≅
      twistedModule B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived q).obj N) L
        fun j => if j ∈ T then 1 else 0 := by
  intro _
  haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS f (L j) (hM := hL j)
  exact twistedModuleMapIso B S hS ((modulePushforward B S hS f).rightDerived q) _ L _
    (fun j N => rightDerivedTwistStepIndicatorIso B S hS f (L j) (j ∈ T) N q) N

/-- **The projection formula for one twisting step at exponent `0` or `1`, in degree zero.** -/
noncomputable def pushforwardTwistStepIndicatorIso (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property L]
    (b : Prop) [Decidable b] (N : Modules.{u, u} B S hS X.1 X.2) :
    letI := stacksIsInvertible_modulePullback_obj B S hS f L (hM := hL)
    (modulePushforward B S hS f).obj
        (twistStep B S hS X.1 X.2 ((modulePullback B S hS f).obj L) (if b then 1 else 0) N) ≅
      twistStep B S hS Y.1 Y.2 L (if b then 1 else 0) ((modulePushforward B S hS f).obj N) := by
  haveI := stacksIsInvertible_modulePullback_obj B S hS f L (hM := hL)
  by_cases h : b
  · simp only [if_pos h]
    exact (modulePushforward B S hS f).mapIso
        (twistStepOneIso B S hS X ((modulePullback B S hS f).obj L) N) ≪≫
      (@pushforwardTensorRightIso B S hS _ _ f L hL).app N ≪≫
      (twistStepOneIso B S hS Y L _).symm
  · simp only [if_neg h]
    exact (modulePushforward B S hS f).mapIso
        (twistStepZeroIso B S hS X.1 X.2 ((modulePullback B S hS f).obj L) N) ≪≫
      (twistStepZeroIso B S hS Y.1 Y.2 L _).symm

/-- **The projection formula for a twist at an indicator exponent, in degree zero**:
`f_*(𝒩 ⊗ ⨂_{j ∈ T} f^*L_j) ≅ f_*𝒩 ⊗ ⨂_{j ∈ T} L_j`. -/
noncomputable def pushforwardTwistedModuleIndicatorIso {d : ℕ} (f : X ⟶ Y)
    (L : Fin d → Modules.{u, u} B S hS Y.1 Y.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
        (L j)]
    (T : Finset (Fin d)) (N : Modules.{u, u} B S hS X.1 X.2) :
    letI := fun j => stacksIsInvertible_modulePullback_obj B S hS f (L j) (hM := hL j)
    (modulePushforward B S hS f).obj
        (twistedModule B S hS X.1 X.2 N (fun j => (modulePullback B S hS f).obj (L j))
          fun j => if j ∈ T then 1 else 0) ≅
      twistedModule B S hS Y.1 Y.2 ((modulePushforward B S hS f).obj N) L
        fun j => if j ∈ T then 1 else 0 := by
  haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS f (L j) (hM := hL j)
  exact twistedModuleMapIso B S hS (modulePushforward B S hS f) _ L _
    (fun j N => pushforwardTwistStepIndicatorIso B S hS f (L j) (j ∈ T) N) N

end Derived

end AlgebraicGeometry.Space

end
