module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatRestrictionEssentiallySmall
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits

/-!
# Tor amplitude over a subring, from local tensor models

Let `(C, O)` be a ringed site whose objects form a type in a universe `c` of their own while its
morphisms and sections lie in one universe `u`, with `C` essentially `u`-small, and let
`φ : O' ⟶ O` be a morphism of sheaves of rings on the same site.  Let `K` be an object of
`D(O)`, read in `D(O')` by restriction of scalars along `φ`, and `G` a complex of `O`-modules
which is bounded and whose terms are flat as `O'`-modules.  Suppose that on the members of a
family covering the final object, either `K|_W ≅ Q(Tot(P ⊗ G|_W))` with `P` strictly perfect and
concentrated in a fixed range `[-N, N]`, or `K|_W` has vanishing cohomology.  Then `K`, as an
object of `D(O')`, has Tor amplitude in `[g₀ - N, g₁ + N]`.

## Main definitions

* `OfEssentiallySmall.restrictScalarsOverIso`: restriction of scalars commutes with restriction
  to a slice.
* `OfEssentiallySmall.derivedRestrictionRestrictScalarsIso`: restriction of scalars commutes with
  derived restriction to a slice.

## Main results

* `OfEssentiallySmall.hasTorAmplitude_restrictScalars_of_flatModels`: Tor amplitude over `O'`
  from local models by bounded complexes of `O'`-flat modules.
* `OfEssentiallySmall.hasTorAmplitude_restrictScalars_of_models`: Tor amplitude over `O'` from
  local models `Tot(P ⊗ G|_W)`.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u c d

namespace Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)
open Stacks.SheafOfModules.Tensor (tensorComplex ringSheaf)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section RestrictScalarsOver

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  {R' R : Sheaf J RingCat.{u}} (φ : R' ⟶ R) (W : C)

/-- Restriction of scalars along the slice of `φ` over `W`. -/
abbrev sliceRestrictScalars :
    _root_.SheafOfModules.{u} (R.over W) ⥤ _root_.SheafOfModules.{u} (R'.over W) :=
  _root_.SheafOfModules.restrictScalars ((J.overPullback RingCat.{u} W).map φ)

/-- **Restriction of scalars commutes with restriction to a slice.**  Both composites are the
identity on underlying presheaves of abelian groups. -/
def restrictScalarsOverIso :
    _root_.SheafOfModules.restrictScalars φ ⋙ _root_.SheafOfModules.overFunctor.{u} R' W ≅
      _root_.SheafOfModules.overFunctor.{u} R W ⋙ sliceRestrictScalars φ W :=
  NatIso.ofComponents
    (fun M => (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl)))
    (fun f => by ext; rfl)

/-- Restriction of scalars followed by the forgetful functor to abelian sheaves is the forgetful
functor. -/
def restrictScalarsCompToSheafIso' {O₁ O₂ : Sheaf J RingCat.{u}} (ψ : O₁ ⟶ O₂) :
    _root_.SheafOfModules.restrictScalars.{u} ψ ⋙ _root_.SheafOfModules.toSheaf.{u} O₁ ≅
      _root_.SheafOfModules.toSheaf.{u} O₂ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- Restriction of scalars along a morphism of sheaves of rings preserves finite limits. -/
theorem preservesFiniteLimits_restrictScalars' {O₁ O₂ : Sheaf J RingCat.{u}} (ψ : O₁ ⟶ O₂) :
    PreservesFiniteLimits (_root_.SheafOfModules.restrictScalars.{u} ψ) :=
  let : PreservesFiniteLimits
      (_root_.SheafOfModules.restrictScalars.{u} ψ ⋙ _root_.SheafOfModules.toSheaf.{u} O₁) :=
    preservesFiniteLimits_of_natIso (restrictScalarsCompToSheafIso' ψ).symm
  preservesFiniteLimits_of_reflects_of_preserves _ (_root_.SheafOfModules.toSheaf.{u} O₁)

/-- Restriction of scalars along a morphism of sheaves of rings preserves finite colimits. -/
theorem preservesFiniteColimits_restrictScalars' {O₁ O₂ : Sheaf J RingCat.{u}} (ψ : O₁ ⟶ O₂) :
    PreservesFiniteColimits (_root_.SheafOfModules.restrictScalars.{u} ψ) :=
  let : PreservesFiniteColimits
      (_root_.SheafOfModules.restrictScalars.{u} ψ ⋙ _root_.SheafOfModules.toSheaf.{u} O₁) :=
    preservesFiniteColimits_of_natIso (restrictScalarsCompToSheafIso' ψ).symm
  preservesFiniteColimits_of_reflects_of_preserves _ (_root_.SheafOfModules.toSheaf.{u} O₁)

end RestrictScalarsOver

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A ringed site with the structure sheaf replaced by another sheaf of rings on the same site. -/
abbrev withStructureSheaf (O' : Sheaf X.J CommRingCat.{u}) : RingedSite.{c, u, u} :=
  ⟨X.C, X.J, O'⟩

variable (O' : Sheaf X.J CommRingCat.{u})
  (φ : ringSheaf O' ⟶ ringSheaf X.O)

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
  preservesFiniteLimits_restriction preservesFiniteColimits_restriction

/-- Restriction to a slice preserves finite limits, over the new structure sheaf. -/
local instance preservesFiniteLimits_restrictionB (U : X.C) :
    PreservesFiniteLimits (restriction (withStructureSheaf X O') U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction to a slice preserves finite colimits, over the new structure sheaf. -/
local instance preservesFiniteColimits_restrictionB (U : X.C) :
    PreservesFiniteColimits (restriction (withStructureSheaf X O') U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} O').Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} O').obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} (withStructureSheaf X O')) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} O') (ComplexShape.up ℤ)]
  [∀ U : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u}
    ((withStructureSheaf X O').over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u}
      ((withStructureSheaf X O').over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex
      (RingedSite.Modules.{max c u, u, u} ((withStructureSheaf X O').over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor ((withStructureSheaf X O').over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]
  [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} (withStructureSheaf X O'))]
  [hSliceDerivedB : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} ((withStructureSheaf X O').over U))]

attribute [local instance] sliceHasDerivedCategory sliceHasDerivedCategory''

/-- The derived category of the modules on a slice, over the new structure sheaf. -/
local instance sliceHasDerivedCategoryC (U : X.C) :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} O').over U)) :=
  hSliceDerivedB U

/-- **Restriction of scalars commutes with derived restriction to a slice.** -/
def derivedRestrictionRestrictScalarsIso (W : X.C) (K : RingedSite.DerivedModules.{c, u, u, d} X) :
    (RingedSite.derivedRestriction.{c, u, u, d} (withStructureSheaf X O') W).obj
        ((_root_.SheafOfModules.restrictScalars φ).mapDerivedCategory.obj K) ≅
      (sliceRestrictScalars φ W).mapDerivedCategory.obj
        ((RingedSite.derivedRestriction.{c, u, u, d} X W).obj K) := by
  let F₁ := _root_.SheafOfModules.restrictScalars.{u} φ
  let F₂ := _root_.SheafOfModules.overFunctor.{u} (ringSheaf O') W
  let G₁ := _root_.SheafOfModules.overFunctor.{u} (ringSheaf X.O) W
  let G₂ := sliceRestrictScalars φ W
  haveI : F₁.Additive := ⟨by intros; ext; rfl⟩
  haveI : PreservesFiniteLimits F₁ := preservesFiniteLimits_restrictScalars' φ
  haveI : PreservesFiniteColimits F₁ := preservesFiniteColimits_restrictScalars' φ
  haveI : F₂.Additive := ⟨by intros; ext; rfl⟩
  haveI : PreservesFiniteLimits F₂ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  haveI : PreservesFiniteColimits F₂ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  haveI : G₁.Additive := ⟨by intros; ext; rfl⟩
  haveI : PreservesFiniteLimits G₁ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  haveI : PreservesFiniteColimits G₁ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  haveI : G₂.Additive := ⟨by intros; ext; rfl⟩
  haveI : PreservesFiniteLimits G₂ := preservesFiniteLimits_restrictScalars' (J := X.J.over W)
    ((X.J.overPullback RingCat.{u} W).map φ)
  haveI : PreservesFiniteColimits G₂ := preservesFiniteColimits_restrictScalars' (J := X.J.over W)
    ((X.J.overPullback RingCat.{u} W).map φ)
  haveI : PreservesFiniteLimits (F₁ ⋙ F₂) := comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (F₁ ⋙ F₂) := comp_preservesFiniteColimits _ _
  haveI : PreservesFiniteLimits (G₁ ⋙ G₂) := comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (G₁ ⋙ G₂) := comp_preservesFiniteColimits _ _
  exact ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F₁ F₂).app K).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F₁ ⋙ F₂) (G₁ ⋙ G₂)
      (restrictScalarsOverIso φ W)).app K ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G₁ G₂).app K

section ColimitsRestrictScalars

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]

/-- Restriction of scalars along a morphism of sheaves of rings preserves coproducts indexed by
a type in the module universe: the underlying abelian sheaf is unchanged, and forgetting the module
structure preserves and reflects them. -/
theorem preservesColimitsOfShape_discrete_restrictScalars' {O₁ O₂ : Sheaf J RingCat.{u}}
    (ψ : O₁ ⟶ O₂) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (_root_.SheafOfModules.restrictScalars.{u} ψ) := by
  have : HasCoproducts.{u} (PresheafOfModules.{u} O₁.obj) :=
    fun _ => PresheafOfModules.hasColimitsOfShape _ _
  have : HasCoproducts.{u} (PresheafOfModules.{u} O₂.obj) :=
    fun _ => PresheafOfModules.hasColimitsOfShape _ _
  have h₁ : PreservesColimitsOfShape (Discrete I) (_root_.SheafOfModules.toSheaf.{u} O₂) :=
    _root_.SheafOfModules.preservesColimitsOfShape_toSheaf O₂
  have h₂ : PreservesColimitsOfShape (Discrete I) (_root_.SheafOfModules.toSheaf.{u} O₁) :=
    _root_.SheafOfModules.preservesColimitsOfShape_toSheaf O₁
  have : PreservesColimitsOfShape (Discrete I)
      (_root_.SheafOfModules.restrictScalars.{u} ψ ⋙ _root_.SheafOfModules.toSheaf.{u} O₁) :=
    preservesColimitsOfShape_of_natIso (restrictScalarsCompToSheafIso' ψ).symm
  have : HasColimitsOfShape (Discrete I) (_root_.SheafOfModules.{u} O₁) :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      O₁ (Discrete I)
  have : ReflectsColimitsOfShape (Discrete I) (_root_.SheafOfModules.toSheaf.{u} O₁) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (_root_.SheafOfModules.toSheaf.{u} O₁)

/-- **Flatness after restriction of scalars is a property closed under isomorphisms and finite
coproducts.** -/
theorem isClosedUnderFiniteCoproducts_isFlat_restrictScalars
    {O₁ : Sheaf J CommRingCat.{u}} {O₂ : Sheaf J RingCat.{u}} (ψ : ringSheaf O₁ ⟶ O₂) :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (fun M : _root_.SheafOfModules.{u} O₂ => AlgebraicGeometry.SheafOfModules.IsFlat
        (O := O₁) ((_root_.SheafOfModules.restrictScalars.{u} ψ).obj M)) := by
  refine ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape.{u}
    fun I _ => ⟨fun M ⟨h⟩ => ?_⟩
  have : HasCoproducts.{u} (PresheafOfModules.{u} O₂.obj) :=
    fun _ => PresheafOfModules.hasColimitsOfShape _ _
  let f : I → _root_.SheafOfModules.{u} O₂ := fun j => h.diag.obj ⟨j⟩
  let e : M ≅ ∐ f :=
    h.isColimit.coconePointUniqueUpToIso (colimit.isColimit h.diag) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := h.diag))
  have := preservesColimitsOfShape_discrete_restrictScalars' ψ I
  let e' : (_root_.SheafOfModules.restrictScalars.{u} ψ).obj M ≅
      ∐ (fun j => (_root_.SheafOfModules.restrictScalars.{u} ψ).obj (f j)) :=
    (_root_.SheafOfModules.restrictScalars.{u} ψ).mapIso e ≪≫
      PreservesCoproduct.iso (_root_.SheafOfModules.restrictScalars.{u} ψ) f
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso O₁ e'.symm
    (Stacks.SheafOfModules.FlatColimits.isFlat_coproduct_finite O₁ _
      fun j => h.prop_diag_obj ⟨j⟩)

end ColimitsRestrictScalars

/-- Restriction of scalars along the slice of `φ` over `W`, with its source spelled as the modules
over the slice `X.O.over W` of the structure sheaf. -/
abbrev sliceRestrictScalarsOver (W : X.C) :
    SliceModules X W ⥤ _root_.SheafOfModules.{u} (ringSheaf (O'.over W)) :=
  sliceRestrictScalars φ W

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)] in
/-- **Tor amplitude over a subring from local flat models.**  If on the members `W` of a family
covering the final object either `K|_W ≅ Q(L)` for a complex `L` concentrated in `[a, b]` whose
terms are flat over `O'|_W`, or `K|_W = 0`, then `K`, read in `D(O')`, has Tor amplitude in
`[a, b]`. -/
theorem hasTorAmplitude_restrictScalars_of_flatModels
    (T' : DerivedTensorProduct.{c, u, u, d} (withStructureSheaf X O'))
    (K : RingedSite.DerivedModules.{c, u, u, d} X) (a b : ℤ)
    {I : Type*} (W : I → X.C) (hW : X.J.CoversTop W)
    (hmod : ∀ i, (∃ L : CochainComplex (SliceModules X (W i)) ℤ,
        (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat (O := O'.over (W i))
          ((sliceRestrictScalarsOver X O' φ (W i)).obj (L.X n))) ∧
        (∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n)) ∧
        Nonempty ((RingedSite.derivedRestriction.{c, u, u, d} X (W i)).obj K ≅
          DerivedCategory.Q.obj L)) ∨
      IsZero ((RingedSite.derivedRestriction.{c, u, u, d} X (W i)).obj K)) :
    HasTorAmplitude T' ((_root_.SheafOfModules.restrictScalars φ).mapDerivedCategory.obj K)
      a b := by
  refine hasTorAmplitude_of_coversTop (withStructureSheaf X O') T'
    (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{max c u, u, d}
      ((withStructureSheaf X O').over U)) hW _ _ _ fun i => ?_
  refine HasTorAmplitude.of_iso (derivedRestrictionRestrictScalarsIso X O' φ (W i) K).symm ?_
  let G₂ := sliceRestrictScalars φ (W i)
  have : PreservesFiniteLimits G₂ := preservesFiniteLimits_restrictScalars'
    (J := X.J.over (W i)) ((X.J.overPullback RingCat.{u} (W i)).map φ)
  have : PreservesFiniteColimits G₂ := preservesFiniteColimits_restrictScalars'
    (J := X.J.over (W i)) ((X.J.overPullback RingCat.{u} (W i)).map φ)
  rcases hmod i with ⟨L, hflat, hLz, ⟨e⟩⟩ | hz
  · let G₂' : SliceModules X (W i) ⥤ _root_.SheafOfModules.{u} (ringSheaf (O'.over (W i))) := G₂
    have : G₂'.Additive := ⟨by intros; ext; rfl⟩
    refine hasTorAmplitude_of_flatRepresentative _ _ _ _
      ((G₂'.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) hflat (fun n hn => ?_)
      ((G₂.mapDerivedCategoryFactors.app L).symm ≪≫ G₂.mapDerivedCategory.mapIso e.symm)
    exact G₂'.map_isZero (hLz n (by simp only [Set.mem_Icc, not_and_or, not_le] at hn; omega))
  · let Z : CochainComplex (RingedSite.Modules.{max c u, u, u}
        ((withStructureSheaf X O').over (W i))) ℤ := HomologicalComplex.zero
    have hZ : IsZero Z := HomologicalComplex.isZero_zero
    refine hasTorAmplitude_of_flatRepresentative _ _ _ _ Z
      (fun n => Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero _
        ((HomologicalComplex.eval _ _ n).map_isZero hZ))
      (fun n _ => (HomologicalComplex.eval _ _ n).map_isZero hZ)
      (IsZero.iso (DerivedCategory.Q.map_isZero hZ) (G₂.mapDerivedCategory.map_isZero hz))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **Tor amplitude over a subring from local tensor models.**  If on the members `W` of a family
covering the final object either `K|_W ≅ Q(Tot(P ⊗ G|_W))` with `P` strictly perfect and
concentrated in `[-N, N]`, or `K|_W = 0`, and if `G` is concentrated in `[g₀, g₁]` with terms flat
over `O'`, then `K`, read in `D(O')`, has Tor amplitude in `[g₀ - N, g₁ + N]`. -/
theorem hasTorAmplitude_restrictScalars_of_models
    (T' : DerivedTensorProduct.{c, u, u, d} (withStructureSheaf X O'))
    (K : RingedSite.DerivedModules.{c, u, u, d} X)
    (G : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ) (N : ℕ) (g₀ g₁ : ℤ)
    (hGb : ∀ q : ℤ, q < g₀ ∨ g₁ < q → IsZero (G.X q))
    (hGflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat (O := O')
      ((_root_.SheafOfModules.restrictScalars φ).obj (G.X q)))
    {I : Type*} (W : I → X.C) (hW : X.J.CoversTop W)
    (hmod : ∀ i, (∃ P : CochainComplex (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (W i))) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (W i)) P ∧
        (∀ n : ℤ, n < -N ∨ (N : ℤ) < n → IsZero (P.X n)) ∧
        Nonempty ((RingedSite.derivedRestriction.{c, u, u, d} X (W i)).obj K ≅
          DerivedCategory.Q.obj (restrictTensorComplex X (W i) P G))) ∨
      IsZero ((RingedSite.derivedRestriction.{c, u, u, d} X (W i)).obj K)) :
    HasTorAmplitude T' ((_root_.SheafOfModules.restrictScalars φ).mapDerivedCategory.obj K)
      (-N + g₀) (N + g₁) := by
  refine hasTorAmplitude_restrictScalars_of_flatModels X O' φ T' K _ _ W hW fun i => ?_
  rcases hmod i with ⟨P₀, hP, hPz, ⟨e⟩⟩ | hz
  · refine Or.inl ⟨restrictTensorComplex X (W i) P₀ G, fun n => ?_, fun n hn => ?_, ⟨e⟩⟩
    · let P : CochainComplex (SliceModules X (W i)) ℤ := P₀
      let G₂' := sliceRestrictScalarsOver X O' φ (W i)
      let Q : ObjectProperty (SliceModules X (W i)) :=
        fun M => AlgebraicGeometry.SheafOfModules.IsFlat (O := O'.over (W i)) (G₂'.obj M)
      have : Q.IsClosedUnderIsomorphisms := ⟨fun e h =>
        Stacks.SheafOfModules.FlatRetract.isFlat_of_iso (O'.over (W i)) (G₂'.mapIso e) h⟩
      have : Q.IsClosedUnderFiniteCoproducts :=
        isClosedUnderFiniteCoproducts_isFlat_restrictScalars (J := X.J.over (W i))
          (O₁ := O'.over (W i)) (O₂ := Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over (W i)))
          ((X.J.overPullback RingCat.{u} (W i)).map φ)
      have hGq : ∀ q : ℤ, Q (((restrictionComplex X (W i)).obj G).X q) := fun q =>
        Stacks.SheafOfModules.FlatRetract.isFlat_of_iso (O'.over (W i))
          ((restrictScalarsOverIso φ (W i)).app (G.X q))
          (Stacks.SheafOfModules.FlatRestriction.OfEssentiallySmall.isFlat_over_of_essentiallySmall
            (withStructureSheaf X O') (W i) _ (hGflat q))
      exact Stacks.TotalComplexTerms.prop_mapBifunctor_X
        (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over (W i)))
        P ((restrictionComplex X (W i)).obj G) Q (-N) N
        hPz n
        (fun p q _ => Stacks.SheafOfModules.prop_sheafTensor_of_isDirectSummandOfFiniteFree
          (X.O.over (W i)) Q
          (fun i' r hir hN => Stacks.SheafOfModules.FlatRetract.isFlat_of_retract (O'.over (W i))
            (G₂'.map i') (G₂'.map r) (by rw [← G₂'.map_comp, hir, G₂'.map_id]) hN)
          (P.X p) _ (hP.termDirectSummand p) (hGq q))
    · let P : CochainComplex (SliceModules X (W i)) ℤ := P₀
      exact Stacks.TotalComplexTerms.isZero_mapBifunctor_X_of_bounds
        (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over (W i)))
        P ((restrictionComplex X (W i)).obj G) (-N) N g₀ g₁ hPz
          (fun q hq => (restriction X (W i)).map_isZero (hGb q hq)) n
          (by omega)
  · exact Or.inr hz

end Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall

end
