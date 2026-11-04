module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Exactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence

/-!
# The obstruction to lifting a map of modules across a first order thickening of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`. Let `F'`, `G'` be `O'`-modules and let `φ : i^*F' ⟶ i^*G'` be a map of their
pullbacks. This file produces a class

```
  o(φ) ∈ Ext¹_O(Li^*F', I·G')
```

whose vanishing is necessary and sufficient for `φ` to be the pullback of a map
`φ' : F' ⟶ G'` of `O'`-modules.

## Main definitions

* `Deformation.ToposThickening.derivedPushforwardMapDerivedCategoryIso`: when the degreewise
  direct image of modules is exact, the derived direct image is it.
* `Deformation.ToposThickening.derivedPushforwardShiftedSingleIso`: consequently
  `Ri_*(K[1]) ≅ (i_*K)[1]` for a module `K`.
* `Deformation.ToposThickening.idealProductDerivedPushforwardIso`: the instance of the previous
  isomorphism at the descended ideal product, which is where exactness comes from the
  thickening (Stacks 08M3).
* `Deformation.ToposThickening.moduleMapObstruction`: **Stacks 08MS**, the obstruction class
  together with its vanishing criterion.
* `Deformation.ToposThickening.moduleMapObstructionClass`: the class itself.

## Main results

* `Deformation.ToposThickening.singleδ_comp_eq_zero_iff`: for a short exact sequence of an
  abelian category, a map into its last term is killed by the connecting map of the associated
  distinguished triangle exactly when it factors through the middle term. This is what turns
  the ideal-product sequence into an obstruction.
* `Deformation.ToposThickening.moduleMapObstructionClass_eq_zero_iff`: **Stacks 08MS**, the
  vanishing criterion, read off the subtype.

## Implementation notes

The class is assembled from the short exact sequence
`0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0` of
`StacksFrontier/Deformation/ToposThickening/IdealProductSequence.lean`. The adjoint transpose of
`φ` is a map `F' ⟶ i_*i^*G'`, i.e. into the last term; composing with the connecting map of the
associated distinguished triangle gives a class in `Ext¹_{O'}(F', I·G')`, which vanishes
exactly when the transpose factors through `G'`, which is exactly when `φ` lifts. The source's
`Ext¹_O(Li^*F', I·G')` is that group read across the adjunction `Li^* ⊣ Ri_*`, for which
`Ri_*` of a module placed in degree `0`, shifted once, has to be identified with the shift of
its degreewise direct image — that is
`Deformation.ToposThickening.derivedPushforwardShiftedSingleIso`, and it is where exactness of
`i_*` (Stacks 08M3) is used.

`I·G'` appears in the source as an `O`-module; here it is named by its descent
`Deformation.ToposThickening.idealProductModule` along the thickening, whose direct image is
the sheaf submodule `I·G'` of `G'`. That descent is what makes the class live in an `Ext` group
over `O` rather than over `O'`.

The derived pullback is taken as an explicit argument
`Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback i` rather than assumed to exist by a
typeclass: that is the form in which Stacks 06YY is available on this branch, the existence of
`Li^*` not being discharged there. No hypothesis beyond the source's is thereby added — the
source's `Li^*` is this datum.

The identification of `Ri_*` with the degreewise direct image is the uniqueness of right
derived functors: `i_*` is exact, so its induced functor on derived categories inverts
quasi-isomorphisms and is therefore itself a right derived functor of the composite
`K(O) ⥤ D(O')` that `Ri_*` derives.

## References

* [Stacks Project, Tag 08MS](https://stacks.math.columbia.edu/tag/08MS)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  LeftDerivedPullback derivedPullbackPushforwardAdjunction)

attribute [local instance] HasDerivedCategory.standard

universe v u v' u' w

namespace Deformation.ToposThickening

/-! ### Connecting maps detect factorizations -/

/-- **In a distinguished triangle, the connecting morphism kills exactly the maps that factor
through the middle object.** -/
theorem triangle_mor₃_comp_eq_zero_iff {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] (T : Triangle D) (hT : T ∈ distTriang D) {P : D} (f : P ⟶ T.obj₃) :
    f ≫ T.mor₃ = 0 ↔ ∃ g : P ⟶ T.obj₂, g ≫ T.mor₂ = f := by
  refine ⟨fun h ↦ (T.coyoneda_exact₃ hT f h).imp fun _ hg ↦ hg.symm, ?_⟩
  rintro ⟨g, rfl⟩
  rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]

/-- **The connecting class of a short exact sequence detects factorizations.** For a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of an abelian category and a map `f : P ⟶ X₃`, the class
`f ≫ δ ∈ Ext¹(P, X₁)` vanishes exactly when `f` factors through `X₂`. -/
theorem singleδ_comp_eq_zero_iff {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {S : ShortComplex A} (hS : S.ShortExact) (P : A) (f : P ⟶ S.X₃) :
    (DerivedCategory.singleFunctor A 0).map f ≫ hS.singleδ = 0 ↔
      ∃ g : P ⟶ S.X₂, g ≫ S.g = f := by
  have h := triangle_mor₃_comp_eq_zero_iff hS.singleTriangle hS.singleTriangle_distinguished
    ((DerivedCategory.singleFunctor A 0).map f)
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective g
    exact ⟨g, (DerivedCategory.singleFunctor A 0).map_injective
      ((Functor.map_comp _ g S.g).trans hg)⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(DerivedCategory.singleFunctor A 0).map g, (Functor.map_comp _ _ _).symm⟩

section Exactness

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {i : RingedToposHom X Y}

/-- The degreewise direct image of modules along a first order thickening preserves finite
limits: a first order thickening is a closed immersion of ringed topoi, and the direct image of
modules along one is exact (Stacks 08M3). -/
theorem preservesFiniteLimits_pushforwardModules (hi : FirstOrderThickening i) :
    PreservesFiniteLimits i.pushforwardModules :=
  (ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).1

/-- The degreewise direct image of modules along a first order thickening preserves finite
colimits. -/
theorem preservesFiniteColimits_pushforwardModules (hi : FirstOrderThickening i) :
    PreservesFiniteColimits i.pushforwardModules :=
  (ClosedRingedImmersion.pushforwardModules_exact hi.closedRingedImmersion).2

end Exactness

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [UnivLE.{u, w}] [UnivLE.{v, w}]
  {i : RingedToposHom X Y}

/-! ### The derived direct image of a module -/

/-- **The derived direct image along a first order thickening is the degreewise direct image.**
The direct image of modules is exact (Stacks 08M3), so the functor it induces on derived
categories inverts quasi-isomorphisms and is a right derived functor of the same functor that
`Ri_*` derives; right derived functors are unique up to a canonical isomorphism. -/
noncomputable def derivedPushforwardMapDerivedCategoryIso (i : RingedToposHom X Y)
    [PreservesFiniteLimits i.pushforwardModules] [PreservesFiniteColimits i.pushforwardModules]
    [i.pushforwardModules.Additive] :
    derivedPushforward.{w, w, v, u, v', u'} i ≅ i.pushforwardModules.mapDerivedCategory := by
  set W := HomotopyCategory.quasiIso
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (ComplexShape.up ℤ) with hW
  have : i.pushforwardModules.mapDerivedCategory.IsRightDerivedFunctor
      i.pushforwardModules.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W _
      i.pushforwardModules.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedUnique _ _
    ((pushforwardOnHomotopy.{w, w, v, u, v', u'} i).totalRightDerivedUnit DerivedCategory.Qh W)
    i.pushforwardModules.mapDerivedCategoryFactorsh.inv W

/-- **`Ri_*(K[1]) ≅ (i_*K)[1]`** for a sheaf of modules `K` on the source: the derived direct
image is the degreewise one, which commutes with the shift and carries a module placed in
degree `0` to its direct image placed in degree `0`. -/
noncomputable def derivedPushforwardShiftedSingleIso (i : RingedToposHom X Y)
    [PreservesFiniteLimits i.pushforwardModules] [PreservesFiniteColimits i.pushforwardModules]
    [i.pushforwardModules.Additive]
    (K : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (derivedPushforward.{w, w, v, u, v', u'} i).obj
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).obj
            K)⟦(1 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
          (i.pushforwardModules.obj K))⟦(1 : ℤ)⟧) :=
  (derivedPushforwardMapDerivedCategoryIso i).app _ ≪≫
    (i.pushforwardModules.mapDerivedCategory.commShiftIso (1 : ℤ)).app _ ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso
        ((i.pushforwardModules.mapDerivedCategorySingleFunctor 0).app K)

/-! ### The obstruction class -/

variable (hi : FirstOrderThickening i) (d : LeftDerivedPullback i)
  (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
    (i.toRingedToposModulesHom.pullbackModules).obj G')

/-- The comparison `Ri_*((I·G')ˇ[1]) ≅ (I·G')[1]` used to read the connecting class of the
ideal-product sequence across the adjunction `Li^* ⊣ Ri_*`: the derived direct image of the
descended ideal product, shifted once, is the ideal product itself, shifted once. -/
noncomputable def idealProductDerivedPushforwardIso :
    (derivedPushforward.{w, w, v, u, v', u'} i).obj
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).obj
            (idealProductModule hi G').val)⟦(1 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) 0).obj
          (idealProductShortComplex hi G').X₁)⟦(1 : ℤ)⟧) := by
  have := preservesFiniteLimits_pushforwardModules (i := i) hi
  have := preservesFiniteColimits_pushforwardModules (i := i) hi
  have : i.pushforwardModules.Additive := Functor.additive_of_preserves_binary_products _
  exact derivedPushforwardShiftedSingleIso i (idealProductModule hi G').val ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (idealProductModule hi G').property.some)

/-- **Stacks 08MS.** There is a class `o(φ)` in `Ext¹_O(Li^*F', I·G')` whose vanishing is
necessary and sufficient for the `O`-linear map `φ : i^*F' ⟶ i^*G'` to be the pullback of an
`O'`-linear map `F' ⟶ G'`.

The class is the connecting class of the sequence `0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0` on the adjoint
transpose of `φ`, read across `Li^* ⊣ Ri_*`. -/
@[stacks 08MS]
noncomputable def moduleMapObstruction :
    { o : DerivedCategory.Ext
        (d.functor.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj F'))
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).obj
            (idealProductModule hi G').val) 1 //
      o = 0 ↔ Nonempty (ModuleMapLift F' G' φ) } := by
  classical
  have := preservesFiniteLimits_pushforwardModules (i := i) hi
  have := preservesFiniteColimits_pushforwardModules (i := i) hi
  have : i.pushforwardModules.Additive := Functor.additive_of_preserves_binary_products _
  have : (derivedPushforward.{w, w, v, u, v', u'} i).Additive :=
    Functor.additive_of_iso (derivedPushforwardMapDerivedCategoryIso i).symm
  let adj := derivedPullbackPushforwardAdjunction.{w, w, v, u, v', u'} i d
  have : d.functor.Additive := adj.left_adjoint_additive
  let adj₀ := i.pullbackAdjPushforwardModulesViaComparison
  let hS := idealProductShortComplex_shortExact hi G'
  let a : F' ⟶ (idealProductShortComplex hi G').X₃ :=
    adj₀.homEquiv F' ((i.toRingedToposModulesHom.pullbackModules).obj G') φ
  let δ := (DerivedCategory.singleFunctor _ 0).map a ≫ hS.singleδ
  let e := idealProductDerivedPushforwardIso hi G'
  refine ⟨(adj.homEquiv _ _).symm (δ ≫ e.inv), ?_⟩
  have ho : (adj.homEquiv _ _).symm (δ ≫ e.inv) = 0 ↔ δ = 0 := by
    rw [← adj.homAddEquiv_symm_zero, (adj.homEquiv _ _).symm.injective.eq_iff]
    refine ⟨fun h ↦ (cancel_mono e.inv).mp ?_, fun h ↦ by rw [h, zero_comp]⟩
    simpa only [zero_comp] using h
  rw [ho]
  exact (singleδ_comp_eq_zero_iff hS F' a).trans
    (nonempty_moduleMapLift_iff_exists_factorization F' G' φ).symm

/-- **Stacks 08MS.** The obstruction class `o(φ) ∈ Ext¹_O(Li^*F', I·G')` itself. -/
@[stacks 08MS]
noncomputable abbrev moduleMapObstructionClass :
    DerivedCategory.Ext
      (d.functor.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj F'))
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) 0).obj
          (idealProductModule hi G').val) 1 :=
  (moduleMapObstruction hi d F' G' φ).val

/-- **Stacks 08MS.** The obstruction class vanishes exactly when `φ` lifts. -/
@[stacks 08MS]
theorem moduleMapObstructionClass_eq_zero_iff :
    moduleMapObstructionClass hi d F' G' φ = 0 ↔ Nonempty (ModuleMapLift F' G' φ) :=
  (moduleMapObstruction hi d F' G' φ).property

end Thickening

end Deformation.ToposThickening

end
