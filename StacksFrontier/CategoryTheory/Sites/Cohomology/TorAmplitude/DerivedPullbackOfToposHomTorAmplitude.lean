module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# Tor amplitude and derived pullback along a morphism of ringed topoi

**Stacks 08H5** for an arbitrary morphism of ringed topoi `f` (`AlgebraicGeometry.RingedToposHom`),
with the universes of the two ringed topoi free and unrelated: if `E` in `D(O')` has Tor
amplitude in `[a, b]`, so has `Lf^*E`. The argument is carried once, for any functor
`L : D(O') ⥤ D(O)` which carries the image of a bounded complex of flat modules to the image of
such a complex: `hasTorAmplitude_obj_of_preservesFlatRepresentatives`.

## References

* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules.DerivedTensorProduct

/-! ## A functor carrying bounded flat representatives to bounded flat representatives -/

section FlatRepresentatives

universe u v w d u' v' w' d'

-- The sections universes are free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w'}}
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasDerivedCategory.{d'} (RingedSite.Modules.{u', v', w'} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u', v', w'} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08H5, the argument without the geometry.**  A functor `L : D(O') ⥤ D(O)` which
carries the image of every complex of flat `O'`-modules vanishing outside an interval
`[a, b]`, `a ≤ b`, to the image of a complex of flat `O`-modules vanishing outside `[a, b]`,
preserves Tor amplitude in `[a, b]`, for arbitrary derived tensor product data on both sides.

The two directions of Stacks 08G1 do it: Tor amplitude in a nonempty interval gives such a
representative, and such a representative gives Tor amplitude.  A degenerate interval `b < a`
says that the Tor amplitude of `E` lies in the one-point interval `[i + 1, i + 1]` for whichever
degree `i` is being examined. -/
theorem hasTorAmplitude_obj_of_preservesFlatRepresentatives
    (L : RingedSite.DerivedModules.{u', v', w', d'} Y ⥤ RingedSite.DerivedModules.{u, v, w, d} X)
    (hL : ∀ (a b : ℤ), a ≤ b → ∀ K : CochainComplex (RingedSite.Modules.{u', v', w'} Y) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) →
      ∃ K' : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ,
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K'.X i)) ∧
        (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K'.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K' ≅ L.obj (DerivedCategory.Q.obj K)))
    (T : DerivedTensorProduct.{u', v', w', d'} Y) (T' : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u', v', w', d'} Y) (a b : ℤ)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' (L.obj E) a b := by
  have key : ∀ a b : ℤ, a ≤ b → HasTorAmplitude T E a b → HasTorAmplitude T' (L.obj E) a b := by
    intro a b hab hamp
    obtain ⟨K, hflat, hzero, ⟨e⟩⟩ :=
      exists_flatRepresentative_of_hasTorAmplitude T E a b hab hamp
    obtain ⟨K', hflat', hzero', ⟨e'⟩⟩ := hL a b hab K hflat hzero
    exact hasTorAmplitude_of_flatRepresentative T' _ a b K' hflat' hzero' (e' ≪≫ L.mapIso e)
  by_cases hab : a ≤ b
  · exact key a b hab hamp
  · intro F i _
    have hamp' : HasTorAmplitude T E (i + 1) (i + 1) :=
      fun G j _ => hamp G j (by simp only [Set.mem_Icc]; omega)
    exact key (i + 1) (i + 1) le_rfl hamp' F i (by simp only [Set.mem_Icc]; omega)

/-- **Finite Tor dimension along a functor carrying bounded flat representatives to bounded flat
representatives**: an interval containing the Tor amplitude of `E` contains that of `L E`. -/
theorem hasFiniteTorDimension_obj_of_preservesFlatRepresentatives
    (L : RingedSite.DerivedModules.{u', v', w', d'} Y ⥤ RingedSite.DerivedModules.{u, v, w, d} X)
    (hL : ∀ (a b : ℤ), a ≤ b → ∀ K : CochainComplex (RingedSite.Modules.{u', v', w'} Y) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (K.X i)) →
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) →
      ∃ K' : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ,
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K'.X i)) ∧
        (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K'.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K' ≅ L.obj (DerivedCategory.Q.obj K)))
    (T : DerivedTensorProduct.{u', v', w', d'} Y) (T' : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u', v', w', d'} Y) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' (L.obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_obj_of_preservesFlatRepresentatives L hL T T' E a b hamp⟩

end FlatRepresentatives

/-! ## An arbitrary morphism of ringed topoi, at free universes -/

section ToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex
  isFlat_pullbackComplex_X)

universe v u w v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

/-- **Stacks 08H5 for an arbitrary morphism of ringed topoi**, in the sense of Stacks 01D3 and
with the universes of the two ringed topoi free and unrelated: `Lf^*` preserves Tor amplitude in
a fixed interval, for any derived tensor product data on the two sides.

A complex `K` of flat `O'`-modules concentrated in `[a, b]` is bounded above, hence K-flat by
Stacks 06YQ, so `Lf^* K ≅ f^* K` by the computation clause of Stacks 06YY; `f^* K` has flat
terms by Stacks 05VD and still vanishes outside `[a, b]`. -/
theorem hasTorAmplitude_derivedPullbackOfToposHom (f : RingedToposHom X Y)
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (a b : ℤ)
    (hamp : HasTorAmplitude T E a b) :
    HasTorAmplitude T' ((derivedPullback f).obj E) a b := by
  refine hasTorAmplitude_obj_of_preservesFlatRepresentatives (derivedPullback f)
    (fun a b _ K hflat hzero => ?_) T T' E a b hamp
  have := RingedToposHom.pullbackModules_additive f
  have hKLE : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hzero i (by simp only [Set.mem_Icc]; omega)
  have hK := Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O K ⟨b, hKLE⟩ hflat
  have hcomp : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    isIso_derivedPullbackComparison_app f
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y))
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y))
      (pullbackInvertsQuasiIso_isKFlat f) _ ⟨hK, hflat⟩
  refine ⟨(pullbackComplex f).obj K, fun i => isFlat_pullbackComplex_X f K hflat i,
    fun i hi => Functor.map_isZero (f.toModulesHom.pullbackModules) (hzero i hi), ⟨?_⟩⟩
  exact ((derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).app K).symm ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).app
        ((pullbackComplex f).obj K)).symm

/-- **Finite Tor dimension is preserved by derived pullback along an arbitrary morphism of
ringed topoi**, Stacks 08H5 for the predicate of Stacks 08FZ (2). -/
theorem hasFiniteTorDimension_derivedPullbackOfToposHom (f : RingedToposHom X Y)
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (h : HasFiniteTorDimension T E) :
    HasFiniteTorDimension T' ((derivedPullback f).obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_derivedPullbackOfToposHom f T T' E a b hamp⟩

end ToposHom

end Stacks.SheafOfModules.DerivedTensorProduct

end
