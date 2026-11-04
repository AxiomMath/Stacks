module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteCohomologySliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsSliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily
import all StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteInverseLimit

/-!
# Inverse limits of derived-complete sheaves, on a slice testing family

On a ringed site with a covering collection of weakly contractible objects, the inverse limit of
a countable inverse system of sheaves of modules that are derived complete along a sheaf of
ideals is itself derived complete (Stacks 099Q). This file proves it when the weakly contractible
objects are given as a `Stacks.WeaklyContractible.SliceTestingFamily` at the universe of the
module sections, which may be any universe `max u v w` containing the site.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_limit_of_sliceTestingFamily`: completeness of
  the inverse limit.

## Implementation notes

`AlgebraicGeometry.RingedSite.isDerivedComplete_limit`
(`StacksFrontier/AlgebraicGeometry/ProEtale/DerivedCompleteInverseLimit.lean`) is the same statement
for sheaves of modules in the universe `max u v` of a small site whose weak contractibility is
tested at the morphism universe. The site here is not assumed small: on a small site a covering
collection of weakly contractible objects is a slice testing family by
`Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`, and the small pro-étale
site of a scheme, which is not essentially small, carries one in every universe.

The argument is that of the base file: the system is regarded in the derived category in degree
zero, where it has a derived limit `L`; derived completeness of `L` is tested on derived sections
over the members of the family
(`AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily`),
where evaluation is exact and preserves countable products, so the derived limit is preserved and
derived completeness passes to it by the Milnor triangle. Finally `L` is identified with the
inverse limit of the system, the derived limit's cohomology sequence having vanishing outer terms.
Countable products of sheaves of modules are exact on such a site (Stacks 0947(4)).

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  AlgebraicGeometry AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

universe u v t w

namespace AlgebraicGeometry.RingedSite

/-- **The inverse limit of a countable system of derived-complete sheaves is derived
complete**, on a ringed site with a slice testing family of weakly contractible objects at the
universe of the module sections. -/
@[stacks 099Q "inverse_limits"]
public theorem isDerivedComplete_limit_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ n : ℕ, AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (F.obj ⟨n⟩))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (limit F)) := by
  classical
  let A := SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : Abelian A := inferInstance
  let W := B
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat.{max u v w}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) B.B B.hasEnoughObjects
      fun _ hU _ _ φ hφ => B.surjective_app hU φ hφ
  let : HasProductsOfShape ℕ (DerivedCategory A) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let K : ℕᵒᵖ ⥤ DerivedCategory A :=
    F ⋙ DerivedCategory.singleFunctor A 0
  obtain ⟨L, hL⟩ := exists_isDerivedLimit K
  have hLcomplete :
      AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I L := by
    apply (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily
      X W I L).mpr
    intro U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op U)
    let : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (Opposite.op U))
      infer_instance
    let : CommRing R := inferInstance
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Opposite.op U)
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : PreservesFiniteLimits G := inferInstance
    let : G.PreservesHomology := by
      let : G.PreservesZeroMorphisms := inferInstance
      exact Functor.preservesHomology_of_map_exact G fun T hT =>
        evaluation_map_exact_of_sliceTestingFamily X W U hU T hT
    let : PreservesFiniteColimits G :=
      Functor.preservesFiniteColimits_of_preservesHomology G
    let : HasProductsOfShape ℕ (ModuleCat.{max u v w} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w} R) :=
      StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let D := G.mapDerivedCategory
    let : PreservesLimitsOfShape (Discrete ℕ) G := inferInstance
    let : PreservesLimitsOfShape (Discrete ℕ) D :=
      Functor.preservesProducts_mapDerivedCategory ℕ G
    let : PreservesLimit (Discrete.functor (fun n : ℕ => K.obj ⟨n⟩)) D := inferInstance
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro f hf
    have hterms : ∀ n : ℕ, IsDerivedCompleteAt ((K ⋙ D).obj ⟨n⟩) f := by
      intro n
      obtain ⟨_, _, _, _, hn⟩ :=
        (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily
          X W I ((DerivedCategory.singleFunctor A 0).obj (F.obj ⟨n⟩))).mp (hF n) U hU
      exact hn f hf
    exact isDerivedCompleteAt_of_isDerivedLimit (K ⋙ D) (D.obj L)
      (isDerivedLimit_map_of_preservesProduct D K L hL) (f := f) hterms
  have hhom := (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology_of_sliceTestingFamily
    X I B L).mp hLcomplete
  obtain ⟨_, _, _, hs⟩ := DerivedCategory.isDerivedLimit_homology_shortExact K L hL
  have hs0 := hs 0
  dsimp only at hs0
  obtain ⟨_, i, q, _, _, _, _, hshort⟩ := hs0
  let Hprev := DerivedCategory.homologyFunctor A (-1)
  let P : ℕ → A := fun n => Hprev.obj (K.obj ⟨n⟩)
  have hP : IsZero (∏ᶜ P) := by
    apply (limit.isLimit _).isZero_pt
    exact Functor.isZero _ (fun n =>
      homology_single_isZero (F.obj (Opposite.op n.as)) (-1) (by norm_num))
  let δ : ∏ᶜ P ⟶ ∏ᶜ P :=
    Pi.lift fun n : ℕ => Pi.π P n - Pi.π P (n + 1) ≫ Hprev.map (K.map (homOfLE (Nat.le_succ n)).op)
  have : IsIso q := hshort.isIso_g_iff.2 (IsZero.of_epi (cokernel.π δ) hP)
  let H0 := DerivedCategory.homologyFunctor A 0
  let hSysIso : (K ⋙ H0) ≅ F :=
    (Functor.associator F (DerivedCategory.singleFunctor A 0) H0) ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0) ≪≫
      Functor.rightUnitor F
  let eLim : limit (K ⋙ H0) ≅ limit F := HasLimit.isoOfNatIso hSysIso
  let eTot : H0.obj L ≅ limit F := asIso q ≪≫ eLim
  exact (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_of_iso X I
    ((DerivedCategory.singleFunctor A 0).mapIso eTot)).mp (hhom 0)

end AlgebraicGeometry.RingedSite

end
