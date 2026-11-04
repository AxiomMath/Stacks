module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HigherDirectImageModels
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianHigherDirectImage

/-!
# A morphism of modules killed by an abelian higher direct image

Let `f : X ⟶ Y` be a morphism of ringed spaces and `φ : M ⟶ M'` a morphism of `𝒪_X`-modules.
The `n`-th higher direct image of `φ` has three readings: the cohomology sheaf
`Hⁿ(Rf_*(φ[0]))` of the unbounded derived direct image, the value at `φ` of the right derived
functor `Rⁿf_*` of the direct image of modules, and the value at the underlying morphism of
abelian sheaves of the abelian higher direct image `Rⁿf_*` of [Stacks, Tag 01F1]. The three agree
naturally, so the vanishing of the last implies that of the first.

## Main results

* `homologyFunctor_map_derivedPushforward_singleFunctor_map_eq_zero`:
  if the abelian higher direct image of the underlying morphism of abelian sheaves vanishes,
  then so does `Hⁿ(Rf_*(φ[0]))`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
  TopologicalSpace

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u w₁ w₂

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- A morphism whose composite with an isomorphism is the composite of an isomorphism with
zero is zero. -/
private theorem eq_zero_of_comp_hom_eq_hom_comp {C : Type*} [Category* C] [HasZeroMorphisms C]
    {P P' Q Q' : C} {g : P ⟶ P'} {g' : Q ⟶ Q'} (e : P ≅ Q) (e' : P' ≅ Q')
    (h : g ≫ e'.hom = e.hom ≫ g') (hg' : g' = 0) : g = 0 := by
  rw [hg', comp_zero] at h
  exact (cancel_mono e'.hom).1 (h.trans zero_comp.symm)

/-- **A morphism of modules whose underlying morphism of abelian sheaves is killed by the abelian
higher direct image `Rⁿf_*` is killed by `Hⁿ(Rf_*(-[0]))`.** The cohomology sheaf of the derived
direct image is the right derived functor of the direct image of modules
(`homologyDerivedPushforwardSingleIso`), which agrees with the one built from injective
resolutions (`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`), which after
forgetting to abelian sheaves is the abelian higher direct image ([Stacks, Tag 01F1] (2)); the
forgetful functor is faithful. -/
theorem homologyFunctor_map_derivedPushforward_singleFunctor_map_eq_zero
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    [EnoughInjectives (SheafOfModules.{u} (structureSheafRing X))]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [EnoughInjectives (X.carrier.Sheaf AddCommGrpCat.{u})]
    {M M' : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ M') (n : ℕ)
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage f.hom.base n).map
      ((SheafOfModules.toSheaf (structureSheafRing X)).map φ) = 0) :
    (DerivedCategory.homologyFunctor _ (n : ℤ)).map
      ((derivedPushforward f).map ((DerivedCategory.singleFunctor _ 0).map φ)) = 0 := by
  -- the abelian higher direct image
  have hab : (SheafOfModules.toSheaf (structureSheafRing X) ⋙
      (Stacks.Cohomology.ModulePushforwardComparison.abelianPushforward f).rightDerived n).map φ =
        0 := h
  -- the right derived functor built from injective resolutions
  have hstd : ((modulePushforward f).rightDerived n).map φ = 0 := by
    apply (SheafOfModules.toSheaf (structureSheafRing Y)).map_injective
    rw [Functor.map_zero]
    let e := Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso
      f n
    exact eq_zero_of_comp_hom_eq_hom_comp (e.app M) (e.app M') (e.hom.naturality φ) hab
  -- the right derived functor on bounded below derived categories
  have hplus : ((modulePushforward f).rightDerivedPlus (n : ℤ)).map φ = 0 := by
    let e := Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
      (modulePushforward f) n
    exact eq_zero_of_comp_hom_eq_hom_comp (e.app M) (e.app M') (e.hom.naturality φ) hstd
  -- the unbounded derived direct image
  have hnat := congrArg (DerivedCategory.homologyFunctor _ (n : ℤ)).map
    ((boundedDerivedPushforwardIso f).inv.naturality
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ))
  rw [Functor.map_comp, Functor.map_comp] at hnat
  exact eq_zero_of_comp_hom_eq_hom_comp (homologyDerivedPushforwardSingleIso f (n : ℤ) M)
    (homologyDerivedPushforwardSingleIso f (n : ℤ) M') hnat hplus

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
