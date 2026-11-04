module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteBiproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# Higher direct images of a finite sum of associated modules

For a morphism `p : h_V ⟶ Y` from a represented algebraic space and an `𝒪_{V₀}`-module `G`,
the higher direct images of the associated module of a finite direct sum `G^{⊕ I}` vanish as
soon as those of `Gᵃ` do: the associated-module functor and the right derived functors of the
direct image are additive, and the identity of `G^{⊕ I}` is the sum of the projections followed
by the inclusions.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_representedModuleOf_biproduct`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of a represented algebraic space,
`AlgebraicGeometry.Space.representedModuleOf` as a functor. -/
abbrev representedModuleOfFunctor (V : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj V).Modules ⥤
      SheafOfModules.{u} (representedStructureRingSheaf B S hS V) :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS V).functor

/-- The associated-module functor of a represented algebraic space is additive. -/
instance additive_representedModuleOfFunctor (V : BigFppfOver B S hS) :
    (representedModuleOfFunctor B S hS V).Additive := by
  have := _root_.AlgebraicGeometry.SmallEtale.additive_associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj V) V.left.property
  have : (representedSmallEtaleModuleEquivalence B S hS V).functor.Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  exact Functor.instAdditiveComp _ _

section

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **The higher direct images of a finite sum of associated modules vanish with those of one
summand.** -/
theorem isZero_rightDerived_modulePushforward_representedModuleOf_biproduct
    {Y : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS) (p : schemeSpace V ⟶ Y)
    (G : ((BigFppfOver.toScheme B S hS).obj V).Modules) {ι : Type} [Fintype ι] (q : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS (schemeSpace V).1 (schemeSpace V).2
      IsZero (((modulePushforward B S hS p).rightDerived q).obj (representedModuleOf B S hS V G))) :
    have := hasInjectiveResolutions_modules B S hS (schemeSpace V).1 (schemeSpace V).2
    IsZero (((modulePushforward B S hS p).rightDerived q).obj
      (representedModuleOf B S hS V (⨁ fun _ : ι => G))) := by
  intro _
  have := enoughInjectives_modules B S hS (schemeSpace V).1 (schemeSpace V).2
  have := additive_representedModuleOfFunctor B S hS V
  let F := representedModuleOfFunctor B S hS V ⋙ (modulePushforward B S hS p).rightDerived q
  have hR : ((modulePushforward B S hS p).rightDerived q).Additive :=
    Stacks.DerivedLinear.rightDerived_additive (modulePushforward B S hS p) q
  have : F.Additive := ⟨fun {_ _ f g} =>
    (congrArg ((modulePushforward B S hS p).rightDerived q).map
      ((representedModuleOfFunctor B S hS V).map_add (f := f) (g := g))).trans
      (((modulePushforward B S hS p).rightDerived q).map_add)⟩
  show IsZero (F.obj (⨁ fun _ : ι => G))
  have h' : IsZero (F.obj G) := h
  have ht : 𝟙 (⨁ fun _ : ι => G) = ∑ j, biproduct.π (fun _ : ι => G) j ≫
      biproduct.ι (fun _ : ι => G) j := (biproduct.total (J := ι) (f := fun _ : ι => G)).symm
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ht, F.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [F.map_comp]
  rw [h'.eq_zero_of_tgt (F.map (biproduct.π (fun _ : ι => G) j)), zero_comp]

end

end AlgebraicGeometry.Space

end
