module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic

/-!
# Higher direct images along a morphism that contracts its source to a point

Let `g : U ⟶ S` be a morphism of schemes whose image is a single point of `S`, and let `F` be a
quasi-coherent `𝒪_U`-module. Then `R ⁿ g_* F = 0` as soon as `H ⁿ(U, F) = 0`.

The reason is that the only opens of `S` that `g` can see are the ones containing the image
point and the ones missing it: the preimage of an open `V ⊆ S` is `U` in the first case and `∅`
in the second. By [Stacks, Tag 01E4] the higher direct image is the sheafification of the
presheaf `V ↦ H ⁿ(g⁻¹(V), F)`, which a basis of opens therefore computes from the two values
`H ⁿ(U, F)` and `H ⁿ(∅, F)`; the first is the hypothesis and the second vanishes because `∅` is
an affine open.

This turns a vanishing theorem on a *proper* scheme — where `g` is very far from affine — into a
vanishing theorem for a higher direct image.

## Main results

* `Stacks.PointImageHigherDirectImage.preimage_eq_top_or_eq_bot`: the preimage of an open under a
  morphism with constant underlying map is everything or nothing.
* `Stacks.PointImageHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_const` and
  `Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_of_const`: `R ⁿ g_* F = 0`
  from `H ⁿ(U, F) = 0`, in the `ℤ`- and the `ℕ`-indexed spelling of the higher direct images.
* `Stacks.PointImageHigherDirectImage.isZero_rightDerived_pushforward_pushforward_of_const`: the
  same conclusion for `R ⁿ f_*(j_* F)`, where `j : U ⟶ X` is affine and `j ≫ f` has constant
  underlying map.

## Implementation notes

The constancy hypothesis is `∀ u v : U, g.base u = g.base v` rather than the naming of an image
point, so that it says nothing when `U` is empty and needs no nonemptiness to apply.

The passage from `R ⁿ (j ≫ f)_* F` to `R ⁿ f_*(j_* F)` is the collapse
`Stacks.AcyclicCollapse.objIso` of [Stacks, Tag 089W], read in the direction that transports
vanishing from the composite to the second leg. It is
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp` with the
affineness of `j ≫ f` replaced by the constancy hypothesis — and that replacement is the point,
since a morphism contracting a proper curve to a point is not affine.

## References

* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeCechAcyclic (rightAcyclic_pushforward_obj_injective)

universe u

namespace Stacks.PointImageHigherDirectImage

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Module sheaves on a scheme form an abelian category, in the spelling that unfolds
`AlgebraicGeometry.Scheme.Modules`. -/
noncomputable local instance abelian_modules (Y : Scheme.{u}) :
    Abelian (SheafOfModules.{u} Y.ringCatSheaf) :=
  inferInstance

/-- Module sheaves on a scheme have enough injectives: they form a Grothendieck abelian
category. -/
local instance enoughInjectives_modules (Y : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} Y.ringCatSheaf) :=
  IsGrothendieckAbelian.enoughInjectives

variable {U X S : Scheme.{u}}

/-- **A morphism with constant underlying map sees only two opens.** If every point of `U` has
the same image under `g`, then the preimage of an open `V` of `S` is `⊤` when some point of `U`
lands in `V` and `⊥` when none does. -/
public theorem preimage_eq_top_or_eq_bot (g : U ⟶ S) (hg : ∀ u v : U, g.base u = g.base v)
    (V : S.Opens) : g ⁻¹ᵁ V = ⊤ ∨ g ⁻¹ᵁ V = ⊥ := by
  by_cases h : ∃ u : U, g.base u ∈ V
  · obtain ⟨u₀, hu₀⟩ := h
    refine Or.inl (TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun u ↦ ?_))
    change g.base u ∈ V
    rwa [hg u u₀]
  · exact Or.inr
      (TopologicalSpace.Opens.ext (Set.eq_empty_of_forall_notMem fun u hu ↦ h ⟨u, hu⟩))

/-- **`R ⁿ g_* F = 0` for a morphism contracting its source to a point**, in the `ℤ`-indexed
spelling `Functor.rightDerivedPlus`. -/
public theorem isZero_rightDerivedPlus_pushforward_of_const (g : U ⟶ S)
    (hg : ∀ u v : U, g.base u = g.base v) (F : U.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : 0 < n) (hvan : IsZero (Hgroup U.ringCatSheaf ⊤ n F)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus (n : ℤ)).obj F) := by
  refine
    Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
    g F n S.isBasis_affineOpens fun V _ ↦ ?_
  rcases preimage_eq_top_or_eq_bot g hg V with hV | hV
  · rw [hV]; exact hvan
  · rw [hV]
    exact Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffineOpen U F ⊥
      (isAffineOpen_bot U) n hn

/-- **`R ⁿ g_* F = 0` for a morphism contracting its source to a point**, in Mathlib's
`ℕ`-indexed spelling `Functor.rightDerived`. -/
public theorem isZero_rightDerived_pushforward_of_const (g : U ⟶ S)
    (hg : ∀ u v : U, g.base u = g.base v) (F : U.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : 0 < n) (hvan : IsZero (Hgroup U.ringCatSheaf ⊤ n F)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj F) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward g)
    (rfl : (n : ℤ) = (n : ℤ)) F).1
    (isZero_rightDerivedPlus_pushforward_of_const g hg F n hn hvan)

/-- **`R ⁿ f_*(j_* F) = 0` when `j` is affine and `j ≫ f` contracts `U` to a point.** -/
public theorem isZero_rightDerived_pushforward_pushforward_of_const (j : U ⟶ X) [IsAffineHom j]
    (f : X ⟶ S) (F : U.Modules) [F.IsQuasicoherent]
    (hg : ∀ u v : U, (j ≫ f).base u = (j ≫ f).base v) (n : ℕ) (hn : 0 < n)
    (hvan : IsZero (Hgroup U.ringCatSheaf ⊤ n F)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      ((Scheme.Modules.pushforward j).obj F)) :=
  (isZero_rightDerived_pushforward_of_const (j ≫ f) hg F n hn hvan).of_iso
    (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward j) (Scheme.Modules.pushforward f)
      (rightAcyclic_pushforward_obj_injective j f)
      (Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward j F) n).symm

end Stacks.PointImageHigherDirectImage

end
