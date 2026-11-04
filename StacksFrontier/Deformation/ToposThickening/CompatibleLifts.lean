module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference
public import StacksFrontier.Deformation.ToposThickening.IdealActionNaturality

/-!
# Compatible lifts between two extensions over a first order thickening form a torsor

Fix two extensions of modules over a first order thickening of ringed topoi, together with maps
of their quotient and of their kernel modules. A *compatible map* is a map of the two middle
terms inducing those two prescribed maps. The compatible maps, when there are any, form a
principal homogeneous space under the group of maps from the first quotient to the second
kernel: translating a compatible map by such a map preserves compatibility, and any two
compatible maps differ by exactly one translation.

Both halves are elementary consequences of exactness. For the first, the translation
`g₁ ≫ α ≫ f₂` is killed on the left by `f₁` and on the right by `g₂`, because `f₁ ≫ g₁ = 0`
and `f₂ ≫ g₂ = 0`. For the second, the difference `δ` of two compatible maps kills the first
kernel and lands in the second kernel, so exactness of the first sequence factors it through the
first quotient and exactness of the second lifts that factorization through the second kernel;
the lift is unique because `g₁` is epi and `f₂` is mono. The resulting map lives over the
quotient structure sheaf, and restriction of scalars along the locally surjective structure map
of the thickening identifies it with a map of the end modules themselves.

## Main definitions

* `Deformation.ToposThickening.CompatibleMap`: a map of the middle terms of two extensions over
  a first order thickening inducing the prescribed maps on kernels and quotients.

## Main results

* `Deformation.ToposThickening.compatibleMap_add_quotientKernel`: adding a map that factors
  through the first quotient and the second kernel preserves compatibility.
* `Deformation.ToposThickening.compatibleMap_unique_quotientKernel_difference`: any two
  compatible maps differ by a unique map from the first quotient to the second kernel.

## Implementation notes

Compatibility of a middle-term map is `Deformation.ToposThickening.IsExtensionLift`, which is
exactly the conjunction of the two commutation conditions, so `CompatibleMap` carries that
predicate rather than a second copy of the two equations. Its first conjunct is oriented
`kernelMap ≫ f₂ = f₁ ≫ hom`.

Together, the two results give the free and transitive action of
`Hom(F, L)` on the compatible maps without choosing a base point, which is the form in which the
source states it.

The instance arguments recording that the Grothendieck topologies admit the forgetful sheaf
compositions are placed before the morphism of ringed topoi, because
`AlgebraicGeometry.RingedToposHom` needs them to elaborate its own type.

## References

* [Stacks Project, Tag 08MC](https://stacks.math.columbia.edu/tag/08MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- A map of the middle terms of two extensions over a first order thickening which induces the
prescribed maps on their kernel and quotient modules. -/
public structure CompatibleMap (D : TwoExtensions i) where
  /-- The map of the two middle terms. -/
  hom : D.firstExtension.Z.left ⟶ D.secondExtension.Z.left
  /-- It induces the prescribed maps on the kernel and on the quotient terms. -/
  isExtensionLift : IsExtensionLift D hom

/-- Adding a map which factors through the first quotient and the second kernel preserves
compatibility. -/
@[stacks 08MC "compatible_lifts_torsor"]
theorem compatibleMap_add_quotientKernel
    (D : TwoExtensions i) (c : CompatibleMap D) (α : D.F ⟶ D.L) :
    ∃ d : CompatibleMap D,
      d.hom = c.hom +
        (D.firstExtension.g ≫
          (SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map α ≫
          D.secondExtension.f) := by
  refine ⟨⟨c.hom + (D.firstExtension.g ≫
    (SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map α ≫
    D.secondExtension.f), ?_, ?_⟩, rfl⟩
  · rw [Preadditive.comp_add, ← Category.assoc,
      yonedaExtension_comp_zero D.firstExtension, zero_comp, add_zero]
    exact c.isExtensionLift.1
  · rw [Preadditive.add_comp, Category.assoc, Category.assoc,
      yonedaExtension_comp_zero D.secondExtension, comp_zero, comp_zero, add_zero]
    exact c.isExtensionLift.2

/-- Any two compatible maps differ by a unique map from the first quotient to the second kernel.
Together with closure under those translations, this is the torsor assertion. -/
@[stacks 08MC "compatible_lifts_torsor"]
theorem compatibleMap_unique_quotientKernel_difference
    (D : TwoExtensions i) (c d : CompatibleMap D) :
    ∃! α : D.F ⟶ D.L,
      d.hom = c.hom +
        (D.firstExtension.g ≫
      (SheafOfModules.restrictScalars
        ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map α ≫
          D.secondExtension.f) := by
  let ρ := (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let R := SheafOfModules.restrictScalars ρ
  let δ := d.hom - c.hom
  have hkernel : D.firstExtension.f ≫ δ = 0 := by
    rw [show δ = d.hom - c.hom from rfl, Preadditive.comp_sub,
      ← d.isExtensionLift.1, ← c.isExtensionLift.1, sub_self]
  have hquotient : δ ≫ D.secondExtension.g = 0 := by
    rw [show δ = d.hom - c.hom from rfl, Preadditive.sub_comp,
      d.isExtensionLift.2, c.isExtensionLift.2, sub_self]
  let E₁ := (yonedaExtension_shortExact D.firstExtension).exact
  let E₂ := (yonedaExtension_shortExact D.secondExtension).exact
  let αr := E₂.lift (E₁.desc δ hkernel)
    ((cancel_epi D.firstExtension.g).mp (by
      rw [comp_zero, ← Category.assoc, E₁.g_desc δ hkernel, hquotient]))
  have hlift : αr ≫ D.secondExtension.f = E₁.desc δ hkernel :=
    E₂.lift_f _ _
  let e := moduleHomEquivOfLocallySurjective ρ (structureMap_locallySurjective D)
    (M := D.F) (N := D.L)
  have hfactor : D.firstExtension.g ≫ R.map (e αr) ≫ D.secondExtension.f = δ := by
    rw [show R.map (e αr) = αr from e.symm_apply_apply αr, hlift, E₁.g_desc δ hkernel]
  have hmain : d.hom = c.hom +
      D.firstExtension.g ≫ R.map (e αr) ≫ D.secondExtension.f := by
    rw [hfactor, show δ = d.hom - c.hom from rfl]
    abel
  refine ⟨e αr, hmain, ?_⟩
  · intro β hβ
    have hβ' : d.hom = c.hom +
      D.firstExtension.g ≫ R.map β ≫ D.secondExtension.f := hβ
    have hcomp : D.firstExtension.g ≫ R.map β ≫ D.secondExtension.f =
        D.firstExtension.g ≫ R.map (e αr) ≫ D.secondExtension.f :=
      add_left_cancel (hβ'.symm.trans hmain)
    have hmid : R.map β ≫ D.secondExtension.f = R.map (e αr) ≫ D.secondExtension.f :=
      (cancel_epi D.firstExtension.g).mp (by simpa only [Category.assoc] using hcomp)
    exact e.symm.injective ((cancel_mono D.secondExtension.f).mp hmid)

/-! ## The remaining clause of the tag

Stacks 08MC also asserts that a compatible middle-term map commutes with multiplication by
sections of the square-zero ideal. That is
`Deformation.ToposThickening.idealActionMap_naturality`, in
`StacksFrontier/Deformation/ToposThickening/IdealActionNaturality.lean`; the tag is recorded
against it here, so that the whole covering set of 08MC carries the tag. -/

add_to_stacks 08MC "ideal_action_compatible" idealActionMap_naturality

end Deformation.ToposThickening

end
