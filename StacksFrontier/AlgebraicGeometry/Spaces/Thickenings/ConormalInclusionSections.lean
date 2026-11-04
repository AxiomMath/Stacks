module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapComorphism

/-!
# The two inclusions of the conormal module of a first-order thickening agree as sheaves of sets

Let `i : Z ⟶ X` be a first-order thickening of algebraic spaces, with conormal module `𝒞_{Z/X}`.
Two inclusions of `𝒞_{Z/X}` into the inverse image `i^{-1}𝒪_X` are in use:

* `AlgebraicGeometry.Space.conormalInverseImageι`, a morphism of sheaves of
  `i^{-1}𝒪_X`-modules, obtained by transporting the inclusion of the kernel ideal of
  `i^♯ : 𝒪_X ⟶ i_*𝒪_Z` to the small étale site of `Z`;
* `AlgebraicGeometry.Space.conormalSetInclusion`, a morphism of sheaves of sets, the preimage
  under the fully faithful direct image along `i` of `i_*𝒞_{Z/X} ≅ 𝓘 ⟶ 𝒪_X ⟶ i_*i^{-1}𝒪_X`.

`AlgebraicGeometry.Space.moduleSheafFunctor_map_conormalInverseImageι` proves that the first,
on underlying sheaves of sets, is the second.  The one input that is not formal is that the
comparison `AlgebraicGeometry.Space.thickeningTransportIso` of the two direct images of
`𝒪_Z`-modules along `i` is the identity on sections
(`AlgebraicGeometry.Space.thickeningTransportIso_hom_app_val_app`).

## Implementation notes

`AlgebraicGeometry.Space.thickeningTransportIso` is the transport along an equality of functors
followed by `AlgebraicGeometry.Space.modulePushforwardIso`.  The source of the transport, its
target and the target of the second factor have definitionally equal sections, but the
elaborator and the kernel cannot afford to check two of the three identifications (each runs
into the two non-definitionally-equal forms of the structure map).  So the computation is made
by `Stacks.Sheaves.RingedToposModules.iso_hom_app_val_app_heq_of_eq_eqToIso_trans`, a
heterogeneous equality at abstract functors, proved by `cases`, which is instantiated with the
isomorphism itself and the factorization `rfl`: only the affordable identification of the source
with the final target is ever checked.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w u

namespace Stacks.Sheaves.RingedToposModules

/-- **An isomorphism of functors into sheaves of modules that factors as a transport along an
equality followed by an isomorphism which is the identity on sections is the identity on
sections**, as a heterogeneous equality (the source and the target of the isomorphism need not be
identified).  Proved by `cases` on the equality, which is what makes it cheap: every functor is a
variable. -/
theorem iso_hom_app_val_app_heq_of_eq_eqToIso_trans {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} {A : Type*} [Category A]
    {F₁ F₂ F₃ : A ⥤ SheafOfModules.{w} R} (τ : F₁ ≅ F₃) (β : F₂ ≅ F₃) (h : F₁ = F₂)
    (hτ : τ = eqToIso h ≪≫ β) (N : A) (W : Cᵒᵖ)
    (hβ : ∀ y : (F₂.obj N).val.obj W, HEq ((β.hom.app N).val.app W y) y)
    (x : (F₁.obj N).val.obj W) :
    HEq ((τ.hom.app N).val.app W x) x := by
  subst hτ
  cases h
  exact hβ x

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of the two direct images of modules is the identity on sections**, read as
a heterogeneous equality: `AlgebraicGeometry.Space.modulePushforwardIso_hom_app_val_app` with the
section taken in the source of the comparison. -/
theorem modulePushforwardIso_hom_app_val_app_heq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj N).val.obj W) :
    HEq (((modulePushforwardIso B S hS f).hom.app N).val.app W y) y :=
  heq_of_eq (modulePushforwardIso_hom_app_val_app B S hS f N W y)

section Transport

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (M : Modules.{u, u} B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).2)
  (V : (SmallEtale B S hS X.1)ᵒᵖ)

/-- **The comparison `AlgebraicGeometry.Space.thickeningTransportIso` of the two direct images
of `𝒪_Z`-modules along `i` is the identity on sections.** -/
theorem thickeningTransportIso_hom_app_val_app
    (x : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) ⋙
        thickeningTransport B S hS Z).obj M).val.obj V) :
    ((thickeningTransportIso B S hS Z).hom.app M).val.app V x = x :=
  eq_of_heq (iso_hom_app_val_app_heq_of_eq_eqToIso_trans (thickeningTransportIso B S hS Z)
    (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z))
    (restrictScalars_comp_thickeningTransport B S hS Z) rfl M V
    (modulePushforwardIso_hom_app_val_app_heq B S hS (subspaceInclusion B S hS X Z) M V) x)

end Transport

section Inclusion

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)

include hZ in
/-- **The inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` on underlying sheaves of sets is
`AlgebraicGeometry.Space.conormalSetInclusion`.**  Both have, after the faithful direct image
along `i`, the inclusion `i_*𝒞_{Z/X} ≅ 𝓘 ⟶ 𝒪_X` followed by the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`. -/
theorem moduleSheafFunctor_map_conormalInverseImageι :
    (Sheaf.moduleSheafFunctor
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).map
        (conormalInverseImageι B S hS Z hZ) =
      conormalSetInclusion B S hS Z hZ := by
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).faithful
  refine (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map_injective
    (Eq.trans ?_ (map_conormalSetInclusion B S hS Z hZ).symm)
  refine Sheaf.hom_ext_sections fun V x ↦ ?_
  have key := SheafOfModules.hom_congr_app_apply
    (Stacks.SheafOfModules.IdealTransport.map_idealι
      (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
      (thickeningRingUnit B S hS Z)
      (structureSharp B S hS (subspaceInclusion B S hS X Z))
      (conormalDirectImageIso B S hS Z hZ)) V x
  refine key.trans (congrArg ((thickeningRingUnit B S hS Z).hom.app V) ?_)
  have hι := SheafOfModules.hom_congr_app_apply
    ((Iso.inv_comp_eq _).2
      (firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι B S hS Z hZ).symm) V x
  refine Eq.trans ?_ hι.symm
  exact congrArg (fun y ↦ ((definingIdealSheaf B S hS X Z).ι.val.app V
    ((firstOrderConormalModuleIso B S hS Z hZ).inv.val.app V y)))
    (thickeningTransportIso_hom_app_val_app B S hS Z (conormalModule B S hS X Z) V x)

end Inclusion

end AlgebraicGeometry.Space

end
