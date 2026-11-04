module

public import StacksFrontier.Deformation.ToposThickening.ExtensionRestriction
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundaryPushout

/-!
# Compatibility of the existence obstructions under a morphism of thickenings, by restriction

Let `(Sh(C), O)` be a ringed topos with two first order thickenings `O'₁` and `O'₂` presented on
one site and a morphism `h^♯ : O'₂ ⟶ O'₁` of thickenings over it, and let `ℐ₂ ⟶ ℐ₁` be the
induced map of defining ideals. For an `O`-module `F`, modules `K₁`, `K₂` with prescribed actions
`cₖ : ℐₖ ⊗ F ⟶ Kₖ` and `κ : K₂ ⟶ K₁` with `c₂ ≫ κ = (ℐ₂ ⟶ ℐ₁) ⊗ F ≫ c₁`, the map induced by `κ`
on `Ext²_O(F, -)` carries `o(F, K₂, c₂)` to `o(F, K₁, c₁)` (Stacks 0CYC). This module proves
the comparison of the universal classes on which that rests, with no constraint on the universes
of the thickened topos.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.universalClass_first_eq_comp_of_hom`:
  a map from an extension over the second thickening with a presentation to an extension over
  the first thickening with a presentation, read over the second, identifies the universal class
  of the first with that of the second pushed forward along `(ℐ₂ ⟶ ℐ₁) ⊗ F`.

## Implementation notes

This is the restriction step of the proof of Stacks 0CYC,
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existenceObstructionClass_first`
(`StacksFrontier/Deformation/ToposThickening/ObstructionCompatibility.lean`). Pushing an extension
over the second thickening out to one over the first along the functoriality of Stacks 08MJ
checks the sheaf condition for `O'₂ ⋉ ℐ₁` through the forgetful functor to types, which forces
the sections of the thickened topos into the universe `max v u` of its site.

Here the comparison goes the other way, by restriction of scalars along `h^♯`, which exists in
every universe. Take a presentation `P₁` of the obstruction class of the first thickening, on an
extension `E₁` with injective action map `d₁ : ℐ₁ ⊗ F ⟶ Q₁`. Read over `O'₂`, `E₁` becomes an
extension with action map `((ℐ₂ ⟶ ℐ₁) ⊗ F) ≫ d₁`
(`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictedExtension_actionMap`),
which need not be injective; a common refinement with an extension over `O'₂` that has injective
action map does have injective action map and maps to it. For a presentation `P` on any extension
`E` over `O'₂` mapping to the restriction of `E₁`, inducing `γ : Q ⟶ Q₁` on kernel modules, the
two defining short exact sequences are related by `((ℐ₂ ⟶ ℐ₁) ⊗ F, γ, c̄)`, and the two descents
by `c̄`, because both restrict along the structure map of the second thickening to the class of
`E` pushed forward to `C₁` and restriction is injective on `Ext¹`. Naturality of the class of a
short exact sequence then compares the two universal classes.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  {i : RingedToposHom X Y}

namespace MorphismOfFirstOrderThickenings

variable (D : MorphismOfFirstOrderThickenings i)
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]

/-- **A map of extensions across a morphism of thickenings compares the universal classes.** Let
`P` be a presentation on an extension `E` of `F` over the second thickening and `P₁` one on an
extension `E₁` over the first. If the middle term of `E` maps over `F` to the middle term of `E₁`
read over the second thickening, inducing `γ` on kernel modules, then the universal class of
`P₁` is that of `P` pushed forward along `(ℐ₂ ⟶ ℐ₁) ⊗ F`

It is the restriction step of Stacks 0CYC,
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existenceObstructionClass_first`. -/
theorem universalClass_first_eq_comp_of_hom
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂))]
    {F Q Q₁ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    {E : Abelian.YonedaExtension ((structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj Q) 0}
    {E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj Q₁) 0}
    (P : MonoActionPresentation D.second E) (P₁ : MonoActionPresentation D.first E₁)
    (γ : Q ⟶ Q₁) (u : E.Z.left ⟶ (D.restrictedExtension E₁).Z.left)
    (hu : E.f ≫ u =
      (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map γ ≫ (D.restrictedExtension E₁).f)
    (hg : u ≫ (D.restrictedExtension E₁).g = E.g) :
    P₁.universalClass = P.universalClass.comp
      (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map
        D.idealMap)) (add_zero 2) := by
  have hex := restrictScalars_exact (structureRingMap (reshapeHom i D.O₂ D.fSharp₂))
  have hlim : PreservesFiniteLimits (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)) := hex.1
  have hcolim : PreservesFiniteColimits (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)) :=
    hex.2
  have hff := D.second.restrictScalarsFullyFaithful
  have hfull : (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).Full := hff.full
  have hfaith : (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).Faithful := hff.faithful
  -- the action maps: `d ≫ γ = ((ℐ₂ ⟶ ℐ₁) ⊗ F) ≫ d₁`
  have hd : (extensionActionMap D.second E).1 ≫ γ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map D.idealMap ≫
        (extensionActionMap D.first E₁).1 :=
    (extensionActionMap_comp_of_hom D.second E (D.restrictedExtension E₁) γ u hu hg).trans
      (D.restrictedExtension_actionMap E₁)
  have hzero : (extensionActionMap D.second E).1 ≫ γ ≫ P₁.proj = 0 := by
    rw [← Category.assoc, hd, Category.assoc, P₁.zero, comp_zero]
  have hepi : Epi P.proj := P.shortExact.epi_g
  obtain ⟨cbar, hbar⟩ := P.shortExact.exact.desc' (γ ≫ P₁.proj) hzero
  -- the comparison exhibiting the restriction of the descent of `P₁` as a pushout of `E`
  let w : (D.restrictedExtension E₁).Z.left ⟶
      (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj P₁.descent.Z.left :=
    (SheafOfModules.restrictScalars D.ringMapH).map P₁.comparison ≫
      (D.restrictHIso P₁.descent.Z.left).hom
  have hw₁ : (D.restrictedExtension E₁).f ≫ w =
      (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map P₁.proj ≫
        (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map P₁.descent.f := by
    ext U x
    exact congrArg (fun φ => φ.val.app U x) P₁.comparison_left
  have hw₂ : w ≫ (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map P₁.descent.g =
      (D.restrictedExtension E₁).g := by
    ext U x
    exact congrArg (fun φ => φ.val.app U x) P₁.comparison_right
  let cmp : E.Z.left ⟶ (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj P₁.descent.Z.left :=
    u ≫ w
  have hcmp₁ : E.f ≫ cmp =
      (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map (γ ≫ P₁.proj) ≫
        (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map P₁.descent.f := by
    rw [Functor.map_comp, Category.assoc, ← hw₁, ← Category.assoc, hu, Category.assoc]
  have hcmp₂ : cmp ≫ (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).map P₁.descent.g = E.g := by
    rw [Category.assoc, hw₂, hg]
  have hξ : (yonedaExtension_shortExact P₁.descent).extClass =
      (yonedaExtension_shortExact P.descent).extClass.comp (Abelian.Ext.mk₀ cbar) (add_zero 1) := by
    apply (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).extMap_injective_of_fullyFaithful F
      P₁.C
    rw [Functor.mapExtAddHom_comp_mk₀,
      mapExtAddHom_descent_extClass (i := reshapeHom i D.O₂ D.fSharp₂) (γ ≫ P₁.proj) P₁.descent
        cmp hcmp₁ hcmp₂,
      mapExtAddHom_descent_extClass (i := reshapeHom i D.O₂ D.fSharp₂) P.proj P.descent
        P.comparison P.comparison_left P.comparison_right,
      Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Functor.map_comp, hbar]
  exact Abelian.comp_extClass_naturality P₁.shortExact P.shortExact
    (⟨((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map D.idealMap, γ, cbar,
      hd.symm, hbar.symm⟩ :
      ShortComplex.mk (extensionActionMap D.second E).1 P.proj P.zero ⟶
        ShortComplex.mk (extensionActionMap D.first E₁).1 P₁.proj P₁.zero)
    (yonedaExtension_shortExact P₁.descent).extClass
    (yonedaExtension_shortExact P.descent).extClass hξ

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

end
