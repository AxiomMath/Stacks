module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting the ideal sheaf of a closed immersion along an open immersion

Let `a : Z ⟶ U` be a morphism of schemes and `j : U ⟶ C` an open immersion.  The ideal sheaf
`ℐ_{a ≫ j} = Ker(𝒪_C ⟶ (a ≫ j)_* 𝒪_Z)` lives on `C`, and this file identifies its restriction
to `U` with `ℐ_a = Ker(𝒪_U ⟶ a_* 𝒪_Z)`, and consequently identifies the pullback
`(a ≫ j)^* ℐ_{a ≫ j}` with `a^* ℐ_a`.

`StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic` already has the case in
which `j` is an *isomorphism* (`Stacks.ClosedImmersion.pullbackIdealSheafIso`), proved by
transporting the ideal sheaf through the equivalence `j_*`.  That argument is unavailable for a
mere open immersion: `j_*` is then only fully faithful.  What replaces it is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, the restriction of a module along an open
immersion, which is a `SheafOfModules.pushforward` along the *image* functor on opens and is
therefore a right adjoint — hence preserves the kernel that defines the ideal sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictPushforwardCompIso`: the restriction along `j` of a
  direct image along `a ≫ j` is the direct image along `a`.
* `Stacks.ClosedImmersion.restrictIdealSheafIsoCompOpenImmersion`:
  `(ℐ_{a ≫ j})|_U ≅ ℐ_a`.
* `Stacks.ClosedImmersion.pullbackIdealSheafIsoCompOpenImmersion`:
  `(a ≫ j)^* ℐ_{a ≫ j} ≅ a^* ℐ_a`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isRightAdjoint_restrictFunctor`: restriction along an open
  immersion admits a left adjoint.  This is what makes it preserve kernels; it is not the
  adjunction `restrictFunctor j ⊣ pushforward j` of Mathlib, which exhibits restriction as a
  *left* adjoint and so gives only preservation of colimits.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_unitToPushforwardObjUnit` and
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_unitToPushforwardObjUnit_comp`: the
  commuting square of structure-sheaf maps that transports the kernel.

## Implementation notes

The three facts that make the restriction cheap are all definitional, and all three are used:

* `𝒪_C ⟶ (a ≫ j)_* 𝒪_Z` *is* `(𝒪_C ⟶ j_* 𝒪_U)` followed by `j_*` of `(𝒪_U ⟶ a_* 𝒪_Z)`,
  because `a_* ⋙ j_* = (a ≫ j)_*` and the structure-sheaf map of a composite is the composite
  of the structure-sheaf maps, both by `rfl`.  So the ideal sheaf of `a ≫ j` is the kernel of a
  two-step composite, and the first step is what the restriction cancels.
* `Γ(M|_U, V) = Γ(M, j ''ᵁ V)` by `rfl`, so `Mathlib`'s counit
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` is a single restriction map on
  sections, and the square against `restrictUnitIso` is exactly
  `AlgebraicGeometry.Scheme.Hom.appIso_hom`.
* `AlgebraicGeometry.Scheme.Modules.pullback f` is
  `RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom`, and likewise for the
  pushforward, by `rfl`.  So the `Scheme.Modules` vocabulary used here and the ringed-space
  vocabulary in which `Stacks.ClosedImmersion.idealSheaf` is stated need no bridge.

The left adjoint of `restrictFunctor j` is produced by Mathlib's instance for
`SheafOfModules.pushforward`, which is not found by instance search here: its hypothesis
`(PresheafOfModules.pushforward φ.hom).IsRightAdjoint` is stated for a morphism of presheaves
of rings with target `F.op ⋙ R`, whereas the morphism at hand has target the `.val` of a
sheaf-level pushforward, and the two agree only after unfolding past reducible transparency.
`Stacks.SheafOfModules.isRightAdjoint_pushforward_of_smallSites` supplies the hypothesis
explicitly, exactly as `RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint` does for
a morphism of ringed spaces.

## References

* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks

/-- A two-step rearrangement used to transport a kernel across a commuting square: from
`g ≫ h = m ≫ l` and `f ≫ m = k` conclude `(f ≫ g) ≫ h = k ≫ l`.  Stated separately so that the
rewriting happens on abstract morphisms, where the motive is manifestly well typed. -/
private theorem comp_comp_eq_comp_of_square {D : Type*} [CategoryTheory.Category D]
    {W X Y T Q : D}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Q) (m : X ⟶ T) (l : T ⟶ Q) (k : W ⟶ T)
    (h₁ : g ≫ h = m ≫ l) (h₂ : f ≫ m = k) : (f ≫ g) ≫ h = k ≫ l := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

end Stacks

namespace Stacks.SheafOfModules

/-- **The pushforward of sheaves of modules along a continuous functor between small sites
admits a left adjoint.**

This is Mathlib's instance for `CategoryTheory.SheafOfModules.pushforward`, with its
presheaf-level hypothesis discharged by hand.  Instance search does not discharge it: the
hypothesis asks for a left adjoint of `PresheafOfModules.pushforward ψ` for
`ψ : S.val ⟶ F.op ⋙ R.val`, and the morphism produced by `φ.hom` has as its target the `.val`
of the sheaf-level pushforward of `R`, which is that functor only after unfolding a definition
that instance search does not unfold. -/
theorem isRightAdjoint_pushforward_of_smallSites {A B : Type u} [SmallCategory A]
    [SmallCategory B] {J : GrothendieckTopology A} {K : GrothendieckTopology B} {F : A ⥤ B}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint :=
  have : (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  _root_.SheafOfModules.instIsRightAdjointPushforward φ

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Z U C : Scheme.{u}}

/-- **Restriction of modules along an open immersion admits a left adjoint**, because it is a
`CategoryTheory.SheafOfModules.pushforward` — along the functor `V ↦ j ''ᵁ V` on opens.

Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` exhibits restriction as a
*left* adjoint, which gives preservation of colimits; this gives preservation of limits, and in
particular of the kernel that defines an ideal sheaf. -/
@[sga "4 IV 11.2.2" "special case"]
instance isRightAdjoint_restrictFunctor (j : U ⟶ C) [IsOpenImmersion j] :
    (restrictFunctor j).IsRightAdjoint := by
  delta restrictFunctor
  exact Stacks.SheafOfModules.isRightAdjoint_pushforward_of_smallSites _

/-- **The restriction along `j` of a direct image along `a ≫ j` is the direct image along `a`.**

This is the counit of Mathlib's adjunction `restrictFunctor j ⊣ pushforward j`, which is an
isomorphism, read at `a_* M`: the equality `a_* ⋙ j_* = (a ≫ j)_*` holds by `rfl`, so no
transport along `AlgebraicGeometry.Scheme.Modules.pushforwardComp` is needed. -/
noncomputable def restrictPushforwardCompIso (a : Z ⟶ U) (j : U ⟶ C) [IsOpenImmersion j]
    (M : Z.Modules) :
    (restrictFunctor j).obj ((pushforward (a ≫ j)).obj M) ≅ (pushforward a).obj M :=
  (restrictFunctorAdjCounitIso j).app ((pushforward a).obj M)

/-- **The structure-sheaf map of an open immersion is cancelled by restricting along it.**

On sections over `V` the left-hand side is the map `Γ(C, j ''ᵁ V) ⟶ Γ(U, j ⁻¹ᵁ (j ''ᵁ V))`
induced by `j` followed by the restriction to `V`, and that composite is the inverse of the
section-level isomorphism `AlgebraicGeometry.Scheme.Hom.appIso` of the open immersion. -/
theorem restrictFunctor_map_unitToPushforwardObjUnit (j : U ⟶ C) [IsOpenImmersion j] :
    (restrictFunctor j).map (_root_.SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom j.toLRSHom.toShHom)) ≫
      (restrictFunctorAdjCounitIso j).hom.app
        (_root_.SheafOfModules.unit U.ringCatSheaf) =
      (restrictUnitIso j).hom := by
  ext V x
  exact congr($(j.appIso_hom V) x).symm

/-- **The commuting square that restricts the ideal sheaf.**  Restricting the structure-sheaf
map `𝒪_C ⟶ (a ≫ j)_* 𝒪_Z` of a composite along the open immersion `j` yields the
structure-sheaf map `𝒪_U ⟶ a_* 𝒪_Z` of `a`, up to the two canonical identifications of the
restricted source and target. -/
theorem restrictFunctor_map_unitToPushforwardObjUnit_comp (a : Z ⟶ U) (j : U ⟶ C)
    [IsOpenImmersion j] :
    (restrictFunctor j).map (_root_.SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (a ≫ j).toLRSHom.toShHom)) ≫
      (restrictPushforwardCompIso a j
        (_root_.SheafOfModules.unit (structureSheafRing Z.toRingedSpace))).hom =
      (restrictUnitIso j).hom ≫ _root_.SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom a.toLRSHom.toShHom) := by
  have hnat : (restrictFunctor j).map ((pushforward j).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a.toLRSHom.toShHom))) ≫
      (restrictFunctorAdjCounitIso j).hom.app
        ((pushforward a).obj (_root_.SheafOfModules.unit Z.ringCatSheaf)) =
      (restrictFunctorAdjCounitIso j).hom.app
          (_root_.SheafOfModules.unit U.ringCatSheaf) ≫
        _root_.SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a.toLRSHom.toShHom) :=
    (restrictFunctorAdjCounitIso j).hom.naturality _
  show ((restrictFunctor j).map (_root_.SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom j.toLRSHom.toShHom)) ≫
      (restrictFunctor j).map ((pushforward j).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom a.toLRSHom.toShHom)))) ≫
      (restrictFunctorAdjCounitIso j).hom.app
        ((pushforward a).obj (_root_.SheafOfModules.unit Z.ringCatSheaf)) = _
  exact Stacks.comp_comp_eq_comp_of_square _ _ _ _ _ _ hnat
    (restrictFunctor_map_unitToPushforwardObjUnit j)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.ClosedImmersion

variable {Z U C : Scheme.{u}}

/-- **The restriction along an open immersion `j : U ⟶ C` of the ideal sheaf of `a ≫ j` is the
ideal sheaf of `a`.**

Restriction preserves the kernel defining the ideal sheaf
(`AlgebraicGeometry.Scheme.Modules.isRightAdjoint_restrictFunctor`), and the two kernels are
then identified by the commuting square
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_unitToPushforwardObjUnit_comp`. -/
noncomputable def restrictIdealSheafIsoCompOpenImmersion (a : Z ⟶ U) (j : U ⟶ C)
    [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).obj (idealSheaf (a ≫ j).toLRSHom.toShHom) ≅
      idealSheaf a.toLRSHom.toShHom :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor j) _ ≪≫
    kernel.mapIso _ _ (Scheme.Modules.restrictUnitIso j)
      (Scheme.Modules.restrictPushforwardCompIso a j _)
      (Scheme.Modules.restrictFunctor_map_unitToPushforwardObjUnit_comp a j)

/-- **The pullback of the ideal sheaf is unchanged by enlarging the ambient scheme along an open
immersion**: for `j : U ⟶ C` an open immersion, `(a ≫ j)^* ℐ_{a ≫ j} ≅ a^* ℐ_a`.

This is `Stacks.ClosedImmersion.pullbackIdealSheafIso` with the hypothesis that `j` be an
isomorphism relaxed to `j` being an open immersion, which is the form [Stacks, Tag 01R3] (1)
needs: a closed-immersion factorization of an immersion through an arbitrary open subscheme is
related to the canonical one through `Scheme.Hom.coborderRange` by an open immersion, not by an
isomorphism. -/
noncomputable def pullbackIdealSheafIsoCompOpenImmersion (a : Z ⟶ U) (j : U ⟶ C)
    [IsOpenImmersion j] :
    (Scheme.Modules.pullback (a ≫ j)).obj (idealSheaf (a ≫ j).toLRSHom.toShHom) ≅
      (Scheme.Modules.pullback a).obj (idealSheaf a.toLRSHom.toShHom) :=
  (Scheme.Modules.pullbackComp a j).symm.app _ ≪≫
    (Scheme.Modules.pullback a).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app _ ≪≫
        restrictIdealSheafIsoCompOpenImmersion a j)

end Stacks.ClosedImmersion

end
