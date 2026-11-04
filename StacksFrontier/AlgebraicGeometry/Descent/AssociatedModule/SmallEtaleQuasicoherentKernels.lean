module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BoundedSmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The counit at a quasi-coherent module, and exactness of `ε_*` there

Let `S` be a scheme contained in a big étale site `B`, and write `ε^*` for the associated-module
functor `𝓕 ↦ 𝓕^a` of Stacks 03DU (4) at `τ = étale`,
`AlgebraicGeometry.SmallEtale.associatedModule`, with right adjoint `ε_*` the restriction
`AlgebraicGeometry.SmallEtale.restrictModule` along the inclusion of the small Zariski site.

This file records, with no hypothesis, that the counit `ε^*ε_*𝒢 ⟶ 𝒢` is an isomorphism at a
quasi-coherent `𝒢` on `S_étale` — so that such a `𝒢` *is* `(ε_*𝒢)^a` with `ε_*𝒢` quasi-coherent on
`S`, which is what every argument about quasi-coherent modules on `S_étale` in this development
starts from — and the consequence that `ε_*` is exact at a short exact sequence whose sub-object
is quasi-coherent.

## The two inputs of the counit statement

* `AlgebraicGeometry.SmallEtale.isIso_counit`, the counit criterion, whose hypothesis is that
  `ε_*𝒢` be quasi-coherent on `S`;
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, which discharges it.

## Exactness of `ε_*`

`ε_*` is left exact, being a right adjoint.  It is exact on the right as well at a short exact
sequence `0 → 𝓗₁ → ℰ → 𝓗₂ → 0` whose sub-object `𝓗₁` is quasi-coherent, because the first higher
direct image of the abelian sheaf underlying `𝓗₁` vanishes: that is Stacks 03DW, formalized as
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_opensToSmallEtale`, read at a sheaf
of *modules* through the sections formula `𝓕^a(T) = Γ(T, f^*𝓕)` of Stacks 070S (2),
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`.  A left exact functor is right exact
at such a sequence by
`Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one`.

## Main results

* `AlgebraicGeometry.SmallEtale.counit_naturality_associatedModule`: the naturality square of the
  counit, in the form its consumers use it.
* `AlgebraicGeometry.SmallEtale.toSheafAssociatedModuleIso`: the abelian sheaf underlying `𝓕^a`
  is the associated abelian sheaf of `𝓕`, which is the sections formula of Stacks 070S (2) in
  the shape the higher direct images are stated in.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf`: the higher direct
  images along `ε` of the abelian sheaf underlying a quasi-coherent module on `S_étale` vanish.
* `AlgebraicGeometry.SmallEtale.epi_restrictModule_map_g` and
  `AlgebraicGeometry.SmallEtale.shortExact_restrictModule_map`: `ε_*` is exact at a short exact
  sequence whose sub-object is quasi-coherent.

## Where the closure properties of quasi-coherence are

The kernel and cokernel clauses of Stacks 0GNB part (3) are
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_kernel` and
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_cokernel`, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentExtensions.lean`
alongside the extension clause they combine with; the object-property instances
`AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite` and
`AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite` that instance search
uses are in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentAbelian.lean` and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentWeakSerre.lean`.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The naturality square of the counit at a morphism of modules on the small étale site:
`ε^*(ε_* a)` followed by the counit is the counit followed by `a`. -/
public theorem counit_naturality_associatedModule
    {F F' : SheafOfModules.{u} (structureSheaf B S hS)} (a : F ⟶ F') :
    (associatedModule B S hS).map ((restrictModule B S hS).map a) ≫
        (associatedModuleAdjunction B S hS).counit.app F' =
      (associatedModuleAdjunction B S hS).counit.app F ≫ a :=
  (associatedModuleAdjunction B S hS).counit.naturality a

/-! ### The sections formula as an identification of abelian sheaves -/

/-- **The abelian sheaf underlying `𝓕^a` is the associated abelian sheaf of `𝓕`.**  Both have
`(f : T → S) ↦ Γ(T, f^*𝓕)` as their presheaf of sections, the first by the sections formula of
Stacks 070S (2) and the second by construction, so the identification is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` read through the full faithfulness of
the inclusion of sheaves into presheaves. -/
public def toSheafAssociatedModuleIso (F : S.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F) ≅
      boundedSmallEtaleAssociatedSheaf B S hS F :=
  (fullyFaithfulSheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).preimageIso
    (associatedModulePresheafIso B S hS F)

/-- **The higher direct images along `ε : S_étale ⟶ S_Zar` of the abelian sheaf underlying a
quasi-coherent module on `S_étale` vanish**, with no hypothesis.  This is Stacks 03DW read at a
sheaf of modules.

A quasi-coherent `𝒢` on `S_étale` is `(ε_*𝒢)^a` by
`AlgebraicGeometry.SmallEtale.isIso_counit'`, with `ε_*𝒢` quasi-coherent
on `S`; the identification of abelian sheaves is
`AlgebraicGeometry.SmallEtale.toSheafAssociatedModuleIso`; and the vanishing for the associated
abelian sheaf of a quasi-coherent `𝒪_S`-module is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_opensToSmallEtale`. -/
public theorem isZero_rightDerived_pushforward_toSheaf
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((boundedZariskiAbelianPushforward B S hS).rightDerived p).obj
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G)) := by
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := isQuasicoherent_restrictModule B S hS G hG
  have : IsIso ((associatedModuleAdjunction B S hS).counit.app G) :=
    isIso_counit' B S hS G hG
  have e : (SheafOfModules.toSheaf (structureSheaf B S hS)).obj G ≅
      boundedSmallEtaleAssociatedSheaf B S hS ((restrictModule B S hS).obj G) :=
    (SheafOfModules.toSheaf (structureSheaf B S hS)).mapIso
        (asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm ≪≫
      toSheafAssociatedModuleIso B S hS _
  exact (isZero_rightDerived_pushforward_opensToSmallEtale B S hS
    ((restrictModule B S hS).obj G) p hp).of_iso
      (((boundedZariskiAbelianPushforward B S hS).rightDerived p).mapIso e)

/-! ### `ε_*` is exact at a sequence with quasi-coherent sub-object -/

/-- A functor preserving monomorphisms and the kernel of `g` maps a short exact sequence to a short
exact sequence as soon as it preserves the epimorphism `g`. -/
private theorem shortExact_map_of_epi_map_g {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] {T : ShortComplex C} (hT : T.ShortExact) (F : C ⥤ D) [F.Additive]
    [F.PreservesMonomorphisms] [PreservesLimit (parallelPair T.g 0) F] (hg : Epi (F.map T.g)) :
    (T.map F).ShortExact :=
  have := hT.mono_f
  { exact := hT.exact.map_of_mono_of_preservesKernel F hT.mono_f inferInstance
    mono_f := F.map_mono T.f
    epi_g := hg }

/-- **`ε_*` is right exact at a short exact sequence whose sub-object is quasi-coherent.**  The
image of the short exact sequence under `ε_*` is exact on the right.

The underlying abelian sheaves form a short exact sequence, because the forgetful functor to
abelian sheaves preserves finite limits and epimorphisms; the first higher direct image of its
sub-object vanishes by
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf`; so the direct image of
abelian sheaves, being left exact, is right exact there by
`Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one`.  Direct image of
modules and direct image of abelian sheaves agree, and a morphism of sheaves of modules is an
epimorphism exactly when the underlying morphism of abelian presheaves is locally surjective. -/
public theorem epi_restrictModule_map_g
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) : Epi ((restrictModule B S hS).map T.g) := by
  have := hT.mono_f
  have := hT.epi_g
  have hab : (T.map (SheafOfModules.toSheaf (structureSheaf B S hS))).ShortExact :=
    shortExact_map_of_epi_map_g hT _ (Stacks.SheafOfModules.EpiMono.epi_toSheaf_map T.g)
  have hzero : IsZero (((boundedZariskiAbelianPushforward B S hS).rightDerived 1).obj
      (T.map (SheafOfModules.toSheaf (structureSheaf B S hS))).X₁) :=
    isZero_rightDerived_pushforward_toSheaf B S hS T.X₁ h₁ 1 Nat.one_pos
  have hq : Epi ((SheafOfModules.toSheaf S.ringCatSheaf).map
      ((restrictModule B S hS).map T.g)) :=
    Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one hab
      (boundedZariskiAbelianPushforward B S hS) hzero
  have hls : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf S.ringCatSheaf).map
      ((restrictModule B S hS).map T.g)) := by
    rw [Sheaf.isLocallySurjective_iff_epi']
    exact hq
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ hls

/-- **`ε_*` is exact at a short exact sequence whose sub-object is quasi-coherent.**  Left
exactness is automatic, `ε_*` being a right adjoint, and right exactness is
`AlgebraicGeometry.SmallEtale.epi_restrictModule_map_g`.

Additivity of `ε_*`, which the statement needs for `CategoryTheory.ShortComplex.map` to be
formed, is the imported `AlgebraicGeometry.SmallEtale.additive_restrictModule`.  That `ε_*` is a
right adjoint, from which limit preservation follows, is established in the proof rather than
declared as an instance. -/
public theorem shortExact_restrictModule_map
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) : (T.map (restrictModule B S hS)).ShortExact :=
  have : (restrictModule B S hS).IsRightAdjoint :=
    (associatedModuleAdjunction B S hS).isRightAdjoint
  have := hT.mono_f
  shortExact_map_of_epi_map_g hT _ (epi_restrictModule_map_g B S hS hT h₁)

end AlgebraicGeometry.SmallEtale

end
