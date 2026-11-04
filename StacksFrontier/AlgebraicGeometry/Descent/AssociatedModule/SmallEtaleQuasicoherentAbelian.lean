module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Colimits and kernels of quasi-coherent modules on the small étale site

Let `S` be a scheme contained in a big étale site.  The quasi-coherent `𝒪`-modules on the small
étale site of `S` are closed, inside all `𝒪`-modules, under colimits and under kernels.  These
are the colimit and kernel clauses of Descent, Lemma 0GNB, and the proof is the one of the
source: the functor `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` (Stacks 03DX
(2) at `τ = étale`, unconditional in this library), the corresponding closure properties hold
for quasi-coherent modules on the scheme `S`, and `𝓕 ↦ 𝓕^a` commutes with colimits, being a
left adjoint, and with finite limits, being the pullback along a flat morphism of ringed sites.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_equivalence` and
  `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_of_equivalence`: a property of
  objects closed under isomorphisms whose full subcategory is equivalent to one with colimits
  (resp. limits) of a shape is closed under them, as soon as the equivalence followed by the
  inclusion preserves them.
* `AlgebraicGeometry.SmallEtale.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`: a colimit
  of quasi-coherent modules on the small étale site is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite` and
  `AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite`: so are a kernel
  and a cokernel of a morphism of quasi-coherent modules.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty C} {Q : ObjectProperty D}

/-- A property of objects closed under isomorphisms is closed under colimits of shape `K` as soon
as its full subcategory is equivalent to one with colimits of shape `K`, by an equivalence whose
composite with the inclusion preserves them: the inclusion then preserves them as well, and the
colimit of a diagram of objects with the property is the image of a colimit in the full
subcategory. -/
theorem isClosedUnderColimitsOfShape_of_equivalence
    (e : P.FullSubcategory ≌ Q.FullSubcategory) [Q.IsClosedUnderIsomorphisms]
    (K : Type*) [Category* K] [HasColimitsOfShape K P.FullSubcategory]
    [PreservesColimitsOfShape K (e.functor ⋙ Q.ι)] :
    Q.IsClosedUnderColimitsOfShape K := by
  have : PreservesColimitsOfShape K Q.ι :=
    preservesColimitsOfShape_of_natIso (e.invFunIdAssoc Q.ι)
  have : HasColimitsOfShape K Q.FullSubcategory :=
    Adjunction.hasColimitsOfShape_of_equivalence e.inverse
  refine ⟨fun X ⟨h⟩ => ?_⟩
  let F := Q.lift h.diag h.prop_diag_obj
  exact Q.prop_of_iso
    ((isColimitOfPreserves Q.ι (colimit.isColimit F)).coconePointUniqueUpToIso h.isColimit)
    (colimit F).property

/-- A property of objects closed under isomorphisms is closed under limits of shape `K` as soon
as its full subcategory is equivalent to one with limits of shape `K`, by an equivalence whose
composite with the inclusion preserves them. -/
theorem isClosedUnderLimitsOfShape_of_equivalence
    (e : P.FullSubcategory ≌ Q.FullSubcategory) [Q.IsClosedUnderIsomorphisms]
    (K : Type*) [Category* K] [HasLimitsOfShape K P.FullSubcategory]
    [PreservesLimitsOfShape K (e.functor ⋙ Q.ι)] :
    Q.IsClosedUnderLimitsOfShape K := by
  have : PreservesLimitsOfShape K Q.ι :=
    preservesLimitsOfShape_of_natIso (e.invFunIdAssoc Q.ι)
  have : HasLimitsOfShape K Q.FullSubcategory :=
    Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  refine ⟨fun X ⟨h⟩ => ?_⟩
  let F := Q.lift h.diag h.prop_diag_obj
  exact Q.prop_of_iso
    ((isLimitOfPreserves Q.ι (limit.isLimit F)).conePointUniqueUpToIso h.isLimit)
    (limit F).property

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A property of objects closed under colimits of parallel pairs is closed under cokernels. -/
theorem isClosedUnderCokernels_of_isClosedUnderColimitsOfShape
    [Q.IsClosedUnderColimitsOfShape WalkingParallelPair] : Q.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨_, _, hk, hX, hY⟩
    exact Q.prop_of_isColimit hk (by rintro (_ | _) <;> assumption)

/-- A property of objects closed under isomorphisms is closed under kernels as soon as its full
subcategory is equivalent to the full subcategory of a property closed under kernels, by an
equivalence which, followed by the inclusion, is the inclusion followed by a functor preserving
kernels. -/
theorem isClosedUnderKernels_of_equivalence
    (e : P.FullSubcategory ≌ Q.FullSubcategory) [Q.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [HasKernels C] (a : C ⥤ D) [a.PreservesZeroMorphisms]
    [PreservesLimitsOfShape WalkingParallelPair a] (eα : e.functor ⋙ Q.ι ≅ P.ι ⋙ a) :
    Q.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, h₁, h₂⟩
    let X₁ : Q.FullSubcategory := ⟨_, h₁⟩
    let X₂ : Q.FullSubcategory := ⟨_, h₂⟩
    let f' : X₁ ⟶ X₂ := ObjectProperty.homMk f
    let g := e.inverse.map f'
    let α₁ : a.obj (e.inverse.obj X₁).obj ≅ X₁.obj :=
      (eα.app _).symm ≪≫ Q.ι.mapIso (e.counitIso.app X₁)
    let α₂ : a.obj (e.inverse.obj X₂).obj ≅ X₂.obj :=
      (eα.app _).symm ≪≫ Q.ι.mapIso (e.counitIso.app X₂)
    have w : a.map g.hom ≫ α₂.hom = α₁.hom ≫ f := by
      have h₁ := eα.inv.naturality g
      have h₂ := e.counitIso.hom.naturality f'
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc, α₁, α₂, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
        Functor.mapIso_hom, Iso.app_hom, ObjectProperty.ι_map]
      rw [reassoc_of% h₁]
      congr 1
      exact congrArg InducedCategory.Hom.hom h₂
    have iso := KernelFork.mapIsoOfIsLimit (isLimitOfHasKernelOfPreservesLimit a g.hom) hk
      (Arrow.isoMk α₁ α₂ w.symm)
    exact Q.prop_of_iso iso <| Q.prop_of_iso
      (eα.app ⟨_, P.prop_kernel g.hom (e.inverse.obj X₁).property (e.inverse.obj X₂).property⟩)
      (e.functor.obj _).property

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Colimits of quasi-coherent modules on the small étale site are quasi-coherent** (Descent,
Lemma 0GNB, the colimit clause), for every shape along which modules over a ring and modules on
`S` have colimits.  The quasi-coherent modules on `S` are closed under such colimits, the
associated-module functor `𝓕 ↦ 𝓕^a` preserves them, and it is an equivalence onto the
quasi-coherent modules on the small étale site. -/
theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite (K : Type*) [Category* K]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape K := by
  have := BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι S K
  have : HasColimitsOfShape K (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    BigFppfOver.hasColimitsOfShape_isQuasicoherent S K
  have : PreservesColimitsOfShape K
      ((associatedModuleEquivalence' B S hS).functor ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)).ι) :=
    preservesColimitsOfShape_associatedModuleQcoh B S hS K
  exact ObjectProperty.isClosedUnderColimitsOfShape_of_equivalence
    (associatedModuleEquivalence' B S hS) K

/-- **Cokernels of quasi-coherent modules on the small étale site are quasi-coherent.** -/
instance isClosedUnderCokernels_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderCokernels :=
  have := isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS WalkingParallelPair
  ObjectProperty.isClosedUnderCokernels_of_isClosedUnderColimitsOfShape

/-- **Kernels of quasi-coherent modules on the small étale site are quasi-coherent** (Descent,
Lemma 0GNB, the kernel clause).  The quasi-coherent modules on `S` are closed under kernels, the
associated-module functor is left exact, being the pullback along a flat morphism of ringed
sites (Stacks 08H8), and it is an equivalence onto the quasi-coherent modules on the small étale
site. -/
instance isClosedUnderKernels_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderKernels :=
  ObjectProperty.isClosedUnderKernels_of_equivalence (associatedModuleEquivalence' B S hS)
    (associatedModuleOfSheaf B S hS) (Iso.refl _)

end AlgebraicGeometry.SmallEtale

end
