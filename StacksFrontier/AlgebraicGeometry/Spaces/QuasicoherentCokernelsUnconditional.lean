module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffinePresentationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# The cokernel of a morphism of quasi-coherent modules on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. This file
proves that the cokernel of a morphism of quasi-coherent `𝒪_F`-modules on the small étale site
of `F` is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_cokernel_over_of_isAffineChart`: over an affine
  étale chart carrying global presentations of the source and the target, the restricted
  cokernel has a global presentation.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`: the cokernel of a
  morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent.
* `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`: the same in the
  `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` form.

## Implementation notes

The module universe is the universe `u` of the schemes, as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_affineCharts`: a cokernel of sheaves
of modules is the sheafification of the cokernel of presheaves, and sheafification of
`AddCommGrpCat`-valued presheaves on the small étale site is available at `u` and at every
universe containing the objects of the site. The universe of the indexing types of a
presentation is `u + 1`, the universe of the objects of the site, as
`SheafOfModules.HasGlobalPresentation` prescribes; at that universe the sheafification
conditions on the slice sites come from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A functor preserving zero morphisms sends a composite equal to zero to a composite equal to
zero. -/
private theorem map_comp_eq_zero {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms] {X Y Z : C} {g : X ⟶ Y}
    {h : Y ⟶ Z} (w : g ≫ h = 0) : G.map g ≫ G.map h = 0 := by
  rw [← G.map_comp, w, G.map_zero]

/-- Let `f : M ⟶ N` be a morphism of `𝒪_F`-modules and let `V` be an étale chart of `F` whose
underlying scheme is affine, over which both `M` and `N` admit a global presentation. Then the
restriction of the cokernel of `f` to `V` admits a global presentation. -/
theorem hasGlobalPresentation_cokernel_over_of_isAffineChart
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N)
    (V : (smallEtaleRingedSite B S hS F hF).C) (hV : IsAffineChart B S hS F V)
    (hM : (M.over V).HasGlobalPresentation) (hN : (N.over V).HasGlobalPresentation) :
    ((cokernel f).over V).HasGlobalPresentation := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hN
  obtain ⟨I', F', ν, ⟨hF'⟩, p, hp⟩ := hM.exists_epi_of_isColimit_cofan
  have hsheaf : HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over V)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1}
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have hwloc : ((smallEtaleRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u}
      ((smallEtaleRingedSite B S hS F hF).J.over V)
  have hab' : a.val ≫ b.val = 0 := by
    rw [show a.val ≫ b.val = (a ≫ b).val from rfl, hab]; rfl
  have hbepi : Epi b := Cofork.IsColimit.epi hb
  have hsurj := SmallEtale.surjective_val_app_of_isColimit_of_isAffineOver
    B S hS F hF κ ι hQ hP a b hab' hab hb (Over.mk (𝟙 V)) hV
  set E := SheafOfModules.overFunctor.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) V with hE
  have hEzero : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hshAll : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over U) AddCommGrpCat.{u} := by
    change ∀ U : SmallEtale B S hS F,
      HasSheafify ((SmallEtale.topology B S hS F).over U) AddCommGrpCat.{u}
    infer_instance
  have hshV := hshAll V
  have hEfin : PreservesFiniteColimits E :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hzE := map_comp_eq_zero E (cokernel.condition f)
  have hcokover : IsColimit (CokernelCofork.ofπ (E.map (cokernel.π f)) hzE) :=
    isColimitCoforkMapOfIsColimit' E (cokernel.condition f) (cokernelIsCokernel f)
  set L := SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u + 1}
    (R := ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).over V) with hL
  have hLfin : PreservesFiniteColimits L :=
    SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u + 1, u, u, u, u + 1}
  have hzL := map_comp_eq_zero L hzE
  have hcokulift : IsColimit (CokernelCofork.ofπ (L.map (E.map (cokernel.π f))) hzL) :=
    isColimitCoforkMapOfIsColimit' L hzE hcokover
  exact SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app
    hP hQ hF' hab hb Over.mkIdTerminal hsurj (p := p) hzL hcokulift

/-- The cokernel of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent. -/
theorem isQuasicoherentOnSite_cokernel_unconditional {M N : Modules.{u, u} B S hS F hF}
    [M.IsQuasicoherentOnSite] [N.IsQuasicoherentOnSite] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_cokernel_of_affineCharts B S hS F hF f
    fun V hV hMV hNV =>
      hasGlobalPresentation_cokernel_over_of_isAffineChart B S hS F hF f V hV hMV hNV

/-- The quasi-coherent `𝒪_F`-modules are closed under cokernels. -/
theorem isClosedUnderCokernels_quasicoherentSheaves :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels where
  cokernels_le := by
    rintro T ⟨f, k, hk, hf⟩
    have hM : (_ : Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite := hf.1
    have hN : (_ : Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite := hf.2
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (isQuasicoherentOnSite_cokernel_unconditional B S hS F hF f)

end AlgebraicGeometry.Space

end
