module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSmallEtaleQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSliceAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentLocalSerre

/-!
# Quasi-coherence on the spaces-étale site is a weak Serre class

Let `X` be an algebraic space over a scheme `S`.  This file proves that the quasi-coherent modules
on each slice of the ringed spaces-étale site `X_{spaces, étale}`, with their sections in the
universe `u + 1` of that site, form a weak Serre subcategory: they are closed under kernels,
cokernels and extensions (Stacks 03M1).  This is the standing assumption of the unbounded
cohomological descent of Stacks 0DC1 for the family of Stacks 0DC5.

## The argument

The slice at `V` is the spaces-étale site of the algebraic space underlying `V` (Stacks 04LY),
and modules on the spaces-étale site of an algebraic space `Y` are `𝒪_Y`-modules on its small
étale site with sections in `Type (u + 1)`, quasi-coherence corresponding
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_smallEtale`).  On the small étale site
quasi-coherence is being cartesian on affine charts, Descent, Proposition 03DX (2): the
implication from cartesian to quasi-coherent is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse`, and
the converse at `Type (u + 1)` is read off the spaces-étale site through Stacks 0H04
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_smallEtaleModule`).  Being cartesian is
stable under kernels by flatness, and under cokernels and extensions once the relevant maps are
surjective on the sections over affine charts; that surjectivity is the vanishing of the first
cohomology of a quasi-coherent module over an affine object of the spaces-étale site
(`AlgebraicGeometry.Space.SpacesEtale.surjective_val_app_of_shortExact_of_isAffineSpace`), read
on the small étale site (`AlgebraicGeometry.Space.surjective_val_app_of_epi_succ`, Stacks 03DW).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_succ`: Descent,
  Proposition 03DX (2), at module sections in `Type (u + 1)`.
* `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_succ`: Stacks 03M1 as a weak
  Serre class on the small étale site, at module sections in `Type (u + 1)`.
* `AlgebraicGeometry.Space.quasicoherentSheaves_spacesEtale_isWeakSerreClass`: the same on the
  ringed spaces-étale site.
* `AlgebraicGeometry.Space.isWeakSerreClass_spacesEtaleQuasicoherentSlices`: **the same on every
  slice of the spaces-étale site.**

## Implementation notes

`CategoryTheory.SheafOfModules.instAbelian` is raised locally in priority, as in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional`, so that the kernels
and cokernels named below are those of the abelian structure at the module universe in play.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0DC1](https://stacks.math.columbia.edu/tag/0DC1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- The transport of a quasi-coherent module to the spaces-étale site is quasi-coherent. -/
private theorem isQuasicoherentOnSite_smallEtaleModuleEquivalence_inverse_obj
    {G : Modules.{u, u + 1} B S hS Y.obj Y.2} (hG : G.IsQuasicoherentOnSite) :
    ((smallEtaleModuleEquivalence B S hS Y).inverse.obj G).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_smallEtale B S hS Y _).2
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((smallEtaleModuleEquivalence B S hS Y).counitIso.app G).symm hG)

/-- **Descent, Proposition 03DX (2), one implication, at module sections in `Type (u + 1)`.** -/
theorem isCartesianOnAffineCharts_of_isQuasicoherentOnSite_succ
    (G : Modules.{u, u + 1} B S hS Y.obj Y.2) (hG : G.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts G := by
  let E := smallEtaleModuleEquivalence B S hS Y
  exact IsCartesianOnAffineCharts.of_iso (E.counitIso.app G)
    (isCartesianOnAffineCharts_smallEtaleModule B S hS Y _
      (isQuasicoherentOnSite_smallEtaleModuleEquivalence_inverse_obj B S hS Y hG))

/-- Surjectivity on sections is read through the restriction to the lifted small étale site. -/
theorem surjective_moduleRestrictionEquivalence_map_val_app
    {M N : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)} (φ : M ⟶ N)
    (Z : SmallEtaleLifted B S hS Y)
    (h : Function.Surjective (φ.val.app (op ((liftedComparisonFunctor B S hS Y).obj Z)))) :
    Function.Surjective
      (((Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (smallEtaleLiftedTopology B S hS Y)
        (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).functor.map φ).val.app (op Z)) := h

set_option synthInstance.maxHeartbeats 400000 in
/-- Surjectivity on sections is read through the transport to the small étale site. -/
theorem surjective_readingEquivalence_map_val_app
    {M N : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)} (φ : M ⟶ N)
    (W : SmallEtale B S hS Y.obj)
    (h : Function.Surjective
      (((Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (smallEtaleLiftedTopology B S hS Y)
        (SpacesEtale.topology B S hS Y) (liftedComparisonFunctor B S hS Y)
        (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).functor.map φ).val.app
          (op ((smallEtaleLiftedEquiv B S hS Y).functor.obj W)))) :
    Function.Surjective (((readingEquivalence B S hS Y).functor.map φ).val.app (op W)) := h

/-- Surjectivity on sections is read through the change of coefficients. -/
theorem surjective_smallEtaleModuleEquivalence_map_val_app
    {M N : SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)} (φ : M ⟶ N)
    (W : SmallEtale B S hS Y.obj)
    (h : Function.Surjective (((readingEquivalence B S hS Y).functor.map φ).val.app (op W))) :
    Function.Surjective
      (((smallEtaleModuleEquivalence B S hS Y).functor.map φ).val.app (op W)) := h

/-- **Descent, Proposition 03DW, in the form the closure arguments use it, at module sections in
`Type (u + 1)`.**  An epimorphism of `𝒪_Y`-modules whose kernel is cartesian on affine charts is
surjective on the sections over every affine étale chart. -/
theorem surjective_val_app_of_epi_succ {P Q : Modules.{u, u + 1} B S hS Y.obj Y.2} (q : P ⟶ Q)
    (hq : Epi q) (hK : IsCartesianOnAffineCharts (kernel q)) (W : SmallEtale B S hS Y.obj)
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.obj ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  let E := smallEtaleModuleEquivalence B S hS Y
  let q' := E.inverse.map q
  have : Epi q' := E.inverse.map_epi q
  let T : ShortComplex (SheafOfModules.{u + 1} (ringSheaf (spacesEtaleRingedSite B S hS Y).O)) :=
    ShortComplex.mk (kernel.ι q') q' (kernel.condition q')
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel T (kernelIsKernel q'))
      (inferInstanceAs (Mono (kernel.ι q'))) (inferInstanceAs (Epi q'))
  have hK' : (kernel q').IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (PreservesKernel.iso E.inverse q)
      (isQuasicoherentOnSite_smallEtaleModuleEquivalence_inverse_obj B S hS Y
        (isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse _ hK))
  let Z := (smallEtaleLiftedEquiv B S hS Y).functor.obj W
  have h1 : Function.Surjective (q'.val.app (op ((liftedComparisonFunctor B S hS Y).obj Z))) :=
    SpacesEtale.surjective_val_app_of_shortExact_of_isAffineSpace (X := Y) hT hK'
      ((liftedComparisonFunctor B S hS Y).obj Z) (isAffineSpace_yoneda B S hS _ hW)
  have hs : Function.Surjective ((E.functor.map q').val.app (op W)) :=
    surjective_smallEtaleModuleEquivalence_map_val_app B S hS Y q' W
      (surjective_readingEquivalence_map_val_app B S hS Y q' W
        (surjective_moduleRestrictionEquivalence_map_val_app B S hS Y q' Z h1))
  have heq : (E.counitIso.app P).inv ≫ E.functor.map q' ≫ (E.counitIso.app Q).hom = q := by
    rw [show E.functor.map q' ≫ (E.counitIso.app Q).hom = (E.counitIso.app P).hom ≫ q from
      E.counitIso.hom.naturality q, Iso.inv_hom_id_assoc]
  rw [← heq]
  exact (SheafOfModules.bijective_iso_hom_val_app (E.counitIso.app Q) (op W)).2.comp
    (hs.comp (SheafOfModules.bijective_iso_hom_val_app (E.counitIso.app P).symm (op W)).2)

/-- Descent, Proposition 03DX (2), at module sections in `Type (u + 1)`. -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_succ
    (G : Modules.{u, u + 1} B S hS Y.obj Y.2) :
    G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G :=
  ⟨isCartesianOnAffineCharts_of_isQuasicoherentOnSite_succ B S hS Y G,
    isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse G⟩

/-! ### The cokernel clause at module sections in `Type (u + 1)` -/

variable {B S hS Y}

/-- The kernel of the projection of a morphism of cartesian modules onto its image is cartesian. -/
theorem isCartesianOnAffineCharts_kernel_factorThruImage_succ
    {M N : Modules.{u, u + 1} B S hS Y.obj Y.2} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (kernel (Abelian.factorThruImage f)) :=
  IsCartesianOnAffineCharts.of_iso
    (kernelIsoOfEq (Abelian.image.fac f).symm ≪≫
      kernelCompMono (Abelian.factorThruImage f) (Abelian.image.ι f))
    (isCartesianOnAffineCharts_kernel f hM hN)

/-- The projection of a morphism of cartesian modules onto its image is surjective on the sections
over an affine chart. -/
theorem surjective_val_app_factorThruImage_succ
    {M N : Modules.{u, u + 1} B S hS Y.obj Y.2} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (U : SmallEtale B S hS Y.obj)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.obj ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((Abelian.factorThruImage f).val.app (op U)) :=
  surjective_val_app_of_epi_succ B S hS Y (Abelian.factorThruImage f) inferInstance
    (isCartesianOnAffineCharts_kernel_factorThruImage_succ f hM hN) U hU

/-- The image of a morphism of cartesian modules is cartesian. -/
theorem isCartesianOnAffineCharts_image_succ
    {M N : Modules.{u, u + 1} B S hS Y.obj Y.2} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (Abelian.image f) := by
  have hk : IsCartesianOnAffineCharts (kernel f) := isCartesianOnAffineCharts_kernel f hM hN
  have hki : IsCartesianOnAffineCharts (kernel (cokernel.π (kernel.ι f))) :=
    IsCartesianOnAffineCharts.of_iso (asIso (Abelian.factorThruImage (kernel.ι f))) hk
  have hiso : ∀ W : SmallEtale B S hS Y.obj, Function.Surjective
      ((Abelian.factorThruImage (kernel.ι f)).val.app (op W)) := fun W =>
    (bijective_moduleHom_app (Abelian.factorThruImage (kernel.ι f))
      (inv (Abelian.factorThruImage (kernel.ι f))) (IsIso.hom_inv_id _)
      (IsIso.inv_hom_id _) W).2
  exact IsCartesianOnAffineCharts.of_iso (Abelian.coimageIsoImage f)
    (isCartesianOnAffineCharts_cokernel (kernel.ι f) (cokernel.π (kernel.ι f))
      (fun W hW => surjective_val_app_of_epi_succ B S hS Y (cokernel.π (kernel.ι f))
        inferInstance hki W hW)
      (fun W _ => SheafOfModules.exact_val_app_cokernel_π (kernel.ι f) (op W) (hiso W))
      hk hM)

/-- The cokernel of a morphism of cartesian modules is cartesian. -/
theorem isCartesianOnAffineCharts_cokernel_succ
    {M N : Modules.{u, u + 1} B S hS Y.obj Y.2} (f : M ⟶ N)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) :
    IsCartesianOnAffineCharts (cokernel f) :=
  isCartesianOnAffineCharts_cokernel f (cokernel.π f)
    (fun U hU => surjective_val_app_of_epi_succ B S hS Y (cokernel.π f) inferInstance
      (isCartesianOnAffineCharts_image_succ f hM hN) U hU)
    (fun U hU => SheafOfModules.exact_val_app_cokernel_π f (op U)
      (surjective_val_app_factorThruImage_succ f hM hN U hU))
    hM hN

/-! ### The extension clause at module sections in `Type (u + 1)` -/

/-- The base change comparison of the middle term of a short exact sequence is bijective when those
of the outer terms are and the right-hand map is surjective on sections over the larger chart. -/
theorem bijective_sectionsBaseChange_shortExact_X₂_succ
    (T : ShortComplex (Modules.{u, u + 1} B S hS Y.obj Y.2)) (hT : T.ShortExact)
    {U V : SmallEtale B S hS Y.obj} (f : V ⟶ U)
    (hgU : Function.Surjective (T.g.val.app (op U)))
    (h₁ : Function.Bijective (sectionsBaseChange T.X₁ f))
    (h₃ : Function.Bijective (sectionsBaseChange T.X₃ f)) :
    Function.Bijective (sectionsBaseChange T.X₂ f) := by
  let _ := chartAlgebra (hF := Y.2) f
  exact bijective_baseChange_of_shortExact_middle
    (φU := (T.f.val.app (op U)).hom) (πU := (T.g.val.app (op U)).hom)
    (φV := (T.f.val.app (op V)).hom) (πV := (T.g.val.app (op V)).hom)
    hgU (SheafOfModules.exact_val_app_of_shortExact hT (op U))
    (SheafOfModules.injective_f_val_app_of_shortExact hT (op V))
    (SheafOfModules.exact_val_app_of_shortExact hT (op V))
    (app_sectionsBaseChange T.f f) (app_sectionsBaseChange T.g f) h₁ h₃

/-- An extension of modules cartesian on affine charts is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_shortExact_X₂_succ
    (T : ShortComplex (Modules.{u, u + 1} B S hS Y.obj Y.2)) (hT : T.ShortExact)
    (h₁ : IsCartesianOnAffineCharts T.X₁) (h₃ : IsCartesianOnAffineCharts T.X₃) :
    IsCartesianOnAffineCharts T.X₂ := by
  obtain ⟨e, -⟩ := SheafOfModules.exists_isKernelIso_of_shortExact hT
  exact fun U V hU hV f => bijective_sectionsBaseChange_shortExact_X₂_succ T hT f
    (surjective_val_app_of_epi_succ B S hS Y T.g hT.epi_g
      (IsCartesianOnAffineCharts.of_iso e h₁) U hU) (h₁ U V hU hV f) (h₃ U V hU hV f)

variable (B S hS Y)

/-- **Quasi-coherence of `𝒪_Y`-modules with sections in `Type (u + 1)` on the small étale site of
an algebraic space is a weak Serre class**: closed under kernels, cokernels and extensions. -/
theorem quasicoherentSheaves_isWeakSerreClass_succ :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)).IsWeakSerreClass := by
  have hiff := isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_succ B S hS Y
  have := isClosedUnderKernels_quasicoherentSheaves B S hS Y.obj Y.2 hiff
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)).IsClosedUnderCokernels :=
    { cokernels_le := by
        rintro _ ⟨f, c, hc, hf⟩
        exact ObjectProperty.prop_of_iso _
          (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hc)
          ((hiff _).2 (isCartesianOnAffineCharts_cokernel_succ f ((hiff _).1 hf.1)
            ((hiff _).1 hf.2))) }
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      (ringSheaf (smallEtaleRingedSite B S hS Y.obj Y.2).O)).IsClosedUnderExtensions :=
    { prop_X₂_of_shortExact := fun {T} hT h₁ h₃ =>
        (hiff _).2 (isCartesianOnAffineCharts_shortExact_X₂_succ T hT ((hiff _).1 h₁)
          ((hiff _).1 h₃)) }
  exact {}

/-- **Stacks 03M1 on the spaces-étale site, as a weak Serre class.**  The quasi-coherent modules
on the ringed spaces-étale site of an algebraic space form a weak Serre subcategory: they
correspond to the quasi-coherent `𝒪_Y`-modules on the small étale site under the equivalence of
Stacks 03G1, which is exact. -/
theorem quasicoherentSheaves_spacesEtale_isWeakSerreClass :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (ringSheaf (spacesEtaleRingedSite B S hS Y).O)).IsWeakSerreClass :=
  have := quasicoherentSheaves_isWeakSerreClass_succ B S hS Y
  ObjectProperty.isWeakSerreClass_of_iff _ (smallEtaleModuleEquivalence B S hS Y).functor
    (isQuasicoherentOnSite_iff_smallEtale B S hS Y)

/-- **The standing assumption of Stacks 0DC1 for the family of Stacks 0DC5**: on every slice of the
spaces-étale site of `X`, the quasi-coherent modules form a weak Serre subcategory.  The slice at
`V` is the spaces-étale site of the algebraic space underlying `V` (Stacks 04LY), and
quasi-coherence is invariant under that equivalence of ringed sites. -/
theorem isWeakSerreClass_spacesEtaleQuasicoherentSlices (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X) :
    (spacesEtaleQuasicoherentSlices B S hS X V).IsWeakSerreClass := by
  let e := (SpacesEtale.sliceEquivSmall B S hS V).symm
  let R := (ringSheaf (spacesEtaleRingedSite B S hS X).O).over V
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.reindexRing (SpacesEtale.topology B S hS V.obj.left) e
        R)).IsWeakSerreClass :=
    quasicoherentSheaves_spacesEtale_isWeakSerreClass B S hS V.obj.left
  exact ObjectProperty.isWeakSerreClass_of_iff _
    (Stacks.SheafOfModules.reindexEquivalence (J' := SpacesEtale.topology B S hS V.obj.left)
      e R).functor
    (fun A => (Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
      (J' := SpacesEtale.topology B S hS V.obj.left) e R A).symm)

end AlgebraicGeometry.Space
