module

public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionObstruction

/-!
# The ideal multiple of a module on a thickening (towards Stacks 08LI)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a thickening of ringed spaces with ideal
`ℐ = ker(𝒪_{X'} ⟶ i_* 𝒪_X)`, and let `ℱ'` be an `𝒪_{X'}`-module. The unit
`ℱ' ⟶ i_* i^* ℱ'` of the adjunction `i^* ⊣ i_*` is the reduction of `ℱ'` modulo `ℐ`, and the
submodule of `ℱ'` it kills is exactly the ideal multiple `ℐℱ'`, the image of the action
`ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ'`:

    ℐℱ' = ker(ℱ' ⟶ i_* i^* ℱ').

This file proves that identification and produces the isomorphism realising it, together with
the compatibility of the two inclusions into `ℱ'`.

## Main definitions

* `CategoryTheory.Abelian.imageIsoKernelOfExact`: for an exact short complex in an abelian
  category, the canonical isomorphism from the image of its first map to the kernel of its
  second, compatible with the inclusions of both into the middle term.
* `AlgebraicGeometry.RingedSpaceThickening.moduleReduction` and
  `AlgebraicGeometry.RingedSpaceThickening.moduleReductionMap`: the reduction `i_* i^* ℱ'` of
  an `𝒪_{X'}`-module along `i` and the unit `ℱ' ⟶ i_* i^* ℱ'` reducing to it.
* `AlgebraicGeometry.RingedSpaceThickening.idealMultipleIso`: the identification
  `ℐℱ' ≅ ker(ℱ' ⟶ i_* i^* ℱ')` of the ideal multiple with the kernel of the reduction,
  bundled with the compatibility of the inclusions into `ℱ'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.idealAction_comp_moduleReductionMap_eq_zero`: the
  ideal action followed by the reduction is zero, so the ideal multiple is contained in the
  kernel of the reduction. This holds because `ℐ` annihilates every module in the essential
  image of `i_*`, in particular `i_* i^* ℱ'`.
* `AlgebraicGeometry.RingedSpaceThickening.exact_idealAction_moduleReductionMap`: the resulting
  short complex `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ' ⟶ i_* i^* ℱ'` is exact, which is the reverse
  containment.

## Implementation notes

Exactness is proved by identifying the reduction with the cokernel of the ideal action, rather
than by a computation on stalks. The ideal acts as zero on that cokernel, because the action is
natural and tensoring the cokernel projection with the identity of `ℐ` is again an
epimorphism, which cancels; so the cokernel lies in the essential image of `i_*` by
**Stacks 08KS** and the unit at it is invertible. Comparing that with the universal property of
the cokernel and with surjectivity of the unit (`epi_unit_app_of_isThickening`) shows that the
descent of the unit along the cokernel projection is an isomorphism, that is, that the unit
itself is a cokernel of the action.

`idealMultipleIso` is therefore the canonical isomorphism
`Abelian.imageIsoImage ≪≫ asIso (imageToKernel' …)` of an exact short complex, not a choice of
an unspecified isomorphism: the zero-composition and the exactness are separate statements
precisely so that the zero-composition is available as a term before exactness is proved, which
is what lets the image and the kernel be compared by a named map.

Only `IsThickening` is needed, not `IsFirstOrderThickening`: the identification
`ℐℱ' = ker(ℱ' ⟶ ℱ'/ℐℱ')` is a statement about an arbitrary ideal.

Two spellings of the sheaf of rings `𝒪_{X'}` are in play. The adjunction `i^* ⊣ i_*`, and every
statement of this file, name it `structureSheafRing X'`; the canonical tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf, X'.IsSheaf⟩` instead lands in the
category of modules indexed by `Stacks.SheafOfModules.Tensor.ringSheaf ⟨X'.presheaf, X'.IsSheaf⟩`.
The two sheaves of rings are equal by `rfl`, but `Tensor.ringSheaf` is a plain `def`, so instance
search — which runs at instance transparency — will not unfold it, and a morphism whose source is
a tensor product and whose target is written with `structureSheafRing` therefore has no zero
morphism that search can find: `idealAction i ℱ' ≫ moduleReductionMap i ℱ' = 0` fails to
elaborate its own `0`. Hence the file-local
`attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf`, the per-file
opt-in this repository uses for exactly that purpose (as in
`StacksFrontier/CategoryTheory/Sites/Modules/InvertibleRankOne.lean`). Raising
`structureSheafRing` instead does not help, because it is already instance-reducible and it is
the `Tensor.ringSheaf` side of the comparison that stays folded. `moduleReduction` names
`i_* i^* ℱ'` in the `structureSheafRing` spelling, which is the one its consumers read.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf

universe u

namespace CategoryTheory.Abelian

/-- **The image of the first map of an exact short complex is the kernel of its second.** In an
abelian category, an exact short complex `A ⟶ B ⟶ C` has a canonical isomorphism from
`Abelian.image` of its first map onto the kernel of its second, and that isomorphism identifies
the two inclusions into `B`.

The isomorphism is `Abelian.imageIsoImage` followed by the comparison map `imageToKernel'`,
which exactness makes invertible; so it is determined, not chosen.

This is a general statement about abelian categories, with no sheaf-theoretic content, and
would ideally live in a categorical file. -/
noncomputable def imageIsoKernelOfExact {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) (h : S.Exact) :
    { e : Abelian.image S.f ≅ kernel S.g // e.hom ≫ kernel.ι S.g = Abelian.image.ι S.f } :=
  haveI := h.isIso_imageToKernel'
  ⟨Abelian.imageIsoImage S.f ≪≫ asIso (imageToKernel' S.f S.g S.zero), by
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, imageToKernel', kernel.lift_ι,
      Abelian.imageIsoImage_hom_comp_image_ι]⟩

/-- A map out of `A` whose descent along the cokernel of `f : B ⟶ A` is an isomorphism is
itself a cokernel of `f`, so the short complex `B ⟶ A ⟶ T` it forms with `f` is exact. -/
theorem exact_of_isIso_cokernel_desc {C : Type*} [Category C] [Abelian C] {A B T : C}
    (f : B ⟶ A) (g : A ⟶ T) (w : f ≫ g = 0) [IsIso (cokernel.desc f g w)] :
    (ShortComplex.mk f g w).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (IsColimit.ofIsoColimit (cokernelIsCokernel f)
      (Cofork.ext (asIso (cokernel.desc f g w)) (by simp)))

end CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

/-- **A criterion for the unit of an adjunction to be a cokernel.** Let `adj : L ⊣ R` be an
adjunction between categories with zero morphisms, let `f : B ⟶ A` be a map killed by
`adj.unit.app A`, and suppose the unit is invertible at `cokernel f` and epimorphic at `A`.
Then the descent of `adj.unit.app A` along `cokernel.π f` is an isomorphism, so `adj.unit.app A`
is a cokernel of `f`.

Inverting the unit at `cokernel f` turns the naturality square of the unit at `cokernel.π f`
into a factorization of `cokernel.π f` through `adj.unit.app A`; that factorization and the
descent are mutually inverse because `cokernel.π f` and `adj.unit.app A` are epimorphisms. -/
theorem isIso_cokernel_desc_unit_app {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A B : C} (f : B ⟶ A)
    [Limits.HasCokernel f] (w : f ≫ adj.unit.app A = 0)
    [IsIso (adj.unit.app (Limits.cokernel f))] [Epi (adj.unit.app A)] :
    IsIso (Limits.cokernel.desc f (adj.unit.app A) w) := by
  have hc : adj.unit.app A ≫ (R.map (L.map (Limits.cokernel.π f)) ≫
      inv (adj.unit.app (Limits.cokernel f))) = Limits.cokernel.π f := by
    simp
  refine ⟨⟨R.map (L.map (Limits.cokernel.π f)) ≫ inv (adj.unit.app (Limits.cokernel f)),
    ?_, ?_⟩⟩
  · rw [← cancel_epi (Limits.cokernel.π f), Category.comp_id, ← Category.assoc,
      Limits.cokernel.π_desc, hc]
  · rw [← cancel_epi (adj.unit.app A), Category.comp_id, ← Category.assoc, hc,
      Limits.cokernel.π_desc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The reduction `i_* i^* ℱ'` of an `𝒪_{X'}`-module along a morphism `i : X ⟶ X'` of ringed
spaces, named in the spelling of the category of `𝒪_{X'}`-modules that the tensor product and
the ideal action use. -/
noncomputable abbrev moduleReduction (F' : SheafOfModules.{u} (structureSheafRing X')) :
    SheafOfModules.{u} (structureSheafRing X') :=
  (modulePullback i ⋙ modulePushforward i).obj F'

/-- The reduction map `ℱ' ⟶ i_* i^* ℱ'`, the unit of the adjunction `i^* ⊣ i_*`. For a
thickening it is the reduction of `ℱ'` modulo the ideal of the thickening. -/
noncomputable abbrev moduleReductionMap (F' : SheafOfModules.{u} (structureSheafRing X')) :
    F' ⟶ moduleReduction i F' :=
  (modulePullbackPushforwardAdjunction i).unit.app F'

/-- **The ideal multiple is contained in the kernel of the reduction.** For a thickening
`i : X ⟶ X'`, the action of the ideal `ℐ` on an `𝒪_{X'}`-module `ℱ'` followed by the reduction
`ℱ' ⟶ i_* i^* ℱ'` is zero.

The action is natural, so this composite is the action on `i_* i^* ℱ'` precomposed with a map,
and `ℐ` annihilates every module in the essential image of `i_*`. -/
theorem idealAction_comp_moduleReductionMap_eq_zero (hi : IsThickening i)
    (F' : SheafOfModules.{u} (structureSheafRing X')) :
    idealAction i F' ≫ moduleReductionMap i F' = 0 := by
  have hnat := idealAction_naturality i (moduleReductionMap i F')
  rw [idealAction_eq_zero_of_essImage i hi (moduleReduction i F')
    ⟨(modulePullback i).obj F', ⟨Iso.refl _⟩⟩, comp_zero] at hnat
  exact hnat

/-- **The ideal acts as zero on the cokernel of its own action.** The action is natural, and
tensoring the cokernel projection with the identity of the ideal is again an epimorphism, so
the naturality square cancels it. -/
theorem idealAction_cokernel_self_eq_zero (F' : SheafOfModules.{u} (structureSheafRing X')) :
    idealAction i (cokernel (idealAction i F')) = 0 := by
  have h0 := (idealAction_naturality i (cokernel.π (idealAction i F'))).symm.trans
    (cokernel.condition (idealAction i F'))
  exact Epi.left_cancellation (self :=
    Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi X'
      (𝟙 (idealSheafModule i)) (cokernel.π (idealAction i F'))) _ _ (h0.trans comp_zero.symm)

/-- **The reduction is a cokernel of the ideal action.** For a thickening `i : X ⟶ X'` the map
induced on `cokernel (idealAction i ℱ')` by the reduction `ℱ' ⟶ i_* i^* ℱ'` is an isomorphism.

The cokernel is annihilated by the ideal, hence lies in the essential image of `i_*` by
**Stacks 08KS**, so the unit at it is invertible; inverting it factors the cokernel projection
through the reduction. That factorization and the descent of the reduction are mutually
inverse, because the projection and the reduction are both epimorphisms. -/
theorem isIso_cokernel_desc_moduleReductionMap (hi : IsThickening i)
    (F' : SheafOfModules.{u} (structureSheafRing X')) :
    IsIso (cokernel.desc (idealAction i F') (moduleReductionMap i F')
      (idealAction_comp_moduleReductionMap_eq_zero i hi F')) := by
  let S := closedQuotientOfIsThickening i hi
  have : (modulePushforward i).Full := S.full_modulePushforward
  have : (modulePushforward i).Faithful := S.faithful_modulePushforward
  have : IsIso ((modulePullbackPushforwardAdjunction i).unit.app
      (cokernel (idealAction i F'))) :=
    ((modulePullbackPushforwardAdjunction i).isIso_unit_app_iff_mem_essImage).2
      (essImage_of_idealAction_eq_zero i hi _ (idealAction_cokernel_self_eq_zero i F'))
  have : Epi ((modulePullbackPushforwardAdjunction i).unit.app F') :=
    epi_unit_app_of_isThickening i hi F'
  exact (modulePullbackPushforwardAdjunction i).isIso_cokernel_desc_unit_app
    (idealAction i F') (idealAction_comp_moduleReductionMap_eq_zero i hi F')

/-- **The ideal multiple is the kernel of the reduction.** For a thickening `i : X ⟶ X'` the
short complex `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ' ⟶ i_* i^* ℱ'` built from the ideal action and the
reduction is exact, the reduction being a cokernel of the action. -/
theorem exact_idealAction_moduleReductionMap (hi : IsThickening i)
    (F' : SheafOfModules.{u} (structureSheafRing X')) :
    (ShortComplex.mk (idealAction i F') (moduleReductionMap i F')
      (idealAction_comp_moduleReductionMap_eq_zero i hi F')).Exact :=
  haveI := isIso_cokernel_desc_moduleReductionMap i hi F'
  Abelian.exact_of_isIso_cokernel_desc (idealAction i F') (moduleReductionMap i F')
    (idealAction_comp_moduleReductionMap_eq_zero i hi F')

/-- **`ℐℱ' = ker(ℱ' ⟶ i_* i^* ℱ')`.** For a thickening `i : X ⟶ X'` and an `𝒪_{X'}`-module
`ℱ'`, the ideal multiple `ℐℱ'` — the image of the action `ℐ ⊗_{𝒪_{X'}} ℱ' ⟶ ℱ'` — is the
kernel of the reduction `ℱ' ⟶ i_* i^* ℱ'`, by an isomorphism carrying the inclusion of the
kernel into `ℱ'` to the inclusion of the image.

This is the canonical isomorphism of `CategoryTheory.Abelian.imageIsoKernelOfExact` applied to
`exact_idealAction_moduleReductionMap`, so it unfolds to `Abelian.imageIsoImage` followed by
`imageToKernel'`. -/
noncomputable def idealMultipleIso (hi : IsThickening i)
    (F' : SheafOfModules.{u} (structureSheafRing X')) :
    { e : Abelian.image (idealAction i F') ≅
        kernel ((modulePullbackPushforwardAdjunction i).unit.app F') //
      e.hom ≫ kernel.ι ((modulePullbackPushforwardAdjunction i).unit.app F') =
        Abelian.image.ι (idealAction i F') } :=
  Abelian.imageIsoKernelOfExact
    (ShortComplex.mk (idealAction i F') (moduleReductionMap i F')
      (idealAction_comp_moduleReductionMap_eq_zero i hi F'))
    (exact_idealAction_moduleReductionMap i hi F')

end AlgebraicGeometry.RingedSpaceThickening

end
