module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealAssociatedModuleChart

/-!
# The defining ideal sheaf of a closed subspace is the inverse image of a Zariski sheaf of ideals

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an object of the big fppf
category over `S` and let `Z ⊆ h_V = yoneda.obj V` be a closed subspace.  The defining ideal
sheaf `𝓘_Z ⊆ 𝒪_{h_V}` of Stacks 083B lives on the small étale site of `h_V`, while
`AlgebraicGeometry.Space.schemeSpaceIdeal` cuts `Z` out by a single Zariski sheaf of ideals
`I ⊆ 𝒪_V` of the representing scheme.  This file proves that the two agree as sheaves of
modules: `𝓘_Z` is the inverse image `ε^*I` along the comparison `ε` of Stacks 070R, read on the
represented space by `AlgebraicGeometry.Space.representedAssociatedModule`.

This is `AlgebraicGeometry.Space.SchemeSpaceIdealModuleComparison`, which
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparison.lean` states and leaves
unproved; `AlgebraicGeometry.Space.schemeSpaceIdealModuleComparison` discharges it, so its
consumers no longer have to carry it as a hypothesis.

## The route

The comparison map `ε^*I ⟶ 𝒪_{h_V}` is the inverse image of the inclusion of the sheaf of
ideals followed by the comparison of structure sheaves
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.  It is a monomorphism, the
first factor by `AlgebraicGeometry.Space.mono_representedAssociatedModule_map` — `ε^*` is left
exact — and the second because it is an isomorphism.  A monomorphism of sheaves of modules is
isomorphic onto its image subsheaf,
`Stacks.SheafOfModules.ImageSubsheaf.imageIso`, so all that is left is to identify that image
subsheaf with `𝓘_Z`.  Both are sheaf submodules of `𝒪_{h_V}`, and a sheaf submodule of the
structure sheaf of an algebraic space is determined by its sections over the *affine* étale
charts (`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine`); over an affine
étale chart the two agree by the chartwise identification
`exists_representedAssociatedModule_idealIota_app_eq_iff_mem_definingIdealAt` in the namespace
`AlgebraicGeometry.Space`.  No sheafification, and no inverse image of a module, is ever unfolded.

## Main definitions

* `AlgebraicGeometry.Space.representedIdealComparison`: the comparison map `ε^*I ⟶ 𝒪_{h_V}`.
* `AlgebraicGeometry.Space.representedIdealImageSubmodule`: its image subsheaf, a sheaf
  submodule of `𝒪_{h_V}`.
* `AlgebraicGeometry.Space.representedDefiningIdealSheafIso`: **the comparison**, as an
  isomorphism `ε^*I ≅ 𝓘_Z`.
* `AlgebraicGeometry.Space.chartModulePullbackDefiningIdealSheafIso`: **the chart inverse image
  of the defining ideal sheaf of a closed subspace of an arbitrary algebraic space**, identified
  with `ε^*` of the Zariski sheaf of ideals which the inverse-image subspace cuts out on the
  chart scheme.

## Main results

* `AlgebraicGeometry.Space.mono_representedIdealComparison`: the comparison map is a
  monomorphism.
* `AlgebraicGeometry.Space.representedIdealImageSubmodule_eq_definingIdealSheaf`: its image
  subsheaf is the defining ideal sheaf.
* `AlgebraicGeometry.Space.representedDefiningIdealSheafIso_hom_comp_ι`: the comparison is the
  canonical one — composed with the inclusion of `𝓘_Z` into the structure sheaf it is the
  comparison map itself, so it introduces no twist.
* `AlgebraicGeometry.Space.schemeSpaceIdealModuleComparison`:
  `AlgebraicGeometry.Space.SchemeSpaceIdealModuleComparison`, proved.

## Implementation notes

`AlgebraicGeometry.schemeSpace` is a plain `def`, so `(schemeSpace V).property` is not a term of
type `IsAlgebraicSpace B S hS (yoneda.obj V)` at *reducible* transparency, and every instance
search touching `representedAssociatedModule B S hS V (schemeSpace V).property` fails.  Every
statement below therefore carries the hypothesis `hF : IsAlgebraicSpace B S hS (yoneda.obj V)`
as a variable and spells the algebraic space `⟨yoneda.obj V, hF⟩`; proof irrelevance makes that
defeq to `schemeSpace V`, so the lemmas stated at `schemeSpace V` — among them
`AlgebraicGeometry.Space.mono_representedAssociatedModule_map` and the chartwise identification
— still apply, and `AlgebraicGeometry.Space.schemeSpaceIdealModuleComparison` instantiates back.

For the same reason `Mono` and `IsIso` have to be supplied by hand rather than found: the
monomorphism of the inclusion of a sheaf of ideals is stated at `SheafOfModules` and exchanged
with the `AlgebraicGeometry.Scheme.Modules` reading by
`AlgebraicGeometry.Scheme.Modules.mono_of_mono_sheafOfModules`, and the two instance arguments
of `CategoryTheory.mono_comp` are passed positionally with `@`, which keeps the composite's
objects explicit and avoids unifying through `CategoryTheory.Category.assoc`.

The image subsheaf of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiImageSubsheaf.lean` is
used rather than the sectionwise range `CategoryTheory.SheafOfModules.Submodule.range` of
`StacksFrontier/AlgebraicGeometry/Modules/SubobjectSubmodule.lean`, because the latter is stated
for a site in a single universe while the small étale site of an algebraic space has its objects
one universe above its morphisms.  For a monomorphism the two agree, by
`Stacks.SheafOfModules.ImageSubsheaf.mem_imageSubmodule_obj_iff_of_mono`.

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B), the ideal sheaf of a
  closed subspace.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the correspondence on
  the small étale site.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the
  associated module.
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), the ideal sheaf of an
  inverse image.
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW), the inverse image of
  modules along an étale morphism.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u t

namespace CategoryTheory.SheafOfModules.Submodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{t} R}

/-- Transporting a submodule of a sheaf of modules along an equality of submodules commutes with
the inclusions into the ambient sheaf. -/
theorem eqToIso_hom_comp_ι {N₁ N₂ : M.Submodule} (h : N₁ = N₂) :
    (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules h)).hom ≫ N₂.ι = N₁.ι := by
  subst h
  exact Category.id_comp _

end CategoryTheory.SheafOfModules.Submodule

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (V : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj V))
  (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)

/-! ### The comparison map and its image subsheaf -/

/-- **The comparison map `ε^*I ⟶ 𝒪_{h_V}`** attached to a Zariski sheaf of ideals `I ⊆ 𝒪_V`:
the inverse image along `ε` of the inclusion of `I` into the structure sheaf of the scheme,
followed by the comparison `ε^*𝒪_V ≅ 𝒪_{h_V}` of structure sheaves. -/
noncomputable def representedIdealComparison :
    (representedAssociatedModule B S hS V hF).obj I.unitSubmodule.toSheafOfModules ⟶
      SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj V, hF⟩) :=
  (representedAssociatedModule B S hS V hF).map (Stacks.ClosedSubscheme.idealIota I) ≫
    (representedAssociatedModuleObjUnitIso B S hS V hF).hom

/-- **The comparison map is a monomorphism.**  Its first factor is the inverse image along `ε`
of the inclusion of a sheaf of ideals, a monomorphism because `ε^*` is left exact
(`AlgebraicGeometry.Space.mono_representedAssociatedModule_map`); its second factor is an
isomorphism of structure sheaves.

So `ε^*I` is a sheaf of *ideals* of `𝒪_{h_V}`, which is what makes the comparison with `𝓘_Z` a
comparison of two submodules of the structure sheaf. -/
theorem mono_representedIdealComparison : Mono (representedIdealComparison B S hS V hF I) :=
  @mono_comp _ _ _ _ _ _
    (@mono_representedAssociatedModule_map B S hS V _ _ _
      (Scheme.Modules.mono_of_mono_sheafOfModules _
        (SheafOfModules.Submodule.mono_ι I.unitSubmodule)))
    _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _))

/-- **The image of `ε^*I` in the structure sheaf of `h_V`**, as a sheaf submodule: the sheaf of
ideals of `𝒪_{h_V}` that the Zariski sheaf of ideals `I` generates. -/
noncomputable def representedIdealImageSubmodule :
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj V, hF⟩)).Submodule :=
  @Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule _ _ _ _ _ _
    (representedIdealComparison B S hS V hF I)

/-! ### The comparison -/

variable (Z : ClosedSubspaces B S hS (yoneda.obj V))

/-- **The image of `ε^*` of the Zariski sheaf of ideals cut out by a closed subspace of `h_V` is
the defining ideal sheaf of that subspace.**

Both sides are sheaf submodules of `𝒪_{h_V}`, and such a submodule is determined by its sections
over the affine étale charts, by
`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine`.  Over an affine étale chart
the comparison map hits exactly the defining ideal there,
`exists_representedAssociatedModule_idealIota_app_eq_iff_mem_definingIdealAt`, and the image
subsheaf of a monomorphism is its sectionwise range,
`Stacks.SheafOfModules.ImageSubsheaf.mem_imageSubmodule_obj_iff_of_mono`. -/
theorem representedIdealImageSubmodule_eq_definingIdealSheaf :
    representedIdealImageSubmodule B S hS V hF (schemeSpaceIdeal B S hS V Z) =
      definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z :=
  structureSubmodule_ext_of_forall_isAffine B S hS ⟨yoneda.obj V, hF⟩ _ _ fun A hA =>
    Submodule.ext fun a =>
      (@Stacks.SheafOfModules.ImageSubsheaf.mem_imageSubmodule_obj_iff_of_mono _ _ _ _ _ _
          (representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z))
          (mono_representedIdealComparison B S hS V hF _) (op A) a).trans
        (@exists_representedAssociatedModule_idealIota_app_eq_iff_mem_definingIdealAt
          B S hS V A Z hA a)

/-- **The defining ideal sheaf of a closed subspace of a represented algebraic space is the
inverse image along `ε` of the Zariski sheaf of ideals it cuts out.**

The comparison map is a monomorphism, so it presents `ε^*I` as its image subsheaf
(`Stacks.SheafOfModules.ImageSubsheaf.imageIso`), and that image subsheaf is `𝓘_Z` by
`AlgebraicGeometry.Space.representedIdealImageSubmodule_eq_definingIdealSheaf`. -/
noncomputable def representedDefiningIdealSheafIso :
    (representedAssociatedModule B S hS V hF).obj
        (schemeSpaceIdeal B S hS V Z).unitSubmodule.toSheafOfModules ≅
      (definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z).toSheafOfModules :=
  (@Stacks.SheafOfModules.ImageSubsheaf.imageIso _ _ _ _ _ _
        (representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z))
        (mono_representedIdealComparison B S hS V hF _)).trans
    (eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (representedIdealImageSubmodule_eq_definingIdealSheaf B S hS V hF Z)))

/-- **The comparison is the canonical one.**  Composed with the inclusion of the defining ideal
sheaf into the structure sheaf of `h_V`, the comparison isomorphism is the comparison map
`ε^*I ⟶ 𝒪_{h_V}` itself.

So the isomorphism introduces no twist of its own, and any morphism out of `𝓘_Z` which is
determined by its composite with the inclusion — `AlgebraicGeometry.Space.idealSheafMap` is one,
by `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` — can be transported across
it by cancelling that monomorphism. -/
theorem representedDefiningIdealSheafIso_hom_comp_ι :
    (representedDefiningIdealSheafIso B S hS V hF Z).hom ≫
        (definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z).ι =
      representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z) :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (SheafOfModules.Submodule.eqToIso_hom_comp_ι
      (representedIdealImageSubmodule_eq_definingIdealSheaf B S hS V hF Z))).trans
      (Stacks.SheafOfModules.ImageSubsheaf.toImage_ι _)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`AlgebraicGeometry.Space.SchemeSpaceIdealModuleComparison`, proved.**  For every object `V`
of the big fppf category over `S` and every closed subspace `Z ⊆ h_V`, the defining ideal sheaf
`𝓘_Z ⊆ 𝒪_{h_V}` is the inverse image along `ε` of the submodule of `𝒪_V` attached to
`AlgebraicGeometry.Space.schemeSpaceIdeal`.

This discharges the hypothesis of
`AlgebraicGeometry.Space.schemeSpaceIdealModuleComparisonIso`; the isomorphism itself is
`AlgebraicGeometry.Space.representedDefiningIdealSheafIso`. -/
theorem schemeSpaceIdealModuleComparison : SchemeSpaceIdealModuleComparison B S hS :=
  fun V Z => ⟨(representedDefiningIdealSheafIso B S hS V (schemeSpace V).property Z).symm⟩

/-! ### The chart inverse image of the defining ideal sheaf -/

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (V : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj V))
  (φ : (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)

/-- **The inverse image of the defining ideal sheaf of a closed subspace along an étale scheme
chart is `ε^*` of a single Zariski sheaf of ideals of the chart scheme.**

Three steps, no computation.  Along an étale morphism the inverse image of modules is étale
restriction, Stacks Equation 03LW
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`); the étale restriction of a
defining ideal sheaf is the defining ideal sheaf of the inverse-image subspace, Stacks 04CO
(`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`); and on the represented algebraic space
of the chart scheme that defining ideal sheaf is `ε^*` of the Zariski sheaf of ideals which the
inverse-image subspace cuts out, by
`AlgebraicGeometry.Space.representedDefiningIdealSheafIso`. -/
noncomputable def chartModulePullbackDefiningIdealSheafIso :
    (modulePullback B S hS φ).obj (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (representedAssociatedModule B S hS V hF).obj
        (schemeSpaceIdeal B S hS V ⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage B S hS φ.hom Z.1 X.2 hF Z.2⟩).unitSubmodule.toSheafOfModules :=
  ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).trans
    ((etaleIdealSheafRestrictionIso B S hS φ hφ Z).trans
      (representedDefiningIdealSheafIso B S hS V hF _).symm)

end AlgebraicGeometry.Space

end
