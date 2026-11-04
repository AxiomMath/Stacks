module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite

/-!
# Quasi-coherence of the direct image of the structure sheaf of a closed subspace

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace with inclusion `i`, and let `𝓘_Z = Ker(i♯)` be its defining ideal
sheaf.  By Stacks 09RP in degree zero, available here as
`AlgebraicGeometry.Space.conormalAlgebraDegreeZeroIso`, the quotient `𝒪_X/𝓘_Z` *is* the direct
image `i_*𝒪_Z`.  This file proves that this module is quasi-coherent.

The route is the base change criterion rather than presentations.  The defining ideal sheaf is
cartesian on affine charts unconditionally
(`AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`) and so is the structure
sheaf (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_unit`), so
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian` applies as soon as its
two surjectivity hypotheses are met over the affine charts.  Both are met here, and neither
needs the cohomology vanishing of Stacks 03DW that the general cokernel clause of Stacks 03M1
owes:

* its `hpi`, surjectivity of the projection onto the quotient, is the *affine* case of the
  surjectivity clause of Stacks 03MB, which is
  `AlgebraicGeometry.Space.surjective_structureMapApp_of_isAffine` — a closed immersion of
  schemes with affine target is surjective on regular functions;
* its `him`, surjectivity of the canonical epimorphism onto the image, is free because the
  inclusion of an ideal sheaf is a monomorphism, so that epimorphism is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.surjective_structureSharp_app_of_isAffine`: the structure map `f♯` of
  a closed immersion of algebraic spaces is surjective on the sections over an affine étale
  chart.  This is the sections form of the surjectivity clause of Stacks 03MB over the affine
  charts; `AlgebraicGeometry.Space.isLocallySurjective_structureSharp` is its locally surjective
  form over all charts.
* `AlgebraicGeometry.Space.surjective_cokernel_π_definingIdealSheaf_val_app_of_isAffine`: the
  projection `𝒪_X ⟶ 𝒪_X/𝓘_Z` is surjective on the sections over an affine étale chart.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_definingIdealSheaf` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_pushforwardStructureSheaf`: **`𝒪_X/𝓘_Z` and
  `i_*𝒪_Z` are quasi-coherent.**

## Implementation notes

No tag attribute is claimed.  Quasi-coherence of a direct image is Stacks 03M9, for a
quasi-compact quasi-separated morphism and an arbitrary quasi-coherent module; what is proved
here is the single case of the structure sheaf along a closed immersion, which is an input to
other tags rather than a clause of 03M9.  This is the convention of the sibling files
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealCartesian.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ShortExactQuasicoherent.lean`.

`AlgebraicGeometry.Space.structureSharp_app_hom_eq` and
`AlgebraicGeometry.Space.structureProjection_val_app_hom_eq` are the two reductions this file
needs, and both are `rfl`, but they are stated as equalities of *functions* rather than used
through definitional unfolding at the point of use.  The reason is the module system: the
definitional unfolding of `AlgebraicGeometry.Space.structureSharp` passes through declarations
that are not exposed, so `exact` cannot see that `Function.Surjective` of the structure map on
sections is `Function.Surjective` of the composite, while a `rfl`-proved equation about the two
functions can be rewritten with.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sections

variable {B S hS} {X : AlgebraicSpaces B S hS}

/-- An isomorphism of modules on an algebraic space is bijective on sections. -/
theorem bijective_val_app_of_iso {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) : Function.Bijective (e.hom.val.app U) := by
  let e' := (SheafOfModules.evaluation _ U).mapIso e
  have : IsIso ((SheafOfModules.evaluation _ U).map e.hom) :=
    ⟨e'.inv, e'.hom_inv_id, e'.inv_hom_id⟩
  exact ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation _ U).map e.hom)

/-- A morphism of modules on an algebraic space which is an isomorphism is bijective on
sections. -/
theorem bijective_val_app_of_isIso_module {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hφ : IsIso φ) (U : (SmallEtale B S hS X.1)ᵒᵖ) : Function.Bijective (φ.val.app U) :=
  bijective_val_app_of_iso
    (⟨φ, @inv _ _ _ _ φ hφ, @IsIso.hom_inv_id _ _ _ _ φ hφ, @IsIso.inv_hom_id _ _ _ _ φ hφ⟩ :
      M ≅ N) U

end Sections

variable {X Y : AlgebraicSpaces B S hS}

/-- The structure map on sections, as a function, factors as the chartwise structure map
followed by the comparison of the two forms of the small étale direct image. -/
theorem structureSharp_app_hom_eq (f : X ⟶ Y) (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    ⇑(ConcreteCategory.hom ((structureSharp B S hS f).hom.app V)) =
      ⇑(ConcreteCategory.hom (((smallEtaleDirectImageRanIso B S hS f).inv.app
          (structureRingSheaf B S hS X).ringSheaf).hom.app V)) ∘
        ⇑(ConcreteCategory.hom (structureMapApp B S hS f V.unop)) :=
  rfl

/-- The comparison of the two forms of the small étale direct image is a two-sided inverse
pair on the sections of the structure sheaf over an étale chart. -/
theorem smallEtaleDirectImageRanIso_hom_inv_app_app (f : X ⟶ Y)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureRingSheaf B S hS X).ringSheaf).hom.app V ≫
      ((smallEtaleDirectImageRanIso B S hS f).inv.app
        (structureRingSheaf B S hS X).ringSheaf).hom.app V = 𝟙 _ :=
  congrArg (fun k => k.hom.app V)
    ((smallEtaleDirectImageRanIso B S hS f).hom_inv_id_app
      (structureRingSheaf B S hS X).ringSheaf)

/-- The comparison of the two forms of the small étale direct image is surjective on the
sections of the structure sheaf over an étale chart, being a component of an isomorphism of
functors. -/
theorem surjective_smallEtaleDirectImageRanIso_inv_app_app (f : X ⟶ Y)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Function.Surjective (((smallEtaleDirectImageRanIso B S hS f).inv.app
      (structureRingSheaf B S hS X).ringSheaf).hom.app V) := fun t => by
  refine ⟨((smallEtaleDirectImageRanIso B S hS f).hom.app
    (structureRingSheaf B S hS X).ringSheaf).hom.app V t, ?_⟩
  rw [← CategoryTheory.comp_apply, smallEtaleDirectImageRanIso_hom_inv_app_app,
    CategoryTheory.id_apply]

/-- **The structure map of a closed immersion of algebraic spaces is surjective on the sections
over an affine étale chart.**  This is the sections form, over the affine charts, of the
surjectivity clause of Stacks 03MB; the locally surjective form on all charts is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`. -/
theorem surjective_structureSharp_app_of_isAffine (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    Function.Surjective ((structureSharp B S hS f).hom.app (op V)) := by
  rw [structureSharp_app_hom_eq]
  exact Function.Surjective.comp
    (surjective_smallEtaleDirectImageRanIso_inv_app_app B S hS f (op V))
    (surjective_structureMapApp_of_isAffine B S hS f hf V hV)

section Quotient

variable (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The structure projection `𝒪_X ⟶ i_*𝒪_Z` on sections, as a function, is the structure map of
the inclusion. -/
theorem structureProjection_val_app_hom_eq (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ⇑(ConcreteCategory.hom ((structureProjection B S hS X Z).val.app U)) =
      ⇑(ConcreteCategory.hom ((structureSharp B S hS
        (subspaceInclusion B S hS X Z)).hom.app U)) :=
  rfl

/-- **The structure projection `𝒪_X ⟶ i_*𝒪_Z` of a closed subspace is surjective on the sections
over an affine étale chart.** -/
theorem surjective_structureProjection_val_app_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    Function.Surjective ((structureProjection B S hS X Z).val.app (op U)) := by
  rw [structureProjection_val_app_hom_eq]
  exact surjective_structureSharp_app_of_isAffine B S hS
    (subspaceInclusion B S hS X Z) Z.2.2 U hU

/-- **The projection of `𝒪_X` onto the quotient by the defining ideal sheaf of a closed subspace
is surjective on the sections over an affine étale chart.** -/
theorem surjective_cokernel_π_definingIdealSheaf_val_app_of_isAffine
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    Function.Surjective
      ((cokernel.π (definingIdealSheaf B S hS X Z).ι).val.app (op U)) := by
  intro y
  have hbij := bijective_val_app_of_iso
    (conormalAlgebraDegreeZeroIso B S hS X Z) (op U)
  obtain ⟨a, ha⟩ := surjective_structureProjection_val_app_of_isAffine B S hS X Z U hU
    ((conormalAlgebraDegreeZeroIso B S hS X Z).hom.val.app (op U) y)
  refine ⟨a, hbij.1 ?_⟩
  refine Eq.trans ?_ ha
  rw [← cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom B S hS X Z]
  rfl

/-- **The quotient of `𝒪_X` by the defining ideal sheaf of a closed subspace is quasi-coherent.**

The defining ideal sheaf is cartesian on affine charts, the structure sheaf is, and the
projection onto the quotient is surjective on the sections over an affine chart, which is the
affine case of the surjectivity clause of Stacks 03MB.  The remaining input of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isCartesian` is surjectivity on those
sections of the canonical epimorphism onto the image, and the inclusion of the ideal sheaf is a
monomorphism, so that epimorphism is an isomorphism. -/
theorem isQuasicoherentOnSite_cokernel_definingIdealSheaf :
    (cokernel (definingIdealSheaf B S hS X Z).ι).IsQuasicoherentOnSite := by
  have hmono : Mono (definingIdealSheaf B S hS X Z).ι :=
    (definingIdealShortComplex_shortExact B S hS X Z).mono_f
  have hiso : IsIso (Abelian.factorThruImage (definingIdealSheaf B S hS X Z).ι) :=
    isIso_of_mono_of_epi _
  refine isQuasicoherentOnSite_cokernel_of_isCartesian B S hS X.1 X.2
    (definingIdealSheaf B S hS X Z).ι
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z)
    isCartesianOnAffineCharts_unit ?_ ?_
  · intro U hU
    exact surjective_cokernel_π_definingIdealSheaf_val_app_of_isAffine B S hS X Z U hU
  · intro U _
    exact (bijective_val_app_of_isIso_module
      (Abelian.factorThruImage (definingIdealSheaf B S hS X Z).ι) hiso (op U)).2

/-- **Quasi-coherence of the direct image of the structure sheaf of a closed subspace.**  For a
closed subspace `Z ⊆ X` of an algebraic space with inclusion `i`, the `𝒪_X`-module `i_*𝒪_Z` is
quasi-coherent.  This is the closed-immersion case of Stacks 03M9. -/
theorem isQuasicoherentOnSite_pushforwardStructureSheaf :
    (pushforwardStructureSheaf B S hS X Z).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (conormalAlgebraDegreeZeroIso B S hS X Z)
    (isQuasicoherentOnSite_cokernel_definingIdealSheaf B S hS X Z)

end Quotient

end AlgebraicGeometry.Space

end
