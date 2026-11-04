module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent

/-!
# The sections of a quasi-coherent module over an affine chart are a base change

Let `F` be an algebraic space over a scheme `S` and let `M` be a quasi-coherent `𝒪_F`-module.
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSectionBaseChange` proves the base-change
property of the sections of `M` only over the members of *some* covering family of a chart with
affine underlying scheme, together with the objects lying over them; that restriction is what the
descent argument there produces.

This file removes it.  A quasi-coherent module has a global presentation after restriction to a
chart with affine underlying scheme (`AlgebraicGeometry.Space.hasAffineChartPresentations`), and
a module presented on a chart has its sections over any object with affine underlying scheme
lying over that chart a base change of its sections over any other such object it maps to
(`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation_chart`).
Taking the chart carrying the presentation to be the *target* of the morphism makes the two fit,
and the base-change property holds at every pair of charts with affine underlying scheme, with no
covering anywhere.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isQuasicoherentOnSite`: **a
  quasi-coherent `𝒪_F`-module has a global presentation after restriction to a chart with affine
  underlying scheme**, for an arbitrary universe of module sections.
* `AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_isQuasicoherentOnSite`: **the
  sections of a quasi-coherent `𝒪_F`-module over a chart with affine underlying scheme are the
  base change of its sections over any such chart it maps to**, with no covering hypothesis.
* `AlgebraicGeometry.Space.SmallEtale.hasSectionBaseChangeAt_of_isQuasicoherentOnSite`: the same
  statement in the slice spelling of
  `AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeAt`, at an arbitrary object of the
  slice with affine underlying scheme.

## Implementation notes

**Why the universe lift appears in the first statement and not in the second.**
`AlgebraicGeometry.Space.hasAffineChartPresentations` is stated for modules whose sections lie in
`max (u + 1) m`, because the construction behind it indexes its presentations by types in that
universe; a module whose sections lie in `u` alone is not of that form for any `m`.  Raising the
universe of the sections neither creates nor destroys a global presentation
(`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'` and
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`), and raising it commutes with
restriction to a slice definitionally, so the lift is put in and taken out once here and the rest
of the file is free of it.

**The ring and module structures are given as data**, identified with the sections of the
structure sheaf by the ring equivalences `fA` and `fB` and their compatibilities, exactly as in
`AlgebraicGeometry.Space.SmallEtale.bijective_liftBaseChange_of_hasGlobalPresentation_chart`,
whose hypotheses these are.  The comparison is likewise taken as data together with the identity
describing it.

The base-change property proved here is the affine-chart case of Stacks 03DX.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A quasi-coherent `𝒪_F`-module has a global presentation after restriction to a chart whose
underlying scheme is affine**, for an arbitrary universe of module sections.

`AlgebraicGeometry.Space.hasAffineChartPresentations` says this for the modules whose sections lie
in `max (u + 1) m`; here the sections lie in an arbitrary `m`.  The universe of the sections is
raised, which preserves quasi-coherence
(`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`) and commutes with restriction to
the slice definitionally, and the presentation obtained there is brought back down by
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`. -/
theorem hasGlobalPresentation_over_of_isQuasicoherentOnSite
    (M : SheafOfModules.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hM : M.IsQuasicoherentOnSite) (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V))) :
    (M.over V).HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'.{u + 1, u, u, m, u + 1}
    (hasAffineChartPresentations B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
      (SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, m, u + 1} hM)
      V hV)

namespace SmallEtale

/-- **The sections of a quasi-coherent `𝒪_F`-module over a chart with affine underlying scheme
are the base change of its sections over any chart with affine underlying scheme it maps to**,
with no covering hypothesis.

It is `AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_of_hasGlobalPresentation_chart` with the chart carrying the
presentation taken to be `TL` itself, which is legitimate because
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isQuasicoherentOnSite` provides a
presentation over *every* chart with affine underlying scheme and not only over the members of a
covering family. -/
theorem bijective_liftBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hM : M.IsQuasicoherentOnSite)
    {TL WL : (smallEtaleRingedSite B S hS F hF).C} (hl : WL ⟶ TL)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj TL)))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj WL)))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [algAB : Algebra A Bc]
    [Module A (M.val.obj (op TL))] [Module A (M.val.obj (op WL))] [Module Bc (M.val.obj (op WL))]
    [IsScalarTower A Bc (M.val.obj (op WL))]
    (fA : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O).obj.obj (op TL) : Type u) ≃+* A)
    (hfA : ∀ (c : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj (op TL) : Type u))
      (n : M.val.obj (op TL)), fA c • n = c • n)
    (fB : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O).obj.obj (op WL) : Type u) ≃+* Bc)
    (hfB : ∀ (c : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj (op WL) : Type u))
      (n : M.val.obj (op WL)), fB c • n = c • n)
    (halg : ∀ c : A, algebraMap A Bc c =
      fB (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.map hl.op).hom (fA.symm c)))
    (r : M.val.obj (op TL) →ₗ[A] M.val.obj (op WL))
    (hr : ∀ n, r n = M.val.restrictₛₗ hl.op n) :
    Function.Bijective (r.liftBaseChange Bc) :=
  bijective_liftBaseChange_of_hasGlobalPresentation_chart B S hS F hF M
    (hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS F hF M hM TL hT)
    (𝟙 TL) hl hl (Category.comp_id hl) hT hW A Bc fA hfA fB hfB halg r hr

/-- **The base-change condition of
`AlgebraicGeometry.Space.SmallEtale.HasSectionBaseChangeAt` holds for a quasi-coherent
`𝒪_F`-module at every object of the slice at a chart with affine underlying scheme whose own
underlying scheme is affine**, with no covering hypothesis.

`AlgebraicGeometry.Space.SmallEtale.exists_hasSectionBaseChangeOn_of_isQuasicoherentOnSite`
gives the condition only over the objects lying over the members of some covering family of the
chart; this gives it everywhere, by
`AlgebraicGeometry.Space.SmallEtale`'s
`bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart` at the presentation
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isQuasicoherentOnSite` supplies over the
chart itself. -/
theorem hasSectionBaseChangeAt_of_isQuasicoherentOnSite
    (M : SheafOfModules.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hM : M.IsQuasicoherentOnSite) {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj V)))
    (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    HasSectionBaseChangeAt B S hS F hF (M.over V) W :=
  bijective_liftBaseChange_gamma_of_hasGlobalPresentation_overChart B S hS F hF M
    (hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS F hF M hM V hV) (M.over V) rfl
    (𝟙 V) W.hom (Over.mkIdTerminal.from W) (Over.w _) hV hW _ fun _ => rfl

end SmallEtale

end AlgebraicGeometry.Space

end
