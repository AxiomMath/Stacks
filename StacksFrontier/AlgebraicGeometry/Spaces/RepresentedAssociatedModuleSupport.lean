module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion

/-!
# The support of the module associated to a quasi-coherent module on a represented space

Let `U` be an object of the big fppf site over `S` with underlying scheme `T`, and let `G₀` be a
quasi-coherent `𝒪_T`-module. A point of the represented algebraic space `h_U = yoneda.obj U`
lies in the support of the associated module `ε^* G₀` on the small étale site of `h_U`
(`AlgebraicGeometry.Space.representedAssociatedModule`) exactly when the stalk of `G₀` at the
corresponding point of `T` is nonzero.

## Main results

* `AlgebraicGeometry.Space.mem_supportOfSheaf_representedAssociatedModule_iff`: a point of
  `yoneda.obj U` lies in the support of the module associated to `G₀` exactly when the stalk of
  `G₀` at its image under `AlgebraicGeometry.Space.schemePointsHomeomorph` is nonzero.
* `AlgebraicGeometry.Space.isZero_stalk_of_notMem_supportOfSheaf_representedAssociatedModule`
  and `AlgebraicGeometry.Space.notMem_supportOfSheaf_representedAssociatedModule_of_isZero_stalk`
  are the two directions of the contrapositive.

## Implementation notes

The associated module is, by definition, the transport of `G₀` along
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, and its restriction to the
identity chart `AlgebraicGeometry.Space.selfChart` of `yoneda.obj U` is isomorphic to `G₀`.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The module associated to a quasi-coherent module on the scheme underlying `U` is, on the
nose, its transport along `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`. -/
theorem representedAssociatedModule_obj_eq_representedQuasicoherentSchemeEquivalence
    (G₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG₀ : G₀.IsQuasicoherent) :
    (representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G₀ =
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨G₀, hG₀⟩).obj :=
  rfl

/-- Let `G₀` be a quasi-coherent module on the scheme `T` underlying `U`. A point `p` of
`yoneda.obj U` lies in the support of the associated module `ε^* G₀` on the small étale site of
`yoneda.obj U` exactly when the stalk of `G₀` at the point of `T` corresponding to `p` is
nonzero. -/
theorem mem_supportOfSheaf_representedAssociatedModule_iff
    (G₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG₀ : G₀.IsQuasicoherent)
    (p : points B S hS (yoneda.obj U)) :
    p ∈ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj
          ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G₀)) ↔
      ¬ IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
          G₀.val.presheaf (schemePointsHomeomorph B S hS U p)) := by
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let F : Modules.{u, u} B S hS X.1 X.2 :=
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨G₀, hG₀⟩).obj
  have hF : F.IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨G₀, hG₀⟩).property
  have hsupp := supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X
    (selfChart B S hS U) F
  rw [SheafOfModules.supp_eq_of_iso
    (restrictToChart_selfChart_representedQuasicoherentIso B S hS U G₀ hG₀)] at hsupp
  have hp : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (selfChart B S hS U)))
      (selfChart B S hS U).obj.hom
      ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj (selfChart B S hS U))).symm
        (schemePointsHomeomorph B S hS U p)) = p := by
    change pointsMap B S hS (yoneda.obj U) (𝟙 _)
      ((pointsEquivScheme B S hS U).symm (pointsEquivScheme B S hS U p)) = p
    rw [Equiv.symm_apply_apply, pointsMap_id, id_eq]
  have hpt := Set.ext_iff.1 hsupp (schemePointsHomeomorph B S hS U p)
  refine (hpt.trans (iff_of_eq (congrArg
    (· ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) hp))).symm.trans ?_
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk G₀ _).trans ?_
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- A point of `yoneda.obj U` outside the support of the module associated to a quasi-coherent
module `G₀` on the scheme underlying `U` maps to a point at which the stalk of `G₀` vanishes. -/
theorem isZero_stalk_of_notMem_supportOfSheaf_representedAssociatedModule
    (G₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG₀ : G₀.IsQuasicoherent)
    (p : points B S hS (yoneda.obj U))
    (hp : p ∉ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj
          ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G₀))) :
    IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
      G₀.val.presheaf (schemePointsHomeomorph B S hS U p)) :=
  not_not.1 fun h ↦ hp ((mem_supportOfSheaf_representedAssociatedModule_iff B S hS U G₀ hG₀ p).2 h)

/-- A point of `yoneda.obj U` mapping to a point at which the stalk of a quasi-coherent module
`G₀` on the scheme underlying `U` vanishes lies outside the support of the associated module. -/
theorem notMem_supportOfSheaf_representedAssociatedModule_of_isZero_stalk
    (G₀ : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG₀ : G₀.IsQuasicoherent)
    (p : points B S hS (yoneda.obj U))
    (hp : IsZero (TopCat.Presheaf.stalk (X := (BigFppfOver.toScheme B S hS).obj U)
      G₀.val.presheaf (schemePointsHomeomorph B S hS U p))) :
    p ∉ supportOfSheaf B S hS (yoneda.obj U)
        ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U)).O)).obj
          ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).obj G₀)) :=
  fun h ↦ (mem_supportOfSheaf_representedAssociatedModule_iff B S hS U G₀ hG₀ p).1 h hp

end AlgebraicGeometry.Space

end
