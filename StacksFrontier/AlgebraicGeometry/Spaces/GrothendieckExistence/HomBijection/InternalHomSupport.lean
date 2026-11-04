module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties

/-!
# The support of the internal hom

For `𝒪_X`-modules `F` and `G` on an algebraic space, both annihilator ideal sheaves of `F` and
of `G` annihilate `𝓗om(F, G)`.  For finite type quasi-coherent modules the support is the zero
locus of the annihilator ideal sheaf (Stacks 07U0, part (4)), so the support of a coherent
`𝓗om(F, G)` lies in the intersection of the supports of `F` and `G`.

## Main results

* `AlgebraicGeometry.Space.C1573.supportOfSheaf_eq_idealZeroLocus_annihilatorIdealSheaf`: the
  support of a finite type quasi-coherent module is the zero locus of its annihilator ideal sheaf.
* `AlgebraicGeometry.Space.C1573.supportOfSheaf_smallEtaleInternalHomSmall_subset`: the support
  of a finite type quasi-coherent `𝓗om(F, G)` lies in the intersection of the supports of `F`
  and `G`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The support of a finite type quasi-coherent module is the zero locus of its annihilator
ideal sheaf.** -/
theorem supportOfSheaf_eq_idealZeroLocus_annihilatorIdealSheaf
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) =
      idealZeroLocus B S hS X (annihilatorIdealSheaf B S hS X F) := by
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hF
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hFft)
  rw [supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hF hFft,
    range_pointsMap_ι_eq_idealZeroLocus B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩, hid]

/-- A ring section `b` kills `α` in the internal hom once it kills the sections of the shrunk
image of `α` over every object. -/
private theorem smul_internalHom_eq_zero_of_forall {F G : Modules.{u, u} B S hS X.1 X.2}
    {W : (SmallEtale B S hS X.1)ᵒᵖ}
    (b : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj W)
    (α : (smallEtaleInternalHomSmall B S hS X.1 X.2 F G).val.obj W)
    (h : ∀ V x, ((b • smallEtaleInternalHomSmallShrink B S hS X.1 X.2 F G W α).app V).hom x = 0) :
    b • α = 0 := by
  apply (smallEtaleInternalHomSmallShrink B S hS X.1 X.2 F G W).injective
  refine (smallEtaleInternalHomSmallShrink_smul B S hS X.1 X.2 F G W _ α).trans ?_
  rw [map_zero]
  exact PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext (h V))

/-- **The annihilator of the target annihilates the internal hom.** -/
theorem annihilatorIdealSheaf_target_le_internalHom (F G : Modules.{u, u} B S hS X.1 X.2) :
    annihilatorIdealSheaf B S hS X G ≤
      annihilatorIdealSheaf B S hS X (smallEtaleInternalHomSmall B S hS X.1 X.2 F G) := by
  intro U a ha W g α
  refine smul_internalHom_eq_zero_of_forall B S hS X _ α fun V x => ?_
  exact (annihilatorIdealSheaf B S hS X G).map g ha (op V.unop.left) V.unop.hom.op
    (((smallEtaleInternalHomSmallShrink B S hS X.1 X.2 F G W α).app V).hom x)

/-- **The annihilator of the source annihilates the internal hom.** -/
theorem annihilatorIdealSheaf_source_le_internalHom (F G : Modules.{u, u} B S hS X.1 X.2) :
    annihilatorIdealSheaf B S hS X F ≤
      annihilatorIdealSheaf B S hS X (smallEtaleInternalHomSmall B S hS X.1 X.2 F G) := by
  intro U a ha W g α
  refine smul_internalHom_eq_zero_of_forall B S hS X _ α fun V x => ?_
  exact (LinearMap.map_smul (((smallEtaleInternalHomSmallShrink B S hS X.1 X.2 F G W α).app V).hom)
    _ x).symm.trans ((congrArg _
    ((annihilatorIdealSheaf B S hS X F).map g ha (op V.unop.left) V.unop.hom.op x)).trans
      (map_zero _))

/-- **The support of `𝓗om(F, G)` lies in the intersection of the supports of `F` and `G`**, for
finite type quasi-coherent `F`, `G` with `𝓗om(F, G)` finite type quasi-coherent. -/
theorem supportOfSheaf_smallEtaleInternalHomSmall_subset (F G : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hFft : SheafOfModules.IsFiniteTypeOnSite F)
    (hG : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (hH : (smallEtaleInternalHomSmall B S hS X.1 X.2 F G).IsQuasicoherentOnSite)
    (hHft : SheafOfModules.IsFiniteTypeOnSite (smallEtaleInternalHomSmall B S hS X.1 X.2 F G)) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (smallEtaleInternalHomSmall B S hS X.1 X.2 F G)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ∩
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) := by
  rw [supportOfSheaf_eq_idealZeroLocus_annihilatorIdealSheaf B S hS X _ hH hHft,
    supportOfSheaf_eq_idealZeroLocus_annihilatorIdealSheaf B S hS X _ hF hFft,
    supportOfSheaf_eq_idealZeroLocus_annihilatorIdealSheaf B S hS X _ hG hGft]
  exact Set.subset_inter
    (idealZeroLocus_antitone B S hS X (annihilatorIdealSheaf_source_le_internalHom B S hS X F G))
    (idealZeroLocus_antitone B S hS X (annihilatorIdealSheaf_target_le_internalHom B S hS X F G))

end AlgebraicGeometry.Space.C1573

end
