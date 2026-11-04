module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcohSheafFbcFppfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange

/-!
# Stacks 0779 on `LQCoh^fbc(𝒪_𝒳)`, for any coherator

Let `𝒳` be an algebraic stack and `Q` a right adjoint of the inclusion
`i : QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)`. This file states **Stacks 0779** on `LQCoh^fbc(𝒪_𝒳)` for `Q`:

* `AlgebraicGeometry.Stack.isZero_obj_iff_isParasitic_of_lqcohSheafFbc`: part (1), `Q` kills an
  object of `LQCoh^fbc(𝒪_𝒳)` exactly when it is parasitic;
* `AlgebraicGeometry.Stack.isParasitic_kernel_and_cokernel_counit_of_lqcohSheafFbc`: part (2), the
  kernel and the cokernel of `Q(𝓕) ⟶ 𝓕` are parasitic;
* `AlgebraicGeometry.Stack.preservesFiniteColimits_lqcohSheafFbc_ι_comp` and
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_lqcohSheafFbc_ι_comp`: part (3), the colimit
  half, `Q` is right exact on `LQCoh^fbc(𝒪_𝒳)` and preserves its small colimits.

Each is the statement of `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf`
for modules cartesian along flat arrows between affine objects, applied to the step R2 of the
proof of the source,
`AlgebraicGeometry.Stack.isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules`.
The registered statements are their instances at the canonical coherator, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical`.

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)
  {Q : fppfModules B S hS 𝒳 ⥤ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).FullSubcategory}
  (adj : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)).ι ⊣ Q)

include adj in
/-- **Stacks 0779** (1) for any coherator: an object of `LQCoh^fbc(𝒪_𝒳)` is killed by `Q`
exactly when it is parasitic. -/
theorem isZero_obj_iff_isParasitic_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsZero (Q.obj F) ↔ IsParasitic B S hS 𝒳 .fppf F.val :=
  isZero_obj_iff_isParasitic_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF)

/-- **Stacks 0779** (2), the kernel, for any coherator: for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` the kernel of
`Q(𝓕) ⟶ 𝓕` is parasitic. -/
theorem isParasitic_kernel_counit_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (kernel (adj.counit.app F)).val :=
  isParasitic_kernel_counit_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF)

/-- **Stacks 0779** (2), the cokernel, for any coherator: for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` the cokernel
of `Q(𝓕) ⟶ 𝓕` is parasitic. -/
theorem isParasitic_cokernel_counit_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (cokernel (adj.counit.app F)).val :=
  isParasitic_cokernel_counit_of_isCartesianAlongFlatAffine B S hS 𝒳 adj F
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF)

/-- **Stacks 0779** (2) for any coherator: for `𝓕` in `LQCoh^fbc(𝒪_𝒳)` both the kernel and the
cokernel of `Q(𝓕) ⟶ 𝓕` are parasitic. -/
theorem isParasitic_kernel_and_cokernel_counit_of_lqcohSheafFbc (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsParasitic B S hS 𝒳 .fppf (kernel (adj.counit.app F)).val ∧
      IsParasitic B S hS 𝒳 .fppf (cokernel (adj.counit.app F)).val :=
  ⟨isParasitic_kernel_counit_of_lqcohSheafFbc B E h S hS 𝒳 adj F hF,
    isParasitic_cokernel_counit_of_lqcohSheafFbc B E h S hS 𝒳 adj F hF⟩

include adj in
/-- **Stacks 0779** (3), colimits, for any coherator: `Q` restricted to `LQCoh^fbc(𝒪_𝒳)`
preserves its colimits of `u`-small shapes, which are computed in `Mod(𝒪_𝒳)`. -/
theorem preservesColimitsOfShape_lqcohSheafFbc_ι_comp (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ Q) :=
  preservesColimitsOfShape_ι_comp_of_isCartesianAlongFlatAffine B S hS 𝒳 adj _
    (fun F hF => isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS F hF) J

include adj in
/-- **Stacks 0779** (3), right exactness, for any coherator: `Q` restricted to
`LQCoh^fbc(𝒪_𝒳)` is right exact. -/
theorem preservesFiniteColimits_lqcohSheafFbc_ι_comp :
    PreservesFiniteColimits ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ Q) :=
  preservesFiniteColimits_of_preservesFiniteColimitsOfSize.{u} _ fun J _ _ =>
    preservesColimitsOfShape_lqcohSheafFbc_ι_comp B E h S hS 𝒳 adj J

include E h adj in
/-- **The coherator of a higher direct image of a quasi-coherent module** (the form of
**Stacks 0779** (2) that **Stacks 077A** consumes). Let `f : 𝒴' ⟶ 𝒳` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks, `𝓕` a quasi-coherent module on `𝒴'` and `q ≥ 0`.
Then the kernel and the cokernel of the counit `Q(Rᵠf_*𝓕) ⟶ Rᵠf_*𝓕` are parasitic: `Rᵠf_*𝓕`
lies in `LQCoh^fbc(𝒪_𝒳)` (**Stacks 0771** (4)(b)), where **Stacks 0779** (2) applies. -/
theorem isParasitic_kernel_and_cokernel_counit_higherDirectImage
    {𝒴' : AlgebraicStacks.{u, w} B S hS} (f : 𝒴' ⟶ 𝒳)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒴'.val.val.p 𝒴'.val.isFiberedInGroupoids
        .fppf)).FullSubcategory) (q : ℕ) :
    IsParasitic B S hS 𝒳 .fppf
        (kernel (adj.counit.app ((fppfModulesHigherDirectImage B S hS f q).obj F.obj))).val ∧
      IsParasitic B S hS 𝒳 .fppf
        (cokernel (adj.counit.app ((fppfModulesHigherDirectImage B S hS f q).obj F.obj))).val :=
  isParasitic_kernel_and_cokernel_counit_of_lqcohSheafFbc B E h S hS 𝒳 adj _
    (lqcohSheafFbcFppfModules_fppfModulesHigherDirectImage B E h S hS f hqc hqs F.obj
      (AlgebraicStacks.lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒴' F) q)

end AlgebraicGeometry.Stack

end
