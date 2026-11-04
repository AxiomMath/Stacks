module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianLargeSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeSheafification
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TerminalObjectFreeResolution

/-!
# Quasi-coherent modules on the small étale site of an affine scheme, and base change

Let `S` be an affine scheme in a big étale site and let `X` be a terminal object of the small
étale site `S_ét`. For a quasi-coherent sheaf of modules `𝒢` on `S_ét`, at any module universe
`max (u + 1) m`, the counit `𝒪 ⊗_{𝒪(X)} 𝒢(X) ⟶ 𝒢` of the base change adjunction of
`Stacks.TerminalBaseChange.baseChangeAdj` is locally bijective: over an affine object it is the
base-change comparison of `𝒢`, which is bijective because `𝒢` is cartesian between affine objects,
and affine objects cover `S_ét`. Moreover every `𝒪(X)`-module is the module of sections over `X`
of a sheaf of modules on `S_ét`: sheafify its base change, whose restriction to the affine objects
is already a sheaf.

## Main results

* `AlgebraicGeometry.SmallEtale.generate_isAffine_mem_topology`: affine objects cover `S_ét`.
* `AlgebraicGeometry.SmallEtale.isLocallySurjective_baseChangeAdj_counit` and
  `AlgebraicGeometry.SmallEtale.isLocallyInjective_baseChangeAdj_counit`.
* `AlgebraicGeometry.SmallEtale.exists_isSheaf_obj_iso_of_isTerminal`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.TerminalBaseChange

universe u m

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affine objects cover the small étale site.** -/
theorem generate_isAffine_mem_topology (U : SmallEtale B S hS) :
    Sieve.generate (fun (Z : SmallEtale B S hS) (_ : Z ⟶ U) =>
      AlgebraicGeometry.IsAffine ((toScheme B S hS).obj Z)) ∈ topology B S hS U := by
  have : (SmallAffineEtale.inclusion B S hS).IsCoverDense (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2.isCoverDense'
  refine (topology B S hS).superset_covering ?_
    ((SmallAffineEtale.inclusion B S hS).is_cover_of_isCoverDense (topology B S hS) U)
  rintro Z f ⟨c⟩
  exact ⟨_, c.lift, c.map, c.obj.property, c.fac⟩

/-- The structure sheaf of the small étale site has commutative sections. -/
instance commSections_structureSheaf : CommSections (structureSheaf B S hS).obj :=
  commSections_comp_forget₂ (commStructurePresheaf B S hS)

variable {B S hS} {X : SmallEtale B S hS} (hX : IsTerminal X)
  (hXa : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj X))

include hXa in
/-- Over an affine object of the small étale site, the counit of the base change adjunction at a
quasi-coherent module is bijective. -/
theorem bijective_baseChangeAdj_counit_app_app
    (G : SheafOfModules.{max (u + 1) m} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (Z : SmallEtale B S hS) (hZ : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj Z)) :
    Function.Bijective
      (((baseChangeAdj.{max (u + 1) m} (structureSheaf B S hS).obj hX).counit.app G.val).app
        (op Z)) := by
  have h := bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse B S hS G hG
    hZ hXa (hX.from Z)
  change Function.Bijective (ConcreteCategory.hom
    (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, max (u + 1) m}
      (R := commStructurePresheaf B S hS) G.val (iota hX (op Z)))) at h
  rw [← baseChangeAdj_counit_app_app_eq_restrictionBaseChange.{max (u + 1) m} hX
    (commStructurePresheaf B S hS) G.val (op Z)] at h
  exact h

include hXa in
/-- The counit of the base change adjunction at a quasi-coherent module is locally surjective. -/
theorem isLocallySurjective_baseChangeAdj_counit
    (G : SheafOfModules.{max (u + 1) m} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    PresheafOfModules.IsLocallySurjective (topology B S hS)
      ((baseChangeAdj.{max (u + 1) m} (structureSheaf B S hS).obj hX).counit.app G.val) :=
  isLocallySurjective_of_surjective_app_of_generate_mem
    ((PresheafOfModules.toPresheaf _).map
      ((baseChangeAdj.{max (u + 1) m} (structureSheaf B S hS).obj hX).counit.app G.val)) _
    (generate_isAffine_mem_topology B S hS)
    (fun Z hZ => (bijective_baseChangeAdj_counit_app_app hX hXa G hG Z hZ).2)

include hXa in
/-- The counit of the base change adjunction at a quasi-coherent module is locally injective. -/
theorem isLocallyInjective_baseChangeAdj_counit
    (G : SheafOfModules.{max (u + 1) m} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    PresheafOfModules.IsLocallyInjective (topology B S hS)
      ((baseChangeAdj.{max (u + 1) m} (structureSheaf B S hS).obj hX).counit.app G.val) :=
  Stacks.TerminalFreeResolution.isLocallyInjective_of_injective_app_of_generate_mem
    ((PresheafOfModules.toPresheaf _).map
      ((baseChangeAdj.{max (u + 1) m} (structureSheaf B S hS).obj hX).counit.app G.val)) _
    (generate_isAffine_mem_topology B S hS)
    (fun Z hZ => (bijective_baseChangeAdj_counit_app_app hX hXa G hG Z hZ).1)

include hX hXa in
/-- **Every module over the sections at a terminal object of the small étale site of an affine
scheme is the module of sections of a sheaf of modules**, at module universe `max (u + 1) m`. -/
theorem exists_isSheaf_obj_iso_of_isTerminal
    (Y : ModuleCat.{max (u + 1) m} ((structureSheaf B S hS).obj.obj (op X))) :
    ∃ Q : PresheafOfModules.{max (u + 1) m} (structureSheaf B S hS).obj,
      Presheaf.IsSheaf (topology B S hS) Q.presheaf ∧ Nonempty (Q.obj (op X) ≅ Y) := by
  have hds := SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS
  have := hds.1
  have := hds.2
  have : HasSheafify (topology B S hS) AddCommGrpCat.{max (u + 1) m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _
  have : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m,
      u + 1, u} _
  let X' : SmallAffineEtale B S hS := ⟨X, hXa⟩
  refine exists_isSheaf_obj_iso_of_isDenseSubsite.{max (u + 1) m}
    (J' := SmallAffineEtale.topology B S hS)
    (structureSheaf B S hS)
    (SmallAffineEtale.inclusion B S hS) (X' := X') hX (fun Y' => ?_) Y
  exact isSheaf_of_cartesian_affineChart.{u, max (u + 1) m} B S hS
    ((PresheafOfModules.pushforward₀ (SmallAffineEtale.inclusion B S hS) _).obj
      ((baseChangePresheaf.{max (u + 1) m} (structureSheaf B S hS).obj hX).obj Y'))
    (fun f => isIso_restrictionBaseChange_baseChangePresheaf_commRing.{max (u + 1) m} hX
      (commStructurePresheaf B S hS) Y' ((SmallAffineEtale.inclusion B S hS).op.map f))

end AlgebraicGeometry.SmallEtale

end
