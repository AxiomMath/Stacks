module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.Homology.Perfect.Defs
import all StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect

/-!
# Additions to `StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect`

Supplementary declarations for
`StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect`,
kept in their own module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w d

namespace AlgebraicGeometry.RingedSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

section Associated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-! ### Perfect objects of `D(R)` go to perfect objects -/

/-! ### Strictly perfect objects go to perfect objects of `D(R)` -/

section Sections

variable {B S hS U}

end Sections

end Associated

section Model

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- A direct summand of a finite free module is a retract of a finite biproduct of copies of the
structure sheaf, in the spelling of `AlgebraicGeometry.Space.HasStrictlyPerfectModel`. -/
private theorem isRetractOfFiniteFree_of_isDirectSummandOfFiniteFree_aux
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
    (hM : IsDirectSummandOfFiniteFree (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) M) :
    IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) M := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hM
  let O₁ := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  let eb : SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (ULift.{u} (Fin n)) ≅
      ⨁ fun _ : Fin n => O₁ :=
    (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
      (biproduct.isoCoproduct _).symm
  exact ⟨n, i ≫ eb.hom, eb.inv ≫ r, by simp [hir]⟩

/-- **`Φ` carries a perfect object of `D(R)` to an object with a strictly perfect model**, in the
spelling `AlgebraicGeometry.Space.HasStrictlyPerfectModel` of the derived pullback. -/
theorem hasStrictlyPerfectModel_representedAffineDerivedAssociated_obj
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    HasStrictlyPerfectModel B S hS (Y := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((representedAffineDerivedAssociated B S hS U).obj M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ :=
    exists_isStrictlyPerfect_iso_representedAffineDerivedAssociated_obj B S hS U M hM
  exact ⟨P, fun j => isRetractOfFiniteFree_of_isDirectSummandOfFiniteFree_aux B S hS U _
    (hP.termDirectSummand j), exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect B S hS U P hP,
    ⟨e⟩⟩

end Model

end AlgebraicGeometry.Space

end
