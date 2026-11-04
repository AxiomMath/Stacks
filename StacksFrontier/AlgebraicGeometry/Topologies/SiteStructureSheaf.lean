module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# The sheaf condition for the structure presheaf of a site of schemes

Let `S` be a scheme and let a site of schemes over `S` be given by a functor
`toOver : C ⥤ Over S`.  Its structure presheaf `Stacks.Sites.structurePresheaf S toOver` of
global functions is a sheaf of rings as soon as the restriction along `toOver` of the presheaf
of *types* of global functions is a sheaf.  Since global functions are a sheaf for the fpqc
topology, this reduces the sheaf condition on any of the standard sites to the comparison of
its topology with the fpqc topology.

A second form of the same reduction asks instead that the canonical functor to all schemes be
compatible-preserving and cover preserving for the fpqc topology.  Compatible-preservation is
automatic for a site with fibre products whose canonical functor preserves them, which is
`Stacks.Sites.compatiblePreserving_of_preservesPullbacks`; both inputs are assembled below for
the big étale site.

The same restriction argument applies to the presheaf of global sections of the pullback of a
quasi-coherent module `F` on `S`, whose sheaf condition is the coefficient half of Tag 03DX.
The associated module `Fᵃ` itself is `Stacks.Sites.siteAssociatedModule`.

## Main definitions

* `Stacks.Sites.globalSectionsOver`: the presheaf of types of global functions on the schemes
  over a base scheme.

## Main results

* `Stacks.Sites.isSheaf_fpqcOver_globalSections`: global functions on the schemes over `S` are
  a sheaf of types for the fpqc topology induced on `Over S`.
* `Stacks.Sites.isSheaf_structurePresheaf`: the structure presheaf of a site of schemes over
  `S` is a sheaf of rings as soon as the underlying presheaf of types is a sheaf.
* `Stacks.Sites.compatiblePreserving_of_preservesPullbacks`: a functor out of a category with
  fibre products which preserves them is compatible-preserving for any topology on the target.
* `Stacks.Sites.isSheaf_structurePresheaf_of_coverPreserving`: the structure presheaf of a site
  of schemes over `S` is a sheaf of rings as soon as the canonical functor to all schemes is
  compatible-preserving and cover preserving for the fpqc topology.
* `Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous`: Tag 03DT, the fpqc sheaf condition
  for the presheaf of pullback sections, gives the sheaf condition for the associated presheaf
  on any site whose canonical functor is continuous.
* `AlgebraicGeometry.BigEtaleOver.compatiblePreserving_toScheme` and
  `AlgebraicGeometry.BigEtaleOver.coverPreserving_toScheme`: the two inputs of that reduction
  for the big étale site.
* `AlgebraicGeometry.BigEtaleOver.isSheaf_associatedPresheaf` and
  `AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf`: on those two sites the sheaf
  condition for the associated presheaf follows from Tag 03DT alone.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe w v₁ v₂ u₁ u₂ u

namespace Stacks.Sites

/-- The presheaf of types of global functions on the schemes over `S`.  It is the restriction
of the presheaf of global functions on all schemes along `CategoryTheory.Over.forget`. -/
public abbrev globalSectionsOver (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.forget S).op ⋙ Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat

/-- Global functions on the schemes over `S` are a sheaf of types for the fpqc topology
induced on `Over S`. -/
public theorem isSheaf_fpqcOver_globalSections (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (globalSectionsOver S) :=
  (globalSectionsSheaf.over S).property

/-- The underlying presheaf of types of the structure presheaf of a site of schemes over `S`
is the restriction of the presheaf of global functions on the schemes over `S`. -/
public theorem structurePresheaf_comp_forget (S : Scheme.{u}) {C : Type (u + 1)}
    [Category.{u} C] (toOver : C ⥤ Over S) :
    structurePresheaf S toOver ⋙ CategoryTheory.forget RingCat.{u} =
      toOver.op ⋙ globalSectionsOver S := by
  show (toOver.op ⋙ (Over.forget S).op ⋙ Scheme.Γ.{u} ⋙ forget₂ CommRingCat RingCat) ⋙
      CategoryTheory.forget RingCat.{u} =
    toOver.op ⋙ (Over.forget S).op ⋙ Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat
  simp only [Functor.assoc, HasForget₂.forget_comp]

/-- The structure presheaf of a site of schemes over `S` is a sheaf of rings as soon as the
restriction to the site of the presheaf of global functions is a sheaf of types. -/
public theorem isSheaf_structurePresheaf (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (toOver : C ⥤ Over S)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalSectionsOver S)) :
    Presheaf.IsSheaf J (structurePresheaf S toOver) := by
  refine isSheaf_ringCat_of_isSheaf_forget J _ ?_
  rw [structurePresheaf_comp_forget]
  exact (isSheaf_iff_isSheaf_of_type _ _).1 h

/-! ### The descent argument through compatible preservation -/

/-- A functor out of a category with fibre products which preserves them is
compatible-preserving for any topology on its target. -/
public theorem compatiblePreserving_of_preservesPullbacks {C : Type u₁} [Category.{v₁} C]
    [HasPullbacks C] {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (G : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan G] : CompatiblePreserving.{w} K G := by
  refine compatiblePreserving_of_lift K G ?_
  intro Y₁ Y₂ Z g₁ g₂ T f₁ f₂ e
  have h : IsPullback (G.map (pullback.fst g₁ g₂)) (G.map (pullback.snd g₁ g₂))
      (G.map g₁) (G.map g₂) := (IsPullback.of_hasPullback g₁ g₂).map G
  exact ⟨pullback g₁ g₂, pullback.fst g₁ g₂, pullback.snd g₁ g₂, h.lift f₁ f₂ e,
    pullback.condition, h.lift_fst f₁ f₂ e, h.lift_snd f₁ f₂ e⟩

/-- The structure presheaf of a site of schemes over `S` is a sheaf of rings as soon as the
canonical functor to all schemes is compatible-preserving and cover preserving for the fpqc
topology. -/
public theorem isSheaf_structurePresheaf_of_coverPreserving {C : Type (u + 1)}
    [Category.{u} C] (S : Scheme.{u}) (J : GrothendieckTopology C) (toOver : C ⥤ Over S)
    (hcp : CompatiblePreserving.{u} Scheme.fpqcTopology.{u} (toOver ⋙ Over.forget S))
    (hcov : CoverPreserving J Scheme.fpqcTopology.{u} (toOver ⋙ Over.forget S)) :
    Presheaf.IsSheaf J (structurePresheaf S toOver) := by
  refine isSheaf_ringCat_of_isSheaf_forget _ _ ?_
  intro X R hR
  exact isSheafFor_op_comp hcp globalSectionsSheaf R (hcov.cover_preserve hR)

/-- If the presheaf of pullback sections of Tag 03DS is an fpqc sheaf on all schemes over `S`, then
its restriction along a functor that is continuous for the fpqc topology of the schemes over `S` is
a sheaf on the site. -/
public theorem isSheaf_associatedPresheaf_of_isContinuous {C : Type (u + 1)} [Category.{u} C]
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (toOver : C ⥤ Over S)
    (J : GrothendieckTopology C)
    [toOver.IsContinuous J (Scheme.fpqcTopology.{u}.over S)]
    (h : Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F)) :
    Presheaf.IsSheaf J (associatedPresheaf S F toOver) :=
  toOver.op_comp_isSheaf J _ ⟨_, h⟩

end Stacks.Sites

namespace AlgebraicGeometry.BigEtaleOver

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The big étale site -/

/-- The canonical functor from the big étale category over `S` to all schemes preserves fibre
products. -/
public instance preservesPullbacks_toScheme :
    PreservesLimitsOfShape WalkingCospan (toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

/-- The canonical functor from the big étale category over `S` to all schemes is
compatible-preserving for the fpqc topology. -/
public theorem compatiblePreserving_toScheme :
    CompatiblePreserving.{u} Scheme.fpqcTopology.{u} (toScheme B S hS) :=
  Stacks.Sites.compatiblePreserving_of_preservesPullbacks _ _

/-- The canonical functor from the big étale category over `S` to all schemes is cover
preserving from the big étale topology to the fpqc topology. -/
public theorem coverPreserving_toScheme :
    CoverPreserving (topology B S hS) Scheme.fpqcTopology.{u} (toScheme B S hS) := by
  refine coverPreserving_of_generators (toScheme B S hS) (precoverage B S hS) _ ?_
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [← Sieve.generate_map_eq_functorPushforward, PreZeroHypercover.presieve₀,
    Presieve.map_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.etalePrecoverage_le_fpqcPrecoverage _ hE.etale)

/-! #### The sheaf condition for the associated presheaf, from Tag 03DT -/

/-- The canonical functor from the big étale category over `S` to the schemes over `S` is
compatible-preserving for the fpqc topology on `Over S`. -/
public theorem compatiblePreserving_toOver :
    CompatiblePreserving.{u} (Scheme.fpqcTopology.over S)
      (Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S) := by
  have : PreservesLimitsOfShape WalkingCospan
      ((Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S) ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (toScheme B S hS))
  have : PreservesLimitsOfShape WalkingCospan
      (Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)
  exact Stacks.Sites.compatiblePreserving_of_preservesPullbacks _ _

/-- The sieve generated by the image in `Over S` of a chosen covering family of the big étale
category over `S` is covering for the localized fpqc topology. -/
public theorem functorPushforward_toOver_mem {Y : BigEtaleOver B S hS} (R : Presieve Y)
    (hR : R ∈ precoverage B S hS Y) :
    (Sieve.generate R).functorPushforward
        (Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S) ∈
      (Scheme.fpqcTopology.over S)
        ((Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S).obj Y) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_apply,
    ← Sieve.functorPushforward_comp]
  exact (coverPreserving_toScheme B S hS).cover_preserve
    (Precoverage.generate_mem_toGrothendieck hR)

/-- An abelian-group-valued fpqc sheaf on the schemes over `S` restricts to a sheaf on the big
étale site of `S`.  This is the big étale counterpart of
`AlgebraicGeometry.SmallEtale.isSheaf_toOver_op_comp`. -/
public theorem isSheaf_toOver_op_comp (P : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (P ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presheaf.IsSheaf (topology B S hS)
      ((Over.post B.inclusion : BigEtaleOver B S hS ⥤ Over S).op ⋙ P) :=
  Stacks.Sites.isSheaf_addCommGrpCat_op_comp_of_precoverage _
    (compatiblePreserving_toOver B S hS) P hP
    fun _ _ hR ↦ functorPushforward_toOver_mem B S hS _ hR

/-- If the presheaf of pullback sections of Tag 03DS is an fpqc sheaf on the schemes over `S`, then
its restriction to the big étale site of `S` is a sheaf. -/
public theorem isSheaf_associatedPresheaf (F : S.Modules) [F.IsQuasicoherent]
    (hP : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.associatedPresheaf (C := BigEtaleOver B S hS) S F
        (Over.post B.inclusion)) :=
  isSheaf_toOver_op_comp B S hS _ hP

end AlgebraicGeometry.BigEtaleOver

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small étale site -/

/-- If the presheaf of pullback sections of Tag 03DS is an fpqc sheaf on the schemes over `S`, then
its restriction to the small étale site of `S` is a sheaf. -/
public theorem isSheaf_associatedPresheaf (F : S.Modules) [F.IsQuasicoherent]
    (hP : Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat)) :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.associatedPresheaf (C := SmallEtale B S hS) S F
        (inclusion B S hS ⋙ Over.post B.inclusion)) :=
  isSheaf_toOver_op_comp B S hS _ hP

end AlgebraicGeometry.SmallEtale

end
