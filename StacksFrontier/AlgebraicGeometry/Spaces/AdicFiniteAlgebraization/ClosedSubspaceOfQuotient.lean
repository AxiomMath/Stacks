module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportTransfer
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# The closed subspace cut out by a quotient of the structure sheaf

Let `Y` be an algebraic space and `s : 𝒪_Y ⟶ M` a surjection onto a quasi-coherent module. Its
kernel is a quasi-coherent sheaf of ideals, hence by Stacks 03MB the defining ideal of a closed
subspace `Z ⊆ Y`, and then `M ≅ i_* 𝒪_Z` compatibly with the two maps out of `𝒪_Y`. Conversely a
closed subspace is determined by the module `i_* 𝒪_Z` under `𝒪_Y`. This is the last step of the
proof of Stacks 08BG: once the system `(𝒪_{Z_n})` has been algebraized to a quotient
`𝒪_X ⟶ ℱ`, "setting `Z = V(𝒥)` finishes the proof".

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_of_epi`: a quasi-coherent quotient of `𝒪_Y` is
  `i_* 𝒪_Z` for a closed subspace `Z`, compatibly with the maps out of `𝒪_Y`.
* `AlgebraicGeometry.Space.closedSubspace_eq_of_iso`: two closed subspaces whose direct images
  `i_* 𝒪` are isomorphic under `𝒪_Y` are equal.
* `AlgebraicGeometry.Space.isProper_ι_comp_of_hasProperSupport`: a closed subspace whose
  direct image `i_* 𝒪_Z` has proper support is proper.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the modules of the pinned universe used here; the abelian structure of
`AlgebraicGeometry.Space.Modules` is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- A morphism vanishing on the kernel submodule of `p` vanishes on its inclusion. -/
theorem ker_ι_comp_eq_zero_of_ker_eq {M N N' : Modules.{u, u} B S hS Y.1 Y.2} (p : M ⟶ N)
    (q : M ⟶ N') (h : SheafOfModules.Submodule.ker p = SheafOfModules.Submodule.ker q) :
    (SheafOfModules.Submodule.ker p).ι ≫ q = 0 := by
  rw [h]
  exact SheafOfModules.Submodule.ker_ι_comp q

/-- The factorization of `q` through an epimorphism `p` with the same kernel submodule. -/
def descOfKerEq {M N N' : Modules.{u, u} B S hS Y.1 Y.2} (p : M ⟶ N) (q : M ⟶ N') (hp : Epi p)
    (h : SheafOfModules.Submodule.ker p = SheafOfModules.Submodule.ker q) : N ⟶ N' :=
  haveI := hp
  Abelian.epiDesc p q (by
    rw [← SheafOfModules.Submodule.kerIsoKernel_inv_comp_ι p, Category.assoc,
      ker_ι_comp_eq_zero_of_ker_eq B S hS Y p q h, comp_zero])

/-- The factorization `descOfKerEq` of `q` through the epimorphism `p` composes with `p` to
`q`. -/
theorem comp_descOfKerEq {M N N' : Modules.{u, u} B S hS Y.1 Y.2} (p : M ⟶ N) (q : M ⟶ N')
    (hp : Epi p) (h : SheafOfModules.Submodule.ker p = SheafOfModules.Submodule.ker q) :
    p ≫ descOfKerEq B S hS Y p q hp h = q :=
  have := hp
  Abelian.comp_epiDesc _ _ _

/-- Two epimorphisms out of the same object with the same kernel submodule have isomorphic
targets, compatibly with the two epimorphisms. -/
def isoOfEpiOfKerEq {M N N' : Modules.{u, u} B S hS Y.1 Y.2} (p : M ⟶ N) (q : M ⟶ N')
    (hp : Epi p) (hq : Epi q)
    (h : SheafOfModules.Submodule.ker p = SheafOfModules.Submodule.ker q) : N ≅ N' where
  hom := descOfKerEq B S hS Y p q hp h
  inv := descOfKerEq B S hS Y q p hq h.symm
  hom_inv_id := by
    have := hp
    refine (cancel_epi p).1 ?_
    rw [← Category.assoc, comp_descOfKerEq, comp_descOfKerEq, Category.comp_id]
  inv_hom_id := by
    have := hq
    refine (cancel_epi q).1 ?_
    rw [← Category.assoc, comp_descOfKerEq, comp_descOfKerEq, Category.comp_id]

/-- The isomorphism `isoOfEpiOfKerEq` is compatible with the two epimorphisms: `p` followed by
it is `q`. -/
theorem comp_isoOfEpiOfKerEq_hom {M N N' : Modules.{u, u} B S hS Y.1 Y.2} (p : M ⟶ N) (q : M ⟶ N')
    (hp : Epi p) (hq : Epi q)
    (h : SheafOfModules.Submodule.ker p = SheafOfModules.Submodule.ker q) :
    p ≫ (isoOfEpiOfKerEq B S hS Y p q hp hq h).hom = q :=
  comp_descOfKerEq B S hS Y p q hp h

/-- **A quasi-coherent quotient of `𝒪_Y` is the direct image of the structure sheaf of a closed
subspace**, compatibly with the maps out of `𝒪_Y` (Stacks 03MB). -/
theorem exists_closedSubspace_of_epi {M : Modules.{u, u} B S hS Y.1 Y.2}
    (hM : M.IsQuasicoherentOnSite) (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M)
    (hs : Epi s) :
    ∃ (Z : ClosedSubspaces B S hS Y.1)
      (e : structureSheafPushforward B S hS (closedSubspaceInclusion B S hS Y Z) ≅ M),
      pushforwardStructureProjection B S hS (closedSubspaceInclusion B S hS Y Z) ≫ e.hom = s := by
  have hJ : (SheafOfModules.Submodule.ker s).toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.Submodule.kerIsoKernel s).symm
      (@isQuasicoherentOnSite_kernel_of_quasicoherent B S hS Y.1 Y.2 _ _ s
        (SheafOfModules.isQuasicoherentOnSite_unit _) hM)
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS Y
    (SheafOfModules.Submodule.ker s) hJ
  have hci : IsClosedImmersion B S hS (closedSubspaceInclusion B S hS Y Z).hom := Z.2.2
  have hpe := epi_pushforwardStructureProjection B S hS _ hci
  have hker : SheafOfModules.Submodule.ker
      (pushforwardStructureProjection B S hS (closedSubspaceInclusion B S hS Y Z)) =
      SheafOfModules.Submodule.ker s := by
    rw [ker_pushforwardStructureProjection, ← hZ]
    exact kernelIdealSheaf_eq_definingIdealSheaf B S hS Y Z
  exact ⟨Z, isoOfEpiOfKerEq B S hS Y _ s hpe hs hker,
    comp_isoOfEpiOfKerEq_hom B S hS Y _ s hpe hs hker⟩

/-- **A closed subspace is determined by its direct image `i_* 𝒪_Z` under `𝒪_Y`.** -/
theorem closedSubspace_eq_of_iso (Z Z' : ClosedSubspaces B S hS Y.1)
    (e : structureSheafPushforward B S hS (closedSubspaceInclusion B S hS Y Z) ≅
      structureSheafPushforward B S hS (closedSubspaceInclusion B S hS Y Z'))
    (he : pushforwardStructureProjection B S hS (closedSubspaceInclusion B S hS Y Z) ≫ e.hom =
      pushforwardStructureProjection B S hS (closedSubspaceInclusion B S hS Y Z')) :
    Z = Z' := by
  refine definingIdealSheaf_injective B S hS Y ?_
  rw [← kernelIdealSheaf_eq_definingIdealSheaf, ← kernelIdealSheaf_eq_definingIdealSheaf,
    ← ker_pushforwardStructureProjection, ← ker_pushforwardStructureProjection, ← he]
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  ext x
  let p := pushforwardStructureProjection B S hS (closedSubspaceInclusion B S hS Y Z)
  refine ⟨fun hx => (SheafOfModules.Submodule.mem_ker (p ≫ e.hom) U x).2 ?_,
    fun hx => (SheafOfModules.Submodule.mem_ker p U x).2 ?_⟩
  · have h0 : p.val.app U x = 0 := (SheafOfModules.Submodule.mem_ker p U x).1 hx
    show e.hom.val.app U (p.val.app U x) = 0
    rw [h0, map_zero]
  · have h0 : e.hom.val.app U (p.val.app U x) = 0 :=
      (SheafOfModules.Submodule.mem_ker (p ≫ e.hom) U x).1 hx
    have h2 : e.inv.val.app U (e.hom.val.app U (p.val.app U x)) = p.val.app U x :=
      congrArg (fun k => k.val.app U (p.val.app U x)) e.hom_inv_id
    rw [← h2, h0, map_zero]

/-- **A closed subspace whose direct image `i_* 𝒪_Z` has proper support is proper**: its points
lie in the support of `i_* 𝒪_Z`, the structure sheaf of `Z` being supported everywhere. -/
theorem isProper_ι_comp_of_hasProperSupport {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (f : Y.1 ⟶ T) (hf : IsLocallyOfFiniteType B S hS f)
    (Z : ClosedSubspaces B S hS Y.1) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (e : structureSheafPushforward B S hS (closedSubspaceInclusion B S hS Y Z) ≅ M)
    (hM : HasProperSupport B S hS Y.2 hT f hf ((SheafOfModules.toSheaf _).obj M)) :
    IsProper B S hS (Z.1.ι ≫ f) := by
  refine isProper_comp_of_hasProperSupport_of_range_subset B S hS Y.2 hT f hf hM Z.2.1 Z.1.ι
    Z.2.2 ?_
  rw [← supportOfSheaf_eq_of_iso B S hS Y e]
  have h := image_supportOfSheaf_subset_supportOfSheaf_modulePushforward B S hS
    (closedSubspaceInclusion B S hS Y Z) Z.2.2
    (structureSheafModule B S hS ⟨Z.1.toFunctor, Z.2.1⟩)
  rwa [supportOfSheaf_structureSheafModule, Set.image_univ] at h

end AlgebraicGeometry.Space

end
