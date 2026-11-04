module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SectionMultiplicationExtension
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Ample

/-!
# The support of the cokernel of a map into an invertible module

Let `X` be a scheme, `N` an invertible `𝒪_X`-module, and `φ : M ⟶ N` a morphism out of a module
`M` isomorphic to `𝒪_X` by `c : 𝒪_X ≅ M`. The cokernel of `φ` is supported exactly where the
section `φ(c(1))` of `N` vanishes. This is the scheme-level input to the identification, on the
schemes over an algebraic space, of the open subspace on which a map into an invertible module is
surjective.

## Main results

* `Stacks.CokernelSupport.surjective_mapFun_of_notMem_supp_cokernel`: off the support of the
  cokernel, the stalk map is surjective.
* `Stacks.CokernelSupport.compl_supp_cokernel_eq_nonvanishingLocus`: the complement of the
  support of `Coker φ` is the nonvanishing locus of `φ(c(1))`.
* `Stacks.CokernelSupport.nonvanishingLocus_app_subset`: a morphism of modules can only shrink
  the nonvanishing locus of a section.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper (modulesStalkFunctor)
open Stacks.Ample (nonvanishingLocus IsInvertibleModule unitModule)
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.CokernelSupport

variable {X : Scheme.{u}}

/-- **Off the support of the cokernel the stalk map is surjective.** The stalk functor is a left
adjoint, so it carries the cokernel to the cokernel of the stalk map; a module whose stalk is zero
has surjective stalk map. -/
theorem surjective_mapFun_of_notMem_supp_cokernel {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (hx : x ∉ _root_.SheafOfModules.supp (cokernel φ)) :
    Function.Surjective (Stacks.ModuleStalk.mapFun φ x) := by
  have hsub : Subsingleton ((modulesStalkFunctor X x).obj (cokernel φ)) :=
    ⟨fun a b => by
      by_contra hab
      exact hx ⟨a - b, sub_ne_zero.mpr hab⟩⟩
  have hepi : Epi ((modulesStalkFunctor X x).map φ) :=
    (Preadditive.epi_iff_isZero_cokernel _).mpr ((ModuleCat.isZero_of_subsingleton _).of_iso
      (PreservesCokernel.iso (modulesStalkFunctor X x) φ).symm)
  intro n
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective _).mp hepi n
  exact ⟨m, (AlgebraicGeometry.modulesStalkFunctor_map_apply φ x m).symm.trans hm⟩

/-- A left inverse of a module map acts as a left inverse on stalks. -/
private theorem mapFun_mapFun_of_comp_eq_id {M N : X.Modules} {f : M ⟶ N} {g : N ⟶ M}
    (h : f ≫ g = 𝟙 M) (x : X) (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    Stacks.ModuleStalk.mapFun g x (Stacks.ModuleStalk.mapFun f x m) = m := by
  rw [← Stacks.ModuleStalk.mapFun_comp, h, Stacks.ModuleStalk.mapFun_id]

/-- The image of `1` under an isomorphism `𝒪_X ≅ M` generates every stalk of `M`. -/
theorem exists_smul_Γgerm_of_iso_unit {M : X.Modules} (c : unitModule X ≅ M) (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    ∃ r : X.presheaf.stalk x, m = r •
      (M.presheaf.Γgerm x).hom (c.hom.app ⊤ (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))) := by
  have h1 : x ∈ nonvanishingLocus (unitModule X)
      (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤))) :=
    Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one X x _ rfl
  obtain ⟨r, hr⟩ := Stacks.SectionProduct.exists_smul_Γgerm (unitModule X) _ h1
    (Stacks.ModuleStalk.mapFun c.inv x m)
  refine ⟨r, ?_⟩
  rw [← mapFun_mapFun_of_comp_eq_id c.inv_hom_id x m, hr,
    Stacks.ModuleStalk.mapFun_smul, Stacks.ModuleStalk.mapFun_Γgerm]

/-- **The cokernel of a map out of a trivialised module into an invertible module is supported
exactly where the image of the generator vanishes.** For `c : 𝒪_X ≅ M` and `φ : M ⟶ N` with `N`
invertible, the complement of the support of `Coker φ` is the nonvanishing locus of `φ(c(1))`. -/
theorem compl_supp_cokernel_eq_nonvanishingLocus {M N : X.Modules} [IsInvertibleModule X N]
    (c : unitModule X ≅ M) (φ : M ⟶ N) :
    (_root_.SheafOfModules.supp (cokernel φ))ᶜ =
      nonvanishingLocus N
        (φ.app ⊤ (c.hom.app ⊤ (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤))))) := by
  ext x
  rw [Set.mem_compl_iff, Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates]
  refine ⟨fun hx n => ?_, fun hgen => ?_⟩
  · obtain ⟨m, rfl⟩ := surjective_mapFun_of_notMem_supp_cokernel φ x hx n
    obtain ⟨r, rfl⟩ := exists_smul_Γgerm_of_iso_unit c x m
    exact ⟨r, by rw [Stacks.ModuleStalk.mapFun_smul, Stacks.ModuleStalk.mapFun_Γgerm]⟩
  · refine AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun φ x fun n => ?_
    obtain ⟨r, rfl⟩ := hgen n
    exact ⟨r • (M.presheaf.Γgerm x).hom
        (c.hom.app ⊤ (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))),
      by rw [Stacks.ModuleStalk.mapFun_smul, Stacks.ModuleStalk.mapFun_Γgerm]⟩

/-- **A morphism of modules can only shrink the nonvanishing locus of a section.** -/
theorem nonvanishingLocus_app_subset {M N : X.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    nonvanishingLocus N (φ.app ⊤ s) ⊆ nonvanishingLocus M s := by
  intro x hx hs
  refine hx ?_
  rw [← Stacks.ModuleStalk.mapFun_Γgerm]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul φ x hs

/-- **A point lies off the support of the cokernel exactly when the stalk map is surjective
there.** -/
theorem notMem_supp_cokernel_iff_surjective {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    x ∉ _root_.SheafOfModules.supp (cokernel φ) ↔
      Function.Surjective (Stacks.ModuleStalk.mapFun φ x) :=
  ⟨surjective_mapFun_of_notMem_supp_cokernel φ x,
    AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun φ x⟩

/-- If a composite `e ≫ φ` is surjective at a point, so is `φ`. -/
theorem notMem_supp_cokernel_of_comp {M' M N : X.Modules} (e : M' ⟶ M) (φ : M ⟶ N) (x : X)
    (h : x ∉ _root_.SheafOfModules.supp (cokernel (e ≫ φ))) :
    x ∉ _root_.SheafOfModules.supp (cokernel φ) := by
  refine AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun φ x fun n => ?_
  obtain ⟨m, hm⟩ := surjective_mapFun_of_notMem_supp_cokernel (e ≫ φ) x h n
  exact ⟨Stacks.ModuleStalk.mapFun e x m, (Stacks.ModuleStalk.mapFun_comp e φ x m).symm.trans hm⟩

/-- Precomposing with an isomorphism does not move the support of the cokernel. -/
theorem notMem_supp_cokernel_iso_comp_iff {M' M N : X.Modules} (e : M' ≅ M) (φ : M ⟶ N)
    (x : X) :
    x ∉ _root_.SheafOfModules.supp (cokernel (e.hom ≫ φ)) ↔
      x ∉ _root_.SheafOfModules.supp (cokernel φ) := by
  refine ⟨notMem_supp_cokernel_of_comp e.hom φ x, fun h => ?_⟩
  refine notMem_supp_cokernel_of_comp e.inv (e.hom ≫ φ) x ?_
  exact (congrArg (fun k : M ⟶ N => x ∉ _root_.SheafOfModules.supp (cokernel k))
    (Iso.inv_hom_id_assoc e φ)).mpr h

/-- Postcomposing with an isomorphism does not move the support of the cokernel. -/
theorem notMem_supp_cokernel_comp_iso_iff {M N N' : X.Modules} (φ : M ⟶ N) (e : N ≅ N')
    (x : X) :
    x ∉ _root_.SheafOfModules.supp (cokernel (φ ≫ e.hom)) ↔
      x ∉ _root_.SheafOfModules.supp (cokernel φ) := by
  have hleft := mapFun_mapFun_of_comp_eq_id e.hom_inv_id x
  have hright := mapFun_mapFun_of_comp_eq_id e.inv_hom_id x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun φ x fun n => ?_
    obtain ⟨m, hm⟩ := surjective_mapFun_of_notMem_supp_cokernel _ x h
      (Stacks.ModuleStalk.mapFun e.hom x n)
    exact ⟨m, (hleft _).symm.trans ((congrArg (Stacks.ModuleStalk.mapFun e.inv x)
      ((Stacks.ModuleStalk.mapFun_comp φ e.hom x m).symm.trans hm)).trans (hleft n))⟩
  · refine AlgebraicGeometry.notMem_supp_cokernel_of_surjective_mapFun _ x fun n => ?_
    obtain ⟨m, hm⟩ := surjective_mapFun_of_notMem_supp_cokernel _ x h
      (Stacks.ModuleStalk.mapFun e.inv x n)
    exact ⟨m, (Stacks.ModuleStalk.mapFun_comp φ e.hom x m).trans
      ((congrArg (Stacks.ModuleStalk.mapFun e.hom x) hm).trans (hright n))⟩

/-- **Off the support of the cokernel of a sum, one of the summands is surjective.** For maps
out of a trivialised module into an invertible module this is the nonvanishing locus of a sum
lying in the union of the nonvanishing loci. -/
theorem notMem_supp_cokernel_of_add {M N : X.Modules} [IsInvertibleModule X N]
    (c : unitModule X ≅ M) (φ ψ : M ⟶ N) (x : X)
    (h : x ∉ _root_.SheafOfModules.supp (cokernel (φ + ψ))) :
    x ∉ _root_.SheafOfModules.supp (cokernel φ) ∨
      x ∉ _root_.SheafOfModules.supp (cokernel ψ) := by
  rw [← Set.mem_compl_iff, compl_supp_cokernel_eq_nonvanishingLocus c] at h
  rw [← Set.mem_compl_iff, ← Set.mem_compl_iff, compl_supp_cokernel_eq_nonvanishingLocus c,
    compl_supp_cokernel_eq_nonvanishingLocus c]
  exact Stacks.Ample.nonvanishingLocus_add_subset N _ _ h

/-- The zero map out of a trivialised module into an invertible module is surjective nowhere. -/
theorem mem_supp_cokernel_zero {M N : X.Modules} [IsInvertibleModule X N]
    (c : unitModule X ≅ M) (x : X) :
    x ∈ _root_.SheafOfModules.supp (cokernel (0 : M ⟶ N)) := by
  by_contra h
  rw [← Set.mem_compl_iff, compl_supp_cokernel_eq_nonvanishingLocus c] at h
  have h0 : (0 : M ⟶ N).app ⊤ (c.hom.app ⊤ (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))) = 0 :=
    rfl
  rwa [h0, Stacks.Ample.nonvanishingLocus_zero] at h

/-- An isomorphism of modules carries the nonvanishing locus of a section to the nonvanishing
locus of its image. -/
alias nonvanishingLocus_iso_app := Stacks.Ample.nonvanishingLocus_congr

/-- **The map of multiplication by a section is surjective on the nonvanishing locus of the
section.** -/
theorem notMem_supp_cokernel_unitHom {N : X.Modules} [IsInvertibleModule X N] (s : Γ(N, ⊤))
    (x : X) (hx : x ∈ nonvanishingLocus N s) :
    x ∉ _root_.SheafOfModules.supp (cokernel (Stacks.SheafOfModules.unitHom N s)) := by
  rw [← Set.mem_compl_iff, compl_supp_cokernel_eq_nonvanishingLocus (Iso.refl _)]
  have h : (Stacks.SheafOfModules.unitHom N s).app ⊤
      ((Iso.refl (unitModule X)).hom.app ⊤ (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))) = s := by
    refine (Stacks.SheafOfModules.unitHom_app_one N s ⊤).trans ?_
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rwa [h]

end Stacks.CokernelSupport

end
