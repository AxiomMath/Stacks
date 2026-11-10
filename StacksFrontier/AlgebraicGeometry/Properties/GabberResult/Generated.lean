module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGenerated
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Subsheaf

/-!
# The subsheaf cut out by a compatible family is cardinally generated

If the compatible family `N` of submodules of the sections of `F` over the affine opens of a
scheme is given by spans of sets of at most `κ` sections, then the subsheaf
`Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule` it cuts out is `κ`-generated. This is an
input to Gabber's theorem ([Stacks, Tag 077N](https://stacks.math.columbia.edu/tag/077N)).

## Main results

* `Stacks.AlgebraicGeometry.GabberColimit.epi_freeHomEquiv_symm_mkOver`: a family of sections of
  an `𝒪_X`-module over an open `W` whose restrictions span the sections over arbitrarily small
  opens around every point generates the restriction `M.over W`.
* `Stacks.AlgebraicGeometry.GabberColimit.generatingSectionsOfLocalSpan`: the same statement
  packaged as a `SheafOfModules.GeneratingSections`.
* `Stacks.AlgebraicGeometry.GabberColimit.isCardinalGenerated_sheafSubmodule`: the subsheaf cut
  out by a compatible family of spans of at most `κ` sections is `κ`-generated.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace SheafOfModules
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.GabberColimit

/-- Membership in the span of a set of elements of a submodule `P` is detected in the ambient
module: a span inside `P` is the span inside the ambient module of the underlying elements. -/
theorem mem_span_subtype {R Mm : Type*} [Semiring R] [AddCommMonoid Mm] [Module R Mm]
    (P : Submodule R Mm) (S : Set P) (x : P)
    (h : (x : Mm) ∈ Submodule.span R ((Subtype.val : P → Mm) '' S)) :
    x ∈ Submodule.span R S := by
  have he : ((Subtype.val : P → Mm) '' S) = (P.subtype '' S) := rfl
  rw [he, ← Submodule.map_span P.subtype S, Submodule.mem_map] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact (Subtype.ext hxy : y = x) ▸ hy

/-- `mem_span_subtype` for a span over the range of a family. -/
theorem mem_span_range_subtype {R Mm : Type*} [Semiring R] [AddCommMonoid Mm] [Module R Mm]
    (P : Submodule R Mm) {ι : Type*} (f : ι → P) (x : P)
    (h : (x : Mm) ∈ Submodule.span R (Set.range fun i ↦ (f i : Mm))) :
    x ∈ Submodule.span R (Set.range f) := by
  refine mem_span_subtype P _ x ?_
  rwa [← Set.range_comp]

variable {X : Scheme.{u}}

/-- **A locally spanning family of sections generates.** If the restrictions of a family `t` of
sections of an `𝒪_X`-module `M` over an open `W` span the sections of `M` over arbitrarily small
opens around every point of every open below `W`, then the induced morphism from the free sheaf
of modules on the index set to `M.over W` is an epimorphism. -/
theorem epi_freeHomEquiv_symm_mkOver (M : X.Modules) (W : X.Opens) {I : Type u} (t : I → Γ(M, W))
    (hloc : ∀ (V : X.Opens) (hVW : V ≤ W) (s : Γ(M, V)) (x : X), x ∈ V →
      ∃ (V' : X.Opens) (hV'V : V' ≤ V), x ∈ V' ∧
        M.presheaf.map (homOfLE hV'V).op s ∈
          Submodule.span Γ(X, V')
            (Set.range fun i ↦ M.presheaf.map (homOfLE (hV'V.trans hVW)).op (t i))) :
    Epi ((SheafOfModules.freeHomEquiv (M.over W)).symm
      (fun i ↦ Stacks.SheafOfModules.mkOver (M := M) (V := W) (t i))) := by
  set σ : I → (M.over W).sections :=
    fun i ↦ Stacks.SheafOfModules.mkOver (M := M) (V := W) (t i)
  set φ := (SheafOfModules.freeHomEquiv (M.over W)).symm σ
  apply Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
  refine ⟨fun {Y} s ↦ ?_⟩
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V', hV'V, hxV', hmem⟩ := hloc Y.left (leOfHom Y.hom) s x hx
  refine ⟨V', homOfLE hV'V, ?_, hxV'⟩
  rw [Sieve.overEquiv_iff]
  set Z : Over W := Over.mk (homOfLE hV'V ≫ Y.hom)
  have hgen : ∀ i : I, ∃ a, (φ.val.app (op Z)) a
      = M.presheaf.map (homOfLE (hV'V.trans (leOfHom Y.hom))).op (t i) := by
    intro i
    refine ⟨(SheafOfModules.ιFree i).val.app (op Z)
      (1 : (X.ringCatSheaf.over W).obj.obj (op Z)), ?_⟩
    have h := Stacks.SheafOfModules.FiniteTypeKernel.ιFree_freeHomEquiv_symm σ i
    have h2 := congrArg (fun f : SheafOfModules.unit (X.ringCatSheaf.over W) ⟶ M.over W =>
        f.val.app (op Z) (1 : (X.ringCatSheaf.over W).obj.obj (op Z))) h
    refine h2.trans ?_
    change (LinearMap.ringLmapEquivSelf ((X.ringCatSheaf.over W).obj.obj (op Z)) ℤ
      ((M.over W).val.obj (op Z))).symm ((σ i).val (op Z)) 1 = _
    simp only [Functor.comp_obj, PresheafOfModules.presheaf_obj_coe,
      LinearMap.ringLmapEquivSelf_symm_apply, LinearMap.coe_smulRight, Module.End.one_apply,
      one_smul, homOfLE_leOfHom]
    rfl
  have hsub : ∀ y ∈ Submodule.span Γ(X, V')
      (Set.range fun i ↦ M.presheaf.map (homOfLE (hV'V.trans (leOfHom Y.hom))).op (t i)),
      ∃ a, (φ.val.app (op Z)) a = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hgen i
    | zero => exact ⟨0, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, map_add _ a b⟩
    | smul r u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      exact ⟨(show ToType ((X.ringCatSheaf.over W).obj.obj (op Z)) from r) • a, map_smul _ _ a⟩
  exact hsub _ hmem

/-- Generating sections of the restriction of `M` to an open `W`, from a family of sections over
`W` whose restrictions generate locally. -/
def generatingSectionsOfLocalSpan (M : X.Modules) (W : X.Opens) {I : Type u} (t : I → Γ(M, W))
    (hloc : ∀ (V : X.Opens) (hVW : V ≤ W) (s : Γ(M, V)) (x : X), x ∈ V →
      ∃ (V' : X.Opens) (hV'V : V' ≤ V), x ∈ V' ∧
        M.presheaf.map (homOfLE hV'V).op s ∈
          Submodule.span Γ(X, V')
            (Set.range fun i ↦ M.presheaf.map (homOfLE (hV'V.trans hVW)).op (t i))) :
    (M.over W).GeneratingSections where
  I := I
  s := fun i ↦ Stacks.SheafOfModules.mkOver (M := M) (V := W) (t i)
  epi := epi_freeHomEquiv_symm_mkOver M W t hloc


variable (F : X.Modules) [F.IsQuasicoherent]
  (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1)) (hN : IsCompatible F N)

include hN in
/-- **The subsheaf cut out by a compatible family of spans of at most `κ` sections is
`κ`-generated.** -/
theorem isCardinalGenerated_sheafSubmodule
    (T : ∀ U : X.affineOpens, Set Γ(F, U.1)) (hTN : ∀ U, N U = Submodule.span Γ(X, U.1) (T U))
    (κ : Cardinal.{u}) (hcard : ∀ U, Cardinal.mk (T U) ≤ κ) :
    SheafOfModules.IsCardinalGenerated.{u, u, u} (compatibleModule F N hN) κ := by
  classical
  have hmemU : ∀ (U : X.affineOpens) (y : ↥(T U)), y.1 ∈ localSections F N U.1 := by
    intro U y
    rw [localSections_eq F N hN U, hTN U]
    exact Submodule.subset_span y.2
  have hloc : ∀ (U : X.affineOpens) (V : X.Opens) (hVU : V ≤ U.1)
      (s : Γ(compatibleModule F N hN, V)) (x : X), x ∈ V →
      ∃ (V' : X.Opens) (hV'V : V' ≤ V), x ∈ V' ∧
        (compatibleModule F N hN).presheaf.map (homOfLE hV'V).op s ∈
          Submodule.span Γ(X, V')
            (Set.range fun y : ↥(T U) ↦ (compatibleModule F N hN).presheaf.map
              (homOfLE (hV'V.trans hVU)).op
              (⟨y.1, hmemU U y⟩ : Γ(compatibleModule F N hN, U.1))) := by
    intro U V hVU s x hxV
    obtain ⟨-, ⟨V', hV'aff, rfl⟩, hxV', hV'V⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V : Set X) from hxV) V.isOpen
    have hle : V' ≤ V := hV'V
    refine ⟨V', hle, hxV', ?_⟩
    have h1 : F.presheaf.map (homOfLE hle).op (show ↥(localSections F N V) from s).1
        ∈ N ⟨V', hV'aff⟩ :=
      (show ↥(localSections F N V) from s).2 ⟨V', hV'aff⟩ hle
    rw [hN U ⟨V', hV'aff⟩ (hle.trans hVU), hTN U,
      span_image_span F (hle.trans hVU) (T U), Set.image_eq_range] at h1
    exact mem_span_range_subtype (localSections F N V') _ _ h1
  exact ⟨{ I := X.affineOpens
           X := fun U ↦ U.1
           coversTop := (Opens.coversTop_iff (↥X) _).mpr
             (IsOpenCover.mk (iSup_affineOpens_eq_top X))
           generators := fun U ↦ generatingSectionsOfLocalSpan (compatibleModule F N hN) U.1
             (fun y : ↥(T U) ↦ (⟨y.1, hmemU U y⟩ : Γ(compatibleModule F N hN, U.1)))
             (hloc U) }, hcard⟩

end Stacks.AlgebraicGeometry.GabberColimit

end
