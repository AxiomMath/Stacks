module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# Finitely generated sections over an affine open, from finite type on a quasi-compact open

Let `M` be a quasi-coherent module on a scheme `X`, let `U` be an affine open and let `V ≤ U` be
a quasi-compact open on which `M` is of finite type. This file produces a finitely generated
`Γ(X, U)`-submodule `N'` of `Γ(M, U)` and a finite family `a` of elements of `Γ(X, U)` whose basic
opens cover `V` and lie inside it, such that a power of each `a i` carries every section of `M`
over `U` into `N'`. This is the algebraic content of the affine case of
[Stacks Project, Tag 01PF], over an affine open of an arbitrary scheme.

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isFiniteType_restrict_of_le`: finite type on an
  open is inherited by a smaller open.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_finite_basicOpen_cover`: a quasi-compact
  open inside an affine open is covered by finitely many basic opens of that affine open, all
  contained in it.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.module_finite_sections_of_isFiniteType_restrict`:
  if the restriction of a quasi-coherent module to an affine open is of finite type, its sections
  there are a finite module over the sections of the structure sheaf.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_fg_submodule_pow_smul_mem`: for a finite
  family of basic opens on each of which `M` is of finite type, the sections over `U` contain a
  finitely generated submodule into which a power of each `a i` carries every section.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_finite_basicOpen_cover_and_fg_submodule`:
  the three combined, for a quasi-compact open `V ≤ U`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

/-- Finite type of a restriction is inherited by a further restriction along a morphism. -/
private theorem isFiniteType_restrict_comp {X Y Z : Scheme.{u}} (M : X.Modules) (f : Y ⟶ Z)
    (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] (hft : (M.restrict g).IsFiniteType) :
    (M.restrict (f ≫ g)).IsFiniteType := by
  have : ((Scheme.Modules.restrictFunctor g ⋙
      Scheme.Modules.restrictFunctor f).obj M).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict f _
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.restrictFunctorComp f g).app M).symm

/-- Finite type on an open is inherited by a smaller open. -/
theorem isFiniteType_restrict_of_le {X : Scheme.{u}} (M : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (hft : (M.restrict V.ι).IsFiniteType) : (M.restrict W.ι).IsFiniteType := by
  have := isFiniteType_restrict_comp M (X.homOfLE h) V.ι hft
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)

/-- A quasi-compact open inside an affine open is covered by finitely many basic opens of that
affine open, each contained in it. -/
theorem exists_finite_basicOpen_cover {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hVU : V ≤ U) (hV : IsCompact V.1) :
    ∃ (ι : Type u) (_ : Finite ι) (a : ι → Γ(X, U)),
      (∀ i, X.basicOpen (a i) ≤ V) ∧ V ≤ ⨆ i, X.basicOpen (a i) := by
  classical
  choose g hg1 hg2 using fun x : V => hU.exists_basicOpen_le x (hVU x.2)
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V => (X.basicOpen (g x)).1)
    (fun x => (X.basicOpen (g x)).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hg2 ⟨x, hx⟩⟩)
  refine ⟨{x : V // x ∈ s}, inferInstance, fun i => g i.1, fun i => hg1 i.1, ?_⟩
  intro x hx
  obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hmem⟩

/-- If the restriction of a quasi-coherent
module to an affine open is of finite type, then its sections over that open form a finite module
over the sections of the structure sheaf. -/
theorem module_finite_sections_of_isFiniteType_restrict
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (h : (M.restrict U.ι).IsFiniteType) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have h3 : (M.restrict hU.fromSpec).IsFiniteType := isFiniteType_restrict_comp M _ U.ι h
  have hQC : (M.restrict hU.fromSpec).IsQuasicoherent := inferInstance
  have hfin : Module.Finite Γ(X, U)
      (AlgebraicGeometry.moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) := by
    refine (AlgebraicGeometry.tilde_isFiniteType_iff _).1 ?_
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso (M.restrict hU.fromSpec).fromTildeΓ).symm
  have hfin' : Module.Finite Γ(X, U)
      Γ(M.restrict hU.fromSpec, (⊤ : (Spec Γ(X, U)).Opens)) := hfin
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  exact Module.Finite.equiv
    ((restrictSectionsEquiv M hU ⊤).trans
      (sectionsCongrSelf M hTop (fromSpec_image_le hU ⊤)))

/-- Given a finite family `a` of elements of `Γ(X, U)`, `U` affine, on each of whose basic opens
the quasi-coherent module `M` is of finite type, the sections of `M` over `U` contain a finitely
generated submodule into which a power of each `a i` carries every section. -/
theorem exists_fg_submodule_pow_smul_mem
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {ι : Type*} [Finite ι] (a : ι → Γ(X, U))
    (hft : ∀ i, (M.restrict (X.basicOpen (a i)).ι).IsFiniteType) :
    ∃ N' : Submodule Γ(X, U) Γ(M, U), N'.FG ∧
      ∀ (i : ι) (x : Γ(M, U)), ∃ k : ℕ, a i ^ k • x ∈ N' := by
  classical
  have key : ∀ i, ∃ T : Finset Γ(M, U),
      Submodule.span Γ(X, X.basicOpen (a i))
        ((restrictₗ M (X.basicOpen_le (a i))) '' (T : Set Γ(M, U))) = ⊤ ∧
      ∀ x : Γ(M, U), ∃ k : ℕ, a i ^ k • x ∈ Submodule.span Γ(X, U) (T : Set Γ(M, U)) := by
    intro i
    let := algebraOfLE X (X.basicOpen_le (a i))
    let := moduleOfLE M (X.basicOpen_le (a i))
    have := isScalarTowerOfLE M (X.basicOpen_le (a i))
    have : IsLocalization.Away (a i) Γ(X, X.basicOpen (a i)) :=
      hU.isLocalization_basicOpen (a i)
    have : IsLocalizedModule (Submonoid.powers (a i))
        (restrictₗ M (X.basicOpen_le (a i))) :=
      isLocalizedModule_restrictₗ M hU (a i) rfl (X.basicOpen_le (a i))
    obtain ⟨T, hT⟩ := exists_finset_span_image_eq_top (a i) _ _
      (restrictₗ M (X.basicOpen_le (a i)))
      (module_finite_sections_of_isFiniteType_restrict M (hU.basicOpen (a i)) (hft i))
    exact ⟨T, hT, exists_pow_smul_mem_span_of_span_image_eq_top (a i)
      Γ(X, X.basicOpen (a i)) (restrictₗ M (X.basicOpen_le (a i))) hT⟩
  choose T hT hk using key
  refine ⟨Submodule.span Γ(X, U) (⋃ i, (T i : Set Γ(M, U))),
    Submodule.fg_span (Set.finite_iUnion fun i => (T i).finite_toSet), fun i x => ?_⟩
  obtain ⟨k, hk⟩ := hk i x
  exact ⟨k, Submodule.span_mono (Set.subset_iUnion _ i) hk⟩

/-- For a quasi-coherent module `M` on a scheme `X`, an affine open `U` and a quasi-compact open
`V ≤ U` on which `M` is of finite type, there is a finite family `a` of elements of `Γ(X, U)` whose
basic opens lie in `V` and cover it, together with a finitely generated submodule `N'` of
`Γ(M, U)` into which a power of each `a i` carries every section of `M` over `U`. -/
theorem exists_finite_basicOpen_cover_and_fg_submodule
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hVU : V ≤ U) (hV : IsCompact V.1)
    (hft : (M.restrict V.ι).IsFiniteType) :
    ∃ (ι : Type u) (_ : Finite ι) (a : ι → Γ(X, U)) (N' : Submodule Γ(X, U) Γ(M, U)),
      (∀ i, X.basicOpen (a i) ≤ V) ∧ (V ≤ ⨆ i, X.basicOpen (a i)) ∧ N'.FG ∧
        ∀ (i : ι) (x : Γ(M, U)), ∃ k : ℕ, a i ^ k • x ∈ N' := by
  obtain ⟨ι, hι, a, hle, hcover⟩ := exists_finite_basicOpen_cover hU hVU hV
  obtain ⟨N', hfg, hpow⟩ := exists_fg_submodule_pow_smul_mem M hU a
    fun i => isFiniteType_restrict_of_le M (hle i) hft
  exact ⟨ι, hι, a, N', hle, hcover, hfg, hpow⟩

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
