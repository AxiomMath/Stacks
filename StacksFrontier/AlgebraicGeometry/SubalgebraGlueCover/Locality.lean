module

public import StacksFrontier.AlgebraicGeometry.SubalgebraGlueCover.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Locality

/-!
# Finite type of a quasi-coherent algebra sheaf is local on the base, and the glue is of
finite type

For a quasi-coherent algebra sheaf, finite type of the structural ring map over every affine open
of `X` can be checked on basic opens covering an affine open, and hence on the members of any
family of affine opens covering `X`. Consequently the glue of pieces of finite type is of finite
type.

## Main results

* `finiteType_app_of_span`: for a quasi-coherent algebra sheaf, if the structural ring map over an
  affine open `U` is of finite type over each basic open `D(f)`, `f` in a set spanning `Γ(X, U)`,
  then it is of finite type over `U`.
* `isFiniteType_of_iSup_eq_top`: finite type of a quasi-coherent algebra sheaf follows from finite
  type over the members of a family of affine opens covering `X`.
* `isFiniteType_glue`: the glue of pieces of finite type is of finite type, given that the glue is
  quasi-coherent and that the covering family admits a refinement by affine opens, each inside a
  member.
* `isFiniteType_glue_of_pieces`: the glue of quasi-coherent pieces of finite type is
  quasi-coherent and of finite type.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-! ### Finite type of a quasi-coherent algebra sheaf is local on the base -/

/-- For a quasi-coherent algebra sheaf, if the structural ring map over an affine open `U` is of
finite type over each basic open `D(f)`, `f` in a set spanning `Γ(X, U)`, then it is of finite type
over `U`. -/
theorem finiteType_app_of_span (A : AlgebraSheaf X) [A.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤)
    (hft : ∀ f : s, RingHom.FiniteType (A.hom.hom.app (op (X.basicOpen f.1))).hom) :
    RingHom.FiniteType (A.hom.hom.app (op U)).hom := by
  refine RingHom.OfLocalizationSpan.ofIsLocalization
    RingHom.finiteType_isLocal.ofLocalizationSpan
    RingHom.finiteType_respectsIso _ s hs fun f ↦ ?_
  refine ⟨Γ(X, X.basicOpen f.1), sections A (X.basicOpen f.1), inferInstance,
    inferInstance, algebraOfLE X (X.basicOpen_le f.1),
    algebraRestrict A (X.basicOpen_le f.1), hU.isLocalization_basicOpen f.1,
    Stacks.FPAlgebraSheaf.isLocalization_away_sections A hU f.1,
    (A.hom.hom.app (op (X.basicOpen f.1))).hom, ?_, hft f⟩
  ext x
  exact congr($(presheaf_map_comp_app A (X.basicOpen_le f.1)).hom x)

/-- A quasi-coherent algebra sheaf whose structural ring map is of finite type over the members
of a family of affine opens covering `X` is of finite type. -/
theorem isFiniteType_of_iSup_eq_top (A : AlgebraSheaf X) [A.IsQuasicoherent] {ι : Type*}
    (W : ι → X.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hcov : ⨆ i, W i = ⊤)
    (hft : ∀ i, RingHom.FiniteType (A.hom.hom.app (op (W i))).hom) :
    A.IsFiniteType := by
  intro V hV
  have hspan : Ideal.span {f : Γ(X, V) | ∃ i, X.basicOpen f ≤ W i} = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f ↦ X.basicOpen_le f.1) fun x hx ↦ ?_
    obtain ⟨i, hxi⟩ : ∃ i, x ∈ W i := Opens.mem_iSup.mp (hcov ▸ trivial)
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W i) ⟨x, hxi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨f, i, hfW⟩, hxf⟩
  refine finiteType_app_of_span A hV _ hspan fun f ↦ ?_
  obtain ⟨i, hfW⟩ := f.2
  exact Stacks.QcohAlgebraFPColimit.finiteType_app_of_le A
    (hV.basicOpen f.1) (hW i) hfW (hft i)

/-! ### The glue of pieces of finite type is of finite type -/

section Glue

variable {A : AlgebraSheaf X} {ι : Type*} (W : ι → X.Opens) (C : ι → Subalg A)

/-- The glue of pieces agreeing over the overlaps is of finite type, provided the glue is
quasi-coherent and the covering family admits a refinement by affine opens `V i`, each inside
some member `W j` over which the corresponding piece is of finite type. -/
theorem isFiniteType_glue (hagree : Agree W C)
    [(Subalg.toAlgebraSheaf (glue W C)).IsQuasicoherent] {I : Type*} (V : I → X.Opens)
    (hVaff : ∀ i, IsAffineOpen (V i)) (hVcov : ⨆ i, V i = ⊤)
    (hft : ∀ i : I, ∃ j : ι, V i ≤ W j ∧
      RingHom.FiniteType ((Subalg.toAlgebraSheaf (C j)).hom.hom.app (op (V i))).hom) :
    (Subalg.toAlgebraSheaf (glue W C)).IsFiniteType := by
  refine isFiniteType_of_iSup_eq_top _ V hVaff hVcov fun i ↦ ?_
  obtain ⟨j, hVW, hj⟩ := hft i
  exact finiteType_app_glue_of_le W C hagree hVW hj

/-- The case of two members: the glue of two subalgebras of finite type agreeing over the overlap
of their opens is of finite type, provided the glue is quasi-coherent and the pair admits an
affine refinement as in `isFiniteType_glue`. -/
theorem isFiniteType_glue_pair (W : Bool → X.Opens) (C : Bool → Subalg A)
    (h : ∀ V : X.Opens, V ≤ W false → V ≤ W true → (C false).obj V = (C true).obj V)
    [(Subalg.toAlgebraSheaf (glue W C)).IsQuasicoherent] {I : Type*} (V : I → X.Opens)
    (hVaff : ∀ i, IsAffineOpen (V i)) (hVcov : ⨆ i, V i = ⊤)
    (hft : ∀ i : I, ∃ j : Bool, V i ≤ W j ∧
      RingHom.FiniteType ((Subalg.toAlgebraSheaf (C j)).hom.hom.app (op (V i))).hom) :
    (Subalg.toAlgebraSheaf (glue W C)).IsFiniteType :=
  isFiniteType_glue W C (agree_pair W C h) V hVaff hVcov hft

/-- The glue of quasi-coherent pieces agreeing over the overlaps, with an affine refinement of the
covering family over which the pieces are of finite type, is quasi-coherent and of finite type. -/
theorem isFiniteType_glue_of_pieces (hagree : Agree W C) {I : Type u} (V : I → X.Opens)
    (hVcov : IsOpenCover V) (hVaff : ∀ i, IsAffineOpen (V i)) (hVW : ∀ i, ∃ j, V i ≤ W j)
    (hC : ∀ j, (Subalg.toAlgebraSheaf (C j)).IsQuasicoherent)
    (hft : ∀ i : I, ∃ j : ι, V i ≤ W j ∧
      RingHom.FiniteType ((Subalg.toAlgebraSheaf (C j)).hom.hom.app (op (V i))).hom) :
    (Subalg.toAlgebraSheaf (glue W C)).IsQuasicoherent ∧
      (Subalg.toAlgebraSheaf (glue W C)).IsFiniteType := by
  have hqc := isQuasicoherent_glue W C hagree V hVcov hVaff hVW hC
  exact ⟨hqc, isFiniteType_glue W C hagree V hVaff hVcov.iSup_eq_top hft⟩

end Glue

end Stacks.RelativeSpec.AlgebraSheaf

end
