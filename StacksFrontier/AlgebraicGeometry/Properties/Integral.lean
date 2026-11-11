module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.Irreducible
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral schemes in the sense of the Stacks project

Stacks 01OK calls a scheme integral if it is nonempty and the ring of sections of every nonempty
affine open is a domain, while Mathlib's `AlgebraicGeometry.IsIntegral` asks this for every
nonempty open. This file proves the two notions agree and states Stacks 01ON with the
affine-open condition.

## Main results

* `AlgebraicGeometry.isIntegral_iff_forall_affineOpens`: Mathlib's `IsIntegral` is equivalent to
  the affine-open condition of Stacks 01OK.
* `AlgebraicGeometry.nonempty_and_forall_isDomain_iff_isReduced_and_irreducibleSpace`: a scheme
  satisfies the affine-open condition of Stacks 01OK if and only if it is reduced and
  irreducible (Stacks 01ON).

## References

* [Stacks Project, Tag 01OK](https://stacks.math.columbia.edu/tag/01OK)
* [Stacks Project, Tag 01ON](https://stacks.math.columbia.edu/tag/01ON)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A nonempty affine open of a scheme whose ring of sections is a domain is an integral
scheme. -/
theorem isIntegral_of_isAffineOpen_of_isDomain {X : Scheme.{u}} (U : X.affineOpens)
    (hU : (U : Set X).Nonempty) [IsDomain Γ(X, U)] : IsIntegral (U : X.Opens).toScheme := by
  have : IsAffine (U : X.Opens).toScheme := U.2
  have : Nonempty (U : X.Opens).toScheme := ⟨⟨hU.some, hU.some_mem⟩⟩
  have : IsDomain Γ((U : X.Opens).toScheme, ⊤) :=
    MulEquiv.isDomain Γ(X, U) (U : X.Opens).topIso.commRingCatIsoToRingEquiv.toMulEquiv
  exact isIntegral_of_isAffine_of_isDomain _

/-- Mathlib's `IsIntegral`, which asks every nonempty open to have a domain of sections, is
equivalent to the definition of Stacks 01OK, which asks this only for nonempty affine opens. -/
@[stacks 01OK "Stacks' definition: nonempty, and every nonempty affine open has a domain of \
  sections; equivalent to Mathlib's `IsIntegral`"]
theorem isIntegral_iff_forall_affineOpens (X : Scheme.{u}) :
    IsIntegral X ↔
      Nonempty X ∧ ∀ U : X.affineOpens, (U : Set X).Nonempty → IsDomain Γ(X, U) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun U hU ↦ ?_⟩, fun ⟨_, hdom⟩ ↦ ?_⟩
  · have : Nonempty (U : X.Opens) := ⟨⟨hU.some, hU.some_mem⟩⟩
    infer_instance
  have hint (U : X.affineOpens) (hU : (U : Set X).Nonempty) :
      IsIntegral (U : X.Opens).toScheme :=
    have := hdom U hU
    isIntegral_of_isAffineOpen_of_isDomain U hU
  let V (i : {U : X.affineOpens // (U : Set X).Nonempty}) : X.Opens := i.1
  have hV : IsOpenCover V := .mk <| eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (X.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨x, hxU⟩⟩, hxU⟩
  have : ∀ i, IsReduced ((X.openCoverOfIsOpenCover V hV).X i) := fun i ↦
    have := hint i.1 i.2
    inferInstanceAs (IsReduced (V i).toScheme)
  have : IsReduced X := IsReduced.of_openCover (X := X) (X.openCoverOfIsOpenCover V hV)
  have : IrreducibleSpace X := Scheme.irreducibleSpace_of_forall_isAffineOpen X
    fun U hUa hne ↦
      have := hint ⟨U, hUa⟩ ⟨hne.some.1, hne.some.2⟩
      inferInstanceAs (IrreducibleSpace U.toScheme)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- **Stacks Project, Tag 01ON.** A scheme is integral in the sense of Stacks 01OK, that is,
nonempty with a domain of sections on every nonempty affine open, if and only if it is reduced
and irreducible. -/
@[stacks 01ON]
theorem nonempty_and_forall_isDomain_iff_isReduced_and_irreducibleSpace (X : Scheme.{u}) :
    (Nonempty X ∧ ∀ U : X.affineOpens, (U : Set X).Nonempty → IsDomain Γ(X, U)) ↔
      IsReduced X ∧ IrreducibleSpace X :=
  (isIntegral_iff_forall_affineOpens X).symm.trans
    ((isIntegral_iff_irreducibleSpace_and_isReduced X).trans and_comm)

end AlgebraicGeometry

end
