module

public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Semicontinuity of the fibre rank

Let `F` be a sheaf of modules of finite type on a scheme `X` all of whose stalks are free. Its
fibre rank is then the rank of the stalk, and this file proves the two regularity properties of
that function which turn a topological hypothesis on `X` into local freeness of `F`:

* the fibre rank is **upper semicontinuous**: every `{x | fiberRank F x ≤ n}` is open. A basis of
  the stalk at `x` is realised by sections near `x`, and finiteness of type makes their germs
  generate every nearby stalk, so no nearby stalk needs more generators than the stalk at `x`;
* the fibre rank is **constant along specializations**, when `F` is in addition quasi-coherent:
  the stalk at a generalization is a localization of the stalk, by
  `Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes`, and a basis
  localizes to a basis.

Together these say that each `{x | n ≤ fiberRank F x}` is closed and stable under generalization,
so on a scheme where every such subset is open the fibre rank is locally constant. The support of
`F` is also read off the fibre rank, which makes it open as soon as `F` is finite locally free.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isOpen_setOf_fiberRank_le`: upper semicontinuity.
* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_specializes`: the fibre rank of a
  quasi-coherent module of finite type with free stalks is constant along specializations.
* `AlgebraicGeometry.Scheme.Modules.mem_supp_iff_fiberRank_ne_zero`: a point lies in the support
  exactly when the fibre rank there is nonzero.
* `AlgebraicGeometry.Scheme.Modules.isOpen_supp_of_isFiniteLocallyFree`: the support of a finite
  locally free module is open.
* `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_fiberRank_of_forall_isOpen`: on a scheme
  whose generalization-stable closed subsets are all open, the fibre rank of a quasi-coherent
  module of finite type with free stalks is locally constant.

## Implementation notes

Instance search cannot produce the module structure of a stalk over the local ring of the scheme
(`AlgebraicGeometry.Scheme.Modules.presheaf` does not unfold at instance-reducible
transparency), so every statement carries it in a `letI` binder, exactly as
`AlgebraicGeometry.Scheme.Modules.fiberRank` itself does. In the proof of
`fiberRank_eq_of_specializes` the three structures involved are the *named* definitions
`Stacks.ModuleStalkSpecialization.stalkModule` and `stalkSpecializesModule`, since the
localization statement is stated against those and matching them is what lets instance search
find the `IsLocalizedModule` hypothesis.

Equalities between fibre ranks are chained with `Eq.trans` rather than rewritten: the two
spellings of a stalk's module structure are definitionally but not syntactically equal, so
`rw` cannot build a motive over them while `exact` compares at default transparency.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 053N](https://stacks.math.columbia.edu/tag/053N)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Semicontinuity

/-- A module spanned by a finite family has rank at most the cardinality of that family: taking
combinations of the family is a surjection from the free module on it. -/
private theorem finrank_le_card_of_top_le_span {A : Type*} [CommRing A] [Nontrivial A]
    {M : Type*} [AddCommGroup M] [Module A M] {I : Type*} [Fintype I] (f : I → M)
    (h : ⊤ ≤ Submodule.span A (Set.range f)) :
    Module.finrank A M ≤ Fintype.card I := by
  have hsurj : Function.Surjective (Finsupp.linearCombination A f) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp h
  calc Module.finrank A M ≤ Module.finrank A (I →₀ A) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Fintype.card I := Module.finrank_eq_card_basis (Finsupp.basisSingleOne (ι := I) (R := A))

/-- **The fibre rank does not increase near a point.** For a module of finite type with free
stalks there is a neighbourhood of `x` on which the fibre rank is at most its value at `x`.

A basis of the stalk at `x` is realised by sections on a neighbourhood; because the module is of
finite type their germs still generate every stalk on a smaller neighbourhood, and a module
spanned by that many elements has rank at most that many. -/
theorem exists_isOpen_forall_fiberRank_le {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, fiberRank F y ≤ fiberRank F x := by
  classical
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M := hfree x
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let : IsLocalRing A := X.isLocalRing x
  let I := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis I A M := Module.Free.chooseBasis A M
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite _
  have hcardx : fiberRank F x = Fintype.card I :=
    (fiberRank_eq_finrank_stalk F x (hfree x)).trans (Module.finrank_eq_card_basis b)
  obtain ⟨U, -, hxU, s, hs⟩ :=
    finite_germ_lifts F.val.presheaf x (fun i => (b i : M))
      (V := (⊤ : X.Opens)) (Set.mem_univ x)
  have hspanx : ⊤ ≤ Submodule.span A
      (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
    rw [congrArg Set.range (funext hs)]
    exact b.span_eq.ge
  obtain ⟨W, hWU, hxW, hspanW⟩ := span_germs_near F s x hxU hspanx
  refine ⟨W, hxW, fun y hyW => ?_⟩
  let : Module (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  let : IsLocalRing (ToType (X.presheaf.stalk y)) := X.isLocalRing y
  calc fiberRank F y = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      fiberRank_eq_finrank_stalk F y (hfree y)
    _ ≤ Fintype.card I := finrank_le_card_of_top_le_span _ (hspanW y hyW)
    _ = fiberRank F x := hcardx.symm

/-- **Upper semicontinuity of the fibre rank.** For a module of finite type with free stalks the
locus where the fibre rank is at most `n` is open. -/
theorem isOpen_setOf_fiberRank_le {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (n : ℕ) :
    IsOpen {x : X | fiberRank F x ≤ n} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨U, hxU, hU⟩ := exists_isOpen_forall_fiberRank_le F hfree x
  exact ⟨(U : Set X), fun y hy => (hU y hy).trans hx, U.isOpen, hxU⟩

end Semicontinuity

section Specialization

/-- **The fibre rank is constant along specializations.** Let `F` be a quasi-coherent module of
finite type on a scheme with free stalks and let `y ⤳ x`. Then `F` has the same fibre rank at `y`
as at `x`.

The stalk at the generalization `y` is the localization of the stalk at `x` at a prime of the
local ring at `x`, so a basis of the stalk at `x` localizes to a basis of the stalk at `y`
indexed by the same type. -/
theorem fiberRank_eq_of_specializes {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    {x y : X} (h : y ⤳ x) :
    fiberRank F y = fiberRank F x := by
  classical
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkModule F y
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  let : IsLocalRing (ToType (X.presheaf.stalk x)) := X.isLocalRing x
  let : IsLocalRing (ToType (X.presheaf.stalk y)) := X.isLocalRing y
  have hring : IsLocalization.AtPrime (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
  have htower : IsScalarTower (ToType (X.presheaf.stalk x)) (ToType (X.presheaf.stalk y))
      (ToType (F.presheaf.stalk y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hloc := Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F h
  let : Module.Free (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x)) := hfree x
  let : Module.Finite (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x)) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  let I := Module.Free.ChooseBasisIndex (ToType (X.presheaf.stalk x))
    (ToType (F.presheaf.stalk x))
  let b := Module.Free.chooseBasis (ToType (X.presheaf.stalk x)) (ToType (F.presheaf.stalk x))
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite _
  have hx : fiberRank F x = Fintype.card I :=
    (fiberRank_eq_finrank_stalk F x (hfree x)).trans (Module.finrank_eq_card_basis b)
  have hy : fiberRank F y = Fintype.card I :=
    (fiberRank_eq_finrank_stalk F y (hfree y)).trans
      (Module.finrank_eq_card_basis
        (b.ofIsLocalizedModule (ToType (X.presheaf.stalk y))
          ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under
            (X.presheaf.stalk x)).primeCompl
          (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h)))
  exact hy.trans hx.symm

end Specialization

section Support

/-- **The support is the locus of nonzero fibre rank.** For a module of finite type whose stalk at
`x` is free, `x` lies in the support exactly when the fibre rank there is nonzero: the stalk is
nonzero exactly when a basis of it is indexed by a nonempty type. -/
theorem mem_supp_iff_fiberRank_ne_zero {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType] (x : X)
    (hfree :
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    x ∈ SheafOfModules.supp F ↔ fiberRank F x ≠ 0 := by
  classical
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M := hfree
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let : IsLocalRing A := X.isLocalRing x
  let I := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis I A M := Module.Free.chooseBasis A M
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite _
  have hrank : fiberRank F x = Fintype.card I :=
    (fiberRank_eq_finrank_stalk F x hfree).trans (Module.finrank_eq_card_basis b)
  have hsupp : x ∈ SheafOfModules.supp F ↔ Nonempty I := by
    rw [SheafOfModules.mem_supp_iff_nontrivial_stalk F x]
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · have : Nontrivial M := hne
      exact b.index_nonempty
    · obtain ⟨i⟩ := hne
      exact nontrivial_of_ne (b i) 0 (b.ne_zero i)
  rw [hsupp, hrank]
  exact Fintype.card_pos_iff.symm.trans Nat.pos_iff_ne_zero

/-- **The support of a finite locally free module is open.** Its fibre rank is locally constant,
and the support is the locus where that rank is nonzero. -/
theorem isOpen_supp_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F) :
    IsOpen (SheafOfModules.supp F) := by
  have hbridge := Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F (hM := hF)
  obtain ⟨hft, hfree, hconst⟩ :=
    isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank F
  have := hft
  have hset : SheafOfModules.supp F = fiberRank F ⁻¹' {n : ℕ | n ≠ 0} :=
    Set.ext fun z => mem_supp_iff_fiberRank_ne_zero F z (hfree z)
  rw [hset]
  exact hconst _

end Support

section LocallyConstant

/-- **A topological hypothesis makes the fibre rank locally constant.** On a scheme in which every
closed subset stable under generalization is open, the fibre rank of a quasi-coherent module of
finite type with free stalks is locally constant.

Each locus `{x | n ≤ fiberRank F x}` is the complement of an open set by upper semicontinuity,
hence closed, and it is stable under generalization because the fibre rank does not change along
a specialization; so the hypothesis makes it open, and the locus where the fibre rank equals its
value at a given point is the intersection of two open sets. -/
theorem isLocallyConstant_fiberRank_of_forall_isOpen {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (h : ∀ Z : Set X, IsClosed Z → StableUnderGeneralization Z → IsOpen Z) :
    IsLocallyConstant (fiberRank F) := by
  have hle : ∀ n : ℕ, IsOpen {z : X | fiberRank F z ≤ n} := isOpen_setOf_fiberRank_le F hfree
  have hge : ∀ n : ℕ, IsOpen {z : X | n ≤ fiberRank F z} := by
    rintro (_ | m)
    · simp
    refine h _ ?_ fun a b hba hb => hb.trans_eq (fiberRank_eq_of_specializes F hfree hba).symm
    have he : {z : X | m + 1 ≤ fiberRank F z} = ({z : X | fiberRank F z ≤ m}ᶜ : Set X) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      omega
    rw [he, isClosed_compl_iff]
    exact hle m
  exact (IsLocallyConstant.iff_exists_open _).mpr fun x =>
    ⟨{z : X | fiberRank F x ≤ fiberRank F z} ∩ {z : X | fiberRank F z ≤ fiberRank F x},
      (hge _).inter (hle _), ⟨le_refl (fiberRank F x), le_refl (fiberRank F x)⟩,
      fun y hy => le_antisymm hy.2 hy.1⟩

end LocallyConstant

end AlgebraicGeometry.Scheme.Modules

end
