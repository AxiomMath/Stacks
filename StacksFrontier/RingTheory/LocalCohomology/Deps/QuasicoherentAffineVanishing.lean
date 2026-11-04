module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing

/-!
# Serre vanishing: higher cohomology of a quasi-coherent module on an affine open

The positive-degree cohomology of a quasi-coherent module on an affine open of a scheme
vanishes.

The proof is the dévissage of Stacks 01EW applied to the basis of affine opens and to the
collection of *standard* open covers — finite covers of an affine open `V` by the basic opens of
a family `g : Fin n → Γ(X, V)` generating the unit ideal.  Stacks 01X9 supplies the vanishing of
the positive-degree Čech cohomology for such a cover, and quasi-compactness of an affine open
supplies the cofinality of these covers among all open covers of a member of the basis.

## Main results

* `Stacks.Cohomology.AffineVanishing.cechSurj_liftIndexFamily` — Čech vanishing is insensitive
  to reindexing a family along `ULift`.  This is needed because `Stacks.Cohomology.Basis.OpenCover`
  requires its index type to live in the universe of the space, whereas a standard open cover is
  indexed by `Fin n`.
* `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` — Stacks 01XB.

## Implementation notes

`Stacks.Cohomology.BasisCycles` already has the reindexing along `ULift` in the direction
"vanishing for the lifted family implies vanishing for the family"; what is needed here is the
converse, and at index universes unrelated to the universe of the space, so the cochain calculus
is redone for the other direction.  Everything is componentwise and the two reindexings are
mutually inverse because the intersection selected by a tuple of lifted indices is *literally*
the intersection selected by the underlying tuple.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis Stacks.Cohomology.BasisCycles

universe s t v u

namespace Stacks.Cohomology.AffineVanishing

noncomputable section

/-! ### Reindexing a Čech family along `ULift`, in the direction not already available -/

section Reindex

variable {X : Type u} [TopologicalSpace X] {κ : Type t} (Y : κ → Opens X)
  (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v})

/-- The family `Y` reindexed by a universe-lifted copy of its index type. -/
def liftIndexFamily : ULift.{s} κ → Opens X := fun i => Y i.down

/-- Reindexing the family along `ULift` does not change its union. -/
theorem iSup_liftIndexFamily :
    ⨆ i, (liftIndexFamily.{s} Y) i = ⨆ i, Y i :=
  le_antisymm (iSup_le fun i => le_iSup Y i.down)
    (iSup_le fun i => le_iSup (liftIndexFamily.{s} Y) (ULift.up i))

/-- The intersection selected by a tuple is contained in the one selected by the tuple of lifted
indices; in fact the two are equal. -/
theorem inter_le_liftIndexFamily {m : ℕ} (y : Fin m → κ) :
    inter Y y ≤ inter (liftIndexFamily.{s} Y) fun a => ULift.up (y a) :=
  leOfHom (interLift (liftIndexFamily.{s} Y) fun a => interπ Y y a)

/-- The intersection selected by a tuple of lifted indices is contained in the one selected by
the underlying tuple; in fact the two are equal. -/
theorem liftIndexFamily_inter_le {m : ℕ} (x : Fin m → ULift.{s} κ) :
    inter (liftIndexFamily.{s} Y) x ≤ inter Y fun a => (x a).down :=
  leOfHom (interLift Y fun a => interπ (liftIndexFamily.{s} Y) x a)

variable [HasProducts.{t} AddCommGrpCat.{v}] [HasProducts.{max t s} AddCommGrpCat.{v}]

/-- The components of a Čech cochain, read as components of a cochain for the lifted family. -/
def liftCochainComp {q : ℕ} (c : Cochain Y P q) (x : Fin (q + 1) → ULift.{s} κ) :
    ToType (P.obj (op (inter (liftIndexFamily.{s} Y) x))) :=
  res P (liftIndexFamily_inter_le Y x) (comp Y P c fun a => (x a).down)

/-- The components of a Čech cochain for the lifted family, read as components of a cochain for
the family. -/
def unliftCochainComp {q : ℕ} (c : Cochain (liftIndexFamily.{s} Y) P q)
    (y : Fin (q + 1) → κ) : ToType (P.obj (op (inter Y y))) :=
  res P (inter_le_liftIndexFamily Y y)
    (comp (liftIndexFamily.{s} Y) P c fun a => ULift.up (y a))

/-- A Čech cochain for the family, read as a Čech cochain for the lifted family. -/
def liftCochain {q : ℕ} (c : Cochain Y P q) : Cochain (liftIndexFamily.{s} Y) P q :=
  mk (liftIndexFamily.{s} Y) P (liftCochainComp Y P c)

/-- A Čech cochain for the lifted family, read as a Čech cochain for the family. -/
def unliftCochain {q : ℕ} (c : Cochain (liftIndexFamily.{s} Y) P q) : Cochain Y P q :=
  mk Y P (unliftCochainComp Y P c)

/-- The components of a lifted cochain. -/
@[simp]
theorem comp_liftCochain {q : ℕ} (c : Cochain Y P q) (x : Fin (q + 1) → ULift.{s} κ) :
    comp (liftIndexFamily.{s} Y) P (liftCochain Y P c) x
      = res P (liftIndexFamily_inter_le Y x) (comp Y P c fun a => (x a).down) :=
  comp_mk (liftIndexFamily.{s} Y) P (liftCochainComp Y P c) x

/-- The components of an unlifted cochain. -/
@[simp]
theorem comp_unliftCochain {q : ℕ} (c : Cochain (liftIndexFamily.{s} Y) P q)
    (y : Fin (q + 1) → κ) :
    comp Y P (unliftCochain Y P c) y = res P (inter_le_liftIndexFamily Y y)
      (comp (liftIndexFamily.{s} Y) P c fun a => ULift.up (y a)) :=
  comp_mk Y P (unliftCochainComp Y P c) y

/-- Unlifting kills the zero cochain. -/
theorem unliftCochain_zero {q : ℕ} :
    unliftCochain Y P (0 : Cochain (liftIndexFamily.{s} Y) P q) = 0 := by
  refine cochain_ext Y P _ _ fun y => ?_
  rw [comp_unliftCochain, BasisCycles.comp_zero, BasisCycles.comp_zero, res_zero]

/-- Lifting commutes with the Čech differential. -/
theorem dd_liftCochain {q : ℕ} (c : Cochain Y P q) :
    dd (liftIndexFamily.{s} Y) P (liftCochain Y P c) = liftCochain Y P (dd Y P c) := by
  refine cochain_ext (liftIndexFamily.{s} Y) P _ _ fun x => ?_
  rw [comp_dd, comp_liftCochain, comp_dd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [comp_liftCochain, res_res, res_zsmul, res_res]
  exact congrArg _ (res_comp_congr Y P c rfl _ _)

/-- Unlifting commutes with the Čech differential. -/
theorem dd_unliftCochain {q : ℕ} (c : Cochain (liftIndexFamily.{s} Y) P q) :
    dd Y P (unliftCochain Y P c)
      = unliftCochain Y P (dd (liftIndexFamily.{s} Y) P c) := by
  refine cochain_ext Y P _ _ fun y => ?_
  rw [comp_dd, comp_unliftCochain, comp_dd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [comp_unliftCochain, res_res, res_zsmul, res_res]
  exact congrArg _ (res_comp_congr (liftIndexFamily.{s} Y) P c rfl _ _)

/-- Lifting an unlifted cochain is the identity. -/
theorem liftCochain_unliftCochain {q : ℕ} (c : Cochain (liftIndexFamily.{s} Y) P q) :
    liftCochain Y P (unliftCochain Y P c) = c := by
  refine cochain_ext (liftIndexFamily.{s} Y) P _ _ fun x => ?_
  rw [comp_liftCochain, comp_unliftCochain, res_res,
    res_comp_congr (liftIndexFamily.{s} Y) P c
      (funext fun a => (ULift.up_down (x a)).symm) _
      (le_refl (inter (liftIndexFamily.{s} Y) x)),
    res_id]

/-- **Čech vanishing transfers to the family reindexed along `ULift`.**  The converse direction,
`Stacks.Cohomology.BasisCycles.cechSurj_of_uliftFamily`, is already available. -/
theorem cechSurj_liftIndexFamily (q : ℕ) (h : CechSurj Y P q) :
    CechSurj (liftIndexFamily.{s} Y) P q := by
  intro c hc
  obtain ⟨b, hb⟩ := h (unliftCochain Y P c)
    (by rw [dd_unliftCochain, hc, unliftCochain_zero])
  exact ⟨liftCochain Y P b, by rw [dd_liftCochain, hb, liftCochain_unliftCochain]⟩

/-- **Čech cohomology is insensitive to reindexing along `ULift`.**  If the positive-degree Čech
cohomology of `P` for the family `Y` vanishes, so does that for the lifted family. -/
theorem isZero_homology_liftIndexFamily (q : ℕ)
    (h : IsZero (((cechComplexFunctor Y).obj P).homology (q + 1))) :
    IsZero (((cechComplexFunctor (liftIndexFamily.{s} Y)).obj P).homology (q + 1)) :=
  (cechSurj_iff_isZero_homology (liftIndexFamily.{s} Y) P q).1
    (cechSurj_liftIndexFamily Y P q ((cechSurj_iff_isZero_homology Y P q).2 h))

end Reindex

/-! ### Serre vanishing on an affine open -/

section AffineOpen

variable {X : Scheme.{u}}

/-- The infimum of a family indexed by `Fin (m + 2)` splits off its first member. -/
theorem iInf_fin_succ_eq {m : ℕ} (A : Fin (m + 2) → Opens ↥X) :
    (⨅ k, A k) = A 0 ⊓ ⨅ k : Fin (m + 1), A k.succ := by
  refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le_of_le j.succ le_rfl)) ?_
  refine le_iInf fun k => ?_
  refine Fin.cases inf_le_left (fun j => inf_le_right.trans (iInf_le _ j)) k

/-- The standard open cover of an affine open `U` attached to a family `g` of sections over `U`
whose basic opens cover `Spec Γ(X, U)`, with its index type lifted to the universe of the space
as `Stacks.Cohomology.Basis.OpenCover` requires. -/
def standardOpenCover (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) : OpenCover ↥X where
  ι := ULift.{u} (Fin n)
  carrier := U
  obj := liftIndexFamily.{u} fun i => X.basicOpen (g i)
  iSup_eq := by
    rw [iSup_liftIndexFamily]
    have hspan : Ideal.span (Set.range g) = ⊤ :=
      Stacks.Cohomology.Cech.span_range_eq_top_of_isStandardOpenCoverOfSpectrum hg
    simpa only [iSup_range'] using
      (hU.iSup_basicOpen_eq_self_iff (s := Set.range g)).mpr hspan

-- Stacks 01XB is `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`
-- (StacksFrontier/AlgebraicGeometry/Cohomology/Cech/AffineVanishing.lean:304).  This is an alias spelling of that
-- declaration, not a second copy of it.
export Stacks.Cohomology.Cech (isZero_hgroup_of_isAffineOpen)

end AffineOpen

end

end Stacks.Cohomology.AffineVanishing
