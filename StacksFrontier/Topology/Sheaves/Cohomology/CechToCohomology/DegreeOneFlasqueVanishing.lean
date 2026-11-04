module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree-one Čech vanishing for flasque and injective sheaves of abelian groups

Tag 09SZ gives the vanishing of positive-degree Čech cohomology of a flasque sheaf of abelian
groups, and tag 01EP the same for an injective sheaf of modules.  Both are stated for a cover
whose index type lies in the *same* universe as the sheaf's values: the Čech complex of
`Stacks.Cohomology.FlasqueCech` is assembled from products indexed by tuples of indices, and a
product of groups in `Type v` indexed by a type in `Type w` only lands in `Type v` when `w ≤ v`.

The degree-one statement, however, needs no such restriction, and the consumers in tag 01EQ
quantify over an index type in an unrelated universe.  This file removes the restriction, in
the hand-rolled cochain language of tag 01FJ (`CechCochains.Cochain`, `CechCochains.cechD`), by
`ULift`ing the sheaf's values into a universe large enough to contain the index type: the
cover index type is then replaced by `ULift I`, which *does* lie in that universe, and the
round trip `ULift.down ∘ ULift.up` is the identity on the nose, so no cocycle correction term
is needed.

## Main results

* `Stacks.Cohomology.CechOne.exists_cechD_eq_of_isFlasque`: a Čech `1`-cocycle for a flasque
  sheaf of abelian groups is a coboundary, for an arbitrary family of opens indexed by an
  arbitrary type.
* `Stacks.Cohomology.CechOne.exists_cechD_eq_of_injective`: the same for an injective sheaf of
  abelian groups.
* `Stacks.Cohomology.CechOne.isFlasque_of_injective`: an injective sheaf of abelian groups is
  flasque, with the space's universe independent of the sheaf's.
* `Stacks.Cohomology.CechOne.uliftSheaf`: a sheaf of abelian groups with its values `ULift`ed,
  together with `uliftSheaf_isFlasque` transporting flasqueness.

## Implementation notes

All element-level manipulation is phrased on the plain presheaf `uliftPresheaf F` rather than on
`(uliftSheaf F).presheaf`.  The two are equal by `rfl` (`uliftSheaf_presheaf`), but
`TopCat.Sheaf` is a semireducible `def` wrapping
`CategoryTheory.Sheaf (Opens.grothendieckTopology X)`, and `rw` builds its motive at
`instances` transparency, so a term mentioning the *sheaf* blocks
rewriting.  For the same reason the solution produced by `exists_sum_res_eq` is restated at
`uliftPresheaf F` before use, and the steps that would need a motive across that boundary are
done in term mode, where checking happens at default transparency.

## References

* [Stacks, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sum res_zsmul)
open Stacks.Cohomology.CechSheaf (inter_le_reindex exists_sum_res_eq)
open Stacks.CategoryTheory.CechComplex (inter inter_eq_iInf)

universe uX v w

namespace Stacks.Cohomology.CechOne

variable {X : TopCat.{uX}}

/-! ### `ULift`ing the values of a sheaf of abelian groups -/

/-- The presheaf of `ULift`ed sections of a sheaf of abelian groups. -/
noncomputable abbrev uliftPresheaf (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max v w} :=
  F.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w, v}

/-- A sheaf of abelian groups, with its values `ULift`ed to a larger universe.  `ULift` on
`AddCommGrpCat` preserves limits, hence sheaves. -/
noncomputable def uliftSheaf (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    TopCat.Sheaf AddCommGrpCat.{max v w} X :=
  (sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{w, v}).obj F

/-- The underlying presheaf of `uliftSheaf F` is `uliftPresheaf F`. -/
theorem uliftSheaf_presheaf (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    (uliftSheaf.{uX, v, w} F).presheaf = uliftPresheaf.{uX, v, w} F := rfl

/-- `ULift`ing the values preserves flasqueness: a surjection of groups stays surjective. -/
instance uliftSheaf_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{v} X) [F.IsFlasque] :
    (uliftSheaf.{uX, v, w} F).IsFlasque := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (TopCat.Presheaf.IsFlasque.epi (F := F.presheaf) i) y.down
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- Restriction of a `ULift`ed section is the `ULift` of the restriction. -/
theorem res_uliftPresheaf (F : TopCat.Sheaf AddCommGrpCat.{v} X) {V W : Opens X} (h : V ≤ W)
    (s : ToType (F.presheaf.obj (op W))) :
    res (uliftPresheaf.{uX, v, w} F) h (ULift.up s) = ULift.up (res F.presheaf h s) := rfl

/-- Restriction of a `ULift`ed section, read downstairs. -/
theorem res_uliftPresheaf_down (F : TopCat.Sheaf AddCommGrpCat.{v} X) {V W : Opens X}
    (h : V ≤ W) (t : ToType ((uliftPresheaf.{uX, v, w} F).obj (op W))) :
    res F.presheaf h t.down = (res (uliftPresheaf.{uX, v, w} F) h t).down := rfl

/-- `ULift.down` on `ULift`ed sections, as an additive equivalence. -/
noncomputable def downEquiv (F : TopCat.Sheaf AddCommGrpCat.{v} X) (V : Opens X) :
    ToType ((uliftPresheaf.{uX, v, w} F).obj (op V)) ≃+ ToType (F.presheaf.obj (op V)) :=
  AddEquiv.ulift

/-- `downEquiv F V` sends a `ULift`ed section `t` to `t.down`. -/
@[simp] theorem downEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{v} X) (V : Opens X)
    (t : ToType ((uliftPresheaf.{uX, v, w} F).obj (op V))) :
    downEquiv.{uX, v, w} F V t = t.down := rfl

/-- The inverse of `downEquiv F V` sends a section `t` to `ULift.up t`. -/
@[simp] theorem downEquiv_symm_apply (F : TopCat.Sheaf AddCommGrpCat.{v} X) (V : Opens X)
    (t : ToType (F.presheaf.obj (op V))) :
    (downEquiv.{uX, v, w} F V).symm t = ULift.up t := rfl

/-! ### Matching the two Čech languages -/

/-- `CechCochains.restr` is `Stacks.Cohomology.Basis.res`. -/
theorem restr_eq_res (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) {V W : Opens X} (h : W ≤ V)
    (s : ToType (P.obj (op V))) : CechCochains.restr P h s = res P h s := rfl

/-- The product-style intersection of the Čech machinery, taken over a `ULift`ed tuple, is the
lattice-theoretic intersection of tag 01FJ taken over the underlying tuple. -/
theorem inter_ulift {I : Type w} (Ui : I → Opens X) {m : ℕ} (y : Fin m → ULift.{v} I) :
    inter (fun k : ULift.{v} I => Ui k.down) y = CechCochains.inter Ui (fun a => (y a).down) := by
  rw [inter_eq_iInf]
  rfl

/-! ### The vanishing -/

/-- The Čech `1`-cocycle condition, transported to the `ULift`ed index type and sheaf. -/
theorem sum_res_uliftPresheaf_eq_zero {I : Type w} (Ui : I → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (z : CechCochains.Cochain Ui F.presheaf 1)
    (hz : CechCochains.cechD Ui F.presheaf 1 z = 0) (x : Fin 3 → ULift.{v} I) :
    ∑ a : Fin 3, (-1 : ℤ) ^ (a : ℕ) •
      res (uliftPresheaf.{uX, v, w} F) (inter_le_reindex (fun k => Ui k.down) x a.succAbove)
        (res (uliftPresheaf.{uX, v, w} F) (le_of_eq (inter_ulift Ui (x ∘ a.succAbove)))
          (ULift.up (z (fun b => ((x ∘ a.succAbove) b).down)))) = 0 := by
  have hz' := congrFun hz (fun a => (x a).down)
  rw [CechCochains.cechD_apply, CechCochains.Cochain.zero_apply] at hz'
  have h0 := congrArg (res F.presheaf (le_of_eq (inter_ulift Ui x))) hz'
  simp only [res_sum, res_zero, res_zsmul, restr_eq_res, res_res] at h0
  have key : ∀ a : Fin 3,
      res (uliftPresheaf.{uX, v, w} F) (inter_le_reindex (fun k => Ui k.down) x a.succAbove)
          (res (uliftPresheaf.{uX, v, w} F) (le_of_eq (inter_ulift Ui (x ∘ a.succAbove)))
            (ULift.up (z (fun b => ((x ∘ a.succAbove) b).down))))
        = ULift.up (res F.presheaf
            ((le_of_eq (inter_ulift Ui x)).trans
              (CechCochains.inter_le_omit Ui (fun c => (x c).down) a))
            (z ((fun c => (x c).down) ∘ a.succAbove))) := fun a =>
    (res_res (uliftPresheaf.{uX, v, w} F) _ _ _).trans (res_uliftPresheaf F _ _)
  rw [Finset.sum_congr rfl (fun a _ => by rw [key a])]
  have hup := congrArg (downEquiv.{uX, v, w} F (inter (fun k => Ui k.down) x)).symm h0
  simp only [map_sum, map_zsmul, map_zero, downEquiv_symm_apply] at hup
  exact hup

/-- **Degree-one Čech vanishing for a flasque sheaf of abelian groups.**  Every Čech
`1`-cocycle for an arbitrary family of opens is a coboundary.  The index type of the family
lives in a universe independent of the sheaf's universe of values. -/
theorem exists_cechD_eq_of_isFlasque {I : Type w} (Ui : I → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) [F.IsFlasque]
    (z : CechCochains.Cochain Ui F.presheaf 1)
    (hz : CechCochains.cechD Ui F.presheaf 1 z = 0) :
    ∃ b : CechCochains.Cochain Ui F.presheaf 0, CechCochains.cechD Ui F.presheaf 0 b = z := by
  classical
  let W : ULift.{v} I → Opens X := fun k => Ui k.down
  have hW : ∀ {m : ℕ} (y : Fin m → ULift.{v} I),
      inter W y = CechCochains.inter Ui (fun a => (y a).down) := fun y => inter_ulift Ui y
  let g : ∀ y : Fin 2 → ULift.{v} I,
      ToType ((uliftPresheaf.{uX, v, w} F).obj (op (inter W y))) := fun y =>
    res (uliftPresheaf.{uX, v, w} F) (le_of_eq (hW y))
      (ULift.up (z (fun a => (y a).down)))
  have hgdef : ∀ y : Fin 2 → ULift.{v} I, g y =
      res (uliftPresheaf.{uX, v, w} F) (le_of_eq (hW y))
        (ULift.up (z (fun a => (y a).down))) := fun _ => rfl
  obtain ⟨h'', hh''⟩ := exists_sum_res_eq W (uliftSheaf.{uX, v, w} F) 0 g
    (sum_res_uliftPresheaf_eq_zero Ui F z hz)
  let h' : ∀ y : Fin 1 → ULift.{v} I,
      ToType ((uliftPresheaf.{uX, v, w} F).obj (op (inter W y))) := h''
  have hh' : ∀ x : Fin 2 → ULift.{v} I, ∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
      res (uliftPresheaf.{uX, v, w} F) (inter_le_reindex W x a.succAbove)
        (h' (x ∘ a.succAbove)) = g x := hh''
  refine ⟨fun i => (res (uliftPresheaf.{uX, v, w} F)
    (le_of_eq (hW (fun a => ULift.up (i a))).symm) (h' (fun a => ULift.up (i a)))).down, ?_⟩
  funext i
  refine (CechCochains.cechD_apply Ui (p := 0) _ i).trans ?_
  have h1 := congrArg (res (uliftPresheaf.{uX, v, w} F)
    (le_of_eq (hW (fun a => ULift.up (i a))).symm)) (hh' (fun a => ULift.up (i a)))
  have h2 := congrArg (downEquiv.{uX, v, w} F (CechCochains.inter Ui i)) h1
  simp only [res_sum, res_zsmul, res_res, map_sum, map_zsmul, downEquiv_apply] at h2
  simp only [restr_eq_res, res_uliftPresheaf_down, res_res]
  refine Eq.trans (Finset.sum_congr rfl (fun j _ => rfl))
    (h2.trans (congrArg ULift.down ?_))
  exact (congrArg (res (uliftPresheaf.{uX, v, w} F)
      (le_of_eq (hW (fun a => ULift.up (i a))).symm)) (hgdef _)).trans
    ((res_res (uliftPresheaf.{uX, v, w} F) _ _ _).trans (res_id _ _))

/-- **An injective sheaf of abelian groups is flasque.**  The space's universe is independent
of the sheaf's universe of values, unlike
`Stacks.Cohomology.AbelianVanishing.isFlasque_of_injective`, which pins them equal.  Kept a
plain theorem rather than an instance, so that importing this file adds no second global
`IsFlasque` instance competing with that one. -/
@[sga "4 V 4.6" "special case"]
theorem isFlasque_of_injective (F : TopCat.Sheaf AddCommGrpCat.{v} X) [Injective F] :
    F.IsFlasque := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  exact Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
    F (leOfHom i.unop)

/-- **Degree-one Čech vanishing for an injective sheaf of abelian groups.** -/
theorem exists_cechD_eq_of_injective {I : Type w} (Ui : I → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) [Injective F]
    (z : CechCochains.Cochain Ui F.presheaf 1)
    (hz : CechCochains.cechD Ui F.presheaf 1 z = 0) :
    ∃ b : CechCochains.Cochain Ui F.presheaf 0, CechCochains.cechD Ui F.presheaf 0 b = z :=
  let := isFlasque_of_injective F
  exists_cechD_eq_of_isFlasque Ui F z hz

/-- The Čech `H¹` of a flasque sheaf of abelian groups vanishes, for an arbitrary family of
opens indexed by an arbitrary type. -/
theorem cls_eq_zero_of_isFlasque {I : Type w} (Ui : I → Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) [F.IsFlasque]
    (c : CechCochains.cocycles1 Ui F.presheaf) :
    CechCochains.cls Ui F.presheaf c = 0 :=
  (CechCochains.cls_eq_zero_iff Ui F.presheaf c).mpr
    (exists_cechD_eq_of_isFlasque Ui F c.1
      ((CechCochains.mem_cocycles1_iff Ui F.presheaf c.1).mp c.2))

end Stacks.Cohomology.CechOne
