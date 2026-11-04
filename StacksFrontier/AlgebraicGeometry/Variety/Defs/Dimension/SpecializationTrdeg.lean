module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Sets.Closeds
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Specialization

/-!
# Transcendence degree and specialization

On a scheme locally of finite type over a field, the transcendence degree of the residue field
strictly decreases under a nontrivial specialization. The two points lie on the reduced induced
subscheme on the closure of the more general one, which is irreducible, so the dimension formula
applies with the same left-hand side at both points; the stalk dimension strictly increases, so
the transcendence degree must strictly drop.

## Main results

* `AlgebraicGeometry.trdeg_residueField_lt_of_specialization` states the strict decrease of
  residue-field transcendence degree along a nontrivial specialization.

## Implementation notes

A locally algebraic scheme over `k` is represented by its structure morphism to `Spec k` with a
`LocallyOfFiniteType` instance. The `k`-algebra structure on each residue field is the canonical
composite from `k` through global sections and evaluation at the point. The inequality is stated
between Mathlib's cardinal-valued transcendence degrees, and the specialization relation is
Mathlib's `Specializes`.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory
open CommRingCat TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On a scheme locally of finite type over a field, residue-field transcendence degree strictly
decreases along a nontrivial specialization. -/
@[stacks 0A21 "specialization_trdeg"]
theorem trdeg_residueField_lt_of_specialization
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {x x' : X} (hxx' : x ⤳ x') (hne : x ≠ x') :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra k (X.residueField x') :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x').hom.toAlgebra
    Algebra.trdeg k (X.residueField x') < Algebra.trdeg k (X.residueField x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  let Y := I.subscheme
  let y : Y := ⟨x, subset_closure (Set.mem_singleton x)⟩
  let y' : Y := ⟨x', specializes_iff_mem_closure.mp hxx'⟩
  let i : Y ⟶ X := I.subschemeι
  have iy : i y = x := by simpa [i, y] using I.subschemeι_apply y
  have iy' : i y' = x' := by simpa [i, y'] using I.subschemeι_apply y'
  have hyy' : y ⤳ y' := by
    apply i.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [iy, iy'] using hxx'
  have hneY : y ≠ y' := by
    intro h
    apply hne
    simpa [iy, iy'] using congrArg i h
  let g : Y ⟶ Spec (.of k) := i ≫ f
  have : LocallyOfFiniteType g := locallyOfFiniteType_comp i f
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  let : Algebra k (Y.residueField y') :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation y').hom.toAlgebra
  have htoENatY : Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) < ⊤ :=
    Cardinal.toENat_lt_top.mpr (finTrdeg_iff_trdeg.mp (residueField_finTrdeg k g y))
  have htrdeg : ∀ (w : X) (z : Y), i z = w →
      letI : Algebra k (X.residueField w) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation w).hom.toAlgebra
      letI : Algebra k (Y.residueField z) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Y.Γevaluation z).hom.toAlgebra
      Algebra.trdeg k (X.residueField w) = Algebra.trdeg k (Y.residueField z) := by
    rintro w z rfl
    exact trdeg_residueField_of_surjectiveOnStalks k f i z
  have : IrreducibleSpace Y := Subtype.irreducibleSpace (isIrreducible_singleton (x := x)).closure
  have hstalk := krullDimOfRing_stalk_lt_of_specialization k Y g hyy' hneY
  have hsum :
      (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) +
          ringKrullDim (Y.presheaf.stalk y) =
        (Cardinal.toENat (Algebra.trdeg k (Y.residueField y')) : WithBot ℕ∞) +
          ringKrullDim (Y.presheaf.stalk y') := by
    calc
      _ = topologicalKrullDimAt Y y :=
        (topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y g y).symm
      _ = topologicalKrullDim Y :=
        (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y g y).symm
      _ = topologicalKrullDimAt Y y' :=
        topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y g y'
      _ = _ := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y g y'
  have htrdegY : Algebra.trdeg k (Y.residueField y') < Algebra.trdeg k (Y.residueField y) := by
    by_contra h
    have hle : Algebra.trdeg k (Y.residueField y) ≤ Algebra.trdeg k (Y.residueField y') :=
      le_of_not_gt h
    have hsumlt :
        (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) +
            ringKrullDim (Y.presheaf.stalk y) <
          (Cardinal.toENat (Algebra.trdeg k (Y.residueField y')) : WithBot ℕ∞) +
            ringKrullDim (Y.presheaf.stalk y') := by
      cases hd : ringKrullDim (Y.presheaf.stalk y) with
      | bot =>
          have ht : ⊥ < ringKrullDim (Y.presheaf.stalk y') := by
            simpa [hd] using hstalk
          have hn : ((Cardinal.toENat (Algebra.trdeg k (Y.residueField y')) : WithBot ℕ∞) +
              ringKrullDim (Y.presheaf.stalk y')) ≠ ⊥ :=
            WithBot.add_ne_bot.mpr ⟨by simp, ne_of_gt ht⟩
          simpa [hd] using WithBot.bot_lt_iff_ne_bot.mpr hn
      | coe d =>
          cases hd' : ringKrullDim (Y.presheaf.stalk y') with
          | bot => simp [hd'] at hstalk
          | coe d' =>
              have hdim : d < d' := by simpa [hd, hd'] using hstalk
              rw [← WithBot.coe_add, ← WithBot.coe_add]
              exact WithBot.coe_lt_coe.mpr (WithTop.add_lt_add_of_le_of_lt
                htoENatY.ne (Cardinal.toENat.monotone' hle) hdim)
    rw [hsum] at hsumlt
    exact lt_irrefl _ hsumlt
  rw [htrdeg x' y' iy', htrdeg x y iy]
  exact htrdegY

end AlgebraicGeometry

end
