module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Factoring an immersion of a reduced scheme

An immersion of schemes factors, by definition, as an open immersion into a closed subscheme or as
a closed immersion into an open subscheme. For a *reduced* source the first of these can always be
arranged with the closed subscheme being the reduced induced structure on the closure of the image.

## Main results

* `AlgebraicGeometry.ker_eq_vanishingIdeal_of_reduced_closed_immersion`: a closed immersion with
  reduced source cuts out the reduced induced structure on its image.
* `AlgebraicGeometry.exists_openImmersion_closedImmersion_factorization_of_isReduced`: an immersion
  of a reduced scheme factors as an open immersion followed by a closed immersion.

## References

* [Stacks Project, Tag 03DQ](https://stacks.math.columbia.edu/tag/03DQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A closed immersion with reduced source cuts out the reduced induced structure on its image: its
kernel is the vanishing ideal of the support of that kernel. -/
theorem ker_eq_vanishingIdeal_of_reduced_closed_immersion
    {A B : Scheme.{u}} (g : A ⟶ B) [IsClosedImmersion g] [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
  have hg : IsIso g.toImage := by
    apply IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage <;> simp [Scheme.Hom.imageι]
  let e : A ≅ g.ker.subscheme := asIso g.toImage
  have : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion e.inv
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker g.ker.support rfl

/-- An immersion of a reduced scheme factors as an open immersion followed by a closed
immersion. -/
@[stacks 03DQ, ega "I 5.2.3" "factorization only"]
theorem exists_openImmersion_closedImmersion_factorization_of_isReduced
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f] [IsReduced Z] :
    ∃ (Y : Scheme.{u}) (j : Z ⟶ Y) (i : Y ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f := by
  let T : Closeds X := .closure (Set.range f)
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  let Y : Scheme := I.subscheme
  let i : Y ⟶ X := I.subschemeι
  have hT : Set.range f ⊆ (I.support : Set X) := by
    show Set.range f ⊆ ((Scheme.IdealSheafData.vanishingIdeal T).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact subset_closure
  obtain ⟨j, hj⟩ :=
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support I f).2 hT
  let U := f.coborderRange
  let k : U.toScheme ⟶ X := U.ι
  let g : Z ⟶ U.toScheme := f.liftCoborder
  let P : Scheme := pullback k i
  let p : P ⟶ U.toScheme := pullback.fst k i
  let q : P ⟶ Y := pullback.snd k i
  have hgk : g ≫ k = f := f.liftCoborder_ι
  have hjf : j ≫ i = f := hj.trans (by simp)
  have hrange : Set.range p = Set.range g := by
    show Set.range (pullback.fst k (I.subschemeι)) = Set.range (f.liftCoborder)
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    show k ⁻¹' (closure (Set.range f)) = Set.range g
    have hkg (z : Z) : k (g z) = f z := by
      simpa [Scheme.Hom.comp_apply] using congrArg (fun m : Z ⟶ X => m z) hgk
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ : k x ∈ Set.range f := by
        simpa only [closure_inter_coborder] using
          (show k x ∈ closure (Set.range f) ∩ coborder (Set.range f) from ⟨hx, x.2⟩)
      exact ⟨z, k.isOpenEmbedding.injective ((hkg z).trans hz)⟩
    · rintro ⟨z, rfl⟩
      show k (g z) ∈ closure (Set.range f)
      exact hkg z ▸ subset_closure ⟨z, rfl⟩
  let e : Z ⟶ P := pullback.lift g j (hgk.trans hjf.symm)
  have he₁ : e ≫ p = g := pullback.lift_fst _ _ _
  have he₂ : e ≫ q = j := pullback.lift_snd _ _ _
  have : IsReduced Y := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  have : IsReduced P := isReduced_of_isOpenImmersion q
  have hker : g.ker = p.ker := by
    have hsup : g.ker.support = p.ker.support := SetLike.coe_injective <| by
      rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, hrange]
    rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion g,
      ker_eq_vanishingIdeal_of_reduced_closed_immersion p, hsup]
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq g p e (he₁.trans (by simp)) hker
  refine ⟨Y, j, i, ?_, inferInstance, hjf⟩
  rw [← he₂]
  infer_instance

end AlgebraicGeometry
