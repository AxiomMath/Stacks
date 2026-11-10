module

public import StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts
public import StacksFrontier.CategoryTheory.Monoidal.MateAsInternalHomPre

/-!
# The mate of a map of biproducts is the transposed matrix of mates

Let `C` be a monoidal preadditive category, let `X`, `X'`, `Y`, `Y'` be families of objects
indexed by finite types (two *different* ones: the source and target of a Koszul differential
are biproducts over subsets of different cardinalities), let `X' k` be a dual of `X k` and
`Y' k` a dual of `Y k`, and let `⨁ X'` be the dual of `⨁ X` and `⨁ Y'` of `⨁ Y`
by [Stacks, Tag 0FFT]
(`CategoryTheory.ExactPairing.biproduct`). A morphism `f : ⨁ X ⟶ ⨁ Y` is determined by its
matrix of components `f_{ik} = ι_i ≫ f ≫ π_k`. This file computes the matrix of the **mate**
`f^∨ : ⨁ Y' ⟶ ⨁ X'`: its `(k, i)` entry is the mate of `f_{ik}`,

`ι_{Y' k} ≫ f^∨ ≫ π_{X' i} = (f_{ik})^∨`,

so the mate of a map of biproducts is the map with the **transposed matrix of mates**.

Nothing in Mathlib relates `CategoryTheory.rightAdjointMate` to
`CategoryTheory.Limits.biproduct.π` or `CategoryTheory.Limits.biproduct.ι`; and
`CategoryTheory.ExactPairing.biproduct`, which supplies the pairing, exposes its coevaluation
and evaluation only in the binary case (`CategoryTheory.ExactPairing.biprod_coevaluation`,
`CategoryTheory.ExactPairing.biprod_evaluation`). The family-case accessors are supplied here.

This is the lemma that turns a differential of a dual complex — which
`CochainComplex.dualComplex_d` gives only as a signed mate — into an explicit contraction,
whenever the terms of the complex are biproducts and the differential is given by a matrix. The
Koszul and alternating-Čech complexes are of that form.

## Main results

* `CategoryTheory.ExactPairing.biproduct_evaluation` and
  `CategoryTheory.ExactPairing.biproduct_coevaluation`: the (co)evaluation of the biproduct
  pairing of a finite family.
* `CategoryTheory.ExactPairing.ι_comp_mate_comp_π`: **the matrix of the mate is the transposed
  matrix of the mates.**
* `CategoryTheory.ExactPairing.eq_mate_of_components`: consequently, a candidate morphism whose
  matrix is the transposed matrix of mates *is* the mate.
* `CategoryTheory.ExactPairing.mate_exactPairingUnit`: the mate of an endomorphism of the unit
  object is itself. Combined with the previous results this says that for biproducts of copies of
  the unit — the terms of a Koszul or an alternating-Čech complex — the matrix of the mate is the
  transpose of the matrix, with no mates left in it.

## Implementation notes

**Only the evaluation is used.** The mate is pinned down by the identity
`g ▷ X ≫ ε_X = Y' ◁ f ≫ ε_Y` alone (`CategoryTheory.ExactPairing.eq_mate`), so no coevaluation
and no unfolding of `CategoryTheory.rightAdjointMate` appears below. The two biproduct pairings
enter only through their evaluations, and those are therefore taken as *hypotheses* rather than
read off `CategoryTheory.ExactPairing.biproduct`: the results then apply to any pairing of the
biproducts whose evaluation is the expected sum, in particular to one transported along an
isomorphism of the dual.

**The two collapses.** Whiskering the mate identity with `ι_{Y' k} ⊗ ι_{X i}` kills all but one
term of each of the two sums `ε_{⨁} = ∑ (π ⊗ₘ π) ≫ ε`, by
`CategoryTheory.Limits.biproduct.ι_π_ne` — on the right-hand factor for the source pairing and on
the left-hand factor for the target one. That is the whole proof, together with
`CategoryTheory.MonoidalCategory.whisker_exchange` to move the two inclusions past the mate and
past `f`.

## References

* [Stacks Project, Tag 0FFT](https://stacks.math.columbia.edu/tag/0FFT)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace CategoryTheory.ExactPairing

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

omit [Preadditive C] [MonoidalPreadditive C] in
/-- **The mate of an endomorphism of the unit object is itself**, for the pairing of the unit
with itself. Both whiskerings of such an endomorphism against the evaluation `(ρ_ 𝟙)` are
`(ρ_ 𝟙).hom ≫ f`, the two unitors of the unit being equal. -/
theorem mate_exactPairingUnit (f : 𝟙_ C ⟶ 𝟙_ C) :
    mate exactPairingUnit exactPairingUnit f = f :=
  (eq_mate exactPairingUnit exactPairingUnit f f
    (by
      change f ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom = 𝟙_ C ◁ f ≫ (ρ_ (𝟙_ C)).hom
      rw [MonoidalCategory.rightUnitor_naturality, ← MonoidalCategory.unitors_equal,
        MonoidalCategory.leftUnitor_naturality, MonoidalCategory.unitors_equal])).symm

-- The two index types are `Type 0` because `CategoryTheory.ExactPairing.biproduct` is: it rests
-- on `CategoryTheory.Limits.biproduct.total`, which lives in a `variable {J : Type} [Fintype J]`
-- section of `Mathlib.CategoryTheory.Preadditive.Biproducts`.
variable {ι κ : Type} [Fintype ι] [Fintype κ] {X X' : ι → C} {Y Y' : κ → C}
  [HasBiproduct X] [HasBiproduct X'] [HasBiproduct Y] [HasBiproduct Y']

section Accessors

variable (X X')
variable [∀ k, ExactPairing (X k) (X' k)]

/-- The coevaluation of the biproduct pairing of a finite family. -/
theorem biproduct_coevaluation :
    η_ (⨁ X) (⨁ X') = ∑ k : ι, η_ (X k) (X' k) ≫ (biproduct.ι X k ⊗ₘ biproduct.ι X' k) :=
  rfl

/-- The evaluation of the biproduct pairing of a finite family. -/
theorem biproduct_evaluation :
    ε_ (⨁ X) (⨁ X') = ∑ k : ι, (biproduct.π X' k ⊗ₘ biproduct.π X k) ≫ ε_ (X k) (X' k) :=
  rfl

end Accessors

section Matrix

variable (p : ∀ k, ExactPairing (X k) (X' k)) (r : ∀ k, ExactPairing (Y k) (Y' k))

/-- **One summand of the object, against the biproduct evaluation.** Whiskering the evaluation
of the biproduct pairing with the inclusion of the `i`-th summand of `⨁ X` leaves only the
`i`-th term. -/
theorem whiskerLeft_ι_comp_sum_evaluation (i : ι) :
    (⨁ X') ◁ biproduct.ι X i ≫
        ∑ k : ι, (biproduct.π X' k ⊗ₘ biproduct.π X k) ≫ (p k).evaluation' =
      biproduct.π X' i ▷ X i ≫ (p i).evaluation' := by
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [biproduct.ι_π_self, tensorHom_id]
  · intro k _ hk
    rw [biproduct.ι_π_ne X (Ne.symm hk), MonoidalPreadditive.tensor_zero, zero_comp]

/-- **One summand of the dual, against the biproduct evaluation.** Whiskering the evaluation of
the biproduct pairing with the inclusion of the `j`-th summand of `⨁ Y'` leaves only the `j`-th
term. -/
theorem ι_whiskerRight_comp_sum_evaluation (j : κ) :
    biproduct.ι Y' j ▷ (⨁ Y) ≫
        ∑ k : κ, (biproduct.π Y' k ⊗ₘ biproduct.π Y k) ≫ (r k).evaluation' =
      Y' j ◁ biproduct.π Y j ≫ (r j).evaluation' := by
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [biproduct.ι_π_self, id_tensorHom]
  · intro k _ hk
    rw [biproduct.ι_π_ne Y' (Ne.symm hk), MonoidalPreadditive.zero_tensor, zero_comp]

/-- **The mate of a map of biproducts is the map with the transposed matrix of mates.** The
`(j, i)` entry of the matrix of `f^∨ : ⨁ Y' ⟶ ⨁ X'` is the mate of the `(i, j)` entry of the
matrix of `f : ⨁ X ⟶ ⨁ Y`.

The two pairings of the biproducts are only required to *have* the evaluations that
`CategoryTheory.ExactPairing.biproduct` has, by `hP` and `hR`; for that pairing itself they are
`CategoryTheory.ExactPairing.biproduct_evaluation`. -/
theorem ι_comp_mate_comp_π (P : ExactPairing (⨁ X) (⨁ X')) (R : ExactPairing (⨁ Y) (⨁ Y'))
    (hP : P.evaluation' = ∑ k : ι, (biproduct.π X' k ⊗ₘ biproduct.π X k) ≫ (p k).evaluation')
    (hR : R.evaluation' = ∑ k : κ, (biproduct.π Y' k ⊗ₘ biproduct.π Y k) ≫ (r k).evaluation')
    (f : (⨁ X) ⟶ ⨁ Y) (i : ι) (j : κ) :
    biproduct.ι Y' j ≫ mate P R f ≫ biproduct.π X' i =
      mate (p i) (r j) (biproduct.ι X i ≫ f ≫ biproduct.π Y j) := by
  refine eq_mate (p i) (r j) _ _ ?_
  rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.comp_whiskerRight_assoc,
    ← whiskerLeft_ι_comp_sum_evaluation p i, ← hP,
    ← MonoidalCategory.whisker_exchange_assoc, mate_comp_evaluation P R f,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whisker_exchange_assoc, hR,
    ι_whiskerRight_comp_sum_evaluation r j, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc]

/-- **A morphism whose matrix is the transposed matrix of mates is the mate.** The converse
reading of `CategoryTheory.ExactPairing.ι_comp_mate_comp_π`, which is how a candidate explicit
formula for a mate is verified. -/
theorem eq_mate_of_components (P : ExactPairing (⨁ X) (⨁ X')) (R : ExactPairing (⨁ Y) (⨁ Y'))
    (hP : P.evaluation' = ∑ k : ι, (biproduct.π X' k ⊗ₘ biproduct.π X k) ≫ (p k).evaluation')
    (hR : R.evaluation' = ∑ k : κ, (biproduct.π Y' k ⊗ₘ biproduct.π Y k) ≫ (r k).evaluation')
    (f : (⨁ X) ⟶ ⨁ Y) (g : (⨁ Y') ⟶ ⨁ X')
    (hg : ∀ (i : ι) (j : κ), biproduct.ι Y' j ≫ g ≫ biproduct.π X' i =
      mate (p i) (r j) (biproduct.ι X i ≫ f ≫ biproduct.π Y j)) :
    g = mate P R f :=
  biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun i => by
    rw [Category.assoc, Category.assoc, hg i j,
      ← ι_comp_mate_comp_π p r P R hP hR f i j]

end Matrix

end CategoryTheory.ExactPairing

end

end
