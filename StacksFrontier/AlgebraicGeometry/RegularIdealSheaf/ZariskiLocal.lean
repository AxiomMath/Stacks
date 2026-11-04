module

public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing the regularity conditions on an immersion along an open cover of the target

Let `i : Z ⟶ X` be an immersion of schemes and let `V` be a family of opens of `X` covering `X`.
`StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence` proves that each of parts (2),
(3) and (4) of Stacks tag 063J *restricts*: if `i` satisfies the condition then so does
`i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl`, the restriction of `i` over `V k`
(`isKoszulRegularImmersion_resLE` and its two companions). This file proves the converse, that
each condition *glues*: if every restriction satisfies the condition then so does `i`.

Together the two halves say that parts (2), (3) and (4) of Stacks tag 063J are Zariski local on
the target, which is the first of the three hypotheses the criterion of Stacks tag 02KP consumes
in the proof of Stacks tag 0694.

## Main results

* `isKoszulRegularImmersion_of_resLE`, `isH1RegularImmersion_of_resLE` and
  `isQuasiRegularImmersion_of_resLE`: parts (2), (3) and (4) of Stacks tag 063J glue along an
  open cover of the target.

## Implementation notes

The proof is immediate from the *ambient* reading of the conditions supplied by
`Independence.lean`: `isKoszulRegularIdealSheaf_restrictSubmodule_iff` turns the condition on the
restricted ideal sheaf over an open `A ⊆ X` into the statement that every point of `A` in the
support of `O_X / J` has a Koszul-regular generating sequence for `J` on a neighbourhood
contained in `A`, and `imOpen_coborderRange_resLE` identifies the open belonging to the
restriction of `i` over `V k` as `V k ⊓ i.coborderRange`. Both the hypothesis and the conclusion
are then conditions on `X` about the same ideal sheaf `definingIdealOfHom i`, differing only in
which open bounds the neighbourhood, so gluing is just the choice of a member of the cover
containing the given point: the witness it returns is already contained in
`V k ⊓ i.coborderRange ≤ i.coborderRange` and needs no shrinking.

These two halves are the whole mathematical content of Zariski locality, but they do not yet
give a `CategoryTheory.MorphismProperty.IsLocalAtTarget` instance for the morphism property
`fun _ _ f => ∃ hi : IsImmersion f, IsKoszulRegularImmersion f`, because that class extends
`CategoryTheory.MorphismProperty.RespectsIso` and every constructor for it therefore demands
`RespectsIso` first. Granting `RespectsIso`, `AlgebraicGeometry.IsZariskiLocalAtTarget.mk'` is
discharged by `isKoszulRegularImmersion_resLE` and `isKoszulRegularImmersion_of_resLE` together,
using `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` to pass between the two spellings
of the restricted morphism. What `RespectsIso` needs and this development does not have is
invariance of the conditions of Stacks tag 063D under an *isomorphism* of the ambient ringed
space: a counterpart of `restrictStalkEquiv` for an arbitrary isomorphism, carrying opens,
sections and germs across, after which the germwise conditions transport by the ring-isomorphism
lemmas that do exist (`koszulHomology_isZero_ringEquiv_iff` and `isQuasiRegularRel_ringEquiv`).
Note that the iso-invariance cannot be recovered from the restriction machinery of this file:
comparing `i` with its restriction over `⊤` already requires transporting along
`(⊤ : X.Opens).toScheme ≅ X`, which is an instance of the statement being sought.

Note also that `IsKoszulRegularImmersion` takes the `IsImmersion` instance as an argument, so it
depends on a proof. Rewriting the morphism underneath it with `rw` therefore fails with "motive
is not type correct"; transport along an equality of morphisms by `subst` on the equality and
`exact`, which closes the residual instance mismatch by proof irrelevance.

## References

* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 34.2.6 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Lemma 35.26.1 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.QuasiRegular

universe u

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type*} (V : ι → X.Opens)
  (hV : iSup V = ⊤)

include hV

/-- Every point of the image of `i` lies in the canonical open of the restriction of `i` over some
member of the cover `V`, and that open is contained in `i.coborderRange`. -/
private theorem exists_mem_imOpen_resLE_le {y : X} (hyC : y ∈ i.coborderRange) :
    ∃ k, y ∈ imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange ∧
      imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange ≤ i.coborderRange := by
  obtain ⟨k, hyk⟩ : ∃ k, y ∈ V k := Opens.mem_iSup.mp (hV ▸ Opens.mem_top y)
  simp only [imOpen_coborderRange_resLE]
  exact ⟨k, ⟨hyk, hyC⟩, inf_le_right⟩

/-- **Stacks tag 063J, part (2): Koszul-regularity glues along an open cover of the target.**
If every restriction `i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl` of the immersion `i` over a member of an
open cover `V` of `X` is a Koszul-regular immersion, then so is `i`. -/
@[stacks 063J "part (2): gluing along an open cover of the target"]
theorem isKoszulRegularImmersion_of_resLE
    (h : ∀ k, IsKoszulRegularImmersion (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) :
    IsKoszulRegularImmersion i := by
  refine (isKoszulRegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).mpr ?_
  refine (isKoszulRegularIdealSheaf_restrictSubmodule_iff i.coborderRange
    (definingIdealOfHom i)).mpr fun y hyC hySupp => ?_
  obtain ⟨k, hmem, hle⟩ := exists_mem_imOpen_resLE_le i V hV hyC
  have hk : IsKoszulRegularIdealSheaf
      (X.toLocallyRingedSpace.toRingedSpace.restrict
        (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange).isOpenEmbedding)
      (restrictSubmodule (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange)
        (definingIdealOfHom i)) := by
    refine (isKoszulRegularIdealSheaf_restrictSubmodule_nested_iff (V k)
      (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange (definingIdealOfHom i)).mp ?_
    rw [restrictSubmodule_definingIdealOfHom_resLE i (V k)]
    exact (isKoszulRegularImmersion_iff _ _
      (restrictSubmodule_coborderRange_definingIdealOfHom _)).mp (h k)
  obtain ⟨U, hyU, hUle, r, f, hK, hG⟩ :=
    (isKoszulRegularIdealSheaf_restrictSubmodule_iff _ _).mp hk y hmem hySupp
  exact ⟨U, hyU, hUle.trans hle, r, f, hK, hG⟩

/-- **Stacks tag 063J, part (3): `H₁`-regularity glues along an open cover of the target.** -/
@[stacks 063J "part (3): gluing along an open cover of the target"]
theorem isH1RegularImmersion_of_resLE
    (h : ∀ k, IsH1RegularImmersion (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) :
    IsH1RegularImmersion i := by
  refine (isH1RegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).mpr ?_
  refine (isH1RegularIdealSheaf_restrictSubmodule_iff i.coborderRange
    (definingIdealOfHom i)).mpr fun y hyC hySupp => ?_
  obtain ⟨k, hmem, hle⟩ := exists_mem_imOpen_resLE_le i V hV hyC
  have hk : IsH1RegularIdealSheaf
      (X.toLocallyRingedSpace.toRingedSpace.restrict
        (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange).isOpenEmbedding)
      (restrictSubmodule (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange)
        (definingIdealOfHom i)) := by
    refine (isH1RegularIdealSheaf_restrictSubmodule_nested_iff (V k)
      (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange (definingIdealOfHom i)).mp ?_
    rw [restrictSubmodule_definingIdealOfHom_resLE i (V k)]
    exact (isH1RegularImmersion_iff _ _
      (restrictSubmodule_coborderRange_definingIdealOfHom _)).mp (h k)
  obtain ⟨U, hyU, hUle, r, f, hK, hG⟩ :=
    (isH1RegularIdealSheaf_restrictSubmodule_iff _ _).mp hk y hmem hySupp
  exact ⟨U, hyU, hUle.trans hle, r, f, hK, hG⟩

/-- **Stacks tag 063J, part (4): quasi-regularity glues along an open cover of the target.** -/
@[stacks 063J "part (4): gluing along an open cover of the target"]
theorem isQuasiRegularImmersion_of_resLE
    (h : ∀ k, IsQuasiRegularImmersion (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) :
    IsQuasiRegularImmersion i := by
  refine (isQuasiRegularImmersion_iff i _
    (restrictSubmodule_coborderRange_definingIdealOfHom i)).mpr ?_
  refine (isQuasiRegularIdealSheaf_restrictSubmodule_iff i.coborderRange
    (definingIdealOfHom i)).mpr fun y hyC hySupp => ?_
  obtain ⟨k, hmem, hle⟩ := exists_mem_imOpen_resLE_le i V hV hyC
  have hk : IsQuasiRegularIdealSheaf
      (X.toLocallyRingedSpace.toRingedSpace.restrict
        (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange).isOpenEmbedding)
      (restrictSubmodule (imOpen (V k) (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange)
        (definingIdealOfHom i)) := by
    refine (isQuasiRegularIdealSheaf_restrictSubmodule_nested_iff (V k)
      (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl).coborderRange (definingIdealOfHom i)).mp ?_
    rw [restrictSubmodule_definingIdealOfHom_resLE i (V k)]
    exact (isQuasiRegularImmersion_iff _ _
      (restrictSubmodule_coborderRange_definingIdealOfHom _)).mp (h k)
  obtain ⟨U, hyU, hUle, r, f, hQ, hG⟩ :=
    (isQuasiRegularIdealSheaf_restrictSubmodule_iff _ _).mp hk y hmem hySupp
  exact ⟨U, hyU, hUle.trans hle, r, f, hQ, hG⟩

end Stacks.AlgebraicGeometry.RegularIdealSheaf

end
