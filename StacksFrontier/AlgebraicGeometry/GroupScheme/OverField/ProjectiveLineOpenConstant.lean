module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeProperCurves
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ProjectiveLineConstant
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProjectiveLineNormal

/-!
# Morphisms from an open of the projective line to a proper group scheme are constant

Let `k` be a field, let `G` be a group scheme over `k` which is a proper variety, and let `U` be a
nonempty open subscheme of the projective line `ℙ¹_k`. Every morphism `U ⟶ G` over `k` is
constant: it factors through `U ⟶ Spec k` followed by a `k`-rational point of `G`.

The morphism is a rational map `ℙ¹_k ⇢ G` over `k`; it extends to a morphism `ℙ¹_k ⟶ G`
(Stacks 0BXZ, `AlgebraicGeometry.toRationalMap_bijective`), which is constant by the scheme form
of Stacks 0AEN (`AlgebraicGeometry.exists_section_eq_comp_of_projectiveLineProj`), and the
extension restricts to the given morphism on `U` because `ℙ¹_k` is reduced and `G` is separated.

## Main results

* `AlgebraicGeometry.exists_section_eq_comp_of_opens_projectiveLineProj`: the constancy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Morphisms from a nonempty open of the projective line to a proper group variety are
constant.** Let `G` be a group scheme over a field `k` which is a proper variety over `k` and let
`U` be a nonempty open of `ℙ¹_k`. A morphism `f : U ⟶ G` over `k` is the structure morphism of
`U` followed by a section of `G ⟶ Spec k`. -/
theorem exists_section_eq_comp_of_opens_projectiveLineProj (G : Over (Spec (.of k)))
    [GrpObj G] [IsProperVariety k G.hom] (U : (projectiveLineProj k).Opens)
    (hU : (U : Set (projectiveLineProj k)).Nonempty) (f : U.toScheme ⟶ G.left)
    (hf : f ≫ G.hom = U.ι ≫ projToSpecCoeff k 1) :
    ∃ c : Spec (.of k) ⟶ G.left, c ≫ G.hom = 𝟙 _ ∧ f = U.ι ≫ projToSpecCoeff k 1 ≫ c := by
  let X : Over (Spec (.of k)) := Over.mk (projToSpecCoeff k 1)
  have : IsCurve k X.hom := isCurve_projToSpecCoeff_one k
  have : IsNormal X.left := Stacks.ResolutionOfSurfaces.isNormal_projectiveLineProj k
  have : IsIntegral X.left := inferInstanceAs (IsIntegral (projectiveLineProj k))
  have : IrreducibleSpace (projectiveLineProj k) := inferInstanceAs (IrreducibleSpace X.left)
  have hdense : Dense (U : Set (projectiveLineProj k)) := U.2.dense hU
  let p : X.left.PartialMap G.left := ⟨U, hdense, f⟩
  have hpOver : p.IsOver (Spec (.of k)) := by
    constructor
    exact hf
  obtain ⟨g, hg⟩ := (toRationalMap_bijective k X G).2 ⟨p.toRationalMap, inferInstance⟩
  have hgp : g.left.toRationalMap = p.toRationalMap := congrArg Subtype.val hg
  have hsep : IsSeparated (G.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated G.hom)
  have hgOver : g.left.IsOver (Spec (.of k)) := ⟨Over.w g⟩
  have heq : p.equiv g.left.toPartialMap :=
    (Scheme.PartialMap.toRationalMap_eq_iff).mp hgp.symm
  have hfg : f = U.ι ≫ g.left :=
    (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := Spec (.of k))).mp heq
  obtain ⟨c, hc, hgc⟩ := exists_section_eq_comp_of_projectiveLineProj G g.left (Over.w g)
  exact ⟨c, hc, by rw [hfg, hgc]⟩

end AlgebraicGeometry

end
