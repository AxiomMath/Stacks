module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.NonnegTruncationPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafDegreewise
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.NonnegTruncationInclusion

/-!
# The inclusion of the nonnegative truncation commutes with the algebra pullback

Let `g : X ⟶ Y` be a morphism of schemes, `𝒞` a sheaf of `ℤ`-graded `𝒪_Y`-algebras with
commutative homogeneous multiplication, and `ψ : g^*𝒞 ⟶ ℬ` a unital homomorphism of sheaves of
graded `𝒪_X`-algebras. There are two ways from the algebra pullback of the realisation of
`𝒞_{≥0}` to the realisation of `ℬ`:

* include `𝒞_{≥0}` in `𝒞`, pull back, compare with the realisation of `g^*𝒞`
  (`Stacks.GradedRealizationPullback.comparison`) and apply `ψ`;
* compare with the realisation of `(g^*𝒞)_{≥0}`
  (`Stacks.GradedRealizationPullback.nonnegTruncationAlgebraSheafComparisonIso`), apply the
  truncation of `ψ`, and include `ℬ_{≥0}` in `ℬ`.

**This file proves that they agree.** It is the algebra-level content of the compatibility of
[Stacks, Tag 0EKI]'s identifications with the top arrow of [Stacks, Tag 0EKG]'s diagram: the
inclusion `⨁_{m ≥ 0} 𝒪(m) ⊆ ⨁_{m ∈ ℤ} 𝒪(m)` pulls back to the inclusion
`⨁_{m ≥ 0} 𝓛^{⊗ m} ⊆ ⨁_{m ∈ ℤ} 𝓛^{⊗ m}`.

## Main results

* `Stacks.GradedRealizationPullback.gradedAlgebraSheafMap_right_ungradedIncl`: the morphism of
  algebra sheaves induced by a unital homomorphism on homogeneous local sections.
* `Stacks.GradedRealizationPullback.algebraPullback_map_inclusion_comp`: the two routes agree.
* `Stacks.GradedRealizationPullback.algebraPullback_map_inclusion_comp_hom`: the same with the
  comparisons packaged as the isomorphisms that are assembled downstream.

## Implementation notes

Both sides are morphisms out of an algebra pullback, so by the base-change adjunction
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` it suffices to compare
their adjoint transposes; there the comparison becomes `β`
(`Stacks.GradedRealizationPullback.unit_comp_map_comparison`), and two morphisms out of an
ungraded realisation agree once they agree on homogeneous local sections
(`Stacks.RelativeSpec.gradedAlgebraSheaf_right_hom_ext`). In a nonnegative degree both sides
send `x` to the degree-`n` inclusion of `ψ` of the pullback-unit image of `x`, by `rfl`; in a
negative degree `x` lies in a zero object.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.RingedSpace
open Stacks.AlgebraicGeometry.NonnegTruncation

universe u

namespace Stacks.GradedRealizationPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (𝒞 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝒞.piece i).val.obj W)
    (b : (𝒞.piece j).val.obj W), HEq ((𝒞.mul i j).app W a b) ((𝒞.mul j i).app W b a))
  (ℬ : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hb : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (ℬ.piece i).val.obj W)
    (b : (ℬ.piece j).val.obj W), HEq ((ℬ.mul i j).app W a b) ((ℬ.mul j i).app W b a))
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom (pbGraded g 𝒞) ℬ)

/-- The morphism of algebra sheaves induced by a unital homomorphism is the degreewise map on
homogeneous local sections. -/
theorem gradedAlgebraSheafMap_right_ungradedIncl {Z : Scheme.{u}}
    {A B : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf}
    (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : (Opens ↥Z)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : (Opens ↥Z)ᵒᵖ) (a : (B.piece i).val.obj W)
      (b : (B.piece j).val.obj W), HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
    (W : (Opens ↥Z)ᵒᵖ) (i : ℤ) (x : (A.piece i).val.obj W) :
    (((gradedAlgebraSheafMap Z f hcA hcB).right.hom).app W).hom (A.ungradedIncl i x) =
      B.ungradedIncl i ((f.app i).val.app W x) :=
  SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap f i x

/-- **The inclusion of the nonnegative truncation commutes with the algebra pullback**: including
`𝒞_{≥0}` in `𝒞`, pulling back, comparing and applying `ψ` is comparing with `(g^*𝒞)_{≥0}`,
truncating `ψ` and including `ℬ_{≥0}` in `ℬ`. -/
theorem algebraPullback_map_inclusion_comp :
    (algebraPullback g).map
        (gradedAlgebraSheafMap Y (inclusion 𝒞) (isCommutative_nonnegTruncation 𝒞 hc) hc) ≫
        comparison g 𝒞 hc ≫ gradedAlgebraSheafMap X ψ (pbGraded_mul_comm g 𝒞 hc) hb =
      comparison g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc) ≫
        gradedAlgebraSheafMap X (nonnegTruncationComm g 𝒞) _
          (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc)) ≫
        gradedAlgebraSheafMap X (unitalHom ψ) _ (isCommutative_nonnegTruncation ℬ hb) ≫
        gradedAlgebraSheafMap X (inclusion ℬ) _ hb := by
  apply ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_naturality, Category.assoc, Functor.map_comp, ← Category.assoc
      ((algebraPullbackPushforwardAdjunction g).unit.app _), unit_comp_map_comparison]
  refine Eq.trans ?_ ((congrArg (· ≫ (algebraPushforward g).map _)
    (unit_comp_map_comparison g (nonnegTruncation 𝒞)
      (isCommutative_nonnegTruncation 𝒞 hc)).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)))
  refine Under.UnderMorphism.ext (gradedAlgebraSheaf_right_hom_ext _ _ _ fun n W x => ?_)
  obtain ⟨V⟩ := W
  change ((gradedAlgebraSheafMap X ψ (pbGraded_mul_comm g 𝒞 hc) hb).right.hom.app
        (op (g ⁻¹ᵁ V))).hom
      (((pushforwardHom g 𝒞 hc).right.hom.app (op V)).hom
        (((gradedAlgebraSheafMap Y (inclusion 𝒞) (isCommutative_nonnegTruncation 𝒞 hc)
            hc).right.hom.app (op V)).hom
          ((nonnegTruncation 𝒞).ungradedIncl n x))) =
    ((gradedAlgebraSheafMap X (inclusion ℬ) (isCommutative_nonnegTruncation ℬ hb) hb).right.hom.app
        (op (g ⁻¹ᵁ V))).hom
      (((gradedAlgebraSheafMap X (unitalHom ψ)
          (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc))
          (isCommutative_nonnegTruncation ℬ hb)).right.hom.app (op (g ⁻¹ᵁ V))).hom
        (((gradedAlgebraSheafMap X (nonnegTruncationComm g 𝒞)
          (pbGraded_mul_comm g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc))
          (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc))).right.hom.app
            (op (g ⁻¹ᵁ V))).hom
          (((pushforwardHom g (nonnegTruncation 𝒞)
              (isCommutative_nonnegTruncation 𝒞 hc)).right.hom.app (op V)).hom
            ((nonnegTruncation 𝒞).ungradedIncl n x))))
  rw [gradedAlgebraSheafMap_right_ungradedIncl (inclusion 𝒞)
      (isCommutative_nonnegTruncation 𝒞 hc) hc (op V) n x,
    pushforwardHom_ungradedIncl g 𝒞 hc V n]
  erw [gradedAlgebraSheafMap_right_ungradedIncl ψ (pbGraded_mul_comm g 𝒞 hc) hb]
  rw [pushforwardHom_ungradedIncl g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc)
    V n x]
  erw [gradedAlgebraSheafMap_right_ungradedIncl _ _ _ (op (g ⁻¹ᵁ V)) n,
    gradedAlgebraSheafMap_right_ungradedIncl _ _ _ (op (g ⁻¹ᵁ V)) n,
    gradedAlgebraSheafMap_right_ungradedIncl _ _ _ (op (g ⁻¹ᵁ V)) n]
  rcases n with k | k
  · rfl
  · obtain rfl : x = 0 := eq_zero_of_isZero (isZero_piece_negSucc 𝒞 k) _ x
    simp only [pullbackUnit, map_zero]
    refine congrArg _ ((map_zero _).trans ?_)
    exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (map_zero _)).symm

/-- `algebraPullback_map_inclusion_comp` with the comparisons packaged as isomorphisms, in the
shape in which they are assembled downstream. -/
theorem algebraPullback_map_inclusion_comp_hom [hψ : ∀ n, IsIso (ψ.app n)] :
    (algebraPullback g).map
        (gradedAlgebraSheafMap Y (inclusion 𝒞) (isCommutative_nonnegTruncation 𝒞 hc) hc) ≫
        (comparisonIso g 𝒞 hc ≪≫
          gradedAlgebraSheafIso X (pbGraded_mul_comm g 𝒞 hc) hb ψ).hom =
      (nonnegTruncationAlgebraSheafComparisonIso g 𝒞 hc ≪≫
          nonnegTruncationAlgebraSheafIso (pbGraded g 𝒞) ℬ (pbGraded_mul_comm g 𝒞 hc) hb ψ
            (fun _ => inferInstance)).hom ≫
        gradedAlgebraSheafMap X (inclusion ℬ) (isCommutative_nonnegTruncation ℬ hb) hb := by
  rw [Iso.trans_hom, Iso.trans_hom]
  exact (algebraPullback_map_inclusion_comp g 𝒞 hc ℬ hb ψ).trans
    ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end Stacks.GradedRealizationPullback

end
