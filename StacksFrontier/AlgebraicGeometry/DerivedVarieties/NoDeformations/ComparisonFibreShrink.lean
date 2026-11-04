module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ComparisonClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SingletonFibreGeometricPoint
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksCore.Tactic.StacksAttribute

/-!
# Shrinking the base so that an open around the fibre becomes everything

[Stacks, Tag 0G0R] builds an open `U ⊆ X ×_S Y` containing the fibre `Y_s ×_k Y_s` and then says:
"Since `X ×_S Y → S` is proper, after replacing `S` by an open neighbourhood of `s` we may assume
`U = X ×_S Y`." This file supplies that step, together with the topological fact it rests on.

## Main results

* `AlgebraicGeometry.range_fibreSquareToProductComparison` — the range of the comparison
  morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` is exactly the fibre of `X ×_S Y ⟶ S` over the
  `k`-rational point `s`. This is the topological content of the pullback square
  `AlgebraicGeometry.isPullback_fibreSquareToProductComparison`.
* `AlgebraicGeometry.flat_constantFamilyProductToBase` — `X ×_S Y ⟶ S` is flat when `g` is
  smooth, which is what lets [Stacks, Tag 0G0N] be applied at a point of the fibre.
* `AlgebraicGeometry.isLocallyNoetherian_fibreProduct` and
  `AlgebraicGeometry.isNoetherian_fibreProduct` — `X ×_S Y` is locally Noetherian, which is what
  makes the cohomology sheaves of the kernel coherent, and Noetherian, which is what
  [Stacks, Tag 0G03] asks for.
* `AlgebraicGeometry.exists_opens_preimage_subset_of_range_fibreSquareToProductComparison_subset`
  — **the shrink**: an open `O ⊆ X ×_S Y` containing the range of `i` contains the whole
  preimage of some open neighbourhood `W` of `s` in `S`.

## Implementation notes

*Where properness is used.* Only through `X ×_S Y ⟶ S` being a closed map. That morphism is
proper because `g` is: the fibre `Y_s ⟶ Spec k` is a base change of `g`, hence proper; the
constant family `X = Y_s ×_k S ⟶ S` is a base change of that, hence proper; `X ×_S Y ⟶ Y` is a
base change of it, hence proper; and composing with `g` keeps it proper. Smoothness of `g` is not
used, and is not assumed.

*Why the conclusion is stated with preimages and not with a scheme-level restriction.* The
source's "we may assume `U = X ×_S Y`" is the statement that, after shrinking `S` to `W`, the
open `O` contains everything lying over `W`. That is exactly
`(X ×_S Y → S)⁻¹ W ⊆ O`, which is what is produced; forming the restricted scheme and
transporting the open along it would add nothing and would commit the consumer to one model of
the restriction.

*The point `s` picks out.* As elsewhere in this development, "`s ∈ W`" is rendered
`Set.range s.base ⊆ W`, which for `Spec k` a one-point space says exactly that the point `s`
picks out lies in `W`. The underlying one-point fact enters as
`Subsingleton.elim _ (IsLocalRing.closedPoint k)`.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section ConstantFamily

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- **The range of the comparison morphism is the fibre of `X ×_S Y ⟶ S` over `s`.**

This is the topological content of `AlgebraicGeometry.isPullback_fibreSquareToProductComparison`:
the comparison morphism `i : Y_s ×_k Y_s ⟶ X ×_S Y` exhibits its source as that fibre, so its
image is the set of points of `X ×_S Y` lying over the point `s` picks out. -/
theorem range_fibreSquareToProductComparison (hs : s ≫ q = 𝟙 _) :
    Set.range (fibreSquareToProductComparison q g s hs).base =
      (constantFamilyProductToBase q g s).base ⁻¹' Set.range s.base := by
  have h := isPullback_fibreSquareToProductComparison q g s hs
  rw [← Scheme.Pullback.range_fst (constantFamilyProductToBase q g s) s, ← h.isoPullback_hom_fst,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (show Function.Surjective h.isoPullback.hom.base from
      h.isoPullback.hom.homeomorph.surjective), Set.image_univ]

/-- A property stable under base change and composition passes from `g` and the constant family
`X ⟶ S` to `X ×_S Y ⟶ S`. -/
private theorem constantFamilyProductToBase_of_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hX : P (constantFamilyπ q g s)) (hg : P g) : P (constantFamilyProductToBase q g s) :=
  P.comp_mem _ _ (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (constantFamilyπ q g s) g) hX) hg

/-- `X ×_S Y ⟶ S` is proper when `g : Y ⟶ S` is. -/
theorem isProper_constantFamilyProductToBase [IsProper g] :
    IsProper (constantFamilyProductToBase q g s) :=
  constantFamilyProductToBase_of_property q g s @IsProper
    (by dsimp only [constantFamilyπ, fibreAtRationalPointπ]; infer_instance) inferInstance

/-- **`X ×_S Y ⟶ S` is flat when `g : Y ⟶ S` is smooth.** The fibre `Y_s ⟶ Spec k` is a base
change of `g`, hence flat; the constant family `X = Y_s ×_k S ⟶ S` is a base change of that,
hence flat; `X ×_S Y ⟶ Y` is a base change of it; and composing with `g`, itself flat because
smooth, keeps it flat.

This is the flatness of the base morphism that [Stacks, Tag 0G0N] needs at a point `z` of the
fibre, applied to `𝒪_{S,s} ⟶ 𝒪_{X ×_S Y, z}`. -/
theorem flat_constantFamilyProductToBase [Smooth g] : Flat (constantFamilyProductToBase q g s) :=
  constantFamilyProductToBase_of_property q g s @Flat
    (by dsimp only [constantFamilyπ, fibreAtRationalPointπ]; infer_instance) inferInstance

/-- **`X ×_S Y` is locally Noetherian** when `S` is of finite type over a field and `g` is
proper: `X ×_S Y ⟶ S` is then proper, hence locally of finite type, over a locally Noetherian
base. -/
theorem isLocallyNoetherian_fibreProduct [LocallyOfFiniteType q] [IsProper g] :
    IsLocallyNoetherian (Limits.pullback (constantFamilyπ q g s) g) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsProper (constantFamilyProductToBase q g s) := isProper_constantFamilyProductToBase q g s
  exact LocallyOfFiniteType.isLocallyNoetherian (constantFamilyProductToBase q g s)

/-- **`X ×_S Y` is Noetherian** when `S` is of finite type over a field and `g` is proper: it is
locally Noetherian and quasi-compact, the latter because `X ×_S Y ⟶ S` is proper and `S` is
quasi-compact over `Spec k`. -/
theorem isNoetherian_fibreProduct [LocallyOfFiniteType q] [QuasiCompact q] [IsProper g] :
    IsNoetherian (Limits.pullback (constantFamilyπ q g s) g) := by
  have : IsLocallyNoetherian (Limits.pullback (constantFamilyπ q g s) g) :=
    isLocallyNoetherian_fibreProduct q g s
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
  have : IsProper (constantFamilyProductToBase q g s) := isProper_constantFamilyProductToBase q g s
  have : QuasiCompact (constantFamilyProductToBase q g s) := inferInstance
  have := QuasiCompact.compactSpace_of_compactSpace (constantFamilyProductToBase q g s)
  exact ⟨⟩

/-- **The properness shrink of [Stacks, Tag 0G0R].** Let `g : Y ⟶ S` be proper, let
`X = Y_s ×_k S` be the constant family at a `k`-rational point `s`, and let `O` be an open of
`X ×_S Y` containing the fibre `Y_s ×_k Y_s` over `s` — that is, containing the range of the
comparison morphism. Then some open neighbourhood `W` of `s` in `S` has its entire preimage in
`O`.

This is the source's "since `X ×_S Y → S` is proper, after replacing `S` by an open neighbourhood
of `s` we may assume `U = X ×_S Y`". -/
theorem exists_opens_preimage_subset_of_range_fibreSquareToProductComparison_subset
    [IsProper g] (hs : s ≫ q = 𝟙 _)
    (O : (Limits.pullback (constantFamilyπ q g s) g).Opens)
    (hO : Set.range (fibreSquareToProductComparison q g s hs).base ⊆ (O : Set _)) :
    ∃ W : S.Opens, Set.range s.base ⊆ (W : Set S) ∧
      (constantFamilyProductToBase q g s).base ⁻¹' (W : Set S) ⊆ (O : Set _) := by
  have : IsProper (constantFamilyProductToBase q g s) := isProper_constantFamilyProductToBase q g s
  have hfib : (constantFamilyProductToBase q g s).base ⁻¹' {s.base (IsLocalRing.closedPoint k)} ⊆
      (O : Set _) := by
    refine fun z hz => hO ?_
    rw [range_fibreSquareToProductComparison q g s hs]
    exact ⟨IsLocalRing.closedPoint k, (Set.mem_singleton_iff.mp hz).symm⟩
  obtain ⟨W, hsW, hW⟩ := exists_opens_preimage_subset_of_isClosedMap
    (constantFamilyProductToBase q g s)
    (constantFamilyProductToBase q g s).isClosedMap O (s.base (IsLocalRing.closedPoint k)) hfib
  refine ⟨W, Set.range_subset_iff.mpr fun p => ?_, hW⟩
  rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
  exact hsW

end ConstantFamily

end AlgebraicGeometry

end
