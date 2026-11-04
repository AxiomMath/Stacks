module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.PullbackInjectiveOfSplitMono
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilDivisorAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamSplitting
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DirectImageMapChain
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms

/-!
# Axiom (A7) for de Rham cohomology

Let `k` be a field. Axiom (A7) of Weil Cohomology Theories, Section 0FID, for the data (D0), (D1),
(D2') of de Rham cohomology (`Stacks.DeRhamWeil.deRhamFirstChernClassData`, Section 0FWC) says:
if `b : X' → X` is the blowing up of a smooth projective `X` over `k` in a closed subscheme
`Z ⊆ X` smooth over `k` and nowhere dense in `X`, then `b^* : H^*_{dR}(X/k) → H^*_{dR}(X'/k)` is
injective. The proof of Proposition 0FWD obtains it from Proposition 0FUW: the canonical map
`Ω^•_{X/k} ⟶ Rb_*Ω^•_{X'/k}` has a left inverse in `D(X, (X → Spec k)^{-1}𝒪_{Spec k})`
(`Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp`), so the map it induces on
`H^n(X, -)`, which is `b^*` on `H^n_{dR}` followed by the Leray identification
`H^n(X, Rb_* -) = H^n(X', -)`, is injective
(`Stacks.WeilDeRham.deRhamCohomologyPullback_injective_of_isSplitMono`).

The canonical map of Proposition 0FUW is formed along `Stacks.DeRhamSmooth.relativeBase`, the
pullback along the morphism of the commutative square `b ≫ (X → Spec k) = (X' → Spec k) ≫ 𝟙`;
the two agree by `AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap_comp_eqToHom`.

## Main results

* `Stacks.WeilDeRham.injective_deRhamPullbackSquare_blowupHom`: `b^*` is injective on each
  `H^n_{dR}`.
* `Stacks.WeilDeRham.deRham_blowupAxiom`: **axiom (A7) for de Rham cohomology.**

## Implementation notes

Proposition 0FUW holds at any models of the derived categories; it is applied at
`HasDerivedCategory.standard`, the model in which
`Stacks.WeilDeRham.deRhamCohomologyPullback_injective_of_isSplitMono` is stated, through `let`
in the proof. No instance is declared in this file.

## References

* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme Stacks.DeRhamWeil
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-- **The de Rham pullback along a blowing up with smooth nowhere dense centre is injective in
every degree** ([Stacks, Tag 0FUW]): for a closed immersion `i : Z → X` of smooth projective
schemes over `k` with `Z` nowhere dense in `X`, and `b : X' = Bl_Z X → X`, the pullback
`b^* : H^n_{dR}(X/k) → H^n_{dR}(X'/k)` is injective for every `n`. -/
theorem injective_deRhamPullbackSquare_blowupHom
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] (hZ : IsNowhereDense (Set.range i.hom.left.base)) (n : ℤ) :
    Function.Injective (pullbackPiece (blowupHom i) n) := by
  have hint : interior (Set.range i.hom.left.base) = ∅ :=
    i.hom.left.isClosedEmbedding.isClosed_range.isNowhereDense_iff.mp hZ
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  let := HasDerivedCategory.standard (ModuleSheaves (inverseImageBase X.obj.hom))
  let := HasDerivedCategory.standard
    (ModuleSheaves (inverseImageBase (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left ≫
      X.obj.hom)))
  -- [Stacks, Tag 0FUW].
  obtain ⟨r, hr⟩ :=
    Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp X.obj.hom i.hom.left hint
  -- The canonical map of the square `b ≫ (X → Spec k) = (X' → Spec k) ≫ 𝟙` is a split mono.
  have hc := AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap_comp_eqToHom
    (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left) X.obj.hom
  have hsplit : IsSplitMono (AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap
      (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left) X.obj.hom) := by
    refine IsSplitMono.mk' ⟨eqToHom (congrArg (fun m =>
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward m).obj
        (AlgebraicGeometry.DeRhamLerayHirsch.deRhamObject
          (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left ≫ X.obj.hom)))
      (AlgebraicGeometry.DeRhamLerayHirsch.baseMap_eq_relativeBase
        (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left) X.obj.hom)) ≫ r, ?_⟩
    rw [← Category.assoc, hc]
    exact hr
  have hinj := deRhamCohomologyPullback_injective_of_isSplitMono
    (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left)
    (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left ≫ X.obj.hom) X.obj.hom (𝟙 _)
    (Category.comp_id _).symm hsplit n
  -- The pullback of the de Rham data is read through the comparison of the two realizations.
  change Function.Injective (deRhamPullbackSquare
    (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left)
    (Stacks.DeRham.BlowupTriangle.blowupMap i.hom.left ≫ X.obj.hom) X.obj.hom (𝟙 _)
    (Category.comp_id _).symm n)
  rw [deRhamPullbackSquare, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).1.comp
    (hinj.comp (ConcreteCategory.bijective_of_isIso _).1)

/-- **Axiom (A7) for de Rham cohomology** ([Stacks, Tag 0FUW], as used in the proof of
[Stacks, Proposition 0FWD]): for a closed immersion `i : Z → X` of smooth projective schemes over
`k` with `Z` nowhere dense in `X`, the pullback `b^* : H^*_{dR}(X/k) → H^*_{dR}(X'/k)` along the
blowing up `b : X' = Bl_Z X → X` is injective. -/
theorem deRham_blowupAxiom : (deRhamFirstChernClassData k).BlowupAxiom := by
  intro Z X i _ hZ a b hab
  refine DirectSum.ext fun n => ?_
  exact injective_deRhamPullbackSquare_blowupHom i hZ n
    ((pullback_apply_component (blowupHom i) a n).symm.trans
      ((congrArg (fun c : cohomology (blowupObj i) => c n) hab).trans
        (pullback_apply_component (blowupHom i) b n)))

end Stacks.WeilDeRham

end
