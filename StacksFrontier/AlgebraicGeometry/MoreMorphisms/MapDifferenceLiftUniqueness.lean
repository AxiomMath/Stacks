module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal

/-!
# A lift of a map across a first-order thickening is determined by its difference derivation

Let `i : X ⟶ X'` be a first-order thickening of schemes, let `q : Y ⟶ S` be a morphism and let
`a', b' : X' ⟶ Y` be two morphisms over `S` agreeing on `X`, say `i ≫ a' = i ≫ b' = a`. The
difference derivation `D` of [Stacks Project, Tag 04FG] for the pair, constructed in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf` as
`Stacks.Thickenings.liftDifferenceDerivation`, records the difference of the two comorphisms:
`D s` is the conormal class of `(a')^♯ s - (b')^♯ s`.

**This file proves that `D` determines the pair: if `D` vanishes then `b' = a'`.** Together with
[Stacks Project, Tag 02H5] — `Stacks.Thickenings.existsUnique_derivationActionGlobal`, which
produces a lift realising a prescribed derivation — this is the freeness of the action of
derivations on the lifts of a fixed morphism, the injectivity half of
[Stacks Project, Tag 0D14] part (2).

## Route

The two steps are independent and are stated separately.

* `Stacks.Thickenings.eq_of_liftDiffSection_eq_zero` is purely about schemes: if
  `(a')^♯ s = (b')^♯ s` for every local section `s` of `𝒪_Y`, then `b' = a'`. The two morphisms
  have the same underlying map because `i` is surjective
  (`Stacks.Thickenings.base_eq_of_comm`), hence the same preimages
  (`Stacks.Thickenings.preimage_eq_of_comm`), so the open `(b')⁻¹V ∩ (a')⁻¹V` over which
  `Stacks.Thickenings.liftDiffSection` is formed is already `(a')⁻¹V` and the hypothesis is the
  equality of the two comorphisms over it.
* `Stacks.Thickenings.eq_of_liftDifferenceDerivation_d_eq_zero` feeds that hypothesis from the
  vanishing of `D`, using the factorization
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d` of
  [Stacks Project, Tag 04FG]: the difference of the comorphisms is the image of `D s` under the
  inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}`, so it vanishes with `D s`. No injectivity of that inclusion is
  needed in this direction.

Neither statement needs the conormal sheaf to be read in `AlgebraicGeometry.Scheme.Modules X`,
so neither pays the spelling crossing of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheafModules`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Opposite

universe u

namespace Stacks.Thickenings

open Stacks.Conormal Stacks.Diagonal

variable {S X X' Y : Scheme.{u}}
variable {i : X ⟶ X'} {a : X ⟶ Y} {a' b' : X' ⟶ Y} {q : Y ⟶ S}

/-- **Two lifts of the same morphism across a first-order thickening with the same comorphism
are equal.** The hypothesis is the vanishing of `Stacks.Thickenings.liftDiffSection`, that is
`(a')^♯ s = (b')^♯ s` over the open `(b')⁻¹V ∩ (a')⁻¹V` for every local section `s` of `𝒪_Y`.

The underlying maps agree by `Stacks.Thickenings.base_eq_of_comm`, so that open is `(a')⁻¹V` and
the hypothesis says exactly that the comorphisms agree there. -/
theorem eq_of_liftDiffSection_eq_zero [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a)
    (h : ∀ (V : Y.Opens) (s : Γ(Y, V)), liftDiffSection a' b' V s = 0) :
    b' = a' := by
  have ha := comm_a.trans (Category.comp_id a).symm
  have hb := comm_b.trans (Category.comp_id a).symm
  have hbase : b'.base = a'.base := base_eq_of_comm (j := 𝟙 Y) hsq ha hb
  have hpre : ∀ W : Y.Opens, b' ⁻¹ᵁ W = a' ⁻¹ᵁ W := preimage_eq_of_comm (j := 𝟙 Y) hsq ha hb
  refine Scheme.Hom.ext hbase fun U => ?_
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  have key : ∀ {L : X'.Opens} (_ : L = a' ⁻¹ᵁ U) (e1 : L ≤ a' ⁻¹ᵁ U) (e2 : L ≤ b' ⁻¹ᵁ U),
      (a'.appLE U L e1).hom s = (b'.appLE U L e2).hom s →
      (a'.appLE U (a' ⁻¹ᵁ U) le_rfl).hom s
        = (b'.appLE U (a' ⁻¹ᵁ U) (hpre U).ge).hom s := by
    intro L hL e1 e2 hh
    subst hL
    exact hh
  have hL : liftPairOpen a' b' U = a' ⁻¹ᵁ U := by
    rw [liftPairOpen, hpre U, inf_idem]
  have hdiff := h U s
  rw [liftDiffSection, sub_eq_zero] at hdiff
  have hgoal := key hL inf_le_right inf_le_left hdiff
  rw [Scheme.Hom.appLE_eq_app] at hgoal
  rw [Scheme.Hom.appLE] at hgoal
  change (X'.presheaf.map _).hom ((b'.app U).hom s) = _
  rw [hgoal, CommRingCat.comp_apply]
  exact congrArg (fun z : (a' ⁻¹ᵁ U) ⟶ (b' ⁻¹ᵁ U) =>
    (X'.presheaf.map z.op).hom ((b'.app U).hom s)) (Subsingleton.elim _ _)

/-- **A lift with vanishing difference derivation is the reference lift**, the injectivity half
of [Stacks Project, Tag 0D14] part (2). If the derivation `D` of [Stacks Project, Tag 04FG]
attached to the pair `(a', b')` is zero on every universal differential, then `b' = a'`.

The difference of the two comorphisms is the image of `D s` under the inclusion
`𝒞_{X/X'} ⟶ 𝒪_{X'}` of the first-order thickening, so it vanishes with `D s`, and
`Stacks.Thickenings.eq_of_liftDiffSection_eq_zero` concludes. -/
theorem eq_of_liftDifferenceDerivation_d_eq_zero [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q) (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a)
    (h : ∀ (V : Y.Opens) (s : Γ(Y, V)),
      (liftDifferenceDerivation hq comm_a comm_b).d (X := op V) s = 0) :
    b' = a' := by
  refine eq_of_liftDiffSection_eq_zero hsq comm_a comm_b fun V s => ?_
  have hι := firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d hsq hq comm_a comm_b V s
  rw [h V s] at hι
  exact hι.symm.trans (Eq.trans (congrArg _ (map_zero _)) (map_zero _))

end Stacks.Thickenings

end
