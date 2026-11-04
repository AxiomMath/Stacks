module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleSpreadingOut
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers after an extension of algebraically closed fields

Let `k ⊆ k'` be an extension of algebraically closed fields and let `X` be proper over `k`. This
file proves Stacks Tag 0A49: base change `U ↦ U_{k'}` is an equivalence between the category of
schemes finite étale over `X` and the category of schemes finite étale over `X_{k'}`.

## The argument

The source's proof has two ingredients, both available in this library.

* The filtered-colimit spreading out: write `k'` as the filtered colimit of its finite-type
  `k`-subalgebras `A_i`, descend a finite étale cover of `X_{k'}` to a finite étale cover of some
  `X_{A_i}` (Tags 01ZM, 01ZO, 07RP), and pull it back along `X_{k'} ⟶ X_{A_i^h}` for the
  henselization `A_i^h` of `A_i` at a `k`-point, which maps to `k'` because it is algebraic over
  `A_i` (Tag 0A1W). This is `AlgebraicGeometry.finiteEtaleDescendsToHenselianPoint_of_isAlgClosed`.
* Tag 0A48 for the proper scheme `X_{A_i^h}` over the henselian local ring `A_i^h`, whose closed
  fibre is `X`: `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence`.

`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian_of_isAlgClosed` combines
them, taking Tag 0A48 as an argument; here that argument is supplied by the theorem.

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed` —
  Tag 0A49.

## References

* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0A49.** Let `k ⊆ k'` be an extension of algebraically closed fields and
let `f : X ⟶ Spec k` be proper. Then base change along the projection `X_{k'} ⟶ X`, that is
`U ↦ U_{k'}`, is an equivalence between the category of schemes finite étale over `X` and the
category of schemes finite étale over `X_{k'} = X ×_{Spec k} Spec k'`.

This is `isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian_of_isAlgClosed`
with Tag 0A48 supplied by `properHenselianFiniteEtaleEquivalence`. -/
@[stacks 0A49 "As stated in the source: `k ⊆ k'` algebraically closed, `X` proper over `k`.",
  sga "1 IX 6.3" "more general",
  sga "1 X 1.8" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_isAlgClosed
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian_of_isAlgClosed f
    properHenselianFiniteEtaleEquivalence

end AlgebraicGeometry

end
