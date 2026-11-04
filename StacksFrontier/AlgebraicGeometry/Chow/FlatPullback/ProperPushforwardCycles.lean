module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProperDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules

/-!
# Flat pullback commutes with proper pushforward on cycles

Let `(S, δ)` be a base situation for Chow homology and let

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

be a fibre product diagram of schemes locally of finite type over `S`, with `f` proper and `g`
flat of relative dimension `r`. This file proves the cycle identity of Stacks 02RG with no
hypothesis:

`g^* f_* α = f'_* (g')^* α`  in  `Z_{k+r}(Y')`  for every `k`-cycle `α` on `X`.

## Main results

* `Stacks.Chow.flatPullback_properPushforward_cycles` — the cycle identity of Stacks 02RG.

## Implementation notes

`Stacks.Chow.flatPullback_properPushforward` proves the identity from three sheaf-level inputs,
quantified over the structure sheaves `𝒪_W` of the integral closed subschemes `W ⊆ X`: coherence
of `f_* 𝒪_W` and of `f'_* (g')^* 𝒪_W`, which is the first assertion of Stacks 02O5,
`Stacks.Chow.properDirectImageIsCoherent`, together with Stacks 02RE for the pullback; and
invertibility of the flat base change morphism `g^* f_* 𝒪_W ⟶ f'_* (g')^* 𝒪_W`, which is
Stacks 02KH in degree zero,
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, for the
quasi-compact and quasi-separated morphism `f` and the quasi-coherent module `𝒪_W`. This file
supplies those three inputs.

No `@[stacks 02RG]` attribute is attached here. This statement is needed by part (7) of
Tag 0H4P.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Stacks 02RG, the cycle identity.** In a fibre product diagram

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

of schemes locally of finite type over the base `C.S` of a Chow situation, with `f` proper and
`g` flat of relative dimension `r`, one has `g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')` for every
`k`-cycle `α` on `X`. -/
theorem flatPullback_properPushforward_cycles
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) := by
  have : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  refine flatPullback_properPushforward C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr k α
    (fun x => properDirectImageIsCoherent f _) (fun x => ?_) (fun x => ?_)
  · have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
    have := AlgebraicGeometry.isCoherent_pullback g'
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme))
    exact properDirectImageIsCoherent f' _
  · have := isQuasicoherent_of_isCoherent
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme))
    exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat hsq _

end Stacks.Chow

end
