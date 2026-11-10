module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# A rational equivalence carried by a closed subspace descends to it

In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace and
let `β ∈ Z_k(Y)`.  Pushing forward loses information:
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_cycleGroupClosedPushforward` sends a
rational equivalence on `Y` to one on `X`, and the converse is false — a cycle on `Y` whose
pushforward is rationally equivalent to zero on `X` need not be rationally equivalent to zero on
`Y`, the presenting family on `X` being free to leave `|Y|`.

**It is not false once the presenting family is required to stay inside `|Y|`.**  That is
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin` at the carrier `|Y|`, and this file
proves that at that carrier the pushforward reflects rational equivalence:

`i_*β ∼_rat 0 within |Y|`  implies  `β ∼_rat 0`.

The reason is that an *integral* closed subspace `W ⊆ X` with `|W| ⊆ |Y|` is the image of an
integral closed subspace of `Y`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`), canonically identified
with it (`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`), so the whole
presenting family may be read on `Y`; a principal divisor stays one under that identification
(`AlgebraicGeometry.Space.isPrincipalDivisorCycle_cycleGroupClosedPushforward_of_iso`), and the
sum of Stacks 0EQ6 part (1) over the family read on `Y` pushes forward to the sum over the
original family, so it is `i_*β`.  Pushforward along a closed immersion is injective on
cycles, so it *is* `β`.

This is the last step of the proof of Stacks 0ER9, where the two cycles representing
`i^*div_𝒩(t)` and `c₁(𝒩) ∩ [D]_{n-1}` differ, after pushforward to `X`, by the cycle of the key
formula of Stacks 0EQV, which
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum` exhibits as
rationally equivalent to zero within `|D|`; the source's "thus we get a rational equivalence
between our specific cycles ... on `D`" is exactly the descent proved here.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward_id_eq_self`: the image of an
  integral closed subspace along the identity is itself.
* `AlgebraicGeometry.Space.cycleClosedPushforward_id_eq_self`: pushforward of coefficient
  families along the identity is the identity.
* `AlgebraicGeometry.Space.cycleClosedPushforward_hom_comp_inv_eq_self`: pushing a coefficient
  family forward along an isomorphism and back is the identity.
* `AlgebraicGeometry.Space.exists_isPrincipalDivisorCycle_cycleClosedPushforward_pushforward`: an
  integral closed subspace `V ⊆ Y` and a principal divisor `c ∈ Z_k(i(V))` on its image in `X`
  come from a principal divisor on `V` itself, with the same pushforward to `X`.
* `Space.isRationallyEquivalentToZero_of_isRationallyEquivalentToZeroWithin_closedPushforward`:
  **the descent.**  A cycle on a closed subspace whose pushforward is rationally equivalent to
  zero within the point set of that subspace is rationally equivalent to zero.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Pushforward along an identity and along an isomorphism -/

section Identity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of an integral closed subspace along the identity is itself.**  An integral
closed subspace is determined by its point set, and the map on points of the identity is the
identity. -/
theorem IntegralClosedSubspace.pushforward_id_eq_self (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (hid : IsClosedImmersion B S hS (𝟙 X))
    (Z : IntegralClosedSubspace B S hS X) :
    IntegralClosedSubspace.pushforward B S hS hX hX hXdec hid Z = Z := by
  refine (eq_integralClosedSubspaceOfPoints B S hS hX hXdec Z
    (IntegralClosedSubspace.imagePoints B S hS hX hX hid Z) ?_).symm
  change subspacePointSet B S hS X Z.subspace =
    pointsMap B S hS X (𝟙 X) '' subspacePointSet B S hS X Z.subspace
  rw [pointsMap_id, Set.image_id]

end Identity

section Transport

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Pushforward of coefficient families along the identity is the identity.** -/
theorem cycleClosedPushforward_id_eq_self
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hid : IsClosedImmersion D.site D.base D.base_mem (𝟙 X))
    (β : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    cycleClosedPushforward D hX hX hXdec hid β = β := by
  funext Z
  have h := cycleClosedPushforward_apply_pushforward D hX hX hXdec hid β Z
  rwa [IntegralClosedSubspace.pushforward_id_eq_self D.site D.base D.base_mem hX hXdec hid Z] at h

/-- **Pushing a coefficient family forward along an isomorphism and back is the identity.**  The
two pushforwards compose to the pushforward along `e.inv ≫ e.hom = 𝟙`, which is the identity. -/
theorem cycleClosedPushforward_hom_comp_inv_eq_self
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y) (e : Y ≅ X)
    (β : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    cycleClosedPushforward D hX hY hXdec
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (cycleClosedPushforward D hY hX hYdec
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.inv) β) = β := by
  rw [← cycleClosedPushforward_comp D hX hY hX hXdec hYdec
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.inv)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) β,
    cycleClosedPushforward_congr D hX hX hXdec
      (isClosedImmersion_comp D.site D.base D.base_mem e.inv e.hom
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.inv)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom))
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X)) e.inv_hom_id β,
    cycleClosedPushforward_id_eq_self D hX hXdec _ β]

end Transport

/-! ### The descent -/

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hY in
/-- **A principal divisor on the image of an integral closed subspace of `Y` descends to that
subspace.**  For `Y ⊆ X` a closed subspace of a good algebraic space, `V ⊆ Y` an integral closed
subspace and `c ∈ Z_k(i(V))` a principal divisor on the image of `V` in `X`, there is a principal
divisor on `V` itself whose pushforward to `X` — through `Y` — is the pushforward of `c`.

The two subspaces are identified by
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`, which is an isomorphism of good
integral algebraic spaces over the base, and a principal divisor is carried by such an
isomorphism
(`AlgebraicGeometry.Space.isPrincipalDivisorCycle_cycleGroupClosedPushforward_of_iso`).  The two
pushforwards agree because both are the pushforward of `c` along the inclusion of `i(V)` into
`X`, by `AlgebraicGeometry.Space.cycleClosedPushforward_comp` and the factorization
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp`. -/
theorem exists_isPrincipalDivisorCycle_cycleClosedPushforward_pushforward (k : ℤ)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (c : CycleGroup D ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycle D
      ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX) k c) :
    ∃ c' : CycleGroup D (V.subspace.ι ≫ Y.ι ≫ sX) k,
      IsPrincipalDivisorCycle D (V.subspace.ι ≫ Y.ι ≫ sX) k c' ∧
        cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
            (integralClosedSubspacePushforward D (Y.ι ≫ sX)
              (isGood_ι_of_isClosedSubspace D sX hX Y hY) V k c').1 =
          (integralClosedSubspacePushforward D sX hX
            (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
              (D.isDecentSpace_of_isGood sX hX) hY.2 V) k c).1 := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hVg : D.IsGood (V.subspace.ι ≫ Y.ι ≫ sX) :=
    isGood_integralClosedSubspace D (Y.ι ≫ sX) hYgood V
  have hV'g : D.IsGood ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX) :=
    isGood_integralClosedSubspace D sX hX _
  have hcomp : (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).symm.hom ≫ (V.subspace.ι ≫ Y.ι ≫ sX) =
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX := by
    rw [Iso.symm_hom, show V.subspace.ι ≫ Y.ι ≫ sX = (V.subspace.ι ≫ Y.ι) ≫ sX from
        (Category.assoc _ _ _).symm, ← Category.assoc,
      IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp]
  refine ⟨cycleGroupClosedPushforward D hVg.1 hV'g.1 (isDecentSpace_of_isGood D _ hVg)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem
        (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 V).symm.hom)
      _ hVg.2.2 _ hcomp k c,
    isPrincipalDivisorCycle_cycleGroupClosedPushforward_of_iso D _ hV'g _ hVg
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).isIntegralSpace V.isIntegralSpace _ hcomp k hc,
    ?_⟩
  refine Eq.trans (cycleClosedPushforward_comp D hX.1 hY.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood)
    V.isClosedSubspace.2 hY.2 _).symm ?_
  refine Eq.trans (cycleClosedPushforward_comp D hX.1 V.isClosedSubspace.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) (isDecentSpace_of_isGood D _ hVg)
    (isClosedImmersion_of_isIso D.site D.base D.base_mem
      (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).symm.hom)
    (isClosedImmersion_comp D.site D.base D.base_mem V.subspace.ι Y.ι
      V.isClosedSubspace.2 hY.2) c.1).symm ?_
  exact cycleClosedPushforward_congr D hX.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) _ _
    (IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V) c.1

include hY in
/-- **A rational equivalence carried by a closed subspace descends to it.**  In Situation 0EDT
let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace and let `β ∈ Z_k(Y)`.
If the pushforward `i_*β` is rationally equivalent to zero on `X` **within `|Y|`** — that is, if
the family of integral closed subspaces presenting the rational equivalence can be taken inside
`|Y|` — then `β` is rationally equivalent to zero on `Y`.

Each member `W_j` of the presenting family is integral with `|W_j| ⊆ |Y|`, hence is the image of
an integral closed subspace `V_j ⊆ Y`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`); its δ-dimension is
unchanged (`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward`), the
family `{|V_j|}` is locally finite because it is the preimage of `{|W_j|}` under the closed
embedding on points, and the summand on `W_j` descends to a principal divisor on `V_j` by
`AlgebraicGeometry.Space.exists_isPrincipalDivisorCycle_cycleClosedPushforward_pushforward`.  The
sum of Stacks 0EQ6 part (1) over the descended family pushes forward to the original sum, which
is `i_*β`, and pushforward along a closed immersion is injective on cycles.

This is the closing step of the proof of Stacks 0ER9: the rational equivalence the key formula of
Stacks 0EQV provides lives, by
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_keyFormulaDivisorSum`, inside the
effective Cartier divisor, and that is what lets the identity be read in `CH_{n-2}(D)` rather
than only in `CH_{n-2}(X)`. -/
theorem isRationallyEquivalentToZero_of_isRationallyEquivalentToZeroWithin_closedPushforward
    (k : ℤ) {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZeroWithin.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β)
      (subspacePointSet D.site D.base D.base_mem X Y)) :
    IsRationallyEquivalentToZero.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1 hY.2
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := hβ
  have hex : ∀ j, ∃ V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V = W j := fun j =>
    IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood) hY.2
      (W j) (hsub j)
  choose V hV using hex
  have hWeq : (fun j => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)) = W := funext hV
  subst hWeq
  have hVfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace := by
    have hpre : ∀ j, subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace =
        pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X
            (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
              (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)).subspace := by
      intro j
      rw [IntegralClosedSubspace.subspacePointSet_pushforward,
        Set.preimage_image_eq _ hemb.injective]
    refine LocallyFinite.subset ?_ fun j => (hpre j).subset
    exact hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem Y.ι)
  have hdim' : ∀ j, deltaDimension D (Y.ι ≫ sX) (V j) = k + 1 := by
    intro j
    rw [← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)]
    exact hdim j
  choose c' hprin' hpush using fun j =>
    exists_isPrincipalDivisorCycle_cycleClosedPushforward_pushforward D sX hX Y hY k (V j) (c j)
      (hprin j)
  refine ⟨J, V, hVfin, c', hdim', hprin', ?_⟩
  refine injective_cycleGroupClosedPushforward D hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2 (Y.ι ≫ sX) rfl k ?_
  rw [hsum]
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleFamilySum_apply]
  have hterm : ∀ j : J, (integralClosedSubspacePushforward D sX hX
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)) k (c j)).1 T =
      cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (integralClosedSubspacePushforward D (Y.ι ≫ sX) hYgood (V j) k (c' j)).1 T := fun j =>
    (congrFun (hpush j) T).symm
  rw [finsum_congr hterm]
  change _ = cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
    (cycleFamilySum D (Y.ι ≫ sX) hYgood V hVfin k c').1 T
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    refine finsum_congr fun j => ?_
    rw [cycleClosedPushforward_apply_pushforward]
  · have hz := fun f => cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 f T
      fun T0 hT0 => hT ⟨T0, hT0⟩
    rw [hz]
    exact finsum_eq_zero_of_forall_eq_zero fun j => hz _

end Descent

end AlgebraicGeometry.Space

end
