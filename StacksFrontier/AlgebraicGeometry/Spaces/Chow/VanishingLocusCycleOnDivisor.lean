module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCyclePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GlobalSectionDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata

/-!
# The cycle of an effective Cartier divisor, read on the divisor itself

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module, let `s ∈ Γ(X, ℒ)` be
a global section and let `i : E → X` be the closed immersion of the vanishing locus `E = Z(s)`.

The cycle `[E]_{n-1}` has two readings: on `X`, where Stacks 0EQF identifies it with the Weil
divisor `div_ℒ(s)`, and on `E` itself, as the cycle of Stacks 0EE9 of the *whole* of `E` — the
closed subspace `⊤ ⊆ E` — which is the reading in the right-hand side `c₁(𝒩) ∩ [E]_{n-1}` of
Stacks 0ER9, a class in `CH_{n-2}(E)`.  The pushforward along `i` of the cycle formed on `E` is
`div_ℒ(s)` on `X`.

Likewise the intersection `E ∩ W` with an integral closed subspace `W ⊆ X` has two readings: on
`E`, where it is clause (1)(a) of the refined Gysin map of Stacks 0ER1, and on `W`, where it is
the zero scheme `Z(s|_W)` of the restricted section.  The two have the same pushforward to `X`,
namely the cycle of the intersection `E ⊓ W` formed in `X`.

## Main results

* `AlgebraicGeometry.Space.cycleClosedPushforward_topCycleCoeff_eq_zeroSchemeCycleCoeff`: the
  pushforward along `i : E → X` of the coefficient family of `[⊤]_k` formed on `E` is the
  coefficient family of `[Z(s)]_k` formed on `X`.
* `AlgebraicGeometry.Space.cycleClosedPushforward_topCycleCoeff_eq_sectionWeilDivisor`:
  the identification `i_*[E]_{n-1} = div_ℒ(s)` for a nonzero section of an invertible sheaf
  on a good integral algebraic space, by Stacks 0EQF.
* `AlgebraicGeometry.Space.preimageInfHom` and `AlgebraicGeometry.Space.preimageInfHom'`: the
  two inverse images `G'.preimage G.ι` and `G.preimage G'.ι` of subfunctors, each compared with
  the intersection `G ⊓ G'` by an isomorphism over the ambient functor.
* `cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace`:
  the two readings of `E ∩ W` give the same cycle on `X`. The cycle `[E ∩ W]_k` of
  Stacks 0EE9 formed on `E` — clause (1)(a) of Stacks 0ER1 — and the one formed on a closed
  subspace `W ⊆ X`, which by
  `AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme` is the zero scheme `Z(s|_W)`,
  have the same pushforward to `X`.

## Implementation notes

Both statements are about coefficient *families* rather than about elements of `Z_k`.  Forming
`[⊤]_k` on `E` as an element of `Z_k(E)` asks in addition for the δ-dimension bound
`dim_δ(E) ≤ k`, which at `k = n - 1` is the statement that the generic point of `X` does not lie
on `E`; that bound is not needed for the comparison.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections) (k : ℤ)

/-- **The cycle of the vanishing locus, formed on the vanishing locus, pushes forward to the
cycle formed on `X`.**  The whole of `E = Z(s)` is the top subfunctor of `E`, and the cycle
`[⊤]_k` of Stacks 0EE9 formed on `E` pushes forward along the closed immersion `i : E → X` to the
cycle `[Z(s)]_k` formed on `X`. -/
theorem cycleClosedPushforward_topCycleCoeff_eq_zeroSchemeCycleCoeff :
    cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L s).2.2
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s)
          (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
          (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
            (vanishingLocus D sX hX L s).2.1) k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor).toFunctor)) =
      zeroSchemeCycleCoeff D sX hX L s k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).1.toFunctor) :=
  cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D sX hX (vanishingLocus D sX hX L s).1
    (vanishingLocus D sX hX L s).2 (isGood_vanishingLocus D sX hX L s)
    (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
    (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
      (vanishingLocus D sX hX L s).2.1)
    (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2
    (Subfunctor.ι (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)) rfl k

/-- **`i_*[E]_{n-1} = div_ℒ(s)`.**  In Situation 0EDT let `X/B` be good and integral with
`n = dim_δ(X)`, let `ℒ` be invertible and let `s ∈ Γ(X, ℒ)` be a nonzero global section, with
`i : E → X` the closed immersion of `E = Z(s)`.  The pushforward along `i` of the coefficient
family of the cycle `[E]_{n-1}` of Stacks 0EE9 formed *on `E`* is the Weil divisor `div_ℒ(s)` of
Stacks 0EQE part (1) on `X`. -/
theorem cycleClosedPushforward_topCycleCoeff_eq_sectionWeilDivisor
    (hint : IsIntegralSpace D.site D.base D.base_mem X) (hL : IsInvertibleSheaf D sX hX L)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hs : s ≠ 0) :
    cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L s).2.2
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s)
          (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
          (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
            (vanishingLocus D sX hX L s).2.1) (n - 1)
          (canonicalGeometricPoint D.site D.base D.base_mem
            (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor).toFunctor)) =
      (sectionWeilDivisor D sX hX hint L hL hn
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs)).1 :=
  (cycleClosedPushforward_topCycleCoeff_eq_zeroSchemeCycleCoeff D sX hX L s (n - 1)).trans
    (congrArg Subtype.val
      (sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq.{u, u} D sX hX hint
        L hL hn hs).1).symm

/-! ### The intersection with the divisor, read on the divisor and on the subspace -/

section Inf

variable {C : Type*} [Category C] {F : C ⥤ Type*} (G G' : Subfunctor F)

/-- **The inverse image of `G'` along the inclusion of `G` is the intersection `G ⊓ G'`.**  A
section of `G` whose image in the ambient functor lies in `G'` is a section of `G ⊓ G'`, and this
is the resulting morphism of presheaves. -/
def preimageInfHom : (G'.preimage G.ι).toFunctor ⟶ (G ⊓ G').toFunctor where
  app _ := ↾fun x => ⟨x.1.1, x.1.2, x.2⟩
  naturality _ _ _ := rfl

/-- The comparison of `G'.preimage G.ι` with `G ⊓ G'` is an isomorphism. -/
instance : IsIso (preimageInfHom G G') := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro U
  rw [isIso_iff_bijective]
  exact Function.bijective_iff_has_inverse.2
    ⟨fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- The comparison of `G'.preimage G.ι` with `G ⊓ G'` is a morphism over the ambient functor. -/
theorem preimageInfHom_comp_ι :
    preimageInfHom G G' ≫ (G ⊓ G').ι = (G'.preimage G.ι).ι ≫ G.ι :=
  rfl

/-- The inverse image of `G` along the inclusion of `G'`, compared with the intersection
`G ⊓ G'` (not `G' ⊓ G`): `AlgebraicGeometry.Space.preimageInfHom` with the two subfunctors
exchanged. -/
def preimageInfHom' : (G.preimage G'.ι).toFunctor ⟶ (G ⊓ G').toFunctor where
  app _ := ↾fun x => ⟨x.1.1, x.2, x.1.2⟩
  naturality _ _ _ := rfl

/-- The comparison of `G.preimage G'.ι` with `G ⊓ G'` is an isomorphism. -/
instance : IsIso (preimageInfHom' G G') := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro U
  rw [isIso_iff_bijective]
  exact Function.bijective_iff_has_inverse.2
    ⟨fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩, fun _ => rfl, fun _ => rfl⟩

/-- The comparison of `G.preimage G'.ι` with `G ⊓ G'` is a morphism over the ambient functor. -/
theorem preimageInfHom'_comp_ι :
    preimageInfHom' G G' ≫ (G ⊓ G').ι = (G.preimage G'.ι).ι ≫ G'.ι :=
  rfl

end Inf

/-- **The two readings of the intersection `E ∩ W` give the same cycle on `X`.**  Let `E = Z(s)`
be the vanishing locus of a global section and let `W ⊆ X` be a closed subspace.  The
intersection may be read as a closed subspace of `E` — the inverse image of `W` along
`i : E → X`, which is clause (1)(a) of Stacks 0ER1 — or as a closed subspace of `W` — the inverse
image of `E` along `W → X`, which is the zero scheme `Z(s|_W)` of Stacks 0EQL.  The cycle
`[E ∩ W]_k` of Stacks 0EE9 formed in either and pushed forward to `X` is the same: both are the
cycle of the intersection `E ⊓ W` formed in `X`. -/
theorem cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace
    (W : ClosedSubspaces D.site D.base D.base_mem X) :
    cycleClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L s).2.2
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) (W.1.preimage (vanishingLocus D sX hX L s).1.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem
            (vanishingLocus D sX hX L s).1.ι W.1 hX.1
            (vanishingLocus D sX hX L s).2.1 W.2) k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (W.1.preimage (vanishingLocus D sX hX L s).1.ι).toFunctor)) =
      cycleClosedPushforward D hX.1 W.2.1 (D.isDecentSpace_of_isGood sX hX) W.2.2
        (cycleCoeffOfClosedSubspace D (W.1.ι ≫ sX) (isGood_closedSubspace D sX hX W)
          ((vanishingLocus D sX hX L s).1.preimage W.1.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem W.1.ι
            (vanishingLocus D sX hX L s).1 hX.1 W.2.1 (vanishingLocus D sX hX L s).2) k
          (canonicalGeometricPoint D.site D.base D.base_mem
            ((vanishingLocus D sX hX L s).1.preimage W.1.ι).toFunctor)) := by
  have hinf : IsClosedSubspace D.site D.base D.base_mem
      ((vanishingLocus D sX hX L s).1 ⊓ W.1) :=
    inf_isClosedSubspace D.site D.base D.base_mem X hX.1 (vanishingLocus D sX hX L s) W
  refine (cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D sX hX
    (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2
    (isGood_vanishingLocus D sX hX L s) (W.1.preimage (vanishingLocus D sX hX L s).1.ι) _
    ((vanishingLocus D sX hX L s).1 ⊓ W.1) hinf
    (preimageInfHom (vanishingLocus D sX hX L s).1 W.1)
    (preimageInfHom_comp_ι (vanishingLocus D sX hX L s).1 W.1) k).trans
    (cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D sX hX W.1 W.2
      (isGood_closedSubspace D sX hX W) ((vanishingLocus D sX hX L s).1.preimage W.1.ι) _
      ((vanishingLocus D sX hX L s).1 ⊓ W.1) hinf
      (preimageInfHom' (vanishingLocus D sX hX L s).1 W.1)
      (preimageInfHom'_comp_ι (vanishingLocus D sX hX L s).1 W.1) k).symm

end AlgebraicGeometry.Space

end
