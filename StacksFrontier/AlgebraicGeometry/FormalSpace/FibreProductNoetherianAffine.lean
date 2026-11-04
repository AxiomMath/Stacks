module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOfAffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductAffineTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterizationVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSiteChart
public import StacksFrontier.RingTheory.Rig.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsChartMaps

/-!
# The affine case of clause (5) of Stacks 0GBB

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an affine formal algebraic
space over `S` and let `t : U ⟶ V` and `s : W ⟶ V` be morphisms from affine formal algebraic
spaces with `U` and `W` Noetherian. If the morphism of reductions `U_red ⟶ V_red` induced by
`t` is locally of finite type, then `U ×_V W` is Noetherian. That is the affine case of
**clause (5) of Stacks 0GBB**, and it is the input the globalisation engine
`AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_pullback` consumes at
`P := IsNoetherian` and `Q := HasLocallyOfFiniteTypeReduction`.

The finite type condition is on the morphism `t`, not on the three spaces. Without it the
statement is false: for a field `k` with a residue point in the site and
`K = k(x₁, x₂, …)`, both `Spec k` and `Spec K` are Noetherian affine formal algebraic spaces —
their presenting rings are discrete, hence Noetherian, complete and adic with ideal of
definition `(0)` — while the presenting ring of `Spec K ×_{Spec k} Spec K` is `K ⊗_k K`, which
is not Noetherian. So the affine case of this clause has to see the map, which is why the
engine's affine input is relative to a property of it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasLocallyOfFiniteTypeReduction`: the hypothesis of clause (5)
  of Stacks 0GBB, that the induced morphism `X_red ⟶ Y_red` be locally of finite type.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnReductions_of_comp_of_isAffineFormal`:
  the condition passes from a composite `U ⟶ V' ⟶ V` to its first factor when `V'` is an
  affine formal algebraic space, in the shape of condition (4) of Stacks 0GC7.
* `AlgebraicGeometry.FormalSpace.isNoetherian_pullback_affine`: the affine case of clause (5).
  `AlgebraicGeometry.FormalSpace.affineChartFibreProductStable_isNoetherian`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes`, is it in the shape the engine
  consumes.

## Implementation notes

The proof is the source's. The base is shrunk to a countably indexed — hence, by
**Stacks 0AIK**, McQuillan — subobject `V'` through which both morphisms factor, by
`AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base`; clause (3) of **Stacks 0AN3**
then identifies the fibre product with the formal spectrum of `A ⊗̂_C A'`, where `C` presents
`V'` and `A`, `A'` present `U` and `W`; and clause (5) of **Stacks 0GB4**,
`TopologicalRing.completedTensorProduct_isNoetherianRing_of_isFiniteTypeOnReductions`, makes
that ring Noetherian as soon as one of `C ⟶ A` and `C ⟶ A'` has the property of
**Stacks 0GC2**. Adicness of `A ⊗̂_C A'` is clause (4) of Stacks 0GB4, whose finite generation
hypotheses are free here because `A` and `A'` are Noetherian.

Two steps carry the finite type condition from the morphism to the ring map.

The first is the passage from `t` to `t'`, the morphism into the shrunk base. This is **not** a
transport of the reduction along the monomorphism `V' ⟶ V`: a monomorphism need not have the
same reduction as its target — `AlgebraicGeometry.FormalSpace.isReduction_completionSheaf`
exhibits `X_{/T} ↪ X` with a strictly smaller one — and no such invariance is claimed. What is
used is **Stacks 0AQ6** in the case this library has it: the reduction of `V'` is an affine
formal algebraic space, being the sheaf of a reduced affine object of the site by
`AlgebraicGeometry.FormalSpace.exists_isReduction_reduced_affine_siteObject_of_isAffineFormal`,
so the universal properties of the two reductions factor the morphism of reductions of `t`
through that of `t'` and
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_isAffineFormal` cancels the
second factor. The monomorphism is not needed at all.

The second is the passage from the morphism `t'` to the ring map `algebraMap C A`. That is the
chart dictionary `AlgebraicGeometry.FormalSpace.chartPropertyIsFiniteTypeOnReductions`, the
affine computation of the proof of Stacks 0GC7, applied to the presentation that
`AlgebraicGeometry.FormalSpace.exists_isPresentingRing_completedTensorProduct` returns: it is
there that the continuous homomorphism realising `t'` is identified with `algebraMap C A`.

## References

* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AQ6](https://stacks.math.columbia.edu/tag/0AQ6)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduction of an affine formal algebraic space is an affine formal algebraic space.**
It is the sheaf of a reduced affine object of the site by the affine case of Stacks 0AIN, and
the sheaf of an affine object of the site is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_yonedaSheaf (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffineFormalAlgebraicSpace B S hS (yonedaSheaf B S hS T) :=
  isAffineFormalAlgebraicSpace_of_iso B S hS (yonedaSheafIsoSheafifiedYoneda B S hS T).symm
    (isAffineFormalAlgebraicSpace_sheafifiedYoneda' B S hS T hT)

/-- **Condition (4) of Stacks 0GC7 descends from a composite to its first factor when the
middle object is an affine formal algebraic space.** If the morphism of reductions induced by
`t' ≫ i : U ⟶ V' ⟶ V` is locally of finite type and `V'` is an affine formal algebraic space,
then `t'` is locally of finite type on reductions.

This is **Stacks 0AQ6** read on reductions, in the one case the library has it. The reduction
of `V'` is an affine formal algebraic space, so the universal property of that reduction lifts
`iU ≫ t'` to a morphism `U_red ⟶ V'_red`, the universal property of the reduction of `V` maps
`V'_red` to `V_red`, and the composite of the two agrees with the given morphism of reductions
of `t' ≫ i` because the inclusion of a reduction is a monomorphism. Cancelling the second
factor is `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_comp_of_isAffineFormal`.

Nothing is transported along `i`, which is not even assumed to be a monomorphism. Reduction is
*not* invariant along an arbitrary monomorphism —
`AlgebraicGeometry.FormalSpace.isReduction_completionSheaf` exhibits the completion
`X_{/T} ↪ X`, a monomorphism whose reduction is strictly smaller than that of `X`. -/
theorem isLocallyOfFiniteTypeOnReductions_of_comp_of_isAffineFormal
    {U V V' : FppfSheaf B S hS} (t' : U ⟶ V') (i : V' ⟶ V)
    (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (ht : (∃ (Xred Yred : FppfSheaf B S hS) (iX : Xred ⟶ _) (iY : Yred ⟶ _) (fred : Xred ⟶ Yred),
      IsReduction B S hS _ Xred iX ∧ IsReduction B S hS _ Yred iY ∧
        fred ≫ iY = iX ≫ (t' ≫ i) ∧ IsLocallyOfFiniteType B S hS fred)) :
    IsLocallyOfFiniteTypeOnReductions B S hS t' := by
  obtain ⟨Ured, Vred, iU, iV, tred, hiU, hiV, hcomp, hft⟩ := ht
  obtain ⟨T, g, -, hTaff, -, hiV'⟩ :=
    exists_isReduction_reduced_affine_siteObject_of_isAffineFormal B S hS V' hV'
  obtain ⟨t'red, ht'red, -⟩ := hiV'.universal Ured hiU.algebraic hiU.reduced (iU ≫ t')
  obtain ⟨c, hc, -⟩ := hiV.universal (yonedaSheaf B S hS T) hiV'.algebraic hiV'.reduced (g ≫ i)
  have _ : Mono iV := mono_of_isRepresentableThickening B S hS iV hiV.isRepresentableThickening
  have hfac : t'red ≫ c = tred := by
    refine (cancel_mono iV).1 ?_
    rw [Category.assoc, hc, ← Category.assoc, ht'red, hcomp, Category.assoc]
  refine (isLocallyOfFiniteTypeOnReductions_iff_isLocallyOfFiniteTypeULift B S hS hiU hiV'
    ht'red).2 (isLocallyOfFiniteTypeULift_of_isLocallyOfFiniteType B S hS hiU.algebraic
      hiV'.algebraic (IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t'red c
        (isAffineFormalAlgebraicSpace_yonedaSheaf B S hS T hTaff) ?_))
  rw [hfac]
  exact hft

/-- Finite type on reductions is a property of the ring map alone: the continuity witness it
carries is a proof of a proposition, so two of them agree. -/
private theorem isFiniteTypeOnReductions_congr {R₁ R₂ : Type u} [CommRing R₁]
    [TopologicalSpace R₁] [IsTopologicalRing R₁] [IsLinearTopology R₁ R₁] [CommRing R₂]
    [TopologicalSpace R₂] [IsTopologicalRing R₂] [IsLinearTopology R₂ R₂]
    {φ ψ : R₁ →+* R₂} (h : φ = ψ) {hφ : Continuous φ}
    {hψ : Continuous ψ} (hfin : Rig.IsFiniteTypeOnReductions φ hφ) :
    Rig.IsFiniteTypeOnReductions ψ hψ := by
  subst h
  exact hfin

/-- **The affine case of clause (5) of Stacks 0GBB.** The fibre product of two Noetherian
affine formal algebraic spaces over an affine formal algebraic space is Noetherian, provided
the morphism of reductions induced by the first of the two morphisms is locally of finite
type.

The base is shrunk to a countably indexed one, the fibre product is the formal spectrum of the
completed tensor product of the three presenting rings by clause (3) of **Stacks 0AN3**, and
that ring is Noetherian by clause (5) of **Stacks 0GB4** and adic by clause (4) — the finite
generation hypothesis of the latter being free, the presenting rings of `U` and `W` being
Noetherian. The hypothesis of clause (5) of Stacks 0GB4, the property of **Stacks 0GC2** for
`C ⟶ A`, is the finite type condition on `t` read through the chart dictionary of
**Stacks 0GC7**. -/
theorem isNoetherian_pullback_affine {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWaff : IsAffineFormalAlgebraicSpace B S hS W)
    (ht : (∃ (Xred Yred : FppfSheaf B S hS) (iX : Xred ⟶ _) (iY : Yred ⟶ _) (fred : Xred ⟶ Yred),
      IsReduction B S hS _ Xred iX ∧ IsReduction B S hS _ Yred iY ∧
        fred ≫ iY = iX ≫ t ∧ IsLocallyOfFiniteType B S hS fred))
    (hU : IsNoetherian B S hS U) (hW : IsNoetherian B S hS W) :
    IsNoetherian B S hS (pullback t s) := by
  classical
  obtain ⟨-, A, _, _, _, _, hA, hAnoeth, hAadic⟩ := id hU
  obtain ⟨-, A', _, _, _, _, hA', hA'noeth, hA'adic⟩ := id hW
  have hUc := isCountablyIndexed_of_isNoetherian B S hS hU
  have hWc := isCountablyIndexed_of_isNoetherian B S hS hW
  -- the base is shrunk to a countably indexed, hence McQuillan, subobject
  obtain ⟨V', i, t', s', hV'aff, hV'c, hmono, ht'eq, hs'eq⟩ :=
    exists_isCountablyIndexed_base B S hS t s hUc hVaff hWc
  have := hmono
  have hiso : pullback t' s' ≅ pullback t s := by
    have h := isPullback_comp_mono (IsPullback.of_hasPullback t' s') i
    rw [ht'eq, hs'eq] at h
    exact h.isoPullback
  -- the finite type condition passes to the morphism into the shrunk base, by Stacks 0AQ6
  have ht' : IsLocallyOfFiniteTypeOnReductions B S hS t' :=
    isLocallyOfFiniteTypeOnReductions_of_comp_of_isAffineFormal B S hS t' i hV'aff
      (by rw [ht'eq]; exact ht)
  -- clause (3) of Stacks 0AN3, with the realisation of `t'` by a continuous homomorphism
  obtain ⟨C, k1, k2, k3, k4, alg, alg', hCwa, DC, eV, cToA, hCcount, hcToA, hreal,
      hcont, hcont', hT⟩ :=
    exists_isPresentingRing_completedTensorProduct B S hS t' s' hV'aff hV'c
      (hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hUaff hUc)
      (hasSomeSurjectivePresentation_of_isCountablyIndexed B S hS hWaff hWc) hA hA'
  -- the chart dictionary reads the condition on `t'` as the property of Stacks 0GC2
  obtain ⟨_hcToAcont, hGC2⟩ :=
    (TopologicalRing.finiteTypeOnReductionsProperty_iff cToA.toRingHom).mp
    ((chartPropertyIsFiniteTypeOnReductions B S hS t' hUaff hV'aff hUc hV'c).1 ht'
      C A ⟨hCwa, hCcount⟩ (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdic' hAadic) hCwa DC
      hA.2.some.quotientSystem' hA.2.some.isoFormalSpectrum eV cToA hreal)
  -- clause (5) of Stacks 0GB4
  have hNoeth : IsNoetherianRing
      (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := A')) :=
    TopologicalRing.completedTensorProduct_isNoetherianRing_of_isFiniteTypeOnReductions
      hAadic.1 hA'adic.1 hcont hcont'
      (Or.inl (isFiniteTypeOnReductions_congr hcToA hGC2))
  -- clause (4) of Stacks 0GB4, the finite generation being free over a Noetherian ring
  obtain ⟨I, hIdef, -⟩ := hAadic.1
  obtain ⟨I', hI'def, -⟩ := hA'adic.1
  have hAdic : TopologicalRing.IsAdic
      (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := A')) :=
    TopologicalRing.completedTensorProduct_isAdic hcont hcont' hAadic.1
      ⟨I, hIdef, IsNoetherian.noetherian I⟩ hA'adic.1 ⟨I', hI'def, IsNoetherian.noetherian I'⟩
  have hTfinal : IsPresentingRing B S hS
      (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := A')) (pullback t s) :=
    isPresentingRing_of_iso B S hS _ hiso hT
  have hset : SatisfiesSetTheoreticCondition B S hS (pullback t s) :=
    (isAffineFormalAlgebraicSpace_pullback_of_isAffineFormalAlgebraicSpace B S hS t s hVaff
      hUaff hWaff).1
  exact ⟨(hasSomeSurjectivePresentation_iff_exists_isPresentingRing B S hS hset).2
      ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, hTfinal⟩,
    _, inferInstance, inferInstance, inferInstance, inferInstance, hTfinal, hNoeth, hAdic⟩

end AlgebraicGeometry.FormalSpace

end
