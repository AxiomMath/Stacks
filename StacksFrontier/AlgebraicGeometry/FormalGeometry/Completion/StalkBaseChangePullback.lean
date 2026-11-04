module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChange
public import StacksFrontier.RingTheory.Rig.FlatIsLocal

/-!
# Completions of local rings over an arbitrary completed base change square

Let `(A, 𝔪)` be a local ring with `𝔪` finitely generated, let `X` be a scheme over `Spec A` and
let `Y` sit in *any* cartesian square over `Spec A^ → Spec A`, where `A^` is the `𝔪`-adic
completion of `A`. At a point `y` of `Y` whose image `x` in `X` lies over the closed point of
`Spec A`, the local rings `𝒪_{X,x}` and `𝒪_{Y,y}` have isomorphic completions, compatibly with
the map on stalks. This is [Stacks Project, Tag 0BG5] for an arbitrary cartesian square, rather
than for the literal `pullback` of `AlgebraicGeometry.stalkMap_adicCompletion_isomorphism`.

## Main results

* `StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv`: an isomorphism of local rings
  induces an isomorphism of their completions at the maximal ideals, compatibly with the
  canonical maps into the completions.
* `AlgebraicGeometry.exists_adicCompletion_ringEquiv_stalkMap_of_isPullback`: Tag 0BG5 for an
  arbitrary cartesian square and an arbitrary pair of matched points.

## References

* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft

/-- An isomorphism of local rings carries the maximal ideal onto the maximal ideal. -/
private theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (IsLocalRing.maximalIdeal R).map e.toRingHom = IsLocalRing.maximalIdeal S := by
  have h₁ : IsLocalHom e.toRingHom := isLocalHom_of_leftInverse e.symm e.left_inv
  have h₂ : IsLocalHom e.symm.toRingHom := isLocalHom_of_leftInverse e e.right_inv
  refine le_antisymm (IsLocalRing.map_maximalIdeal_le e.toRingHom) ?_
  simpa [Ideal.map_map] using
    Ideal.map_mono (f := e.toRingHom) (IsLocalRing.map_maximalIdeal_le e.symm.toRingHom)

/-- An isomorphism of local rings induces an isomorphism of their completions at the maximal
ideals, compatibly with the canonical maps into the completions. -/
theorem exists_adicCompletion_ringEquiv_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    ∃ E : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, E (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by
  refine ⟨Rig.adicCompletionCongr e _ _ (map_maximalIdeal_of_ringEquiv e), fun r => ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  show AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n
      (adicCompletionMap e.toRingHom _ _ (map_maximalIdeal_of_ringEquiv e).le
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) = _
  rw [adicCompletionMap_evalₐ, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  simp

end StacksDraft

namespace AlgebraicGeometry

/-- Let `A` be a local ring whose maximal ideal is finitely generated, let `g : X ⟶ Spec A` be a
scheme over `A`, and let `π : Y ⟶ X`, `h : Y ⟶ Spec A^` exhibit `Y` as a fibre product of `X`
with `Spec A^` over `Spec A`, where `A^` is the completion of `A`. If `y : Y` maps to `x : X`
and `x` lies over the closed point of `Spec A`, then the completions of the local rings of `X`
at `x` and of `Y` at `y` are isomorphic, compatibly with the map on stalks
([Stacks Project, Tag 0BG5]). -/
theorem exists_adicCompletion_ringEquiv_stalkMap_of_isPullback
    (A : Type u) [CommRing A] [IsLocalRing A] (hfg : (IsLocalRing.maximalIdeal A).FG)
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of A)) (π : Y ⟶ X)
    (h : Y ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    (hsq : IsPullback π h g (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))))
    (y : Y) (x : X) (hx : π.base y = x)
    (hclosed : g.base x = (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
        ≃+* AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y),
      e.toRingHom.comp
          (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x))) =
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y))).comp
          ((X.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ π.stalkMap y).hom := by
  have hfst := hsq.isoPullback_hom_fst
  have hq : (pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).base
      (hsq.isoPullback.hom.base y) = π.base y :=
    congrArg (fun m : Y ⟶ X => m.base y) hfst
  have hqx : (pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).base
      (hsq.isoPullback.hom.base y) = x := hq.trans hx
  have hstalk : π.stalkMap y =
      (X.presheaf.stalkCongr (Inseparable.of_eq hq.symm)).hom ≫
        ((pullback.fst g (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).stalkMap
            (hsq.isoPullback.hom.base y) ≫ hsq.isoPullback.hom.stalkMap y) := by
    rw [Scheme.Hom.stalkMap_congr_hom π (hsq.isoPullback.hom ≫ pullback.fst g _) hfst.symm y,
      Scheme.Hom.stalkMap_comp]
    rfl
  have hclosed' : g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).base
      (hsq.isoPullback.hom.base y)) =
      (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A) := by
    rwa [hqx]
  obtain ⟨e₀, he₀⟩ := stalkMap_adicCompletion_isomorphism A hfg X g
    (hsq.isoPullback.hom.base y) hclosed'
  obtain ⟨E₁, hE₁⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv
    (X.presheaf.stalkCongr (Inseparable.of_eq hqx.symm)).commRingCatIsoToRingEquiv
  obtain ⟨E₃, hE₃⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv
    (asIso (hsq.isoPullback.hom.stalkMap y)).commRingCatIsoToRingEquiv
  have hmor : (X.presheaf.stalkCongr (Inseparable.of_eq hqx.symm)).hom ≫
      ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).stalkMap
          (hsq.isoPullback.hom.base y) ≫ hsq.isoPullback.hom.stalkMap y) =
      (X.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ π.stalkMap y := by
    have hcongr : (X.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq hq.symm)).hom =
        (X.presheaf.stalkCongr (Inseparable.of_eq hqx.symm)).hom := by
      show X.presheaf.stalkSpecializes (Inseparable.of_eq hx.symm).ge ≫
          X.presheaf.stalkSpecializes (Inseparable.of_eq hq.symm).ge =
        X.presheaf.stalkSpecializes (Inseparable.of_eq hqx.symm).ge
      exact TopCat.Presheaf.stalkSpecializes_comp X.presheaf _ _
    rw [hstalk, ← hcongr, Category.assoc]
  have he₀' := RingHom.ext_iff.mp he₀
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at he₀'
  refine ⟨E₁.trans (e₀.trans E₃), ?_⟩
  rw [← hmor]
  refine RingHom.ext fun r => ?_
  show E₃ (e₀ (E₁ (algebraMap _ _ r))) = _
  rw [hE₁, he₀', hE₃]
  rfl

end AlgebraicGeometry

end
