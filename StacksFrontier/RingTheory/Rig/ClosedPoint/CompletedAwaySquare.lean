module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeriesLocalization
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesMapComp

/-!
# Horizontal naturality of Stacks 0GGG's identification

Let `φ : A → B` be a homomorphism of commutative rings, let `I` be a finitely generated ideal of
`A`, let `f : A` and write `σ` for a set of variables.  Stacks 0GGG identifies the completed
principal localization of a restricted power series ring with the restricted power series ring
over the completed principal localization, and it does so for `A` at `f` and for `B` at `φ f`.
The fourth paragraph of the proof of Stacks 0GGR needs the square

```
A{σ}_{\{f\}} ⟶ B{σ}_{\{φ f\}}
    ↓                ↓
A_{\{f\}}{σ} ⟶ B_{\{φ f\}}{σ}
```

to commute, where the horizontal arrows are the completed principal localization of
`A{σ} → B{σ}` and the coefficientwise reduction along `A_{\{f\}} → B_{\{φ f\}}`, and the
vertical arrows are the two instances of that identification.  The source leaves this as
"details omitted".

On the image of `A{σ}` both routes are a three-fold coefficient reduction — along
`A → B → B[1/φ f] → B_{\{φ f\}}` and along `A → A[1/f] → A_{\{f\}} → B_{\{φ f\}}` — and the two
towers have the same composite `A → B_{\{φ f\}}`, because the map of completed principal
localizations commutes with the structure maps.  That image is dense, so `Rig.completedHom_ext`
lifts the agreement to the whole of `A{σ}_{\{f\}}`.

The coefficient ideals of the two spellings of `B_{\{φ f\}}{σ}` differ: the identification
delivers it extended from `B` through `B[1/φ f]`, whereas the coefficientwise reduction along
`A_{\{f\}} → B_{\{φ f\}}` delivers it extended from `A_{\{f\}}`.  Those two ideals are equal by
`Rig.map_completedAwayCoefficientIdeal_completedAwayMap`, and `RestrictedPowerSeries.congrEquiv`
of that equality is the last arrow of the lower route.

## Main results

* `Rig.restrictedPowerSeriesCompletedAwayEquiv_naturality`: the square commutes, for any arrow
  `A{σ}_{\{f\}} → B{σ}_{\{φ f\}}` commuting with the structure maps of the two completed
  principal localizations.

## References

* [Stacks Project, Tag 0GGG](https://stacks.math.columbia.edu/tag/0GGG)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace Rig

section

universe u

open RestrictedPowerSeries TopologicalRing

section Level

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **Level `n` of the bare-homomorphism coefficient reduction.**  It is reduction of the level
`n` coefficient polynomial along the induced map of coefficient quotients.  Stated for a bare
`φ : A →+* B` so that it can be rewritten with where no `Algebra A B` instance is in scope. -/
private theorem coefficientProjection_restrictedPowerSeriesMapOfRingHom (φ : A →+* B)
    (I : Ideal A) (σ : Type u) (n : ℕ) (x : RestrictedPowerSeries I σ) :
    coefficientProjection (I.map φ) σ n (restrictedPowerSeriesMapOfRingHom φ I σ x) =
      MvPolynomial.map
        (Ideal.quotientMap ((I.map φ) ^ n) φ
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))
        (coefficientProjection I σ n x) := rfl


/-- **Stacks 0GGG's identification sends a constant to the constant of its image.**  Composing
the structure map of `A{σ}_{\{f\}}` with the identification `A{σ}_{\{f\}} = A_{\{f\}}{σ}`
carries the constant series of `a : A` to the constant series of the image of `a` in
`A_{\{f\}}`. -/
public theorem completedAwayEquiv_coefficientRingHom (I : Ideal A) (hI : I.FG) (σ : Type u)
    (f : A) (a : A) :
    restrictedPowerSeriesCompletedAwayEquiv I hI σ f
        (algebraMap (RestrictedPowerSeries I σ)
          (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))
          (coefficientRingHom I σ a)) =
      coefficientRingHom (completedAwayCoefficientIdeal I f) σ
        (algebraMap A (CompletedAway I f) a) := by
  refine (DFunLike.congr_fun
    (restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap I hI σ f)
    (coefficientRingHom I σ a)).trans ?_
  have hstep1 : restrictedPowerSeriesMap (B := Localization.Away f) I σ
        (coefficientRingHom I σ a) =
      coefficientRingHom (I.map (algebraMap A (Localization.Away f))) σ
        (algebraMap A (Localization.Away f) a) :=
    restrictedPowerSeriesMap_coefficientRingHom I σ a
  have hstep2 := restrictedPowerSeriesMap_coefficientRingHom
    (B := CompletedAway I f) (I.map (algebraMap A (Localization.Away f))) σ
    (algebraMap A (Localization.Away f) a)
  have hstep3 : algebraMap (Localization.Away f) (CompletedAway I f)
        (algebraMap A (Localization.Away f) a) = algebraMap A (CompletedAway I f) a :=
    (IsScalarTower.algebraMap_apply A (Localization.Away f) (CompletedAway I f) a).symm
  rw [RingHom.comp_apply, hstep1, hstep2, hstep3]

end Level

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Both three-fold coefficient reductions are the reduction along `A → B_{\{φ f\}}`.**  The
upper-right route of the square, restricted to the image of `A{σ}`, reduces coefficients along
`A → B → B[1/φ f] → B_{\{φ f\}}`; the lower-left route reduces along
`A → A[1/f] → A_{\{f\}} → B_{\{φ f\}}`.  The two towers have the same composite, so at every
level both are the same map of coefficient quotients. -/
private theorem restrictedPowerSeriesMap_completedAway_square (I : Ideal A) (σ : Type u)
    (f : A) :
    (restrictedPowerSeriesMap
          (B := CompletedAway (I.map (algebraMap A B)) (algebraMap A B f))
          ((I.map (algebraMap A B)).map
            (algebraMap B (Localization.Away (algebraMap A B f)))) σ).comp
        ((restrictedPowerSeriesMap (B := Localization.Away (algebraMap A B f))
            (I.map (algebraMap A B)) σ).comp
          (restrictedPowerSeriesMap (B := B) I σ)) =
      (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap
            (algebraMap A B) I f) σ).toRingHom.comp
        ((restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
              (completedAwayCoefficientIdeal I f) σ).comp
          ((restrictedPowerSeriesMap (B := CompletedAway I f)
              (I.map (algebraMap A (Localization.Away f))) σ).comp
            (restrictedPowerSeriesMap (B := Localization.Away f) I σ))) := by
  let : Algebra (CompletedAway I f)
      (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)) :=
    (RingHom.completedAwayMap (algebraMap A B) I f).toAlgebra
  have hbase := RingHom.completedAwayMap_comp_base (algebraMap A B) I f
  refine RingHom.ext fun x => RestrictedPowerSeries.idealSystem_ext fun n => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    coefficientProjection_congrEquiv, coefficientProjection_restrictedPowerSeriesMapOfRingHom,
    coefficientProjection_restrictedPowerSeriesMap, congrLevelEquiv,
    MvPolynomial.mapEquiv_apply, MvPolynomial.map_map]
  refine congrArg (fun g => MvPolynomial.map g (coefficientProjection I σ n x)) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, coefficientQuotientMap, Ideal.quotientMap_mk,
    Ideal.quotEquivOfEq_mk, RingHom.coe_coe]
  rw [← IsScalarTower.algebraMap_apply B (Localization.Away (algebraMap A B f))
      (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)),
    ← IsScalarTower.algebraMap_apply A (Localization.Away f) (CompletedAway I f)]
  exact congrArg (Ideal.Quotient.mk _)
    (DFunLike.congr_fun (RingHom.completedAwayMap_comp_base (algebraMap A B) I f) a).symm

/-- **The square commutes on the image of `A{σ}`.**  Both routes restrict, on the image of the
structure map of `A{σ}_{\{f\}}`, to the three-fold coefficient reductions of
`Rig.restrictedPowerSeriesMap_completedAway_square`, by the defining property of Stacks 0GGG's
identification on the image of the restricted power series ring. -/
private theorem completedAwayEquiv_comp_algebraMap_square (I : Ideal A) (hI : I.FG)
    (σ : Type u) (f : A) :
    ((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B)) (hI.map (algebraMap A B)) σ
            (algebraMap A B f)).comp
        (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
          (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
            (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
      (restrictedPowerSeriesMap (B := B) I σ) =
    ((congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f)
            σ).toRingHom.comp
        ((restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
              (completedAwayCoefficientIdeal I f) σ).comp
          (restrictedPowerSeriesCompletedAwayEquiv I hI σ f))).comp
      (algebraMap (RestrictedPowerSeries I σ)
        (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) := by
  refine RingHom.ext fun x => ?_
  have hA := DFunLike.congr_fun
    (restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap I hI σ f) x
  have hB := DFunLike.congr_fun
    (restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) σ (algebraMap A B f)) (restrictedPowerSeriesMap (B := B) I σ x)
  have h0 := DFunLike.congr_fun (restrictedPowerSeriesMap_completedAway_square (B := B) I σ f) x
  exact hB.trans (h0.trans (congrArg (fun y =>
    congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f) σ
      (restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
        (completedAwayCoefficientIdeal I f) σ y)) hA.symm))

/-- **The image of the ideal of definition of `A{σ}_{\{f\}}` is the coefficient ideal.**  For
any map out of `A{σ}_{\{f\}}` whose restriction to `A{σ}` is the upper-right route of the
square, the ideal of definition of `A{σ}_{\{f\}}` maps onto the coefficient ideal of
`B_{\{φ f\}}{σ}`: the ideal of definition is extended from `A{σ}`, so its image depends only on
that restriction, and on a constant the route is the coefficient inclusion of `B_{\{φ f\}}`.
This is what makes both routes of the square continuous. -/
private theorem map_completedAwayCoefficientIdeal_of_comp_eq (I : Ideal A) (hI : I.FG)
    (σ : Type u) (f : A)
    (g : CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f) →+*
      RestrictedPowerSeries
        (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)) σ)
    (hg : g.comp (algebraMap (RestrictedPowerSeries I σ)
          (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) =
        ((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
              (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
            (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
              (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
                (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
          (restrictedPowerSeriesMap (B := B) I σ)) :
    (completedAwayCoefficientIdeal (coefficientIdeal I σ) (coefficientRingHom I σ f)).map g =
      coefficientIdeal
        (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)) σ := by
  have hsub : (((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
            (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
          (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
            (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
              (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
        (restrictedPowerSeriesMap (B := B) I σ)).comp (coefficientRingHom I σ) =
      (coefficientRingHom (completedAwayCoefficientIdeal (I.map (algebraMap A B))
            (algebraMap A B f)) σ).comp
        ((algebraMap B (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f))).comp
          (algebraMap A B)) := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [restrictedPowerSeriesMap_coefficientRingHom (B := B) I σ a]
    exact completedAwayEquiv_coefficientRingHom (I.map (algebraMap A B))
      (hI.map (algebraMap A B)) σ (algebraMap A B f) (algebraMap A B a)
  calc (completedAwayCoefficientIdeal (coefficientIdeal I σ) (coefficientRingHom I σ f)).map g
      = ((coefficientIdeal I σ).map (algebraMap (RestrictedPowerSeries I σ)
            (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)))).map g :=
        congrArg (Ideal.map g)
          (completedAwayCoefficientIdeal_eq (coefficientIdeal I σ) (coefficientRingHom I σ f))
    _ = (coefficientIdeal I σ).map (g.comp (algebraMap (RestrictedPowerSeries I σ)
            (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)))) :=
        Ideal.map_map _ _
    _ = (coefficientIdeal I σ).map
          (((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
                (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
              (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
                (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
                  (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
            (restrictedPowerSeriesMap (B := B) I σ)) :=
        congrArg (fun h => (coefficientIdeal I σ).map h) hg
    _ = I.map ((((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
                (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
              (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
                (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
                  (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
            (restrictedPowerSeriesMap (B := B) I σ)).comp (coefficientRingHom I σ)) :=
        Ideal.map_map _ _
    _ = I.map ((coefficientRingHom (completedAwayCoefficientIdeal (I.map (algebraMap A B))
              (algebraMap A B f)) σ).comp
          ((algebraMap B (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f))).comp
            (algebraMap A B))) := congrArg (fun h => I.map h) hsub
    _ = ((I.map (algebraMap A B)).map
            (algebraMap B (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)))).map
          (coefficientRingHom (completedAwayCoefficientIdeal (I.map (algebraMap A B))
            (algebraMap A B f)) σ) :=
        (Ideal.map_map _ _).symm.trans
          (congrArg (Ideal.map (coefficientRingHom (completedAwayCoefficientIdeal
            (I.map (algebraMap A B)) (algebraMap A B f)) σ)) (Ideal.map_map _ _).symm)
    _ = (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)).map
          (coefficientRingHom (completedAwayCoefficientIdeal (I.map (algebraMap A B))
            (algebraMap A B f)) σ) :=
        congrArg (Ideal.map (coefficientRingHom (completedAwayCoefficientIdeal
            (I.map (algebraMap A B)) (algebraMap A B f)) σ))
          (completedAwayCoefficientIdeal_eq (I.map (algebraMap A B)) (algebraMap A B f)).symm

/-- **Horizontal naturality of Stacks 0GGG's identification.**  Let `φ : A → B`, let `I` be a
finitely generated ideal of `A` and `f : A`, and let `Ψ : A{σ}_{\{f\}} → B{σ}_{\{φ f\}}` be any
ring homomorphism commuting with the structure maps of the two completed principal localizations
over `A{σ} → B{σ}`.  Then the square formed by `Ψ`, the coefficientwise reduction
`A_{\{f\}}{σ} → B_{\{φ f\}}{σ}` along the induced map `A_{\{f\}} → B_{\{φ f\}}` of completed
principal localizations, and the two instances of the identification of Stacks 0GGG commutes —
the coefficient ideal of the target being respelled by `RestrictedPowerSeries.congrEquiv`.

This is the compatibility the fourth paragraph of the proof of Stacks 0GGR needs in order to
transport a flatness statement about `A_{\{f\}}{σ} → B_{\{φ f\}}{σ}` to one about
`A{σ}_{\{f\}} → B{σ}_{\{φ f\}}`, and leaves as "details omitted". -/
public theorem restrictedPowerSeriesCompletedAwayEquiv_naturality (I : Ideal A) (hI : I.FG)
    (σ : Type u) (f : A)
    (Ψ : CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f) →+*
      CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
        (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))
    (hΨ : Ψ.comp (algebraMap (RestrictedPowerSeries I σ)
          (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) =
        (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
            (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
              (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f)))).comp
          (restrictedPowerSeriesMap (B := B) I σ)) :
    (restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp Ψ =
      (congrEquiv (map_completedAwayCoefficientIdeal_completedAwayMap (algebraMap A B) I f)
          σ).toRingHom.comp
        ((restrictedPowerSeriesMapOfRingHom (RingHom.completedAwayMap (algebraMap A B) I f)
            (completedAwayCoefficientIdeal I f) σ).comp
          (restrictedPowerSeriesCompletedAwayEquiv I hI σ f)) := by
  let : TopologicalSpace (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f)) :=
    (completedAwayCoefficientIdeal (coefficientIdeal I σ)
      (coefficientRingHom I σ f)).adicTopology
  let : T2Space (RestrictedPowerSeries
      (completedAwayCoefficientIdeal (I.map (algebraMap A B)) (algebraMap A B f)) σ) :=
    t2Space_restrictedPowerSeries _ σ
  have hJhat : (completedAwayCoefficientIdeal (I.map (algebraMap A B))
      (algebraMap A B f)).FG :=
    ((hI.map (algebraMap A B)).map
        (algebraMap B (Localization.Away (algebraMap A B f)))).map
      (algebraMap (Localization.Away (algebraMap A B f))
        (CompletedAway (I.map (algebraMap A B)) (algebraMap A B f)))
  have hTadic : IsAdic (coefficientIdeal (completedAwayCoefficientIdeal
      (I.map (algebraMap A B)) (algebraMap A B f)) σ) :=
    isAdic_coefficientIdeal _ hJhat σ
  have hdense : DenseRange (algebraMap (Localization.Away (coefficientRingHom I σ f))
      (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) :=
    denseRange_algebraMap_adicCompletion _
      ((hI.map (coefficientRingHom I σ)).map
        (algebraMap (RestrictedPowerSeries I σ)
          (Localization.Away (coefficientRingHom I σ f))))
  have hcont : ∀ g : CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f) →+*
        RestrictedPowerSeries (completedAwayCoefficientIdeal (I.map (algebraMap A B))
          (algebraMap A B f)) σ,
      g.comp (algebraMap (RestrictedPowerSeries I σ)
          (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) =
        ((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
              (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
            (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
              (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
                (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
          (restrictedPowerSeriesMap (B := B) I σ) → Continuous g := by
    intro g hg
    rw [hTadic]
    exact continuous_adic_of_map_le _ _ g
      (le_of_eq (map_completedAwayCoefficientIdeal_of_comp_eq I hI σ f g hg))
  have hleft : ((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
          (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp Ψ).comp
        (algebraMap (RestrictedPowerSeries I σ)
          (CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f))) =
      ((restrictedPowerSeriesCompletedAwayEquiv (I.map (algebraMap A B))
            (hI.map (algebraMap A B)) σ (algebraMap A B f)).comp
          (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
            (CompletedAway (coefficientIdeal (I.map (algebraMap A B)) σ)
              (coefficientRingHom (I.map (algebraMap A B)) σ (algebraMap A B f))))).comp
        (restrictedPowerSeriesMap (B := B) I σ) :=
    RingHom.ext fun x => congrArg (restrictedPowerSeriesCompletedAwayEquiv
      (I.map (algebraMap A B)) (hI.map (algebraMap A B)) σ (algebraMap A B f))
        (DFunLike.congr_fun hΨ x)
  have hright := (completedAwayEquiv_comp_algebraMap_square (B := B) I hI σ f).symm
  exact completedHom_ext (coefficientRingHom I σ f) hdense _ _ (hcont _ hleft)
    (hcont _ hright) (hleft.trans hright.symm)

end

end Rig

end
