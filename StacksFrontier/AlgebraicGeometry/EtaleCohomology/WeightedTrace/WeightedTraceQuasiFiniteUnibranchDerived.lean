module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceQuasiFiniteUnibranch
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived trace of a locally quasi-finite morphism over a geometrically unibranch base

Let `Y` be a geometrically unibranch and locally Noetherian scheme and let `f : X ⟶ Y` be locally
quasi-finite. Stacks 0GKJ says that `f` carries a weighting `w`, the generic separable degree of
`O_{X, x}^{sh}` over `O_{Y, f(x)}^{sh}` (Stacks 0F3E), and that Stacks 0GKG and 0GKH for `f` and
`w` then give trace maps

`Tr_{f, w, K} : f_! f^{-1}K ⟶ K`

functorial for `K` in `D(Y_étale, Λ)` and compatible with arbitrary base change.

This file states that example with every object of it constructed. The weighting is the one of
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch`; the
trace maps on abelian sheaves are those of Stacks 0GKG; and at coefficients in an arbitrary ring
`Λ` the `Λ`-linear inverse images `AlgebraicGeometry.SmallEtale.pullbackMod`, the two
comparisons `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMod` and
`AlgebraicGeometry.SmallEtale.inverseImageSquareMod` attached to a cartesian square, the trace
maps `AlgebraicGeometry.SmallEtale.weightedTraceMod` and the derived trace
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` are the constructions of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction`,
so nothing is quantified over beyond what the source quantifies over: the ring `Λ`, the object
`K`, the cartesian square, and the model of the derived categories.

## Main results

* `exists_weighting_derivedWeightedTraceMod_of_isGeometricallyUnibranch`, in the namespace
  `AlgebraicGeometry.SmallEtale` — **Stacks 0GKJ.**

## Implementation notes

**Nonnegative, not positive.** The source calls its weighting *positive*, but the lemma it cites,
Stacks 0F3E, gives `w : X → Z_{≥0}`, and strict positivity is false at these hypotheses:
`AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` exhibits the
closed immersion of the closed point `(2)` into `Spec ℤ`, locally quasi-finite over a normal
locally Noetherian base, with no positive weighting. The statement records `0 ≤ w x`; Stacks 0GKG
and 0GKH impose no sign condition, so the trace maps are unaffected.

**Which `w`.** The trace maps are attached to the weighting the example describes: the statement
restates the generic-separable-degree description of `w`, quantified over all compatible choices
of strict henselizations exactly as in
`AlgebraicGeometry.exists_weighting_genericSeparableDegree`, which determines `w` pointwise.

**The closing sentence.** That the restriction `w ∘ p` of `w` to a base change `X'` is a
weighting of `f' : X' ⟶ Y'`, with no hypothesis on `Y'`, is what the closing remark of the
example presupposes; it is part of both base-change clauses. The remark itself, that this
restriction has in general no natural interpretation in terms of `f'`, asserts nothing.

**Universes.** The base-change isomorphism of Stacks 0F5J, on which parts (2) and (3) of
Stacks 0GKH rest, is available at `AddCommGrpCat.{u + 1}`, so the sheaves of `Λ`-modules are
`ModuleSheaf.{u, u + 1, u}` with `Λ : Type u`, as in
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod_spec`. The derived categories are any
models `[HasDerivedCategory.{t} _]`.

## References

* [Stacks Project, Tag 0GKJ](https://stacks.math.columbia.edu/tag/0GKJ)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0F3E](https://stacks.math.columbia.edu/tag/0F3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u t

namespace AlgebraicGeometry.SmallEtale

/-- **The trace for a locally quasi-finite morphism over a geometrically unibranch base.** Let
`f : X ⟶ Y` be a locally quasi-finite morphism (locally of finite type with quasi-finite fibres) of
a big étale site, with `Y` geometrically unibranch and locally Noetherian. Then there is a
weighting `w : X → ℤ` of `f` such that:

* `w` is nonnegative and its value at `x` is the generic separable degree of the strict
  henselization of the local ring at `x` over that of the local ring at `f x` (Stacks 0F3E);
* **Stacks 0GKG for `(f, w)`:** every abelian sheaf `F` on `Y_étale` has exactly one trace map
  `Tr_{f, w, F} : f_! f^{-1}F ⟶ F` with the prescribed behaviour on geometric stalks;
* **Stacks 0GKH (1), (2):** these trace maps are functorial in `F` and compatible with arbitrary
  base change, the restriction `w ∘ p` along a base change being a weighting of `f'`;
* **the trace on `D(Y_étale, Λ)`:** for every ring `Λ` and every cartesian square
  `X' --p--> X`, `f' : X' ⟶ Y'`, `g : Y' ⟶ Y`, the trace map
  `Tr_{f, w, M} = weightedTraceMod` on sheaves of `Λ`-modules has the stalk behaviour of 0GKG and
  is the only morphism with it, and the derived trace
  `Tr_{f, w} = derivedWeightedTraceMod : f_! f^{-1} ⟶ id` of `D(Y_étale, Λ)` is functorial in `K`,
  restricts to the sheaf-level trace, and is compatible with the base change: the comparisons
  `g^{-1}f_! ≅ f'_!p^{-1}` (Stacks 0F5J) and `p^{-1}f^{-1} ≅ f'^{-1}g^{-1}` at `Λ`-coefficients
  carry the derived trace of `(f, w)`, whiskered by the derived `g^{-1}`, to the derived trace of
  `(f', w ∘ p)`.

All the `Λ`-linear functors, comparison isomorphisms and trace maps are the constructed ones of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerivedConstruction`;
the derived categories are arbitrary models. -/
@[stacks 0GKJ "the full example: a locally quasi-finite f (LocallyOfFiniteType together with \
Mathlib's LocallyQuasiFinite) onto a geometrically unibranch locally Noetherian Y carries a \
weighting w, the generic separable degree of the strict henselizations (0F3E), and for this w \
the trace maps of 0GKG exist and are unique on abelian sheaves, are functorial and compatible \
with arbitrary base change (0GKH (1), (2)), and for every ring Λ the constructed trace \
`AlgebraicGeometry.SmallEtale.derivedWeightedTraceMod` : f_!f^{-1}K ⟶ K on D(Y_étale, Λ) (any \
model of the derived categories) is functorial in K, restricts to the sheaf-level trace \
`AlgebraicGeometry.SmallEtale.weightedTraceMod`, and is compatible with arbitrary base change \
through the constructed comparisons `fShriekBaseChangeMod` and `inverseImageSquareMod`, w ∘ p \
being a weighting of every base change f'. Nothing is quantified over beyond Λ, K, the square \
and the derived-category model. The source's word *positive* is false as written: 0F3E gives \
Z_{≥0}, and `AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` \
is a counterexample (the closed point (2) of Spec ℤ), so w is stated nonnegative; 0GKG and 0GKH \
need no sign. Coefficients: ModuleSheaf.{u, u+1, u} with Λ : Type u, where 0F5J is available.",
  sga "4 XVII 6.2.5" "special case"]
public theorem exists_weighting_derivedWeightedTraceMod_of_isGeometricallyUnibranch
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsLocallyNoetherian Y.obj] (hY : IsGeometricallyUnibranch Y.obj) :
    ∃ (w : X.obj → ℤ) (hw : IsWeighting (B.inclusion.map f) w),
      (∀ x : X.obj, 0 ≤ w x) ∧
      (∀ (x : X.obj)
          (κY : Type u) [Field κY]
          [Algebra (maximalIdeal (Y.obj.presheaf.stalk (B.inclusion.map f x))).ResidueField κY]
          [IsSepClosure
            (maximalIdeal (Y.obj.presheaf.stalk (B.inclusion.map f x))).ResidueField κY]
          (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh]
          [Algebra (Y.obj.presheaf.stalk (B.inclusion.map f x)) Rsh]
          (_hRsh : Stacks.StrictHenselization.IsStrictHenselization
            (Y.obj.presheaf.stalk (B.inclusion.map f x)) κY Rsh)
          (κX : Type u) [Field κX]
          [Algebra (maximalIdeal (X.obj.presheaf.stalk x)).ResidueField κX]
          [IsSepClosure (maximalIdeal (X.obj.presheaf.stalk x)).ResidueField κX]
          (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh]
          [Algebra (X.obj.presheaf.stalk x) Ssh] [Algebra Rsh Ssh]
          [Algebra (Y.obj.presheaf.stalk (B.inclusion.map f x)) Ssh]
          [IsScalarTower (Y.obj.presheaf.stalk (B.inclusion.map f x)) Rsh Ssh]
          (_hSsh : Stacks.StrictHenselization.IsStrictHenselization
            (X.obj.presheaf.stalk x) κX Ssh)
          (_hcomp : algebraMap (Y.obj.presheaf.stalk (B.inclusion.map f x)) Ssh =
            (algebraMap (X.obj.presheaf.stalk x) Ssh).comp
              ((B.inclusion.map f).stalkMap x).hom)
          (q : Ideal Rsh) [q.IsPrime] (_hq : q ∈ minimalPrimes Rsh)
          (Kbar : Type u) [Field Kbar]
          [Algebra q.ResidueField Kbar] [IsAlgClosure q.ResidueField Kbar],
          w x = (Nat.card (AlgHom q.ResidueField
            (TensorProduct Rsh q.ResidueField Ssh) Kbar) : ℤ)) ∧
      -- Stacks 0GKG for `(f, w)`: the trace map on abelian sheaves exists and is unique
      (∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1},
        ∃! τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F,
          HasWeightedTraceStalks.{u, u + 1} B f w F τ) ∧
      -- Stacks 0GKH part (1): functoriality in the abelian sheaf
      (∀ (F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
          (φ : F ⟶ G)
          (τF : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F)
          (τG : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj G) ⟶ G),
          HasWeightedTraceStalks.{u, u + 1} B f w F τF →
          HasWeightedTraceStalks.{u, u + 1} B f w G τG →
            (fShriekFunctor.{u, u + 1} B f).map ((abPullback.{u, u + 1} B f).map φ) ≫ τG =
              τF ≫ φ) ∧
      -- Stacks 0GKH part (2): compatibility with arbitrary base change on abelian sheaves
      (∀ (X' Y' : B.Scheme) (p : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          (sq : IsPullback p f' f g)
          (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
          (τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F),
          HasWeightedTraceStalks.{u, u + 1} B f w F τ →
          letI := locallyOfFiniteType_of_isPullback B p f' f g sq
          letI := locallyQuasiFinite_of_isPullback B p f' f g sq
          IsWeighting (B.inclusion.map f') (w ∘ B.inclusion.map p) ∧
          HasWeightedTraceStalks.{u, u + 1} B f' (w ∘ B.inclusion.map p)
              ((abPullback.{u, u + 1} B g).obj F)
              ((fShriekFunctor.{u, u + 1} B f').map
                  ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F) ≫
                (fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
                  ((abPullback.{u, u + 1} B f).obj F) ≫
                (abPullback.{u, u + 1} B g).map τ) ∧
            ∀ τ' : (fShriekFunctor.{u, u + 1} B f').obj
                ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F)) ⟶
                  (abPullback.{u, u + 1} B g).obj F,
              HasWeightedTraceStalks.{u, u + 1} B f' (w ∘ B.inclusion.map p)
                  ((abPullback.{u, u + 1} B g).obj F) τ' →
                (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
                    ((abPullback.{u, u + 1} B f).obj F) ≫
                  (fShriekFunctor.{u, u + 1} B f').map
                    ((inverseImageSquareIso.{u} B p f' f g sq).hom.app F) ≫ τ' =
                  (abPullback.{u, u + 1} B g).map τ) ∧
      -- the trace `Tr_{f, w, K}` on `D(Y_étale, Λ)`, every piece constructed
      (∀ (Λ : Type u) [Ring Λ] (X' Y' : B.Scheme) (p : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          (sq : IsPullback p f' f g)
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y' Λ)],
        letI := locallyOfFiniteType_of_isPullback B p f' f g sq
        letI := locallyQuasiFinite_of_isPullback B p f' f g sq
        -- the trace map at `Λ`-coefficients has the stalk behaviour of 0GKG ...
        (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
            HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f (pullbackMod.{u, u + 1, u} B Λ f)
              (pullbackModForgetIso.{u, u + 1, u} B Λ f) w M
              (weightedTraceMod.{u, u + 1, u} B Λ f hw M)) ∧
          -- ... and is the only morphism with it
          (∀ (M : ModuleSheaf.{u, u + 1, u} B Y Λ)
              (σ : (fShriekMod.{u, u + 1, u} B Λ f).obj
                ((pullbackMod.{u, u + 1, u} B Λ f).obj M) ⟶ M),
              HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f (pullbackMod.{u, u + 1, u} B Λ f)
                (pullbackModForgetIso.{u, u + 1, u} B Λ f) w M σ →
                σ = weightedTraceMod.{u, u + 1, u} B Λ f hw M) ∧
          -- functoriality of `Tr_{f, w, K}` in `K`
          (∀ (K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) (ψ : K ⟶ K'),
              ((pullbackMod.{u, u + 1, u} B Λ f).mapDerivedCategory ⋙
                  (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
                  (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw).app K' =
                (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw).app K ≫ ψ) ∧
          -- the derived trace is the sheaf-level trace, derived
          (derivedWeightedTraceMod.{u, u + 1, t, u} B Λ f hw =
              (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
                  (pullbackMod.{u, u + 1, u} B Λ f) (fShriekMod.{u, u + 1, u} B Λ f)).inv ≫
                NatTrans.mapDerivedCategory
                  (weightedTraceModTrans.{u, u + 1, u} B Λ f hw) ≫
                (Functor.mapDerivedCategoryIdIso _).hom) ∧
          (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
              (weightedTraceModTrans.{u, u + 1, u} B Λ f hw).app M =
                weightedTraceMod.{u, u + 1, u} B Λ f hw M) ∧
          -- compatibility with arbitrary base change
          (NatTrans.mapDerivedCategory
                (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f
                  (pullbackMod.{u, u + 1, u} B Λ f) (pullbackMod.{u, u + 1, u} B Λ f')
                  (pullbackMod.{u, u + 1, u} B Λ g) (pullbackMod.{u, u + 1, u} B Λ p)
                  (fShriekBaseChangeMod.{u} B Λ p f' f g sq)
                  (inverseImageSquareMod.{u} B Λ p f' f g sq)).hom ≫
              (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                (pullbackMod.{u, u + 1, u} B Λ g)
                (pullbackMod.{u, u + 1, u} B Λ f' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
              Functor.whiskerLeft (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory
                (NatTrans.mapDerivedCategory
                  (weightedTraceModTrans.{u, u + 1, u} B Λ f'
                    (AlgebraicGeometry.IsWeighting.comp_of_isPullback hw
                      (sq.map B.inclusion)))) ≫
              (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                (pullbackMod.{u, u + 1, u} B Λ g)
                (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
            (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                (pullbackMod.{u, u + 1, u} B Λ f ⋙ fShriekMod.{u, u + 1, u} B Λ f)
                (pullbackMod.{u, u + 1, u} B Λ g)).hom ≫
              Functor.whiskerRight
                (NatTrans.mapDerivedCategory (weightedTraceModTrans.{u, u + 1, u} B Λ f hw))
                (pullbackMod.{u, u + 1, u} B Λ g).mapDerivedCategory ≫
              (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ))
                (pullbackMod.{u, u + 1, u} B Λ g)).inv) ∧
          AlgebraicGeometry.IsWeighting (B.inclusion.map f') (w ∘ B.inclusion.map p)) := by
  let : IsLocallyNoetherian (B.inclusion.obj Y) := inferInstanceAs (IsLocallyNoetherian Y.obj)
  obtain ⟨w, hw, hnonneg, -, hdesc⟩ :=
    exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch (B.inclusion.map f) hY
  refine ⟨w, hw, hnonneg, hdesc, existsUnique_hasWeightedTraceStalks.{u, u + 1} B f hw,
    fun _ _ φ _ _ hF hG => hasWeightedTraceStalks_naturality.{u, u + 1} B f w φ hF hG,
    fun X' Y' p f' g sq F τ hτ => ?_,
    fun Λ _ X' Y' p f' g sq _ _ _ _ => derivedWeightedTraceMod_spec.{u, t} B Λ p f' f g sq hw⟩
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  exact ⟨hw.comp_of_isPullback (sq.map B.inclusion),
    hasWeightedTraceStalks_baseChange.{u} B p f' f g sq w F hτ⟩

end AlgebraicGeometry.SmallEtale

end
