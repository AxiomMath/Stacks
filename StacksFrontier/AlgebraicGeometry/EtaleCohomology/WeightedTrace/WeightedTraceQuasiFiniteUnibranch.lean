module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceLocallyQuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace maps of a locally quasi-finite morphism over a geometrically unibranch base

Let `Y` be a geometrically unibranch and locally Noetherian scheme — a normal variety, say — and
let `f : X ⟶ Y` be locally quasi-finite. Stacks 0GKJ makes two assertions about this situation.
The first is that `f` carries a weighting `w`, whose value at `x` is the generic separable degree
of `O_{X, x}^{sh}` over `O_{Y, f(x)}^{sh}`; that is
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceLocallyQuasiFinite`.
The second is the one this file states: *thus by Lemmas 0GKG and 0GKH for `f` and `w` we obtain
trace maps*

`Tr_{f, w, K} : f_! f^{-1}K ⟶ K`

*functorial for `K` in `D(Y_étale, Λ)` and compatible with arbitrary base change.*

The trace maps are those of Stacks 0GKG and Stacks 0GKH, applied to this weighting: the trace
map `Tr_{f, w, F}` on abelian sheaves exists and is unique (Stacks 0GKG), it is functorial in
`F` (Stacks 0GKH part (1)), it is compatible with arbitrary base change (part (2)), and at
coefficients in a ring `Λ` it induces on `D(Y_étale, Λ)` a trace `Tr_{f, w, K}` which is
functorial in `K`, restricts to the sheaf-level trace, and is compatible with arbitrary base
change (part (3)). The weighting is nonnegative, `0 ≤ w x`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_weighting_weightedTrace_of_isGeometricallyUnibranch` —
  **the second assertion of Stacks 0GKJ**, together with the description of `w` given by the
  first.
* `AlgebraicGeometry.SmallEtale.exists_weighting_weightedTrace_sheaf_of_isGeometricallyUnibranch`
  — the sheaf-level half alone, at an arbitrary coefficient universe rather than the one the
  derived half requires, and
  `AlgebraicGeometry.SmallEtale.exists_weighting_weightedTrace_sheaf_of_isNormal` for a normal
  locally Noetherian base.

## References

* [Stacks Project, Tag 0GKJ](https://stacks.math.columbia.edu/tag/0GKJ)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0F3E](https://stacks.math.columbia.edu/tag/0F3E)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v t

namespace AlgebraicGeometry.SmallEtale

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The trace maps of a locally quasi-finite morphism over a geometrically unibranch locally
Noetherian base.** Let `f : X ⟶ Y` be a locally
quasi-finite morphism of a big étale site, locally of finite type, with `Y` geometrically
unibranch and locally Noetherian. Then there is an integer-valued function `w` on `X` such that:

* `w` is a weighting of `f`, it is nonnegative, and its value at `x` is the generic separable
  degree of the strict henselization of the local ring at `x` over the strict henselization of
  the local ring at `f x`;
* **Stacks 0GKG for `(f, w)`:** for every abelian sheaf `F` on the small étale site of `Y` there
  is exactly one trace map `Tr_{f, w, F} : f_! f^{-1}F ⟶ F` with the behaviour on geometric
  stalks that lemma prescribes, namely the weighted sum `(a_x̄)_x̄ ↦ ∑_x̄ w(x̄) · a_x̄` over the
  geometric fibre;
* **Stacks 0GKH part (1):** those trace maps are functorial in `F`;
* **Stacks 0GKH part (2):** they are compatible with arbitrary base change — for a cartesian
  square with horizontal morphisms `p : X' ⟶ X`, `g : Y' ⟶ Y`, the restriction `w ∘ p` is a
  weighting of `f'` (with nothing assumed about `Y'`), the base change along `g` of a trace map
  for `(f, w)` is a trace map for `(f', w ∘ p)`, and the square formed by the base-change
  isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J, the comparison
  `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images, and the two trace maps
  commutes;
* **Stacks 0GKH part (3):** given a ring `Λ`, the trace maps induce on unbounded derived
  categories a natural transformation `f_! f^{-1} ⟶ id` of `D(Y_étale, Λ)`, whose component at
  `K` is `Tr_{f, w, K} : f_! f^{-1}K ⟶ K`; it is functorial in `K`, it restricts to the
  sheaf-level trace, and it is compatible with arbitrary base change.

The last clause quantifies over the `Λ`-linear inverse images along the four morphisms of the
square and the two comparisons attached to it, each presented as a lift of its abelian
counterpart, and over the families of `Λ`-linear trace maps characterised on geometric
stalks. -/
@[stacks 0GKJ "the example in the generality of arbitrary Λ-linear lifts, of which the form \
with every lift, comparison and trace family constructed, the faithful registration of 0GKJ, \
is `exists_weighting_derivedWeightedTraceMod_of_isGeometricallyUnibranch` in the namespace \
`AlgebraicGeometry.SmallEtale`: for the nonnegative generic-separable-degree weighting w of \
0F3E, 0GKG and all three parts of 0GKH hold, the derived clause for every choice of Λ-linear \
inverse images, comparisons and trace families compatible with the abelian ones. The source's \
word *positive* is a slip for *nonnegative*: 0F3E, the \
lemma 0GKJ cites, gives Z_{≥0}, and \
`AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` exhibits a \
morphism at these hypotheses with no positive weighting; 0GKG and 0GKH impose no sign condition \
on w, so this costs the trace maps nothing. The trace maps enter through the behaviour on \
geometric stalks by which 0GKG characterises them, whose uniqueness half is one of the clauses, \
and the Λ-linear inverse images and the comparisons attached to the cartesian square are \
quantified over as lifts of the abelian ones exactly as in \
`AlgebraicGeometry.SmallEtale.derivedWeightedTrace_spec_of_lifts`. The coefficient universe is \
AddCommGrpCat.{u+1} with ModuleSheaf.{u, u+1, u} and Λ : Type u, which is where 0F5J and hence \
parts (2) and (3) live. The first assertion on its own is \
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch`.",
  sga "4 XVII 6.2.5" "special case"]
public theorem exists_weighting_weightedTrace_of_isGeometricallyUnibranch
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsLocallyNoetherian Y.obj] (hY : IsGeometricallyUnibranch Y.obj) :
    ∃ w : X.obj → ℤ,
      -- the weighting of the first assertion, which the trace maps below belong to
      IsWeighting (B.inclusion.map f) w ∧
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
      -- Stacks 0GKG for `(f, w)`: the trace map exists and is unique
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
      -- Stacks 0GKH part (2): compatibility with arbitrary base change
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
      -- Stacks 0GKH part (3): the trace on `D(Y_étale, Λ)`
      (∀ (Λ : Type u) [Ring Λ] (X' Y' : B.Scheme) (p : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          (sq : IsPullback p f' f g),
        letI := locallyOfFiniteType_of_isPullback B p f' f g sq
        letI := locallyQuasiFinite_of_isPullback B p f' f g sq
        ∀ (modPullF : ModuleSheaf.{u, u + 1, u} B Y Λ ⥤ ModuleSheaf.{u, u + 1, u} B X Λ)
          (hpullF : modPullF ⋙ forgetModuleSheaf.{u, u + 1, u} B X Λ ≅
            forgetModuleSheaf.{u, u + 1, u} B Y Λ ⋙ abPullback.{u, u + 1} B f)
          (modPullF' : ModuleSheaf.{u, u + 1, u} B Y' Λ ⥤ ModuleSheaf.{u, u + 1, u} B X' Λ)
          (hpullF' : modPullF' ⋙ forgetModuleSheaf.{u, u + 1, u} B X' Λ ≅
            forgetModuleSheaf.{u, u + 1, u} B Y' Λ ⋙ abPullback.{u, u + 1} B f')
          (modPullG : ModuleSheaf.{u, u + 1, u} B Y Λ ⥤ ModuleSheaf.{u, u + 1, u} B Y' Λ)
          (hpullG : modPullG ⋙ forgetModuleSheaf.{u, u + 1, u} B Y' Λ ≅
            forgetModuleSheaf.{u, u + 1, u} B Y Λ ⋙ abPullback.{u, u + 1} B g)
          (modPullP : ModuleSheaf.{u, u + 1, u} B X Λ ⥤ ModuleSheaf.{u, u + 1, u} B X' Λ)
          (hpullP : modPullP ⋙ forgetModuleSheaf.{u, u + 1, u} B X' Λ ≅
            forgetModuleSheaf.{u, u + 1, u} B X Λ ⋙ abPullback.{u, u + 1} B p)
          (bcMod : fShriekMod.{u, u + 1, u} B Λ f ⋙ modPullG ≅
            modPullP ⋙ fShriekMod.{u, u + 1, u} B Λ f')
          (epsMod : modPullF ⋙ modPullP ≅ modPullG ⋙ modPullF')
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B X' Λ)]
          [HasDerivedCategory.{t} (ModuleSheaf.{u, u + 1, u} B Y' Λ)],
          (∀ n : ModuleSheaf.{u, u + 1, u} B X Λ,
            (forgetModuleSheaf.{u, u + 1, u} B Y' Λ).map (bcMod.hom.app n) ≫
                (fShriekModForgetIso.{u, u + 1, u} B Λ f').hom.app (modPullP.obj n) ≫
                (fShriekFunctor.{u, u + 1} B f').map (hpullP.hom.app n) =
              hpullG.hom.app ((fShriekMod.{u, u + 1, u} B Λ f).obj n) ≫
                (abPullback.{u, u + 1} B g).map
                  ((fShriekModForgetIso.{u, u + 1, u} B Λ f).hom.app n) ≫
                (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
                  ((forgetModuleSheaf.{u, u + 1, u} B X Λ).obj n)) →
          (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
            (forgetModuleSheaf.{u, u + 1, u} B X' Λ).map (epsMod.hom.app M) ≫
                hpullF'.hom.app (modPullG.obj M) ≫
                (abPullback.{u, u + 1} B f').map (hpullG.hom.app M) =
              hpullP.hom.app (modPullF.obj M) ≫
                (abPullback.{u, u + 1} B p).map (hpullF.hom.app M) ≫
                (inverseImageSquareIso.{u} B p f' f g sq).hom.app
                  ((forgetModuleSheaf.{u, u + 1, u} B Y Λ).obj M)) →
          ∀ (τ : ∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
              (fShriekMod.{u, u + 1, u} B Λ f).obj (modPullF.obj M) ⟶ M)
            (hτ : ∀ M, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f modPullF hpullF w M (τ M))
            (τ' : ∀ N : ModuleSheaf.{u, u + 1, u} B Y' Λ,
              (fShriekMod.{u, u + 1, u} B Λ f').obj (modPullF'.obj N) ⟶ N)
            (hτ' : ∀ N, HasWeightedTraceStalksMod.{u, u + 1, u} B Λ f' modPullF' hpullF'
              (w ∘ B.inclusion.map p) N (τ' N)),
            letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
            letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
            letI :=
              preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f modPullF hpullF
            letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
            letI :=
              preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
            letI :=
              preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ f' modPullF' hpullF'
            letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
            letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
            letI :=
              preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ g modPullG hpullG
            letI := additive_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
            letI := preservesFiniteLimits_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
            letI :=
              preservesFiniteColimits_of_forgetModPullIso.{u, u + 1, u} B Λ p modPullP hpullP
            -- functoriality in `K`
            (∀ (K K' : DerivedCategory (ModuleSheaf.{u, u + 1, u} B Y Λ)) (ψ : K ⟶ K'),
                (modPullF.mapDerivedCategory ⋙
                    (fShriekMod.{u, u + 1, u} B Λ f).mapDerivedCategory).map ψ ≫
                    (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ).app K' =
                  (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ).app K ≫
                    ψ) ∧
              -- the derived trace is the sheaf-level trace, derived
              (derivedWeightedTrace.{u, u + 1, t, u} B Λ f modPullF hpullF w τ hτ =
                  (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
                      modPullF (fShriekMod.{u, u + 1, u} B Λ f)).inv ≫
                    NatTrans.mapDerivedCategory
                      (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ) ≫
                    (Functor.mapDerivedCategoryIdIso _).hom) ∧
              (∀ M : ModuleSheaf.{u, u + 1, u} B Y Λ,
                  (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ).app M =
                    τ M) ∧
              -- compatibility with arbitrary base change
              (NatTrans.mapDerivedCategory
                    (traceBaseChangeComparison.{u, u + 1, u} B Λ f' f modPullF modPullF' modPullG
                      modPullP bcMod epsMod).hom ≫
                  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
                    (modPullF' ⋙ fShriekMod.{u, u + 1, u} B Λ f')).hom ≫
                  Functor.whiskerLeft modPullG.mapDerivedCategory
                    (NatTrans.mapDerivedCategory
                      (weightedTraceModNatTrans.{u, u + 1, u} B Λ f' modPullF' hpullF'
                        (w ∘ B.inclusion.map p) τ' hτ')) ≫
                  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso modPullG
                    (𝟭 (ModuleSheaf.{u, u + 1, u} B Y' Λ))).inv =
                (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                    (modPullF ⋙ fShriekMod.{u, u + 1, u} B Λ f) modPullG).hom ≫
                  Functor.whiskerRight
                    (NatTrans.mapDerivedCategory
                      (weightedTraceModNatTrans.{u, u + 1, u} B Λ f modPullF hpullF w τ hτ))
                    modPullG.mapDerivedCategory ≫
                  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
                    (𝟭 (ModuleSheaf.{u, u + 1, u} B Y Λ)) modPullG).inv)) := by
  let : IsLocallyNoetherian (B.inclusion.obj Y) := inferInstanceAs (IsLocallyNoetherian Y.obj)
  obtain ⟨w, hw, hnonneg, -, hdesc⟩ :=
    exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch (B.inclusion.map f) hY
  refine ⟨w, hw, hnonneg, hdesc, existsUnique_hasWeightedTraceStalks.{u, u + 1} B f hw,
    fun _ _ φ _ _ hF hG => hasWeightedTraceStalks_naturality.{u, u + 1} B f w φ hF hG,
    fun X' Y' p f' g sq F τ hτ => ?_, fun Λ _ X' Y' p f' g sq => ?_⟩
  · let := locallyOfFiniteType_of_isPullback B p f' f g sq
    let := locallyQuasiFinite_of_isPullback B p f' f g sq
    exact ⟨hw.comp_of_isPullback (sq.map B.inclusion),
      hasWeightedTraceStalks_baseChange.{u} B p f' f g sq w F hτ⟩
  · let := locallyOfFiniteType_of_isPullback B p f' f g sq
    let := locallyQuasiFinite_of_isPullback B p f' f g sq
    intro modPullF hpullF modPullF' hpullF' modPullG hpullG modPullP hpullP bcMod epsMod
      _ _ _ _ hbcForget hepsForget τ hτ τ' hτ'
    obtain ⟨h1, h2, h3, h4, -⟩ := derivedWeightedTrace_spec_of_lifts.{u, t} B Λ p f' f g sq
      modPullF hpullF modPullF' hpullF' modPullG hpullG modPullP hpullP bcMod epsMod
      hbcForget hepsForget w τ hτ τ' hτ'
    exact ⟨h1, h2, h3, h4⟩

/-- **Stacks 0GKG and part (1) of Stacks 0GKH for the weighting of Stacks 0GKJ, at an arbitrary
coefficient universe.** The sheaf-level half of the second assertion of Stacks 0GKJ: the
weighting the example produces admits, for every abelian sheaf `F` with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, a unique trace map `Tr_{f, w, F} : f_! f^{-1}F ⟶ F` with the
behaviour on geometric stalks prescribed by Stacks 0GKG, and those trace maps are functorial in
`F`. -/
public theorem exists_weighting_weightedTrace_sheaf_of_isGeometricallyUnibranch
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsLocallyNoetherian Y.obj] (hY : IsGeometricallyUnibranch Y.obj) :
    ∃ w : X.obj → ℤ,
      IsWeighting (B.inclusion.map f) w ∧
      (∀ x : X.obj, 0 ≤ w x) ∧
      (∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v},
        ∃! τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
          HasWeightedTraceStalks.{u, v} B f w F τ) ∧
      ∀ (F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
          (φ : F ⟶ G)
          (τF : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
          (τG : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj G) ⟶ G),
          HasWeightedTraceStalks.{u, v} B f w F τF →
          HasWeightedTraceStalks.{u, v} B f w G τG →
            (fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ) ≫ τG = τF ≫ φ := by
  let : IsLocallyNoetherian (B.inclusion.obj Y) := inferInstanceAs (IsLocallyNoetherian Y.obj)
  obtain ⟨w, hw, hnonneg, -, -⟩ :=
    exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch (B.inclusion.map f) hY
  exact ⟨w, hw, hnonneg, existsUnique_hasWeightedTraceStalks.{u, v} B f hw,
    fun _ _ φ _ _ hF hG => hasWeightedTraceStalks_naturality.{u, v} B f w φ hF hG⟩

/-- **Stacks 0GKG and part (1) of Stacks 0GKH for the weighting of Stacks 0GKJ over a normal
base.** A locally quasi-finite morphism locally of finite type onto a normal locally Noetherian
scheme carries a nonnegative weighting whose trace maps `Tr_{f, w, F} : f_! f^{-1}F ⟶ F` exist,
are unique and are functorial in `F`. -/
public theorem exists_weighting_weightedTrace_sheaf_of_isNormal
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsLocallyNoetherian Y.obj] [IsNormal Y.obj] :
    ∃ w : X.obj → ℤ,
      IsWeighting (B.inclusion.map f) w ∧
      (∀ x : X.obj, 0 ≤ w x) ∧
      (∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v},
        ∃! τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
          HasWeightedTraceStalks.{u, v} B f w F τ) ∧
      ∀ (F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
          (φ : F ⟶ G)
          (τF : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
          (τG : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj G) ⟶ G),
          HasWeightedTraceStalks.{u, v} B f w F τF →
          HasWeightedTraceStalks.{u, v} B f w G τG →
            (fShriekFunctor.{u, v} B f).map ((abPullback.{u, v} B f).map φ) ≫ τG = τF ≫ φ :=
  exists_weighting_weightedTrace_sheaf_of_isGeometricallyUnibranch.{u, v} B f
    isGeometricallyUnibranch_of_isNormal

end AlgebraicGeometry.SmallEtale

end
