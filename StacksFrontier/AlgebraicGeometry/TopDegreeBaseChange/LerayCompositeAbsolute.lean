module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayCompositeRestrictSource

/-!
# The relative Leray comparison against the absolute one

Let `i : Z ⟶ X` and `p : X ⟶ Y` be morphisms of ringed spaces and let `V ⊆ Y` be open.  Two
transformations compare derived sections over `(p ∘ i)⁻¹V` with the derived direct image along
`i`:

* the **relative** Leray comparison
  `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison i p V`, whose target is
  `Ri_* ⋙ RΓ(p⁻¹V, -)` with the inner sections functor the **total** right derived functor
  `…DerivedSectionsLeray.derivedPreimageSections p V` of sections over `p⁻¹V` read over
  `Γ(V, 𝒪_Y)`;
* the **absolute** Leray comparison `…DerivedSectionsLeray.lerayComparison i (p⁻¹V)` for `i` at
  the open `p⁻¹V` of `X`, whose target is `Ri_* ⋙ RΓ(p⁻¹V, -)` with the inner functor
  `…DerivedSectionsLeray.derivedSectionsOverOpen X (p⁻¹V)` over `Γ(p⁻¹V, 𝒪_X)`, and which has to
  be whiskered by restriction of scalars along `p^♯` to land over `Γ(V, 𝒪_Y)`.

The two have different sources as well: the relative one comes out of
`derivedPreimageSections (i ≫ p) V`, the absolute one out of
`derivedPreimageSections i (p⁻¹V) ⋙ res`.  Both are right derived functors of the **same**
degreewise functor — `preimageSections (i ≫ p) V` *is*
`preimageSections i (p⁻¹V) ⋙ res_{p^♯}` on the nose — with different units, which is the shape
`EdgeCompatPreimageRestrict.lean` and `LerayCompositeRestrictSource.lean` already pay twice.
`derivedPreimageSectionsCompModel` is the comparison of those two models, and
`lerayCompositeComparison_eq_lerayComparison` is the identification of the two Leray
comparisons across it and across `Stacks.EdgeCompat.preimageSectionsModelComparison`.

This is the step conclusion (c) of [Stacks, Tag 0EX3] needs because its `γ⁺` side carries the
relative comparison — `…DerivedSectionsLeray.derivedPreimageSectionsCompIso h' f' V` inverted is
the second leading factor of `Stacks.Cohomology.DerivedBaseChange`
`.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` — while the open-subscheme
crossings of its `ψ` side are stated for the absolute comparison.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompModelUnit` and
  `…isRightDerivedFunctor_preimageSectionsCompModelUnit`: `RΓ(i⁻¹(p⁻¹V), -)` over
  `Γ(p⁻¹V, 𝒪_X)`, followed by restriction of scalars along `p^♯`, is a right derived functor of
  sections over `(p ∘ i)⁻¹V` read over `Γ(V, 𝒪_Y)`.  One application of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` at the pair
  `(preimageSections i (p⁻¹V), res_{p^♯})`, with no degreewise comparison in front of it: the two
  degreewise functors are the same functor.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsCompModel`: the comparison of
  the two right derived functors, by `CategoryTheory.Functor.rightDerivedDesc`, with its
  factorizations.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_eq_lerayComparison`: **the
  relative Leray comparison is the absolute one.**  The relative comparison followed by the
  crossing of the two models of `RΓ(p⁻¹V, -)` is the crossing of the two models of
  `RΓ((p ∘ i)⁻¹V, -)` followed by the absolute Leray comparison for `i` at `p⁻¹V` whiskered by
  restriction of scalars along `p^♯`.  Nothing is assumed of `i`, of `p` or of `V`.

## Implementation notes

*No degreewise comparison is declared, because the identity serves.*
`preimageSections (i ≫ p) V = preimageSections i (p⁻¹V) ⋙ preimageRestrictScalars p V` holds by
`rfl`, by three identifications that are each `CategoryTheory.Iso.refl`:
`…DerivedSectionsLeray.preimageSectionsPushforwardIso` reads sections over `(p ∘ i)⁻¹V` as
sections over `p⁻¹V` of a direct image, the definition of
`…DerivedSectionsLeray.preimageSections` splits off the restriction of scalars, and
`…DerivedSectionsLeray.pushforwardPreimageSectionsIso` reads sections over `p⁻¹V` of a direct
image as sections over `i⁻¹(p⁻¹V)`.  So, unlike
`…DerivedSectionsLeray.preimageSectionsCompRestrictSource`, no transformation of degreewise
functors is whiskered in front of the unit here, and the two ring maps
`Γ(V, 𝒪_Y) ⟶ Γ(i⁻¹(p⁻¹V), 𝒪_Z)` are never compared: they are the same map.

*Where the content sits.*  Both sides of the identification come out of the total right derived
functor `RΓ((p ∘ i)⁻¹V, -)`, so `…DerivedSectionsLeray.lerayComparison_ext` reduces it to the
composites with the derived-functor unit, and those are compared degreewise, exactly as in
`LerayCompositeRestrictSource.lean`.  One naturality square — that of
`Stacks.EdgeCompat.preimageSectionsModelComparison` at the image of the unit of `Ri_*` — and the
two characterizing factorizations do it; the two remaining prefixes are composites of
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`s of identity isomorphisms and agree by `rfl`
once `DerivedCategory.Qh.map_comp` has been read backwards.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit
  exists_quasiIso_isKInjective)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsModelComparison
  preimageSectionsModelComparison_fac_app preimageSectionsCompUnit preimageSectionsCompUnitComp)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (exactPostcomposeUnit
  isRightDerivedFunctor_exactPostcomposeUnit)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Opens Y.carrier)

/-! ### The second model of derived sections over `(p ∘ i)⁻¹V` -/

/-- **The unit exhibiting `RΓ(i⁻¹(p⁻¹V), -)` over `Γ(p⁻¹V, 𝒪_X)`, followed by restriction of
scalars along `p^♯`, as a right derived functor** of sections over `(p ∘ i)⁻¹V` read over
`Γ(V, 𝒪_Y)`.

It is `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` at the pair
`(preimageSections i (p⁻¹V), res_{p^♯})`, restriction of scalars being exact.  Nothing is
whiskered in front of it: the degreewise functor of the pair *is* `preimageSections (i ≫ p) V`,
as the implementation notes record. -/
def preimageSectionsCompModelUnit :
    homotopyPreimageSections (i ≫ p) V ⟶
      DerivedCategory.Qh ⋙ (derivedPreimageSections i ((opensMap p).obj V) ⋙
        (preimageRestrictScalars p V).mapDerivedCategory) :=
  exactPostcomposeUnit (preimageSections i ((opensMap p).obj V)) (preimageRestrictScalars p V)
    (derivedPreimageSections i ((opensMap p).obj V))
    (derivedPreimageSectionsUnit i ((opensMap p).obj V))

/-- **`preimageSectionsCompModelUnit` does exhibit a right derived functor.**  The general brick
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit`, with the K-injective resolutions on `Z` supplied by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`. -/
instance isRightDerivedFunctor_preimageSectionsCompModelUnit :
    (derivedPreimageSections i ((opensMap p).obj V) ⋙
        (preimageRestrictScalars p V).mapDerivedCategory).IsRightDerivedFunctor
      (preimageSectionsCompModelUnit i p V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective Z)

/-- **The comparison of the two right derived functors of sections over `(p ∘ i)⁻¹V` read over
`Γ(V, 𝒪_Y)`**: the transformation from the total right derived functor
`derivedPreimageSections (i ≫ p) V` to `RΓ(i⁻¹(p⁻¹V), -)` over `Γ(p⁻¹V, 𝒪_X)` followed by
restriction of scalars along `p^♯`, induced by `preimageSectionsCompModelUnit` through the
universal property of the former.  By `derivedPreimageSectionsCompModel_fac_app` its composite
with the unit of the former is `preimageSectionsCompModelUnit`, and by `lerayComparison_ext` that
determines it. -/
def derivedPreimageSectionsCompModel :
    derivedPreimageSections (i ≫ p) V ⟶
      derivedPreimageSections i ((opensMap p).obj V) ⋙
        (preimageRestrictScalars p V).mapDerivedCategory :=
  (derivedPreimageSections (i ≫ p) V).rightDerivedDesc (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompModelUnit i p V)

/-- The equation characterizing `derivedPreimageSectionsCompModel`, pointwise: composing it with
the unit of the total right derived functor recovers `preimageSectionsCompModelUnit`. -/
theorem derivedPreimageSectionsCompModel_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (derivedPreimageSectionsCompModel i p V).app (DerivedCategory.Qh.obj K) =
      (preimageSectionsCompModelUnit i p V).app K :=
  (derivedPreimageSections (i ≫ p) V).rightDerived_fac_app
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompModelUnit i p V) K

/-- `derivedPreimageSectionsCompModel_fac_app` with a further morphism appended, the form in which
a rewrite inside a longer composite uses it. -/
theorem derivedPreimageSectionsCompModel_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (g : (derivedPreimageSections i ((opensMap p).obj V) ⋙
      (preimageRestrictScalars p V).mapDerivedCategory).obj (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (derivedPreimageSectionsCompModel i p V).app (DerivedCategory.Qh.obj K) ≫ g =
      (preimageSectionsCompModelUnit i p V).app K ≫ g := by
  rw [← Category.assoc, derivedPreimageSectionsCompModel_fac_app]

/-! ### The two routes written out degreewise -/

/-- **A naturality square and a factorization composed, at variables.**  From `b ≫ c = m ≫ r` and
`a ≫ m = w` it follows that `a ≫ b ≫ c = w ≫ r`.

Stated at variables because the concrete instance cannot be assembled by `rw`: the naturality
square of `Stacks.EdgeCompat.preimageSectionsModelComparison` writes its component at the
composite spelling `(Qh ⋙ Ri_*).obj K` of the object, which `rw` does not match against the
goal's `Ri_*(Qh K)`.  At variables the check is at default transparency, where the two agree. -/
private theorem glue_naturality_fac {C : Type*} [Category* C] {A B D E G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {m : B ⟶ G} {r : G ⟶ E} {w : A ⟶ G}
    (h₁ : b ≫ c = m ≫ r) (h₂ : a ≫ m = w) : a ≫ b ≫ c = w ≫ r := by
  rw [h₁, ← Category.assoc, h₂]

/-- **A factorization pulled through a functor inside a three-fold composite, at variables.**  If
`u ≫ v = w` then `(a ≫ b ≫ G.map u) ≫ G.map v` is `a ≫ b ≫ G.map w`.

Stated at variables because the concrete goal is left-associated at its last factor, and
`CategoryTheory.Category.assoc` is refused there: the target is not type-correct at `implicit`
transparency, `Stacks.EdgeCompat.preimageRestrictScalars` being keyed on the ascribed spelling of
its source ring.  The recorded cure is to reassociate at variables. -/
private theorem glue_map_fac {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B : D} {P Q R : C} {a : A ⟶ B} {b : B ⟶ G.obj P} {u : P ⟶ Q} {v : Q ⟶ R} {w : P ⟶ R}
    (h : u ≫ v = w) : (a ≫ b ≫ G.map u) ≫ G.map v = a ≫ b ≫ G.map w := by
  rw [← h, G.map_comp, Category.assoc, Category.assoc]

/-- The first route, expanded: the relative Leray unit for `i` over `p` at `V`, followed by the
crossing of the two models of `RΓ(p⁻¹V, -)`, is the identification of degreewise sections, the
unit exhibiting `RΓ(p⁻¹V, -) ⋙ res` as a right derived functor, and then `res` of `RΓ(p⁻¹V, -)`
of the unit of `Ri_*`.

Naturality of the model comparison moves it past the image of the pushforward unit, and the
characterizing factorization then collapses the unit of `RΓ(p⁻¹V, -)` followed by it. -/
private theorem lerayCompositeUnit_comp_modelComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (lerayCompositeUnit i p V).app K ≫
        (preimageSectionsModelComparison p V).app
          ((derivedPushforward i).obj (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (preimageSectionsPushforwardIso i p V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (preimageSectionsCompUnitComp p V).app
            (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (preimageRestrictScalars p V).mapDerivedCategory.map
            ((derivedSectionsOverOpen X ((opensMap p).obj V)).map
              ((derivedPushforwardUnit i).app K)) := by
  dsimp only [lerayCompositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [Category.assoc]
  exact whisker_eq _ (glue_naturality_fac
    ((preimageSectionsModelComparison p V).naturality ((derivedPushforwardUnit i).app K))
    (preimageSectionsModelComparison_fac_app p V
      (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))

/-- The second route, expanded: the unit of the second model of sections over `(p ∘ i)⁻¹V`
followed by `res` of the absolute Leray comparison for `i` at `p⁻¹V` is the crossing of the two
readings of restriction of scalars, the identification of degreewise sections, the unit of
`RΓ(p⁻¹V, -)`, and then the unit of `Ri_*`. -/
private theorem preimageSectionsCompModelUnit_comp_lerayComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (preimageSectionsCompModelUnit i p V).app K ≫
        (preimageRestrictScalars p V).mapDerivedCategory.map
          ((lerayComparison i ((opensMap p).obj V)).app (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
              (Iso.refl (preimageSections i ((opensMap p).obj V) ⋙
                preimageRestrictScalars p V))
              (ComplexShape.up ℤ)).inv.app K) ≫
        (preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.app
            (((preimageSections i ((opensMap p).obj V)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (preimageRestrictScalars p V).mapDerivedCategory.map
              (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso
                  (pushforwardPreimageSectionsIso i ((opensMap p).obj V))
                  (ComplexShape.up ℤ)).inv.app K)) ≫
            (preimageRestrictScalars p V).mapDerivedCategory.map
                ((derivedSectionsOverOpenUnit X ((opensMap p).obj V)).app
                  (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
              (preimageRestrictScalars p V).mapDerivedCategory.map
                ((derivedSectionsOverOpen X ((opensMap p).obj V)).map
                  ((derivedPushforwardUnit i).app K)) := by
  dsimp only [preimageSectionsCompModelUnit]
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  refine (glue_map_fac (preimageRestrictScalars p V).mapDerivedCategory
    (lerayComparison_fac_app i ((opensMap p).obj V) K)).trans ?_
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp]
  rfl

/-! ### The relative Leray comparison is the absolute one -/

/-- **The relative Leray comparison is the absolute Leray comparison.**  For morphisms
`i : Z ⟶ X` and `p : X ⟶ Y` of ringed spaces and an open `V ⊆ Y`, the relative Leray comparison
for `i` over `p` at `V`, followed by the crossing of the two models of `RΓ(p⁻¹V, -)`, equals the
crossing of the two models of `RΓ((p ∘ i)⁻¹V, -)` followed by the absolute Leray comparison for
`i` at the open `p⁻¹V` of `X`, whiskered by restriction of scalars along `p^♯`.  Both sides are
transformations

`RΓ((p ∘ i)⁻¹V, -) ⟶ Ri_* ⋙ RΓ(p⁻¹V, -) ⋙ res_{p^♯}` of functors `D(𝒪_Z) ⥤ D(Γ(V, 𝒪_Y))`.

This is what identifies the second leading factor of `Stacks.Cohomology.DerivedBaseChange`
`.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` — the relative comparison
inverted, which is `…DerivedSectionsLeray.derivedPreimageSectionsCompIso` — with the absolute
comparison the open-subscheme crossings of conclusion (c) of [Stacks, Tag 0EX3] speak about.
Nothing is assumed of `i`, of `p` or of `V`; both sides come out of the total right derived
functor `RΓ((p ∘ i)⁻¹V, -)`, so `lerayComparison_ext` reduces the statement to the composites
with the derived-functor unit, and those are compared degreewise. -/
theorem lerayCompositeComparison_eq_lerayComparison :
    lerayCompositeComparison i p V ≫
        Functor.whiskerLeft (derivedPushforward i) (preimageSectionsModelComparison p V) =
      derivedPreimageSectionsCompModel i p V ≫
        Functor.whiskerRight (lerayComparison i ((opensMap p).obj V))
          (preimageRestrictScalars p V).mapDerivedCategory := by
  apply (derivedPreimageSections (i ≫ p) V).rightDerived_ext
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [lerayCompositeComparison_fac_app_comp i p V K,
    derivedPreimageSectionsCompModel_fac_app_comp i p V K]
  refine (lerayCompositeUnit_comp_modelComparison_app i p V K).trans
    (Eq.trans ?_ (preimageSectionsCompModelUnit_comp_lerayComparison_app i p V K).symm)
  -- Naturality of `mapDerivedCategoryFactorsh` moves the identification of degreewise sections
  -- over `p⁻¹V` to the front; the degreewise identifications then agree on the nose.
  have hnat : (preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.app
          (((preimageSections i ((opensMap p).obj V)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (preimageRestrictScalars p V).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (pushforwardPreimageSectionsIso i ((opensMap p).obj V))
              (ComplexShape.up ℤ)).inv.app K)) =
      DerivedCategory.Qh.map
          (((preimageRestrictScalars p V).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso
              (pushforwardPreimageSectionsIso i ((opensMap p).obj V))
              (ComplexShape.up ℤ)).inv.app K)) ≫
        (preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.app
          (((sectionsOverOpen X ((opensMap p).obj V)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
            (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.naturality
      ((Functor.mapHomotopyCategoryCompIso
        (pushforwardPreimageSectionsIso i ((opensMap p).obj V))
        (ComplexShape.up ℤ)).inv.app K)).symm
  simp only [preimageSectionsCompUnitComp, preimageSectionsCompUnit, exactPostcomposeUnit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  rfl

/-- **`lerayCompositeComparison_eq_lerayComparison` solved for the inverse**, which is the form a
chase meets it in: what conclusion (c) of [Stacks, Tag 0EX3] carries is
`…DerivedSectionsLeray.derivedPreimageSectionsCompIso`, the relative Leray comparison
**inverted**, as the second leading factor of `Stacks.Cohomology.DerivedBaseChange`
`.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite`.  So: that inverse, followed
by the crossing of the two models of `RΓ((p ∘ i)⁻¹V, -)` and the absolute Leray comparison for `i`
at `p⁻¹V` whiskered by restriction of scalars along `p^♯`, is the crossing of the two models of
`RΓ(p⁻¹V, -)`.

Nothing new is proved and no invertibility beyond
`…DerivedSectionsLeray.isIso_lerayCompositeComparison`, which is unconditional, is used; in
particular the two model comparisons are not inverted anywhere. -/
theorem derivedPreimageSectionsCompIso_hom_comp_lerayComparison :
    (derivedPreimageSectionsCompIso i p V).hom ≫
        (derivedPreimageSectionsCompModel i p V ≫
          Functor.whiskerRight (lerayComparison i ((opensMap p).obj V))
            (preimageRestrictScalars p V).mapDerivedCategory) =
      Functor.whiskerLeft (derivedPushforward i) (preimageSectionsModelComparison p V) := by
  rw [← lerayCompositeComparison_eq_lerayComparison i p V]
  exact (derivedPreimageSectionsCompIso i p V).hom_inv_id_assoc _

end Stacks.Cohomology.DerivedSectionsLeray

end
