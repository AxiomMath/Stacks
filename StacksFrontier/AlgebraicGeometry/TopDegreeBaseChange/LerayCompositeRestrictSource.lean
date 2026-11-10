module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrictSource

/-!
# The relative Leray comparison against a smaller open downstairs

Let `i : Z ⟶ X` and `p : X ⟶ Y` be morphisms of ringed spaces, let `V ⊆ Y` be open and let
`W ⊆ p⁻¹V` be an open of `X`. The relative Leray comparison
`Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison` reads derived sections over
`(p ∘ i)⁻¹V` as derived sections over `p⁻¹V` of a derived pushforward along `i`, everything over
`Γ(V, 𝒪_Y)`. This file proves that it commutes with shrinking that open of `X` from `p⁻¹V` down to
`W`: one may descend to `p⁻¹V` first and restrict afterwards, or restrict upstairs from
`(p ∘ i)⁻¹V` to `i⁻¹W` first and apply the Leray comparison for `i` at `W`.

That is the coherence conclusion (c) of [Stacks, Tag 0EX3] needs where its two sides restrict at
different times: the comparison of the two iterated derived pushforwards reads the inner morphism
over the *larger* open and restricts afterwards, while the affine computation of [Stacks, Tag 089W]
is already at the restricted morphism.

`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_restrict` is the **absolute** form of the
same compatibility, at two opens of `Y`; it is not this statement, and neither is it this statement
applied to `i`. There the open being shrunk is the base open `V` of the Leray comparison, whose
upstairs open is a preimage; here it is the *source* open of a preimage-sections functor, and
`i⁻¹W` is not the preimage of any open of `Y`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompRestrictSource` — restriction of
  sections over `(p ∘ i)⁻¹V` to `i⁻¹W`, read over `Γ(V, 𝒪_Y)` through sections over `W` on `X`.
* `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompRestrictSourceUnit` and
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsCompRestrictSource` — the
  transformation into `Qh ⋙ (RΓ(i⁻¹W, -) ∘ res)` that the universal property of the derived functor
  consumes, and the derived restriction it induces.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsCompRestrictSource_fac_app` — the
  factorization through the derived-functor unit that characterizes the derived restriction.
* `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource` — **the
  compatibility of the relative Leray comparison with shrinking the open downstairs**. No
  hypothesis on `i`, on `p`, on `V` or on `W`.

## Implementation notes

*The degreewise restriction is free, and that is what makes the statement cheap.*
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections (i ≫ p) V` is
`i_* ⋙ preimageSections p V` on the nose — this is
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsPushforwardIso`, which is
`CategoryTheory.Iso.refl` — and `i_* ⋙ sectionsOverOpen X W` is `preimageSections i W` on the nose,
which is `Stacks.Cohomology.DerivedSectionsLeray.pushforwardPreimageSectionsIso`. So
`preimageSectionsCompRestrictSource` is `Stacks.EdgeCompat.preimageSectionsRestrictSource` at
`(p, V, W)` whiskered on the left by `i_*`, with both its source and its target the intended
functors definitionally. In particular the two factorizations of the ring map
`Γ(V, 𝒪_Y) ⟶ Γ(i⁻¹W, 𝒪_Z)` never have to be compared: writing the restriction this way puts the
one through `Γ(W, 𝒪_X)` in place from the start.

*What is not free.* The derived transformation is a genuine
`CategoryTheory.Functor.rightDerivedDesc` out of the total right derived functor
`RΓ((p ∘ i)⁻¹V, -)`: its target
`RΓ(i⁻¹W, -) ⋙ res.mapDerivedCategory` is a different right derived functor, with a different unit,
from the one `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison` descends to, because
the latter's inner factor is `RΓ(W, -)` on `X` and this one's is `RΓ(i⁻¹W, -)` on `Z`. The unit is
one application of `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`,
so no instance proof is needed, but the descent itself is new.

*Where the content of the compatibility sits.* Both sides are transformations out of the total
right derived functor `RΓ((p ∘ i)⁻¹V, -)`, so
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` reduces the statement to the
composites with the derived-functor unit. Each of those collapses, by the characterizing
factorizations, to a composite of degreewise units, and the two results are matched by naturality
of the two model comparisons, naturality of the comparison `Qh ⋙ res ≅ res ⋙ Qh` of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and the identity of the degreewise
restrictions, which holds on the nose.
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean` is the
template for the
absolute case one lemma for one lemma.

*Why `glue_two_naturalities` is stated at variables.* Moving the two model comparisons past the
image of the pushforward unit by `rw` fails: `Stacks.EdgeCompat.preimageRestrictScalars` carries
its source ring ascribed, and the motive `rw` builds for the second naturality square is not
type-correct at `implicit` transparency. At variables the same shuffle is three uses of
`CategoryTheory.Category.assoc`. This is the same obstruction
`Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsModelComparison` records for
`CategoryTheory.Category.comp_id`.

*Why the file sits in `TopDegreeBaseChange/`.* Its statement names
`Stacks.EdgeCompat.preimageRestrictScalars`, `Stacks.EdgeCompat.preimageSectionsModelComparison`
and `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison`, which are declared there;
the declarations themselves belong to the Leray family and are named in it.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsRestrictSource
  preimageSectionsRestrictSourceCompUnit preimageSectionsModelComparison
  preimageSectionsModelComparison_fac_app preimageSectionsRestrictSourceModelComparison
  preimageSectionsRestrictSourceModelComparison_fac_app)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (exactPostcomposeUnit)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Opens Y.carrier)
  {W : Opens X.carrier} (hW : W ≤ (opensMap p).obj V)

/-! ### The derived restriction to a smaller open downstairs -/

/-- **Restriction of sections over `(p ∘ i)⁻¹V` to `i⁻¹W`, read over `Γ(V, 𝒪_Y)`.** It is
`Stacks.EdgeCompat.preimageSectionsRestrictSource` for `p` at `V` and `W`, applied to a direct
image along `i`.

Nothing new has to be checked: sections over `(p ∘ i)⁻¹V` read over `Γ(V, 𝒪_Y)` are sections over
`p⁻¹V` of the direct image (`preimageSectionsPushforwardIso`), and sections over `i⁻¹W` read over
`Γ(W, 𝒪_X)` are sections over `W` of the direct image (`pushforwardPreimageSectionsIso`), both on
the nose. In particular the scalars are read through `Γ(W, 𝒪_X)` from the start, so the two
factorizations of the ring map `Γ(V, 𝒪_Y) ⟶ Γ(i⁻¹W, 𝒪_Z)` are never compared. -/
def preimageSectionsCompRestrictSource :
    preimageSections (i ≫ p) V ⟶
      preimageSections i W ⋙ (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V) :=
  Functor.whiskerLeft (modulePushforward i) (preimageSectionsRestrictSource p V hW)

/-- The canonical transformation from termwise sections over `(p ∘ i)⁻¹V` to `RΓ(i⁻¹W, -)` followed
by restriction of scalars from `Γ(W, 𝒪_X)` to `Γ(V, 𝒪_Y)`: the degreewise restriction maps, read on
the homotopy category, followed by the unit exhibiting that composite as a right derived functor.

The second factor is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` at the pair
`(Γ(i⁻¹W, -) over Γ(W, 𝒪_X), res_{W ≤ p⁻¹V} ⋙ res_{p^♯})`, the second member being a composite of
restrictions of scalars and so exact, which is that brick's only hypothesis on it. -/
def preimageSectionsCompRestrictSourceUnit :
    homotopyPreimageSections (i ≫ p) V ⟶
      DerivedCategory.Qh ⋙ (derivedPreimageSections i W ⋙
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory) :=
  Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (preimageSectionsCompRestrictSource i p V hW)
        (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    exactPostcomposeUnit (preimageSections i W)
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V)
      (derivedPreimageSections i W) (derivedPreimageSectionsUnit i W)

/-- **The derived restriction of sections over `(p ∘ i)⁻¹V` to `i⁻¹W`, read over `Γ(V, 𝒪_Y)`**, the
transformation induced by `preimageSectionsCompRestrictSourceUnit` through the universal property
of the right derived functor of sections over `(p ∘ i)⁻¹V`. By
`derivedPreimageSectionsCompRestrictSource_fac_app` its composite with the derived-functor unit is
that transformation, and that equation determines it. -/
def derivedPreimageSectionsCompRestrictSource :
    derivedPreimageSections (i ≫ p) V ⟶
      derivedPreimageSections i W ⋙
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory :=
  (derivedPreimageSections (i ≫ p) V).rightDerivedDesc (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompRestrictSourceUnit i p V hW)

/-- The equation characterizing the derived restriction to a smaller open downstairs, pointwise:
composing it with the unit of `RΓ((p ∘ i)⁻¹V, -)` recovers
`preimageSectionsCompRestrictSourceUnit`. -/
theorem derivedPreimageSectionsCompRestrictSource_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (derivedPreimageSectionsCompRestrictSource i p V hW).app (DerivedCategory.Qh.obj K) =
      (preimageSectionsCompRestrictSourceUnit i p V hW).app K :=
  (derivedPreimageSections (i ≫ p) V).rightDerived_fac_app
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) _
    (preimageSectionsCompRestrictSourceUnit i p V hW) K

/-- `derivedPreimageSectionsCompRestrictSource_fac_app` with a further morphism appended, the form
in which a rewrite inside a longer composite uses it. -/
theorem derivedPreimageSectionsCompRestrictSource_fac_app_comp
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    {T : DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (g : (derivedPreimageSections i W ⋙
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory).obj
        (DerivedCategory.Qh.obj K) ⟶ T) :
    (derivedPreimageSectionsUnit (i ≫ p) V).app K ≫
        (derivedPreimageSectionsCompRestrictSource i p V hW).app (DerivedCategory.Qh.obj K) ≫ g =
      (preimageSectionsCompRestrictSourceUnit i p V hW).app K ≫ g := by
  rw [← Category.assoc, derivedPreimageSectionsCompRestrictSource_fac_app]

/-! ### The two routes written out degreewise -/

/-- **Two naturality squares and a factorization composed, at variables.** From `m ≫ φ₁ = ψ₁ ≫ m'`,
`m' ≫ φ₂ = ψ₂ ≫ n` and `u ≫ ψ₁ ≫ ψ₂ = w` it follows that `u ≫ m ≫ φ₁ ≫ φ₂ = w ≫ n`.

Stated at variables because the concrete instance cannot be assembled by `rw`: the second
naturality square's motive is not type-correct at `implicit` transparency,
`preimageRestrictScalars` being keyed on the ascribed spelling of its source ring. At variables the
check is at default transparency. -/
private theorem glue_two_naturalities {C : Type*} [Category* C] {A B B' D D' E G : C}
    {u : A ⟶ B} {m : B ⟶ D} {φ₁ : D ⟶ D'} {ψ₁ : B ⟶ B'} {m' : B' ⟶ D'}
    {φ₂ : D' ⟶ E} {ψ₂ : B' ⟶ G} {n : G ⟶ E} {w : A ⟶ G}
    (h₁ : m ≫ φ₁ = ψ₁ ≫ m') (h₂ : m' ≫ φ₂ = ψ₂ ≫ n) (h₃ : u ≫ ψ₁ ≫ ψ₂ = w) :
    u ≫ m ≫ φ₁ ≫ φ₂ = w ≫ n := by
  rw [← h₃, ← Category.assoc m, h₁, Category.assoc, h₂]
  simp only [Category.assoc]

/-- The first route, expanded: the relative Leray unit for `i` over `p` at `V`, followed by the
crossing of the two models of `RΓ(p⁻¹V, -)` and the derived restriction to `W`, is the
identification of degreewise sections, the degreewise restriction to `W`, the unit exhibiting
`RΓ(W, -) ⋙ res` as a right derived functor, and then the unit of `Ri_*`.

Naturality of the two model comparisons moves them past the image of the pushforward unit, and the
two characterizing factorizations then collapse the unit of `RΓ(p⁻¹V, -)` followed by them. -/
private theorem lerayCompositeUnit_comp_restrictSourceModelComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (lerayCompositeUnit i p V).app K ≫
        (preimageSectionsModelComparison p V).app
            ((derivedPushforward i).obj (DerivedCategory.Qh.obj K)) ≫
          (preimageSectionsRestrictSourceModelComparison p V hW).app
            ((derivedPushforward i).obj (DerivedCategory.Qh.obj K)) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (preimageSectionsPushforwardIso i p V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource p V hW)
              (ComplexShape.up ℤ)).app
                (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
          (preimageSectionsRestrictSourceCompUnit p V hW).app
              (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory.map
              ((derivedSectionsOverOpen X W).map ((derivedPushforwardUnit i).app K)) := by
  have h₃ : (derivedPreimageSectionsUnit p V).app
          (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (preimageSectionsModelComparison p V).app
            (DerivedCategory.Qh.obj
              (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
          (preimageSectionsRestrictSourceModelComparison p V hW).app
            (DerivedCategory.Qh.obj
              (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource p V hW)
            (ComplexShape.up ℤ)).app
              (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (preimageSectionsRestrictSourceCompUnit p V hW).app
          (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :=
    ((Category.assoc _ _ _).symm.trans
        (eq_whisker (preimageSectionsModelComparison_fac_app p V
          (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) _)).trans
      (preimageSectionsRestrictSourceModelComparison_fac_app p V hW
        (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
  dsimp only [lerayCompositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [Category.assoc]
  exact whisker_eq _ ((glue_two_naturalities
    ((preimageSectionsModelComparison p V).naturality ((derivedPushforwardUnit i).app K))
    ((preimageSectionsRestrictSourceModelComparison p V hW).naturality
      ((derivedPushforwardUnit i).app K)) h₃).trans (Category.assoc _ _ _))

/-- The restriction unit for sections over `(p ∘ i)⁻¹V` followed by the Leray comparison for `i`
at `W`, compared with the pushforward form of the degreewise restriction. Naturality of the
comparison of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` moves the identification of
degreewise sections over `W` to the front, and the degreewise restrictions then compose to one
another on the nose: restriction for sections over `(p ∘ i)⁻¹V` is by construction restriction for
sections over `p⁻¹V` evaluated at a direct image. -/
private theorem restrictSourceCompUnit_pushforward_eq_unit_comp_lerayComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (preimageSectionsPushforwardIso i p V)
            (ComplexShape.up ℤ)).inv.app K) ≫
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource p V hW)
              (ComplexShape.up ℤ)).app
                (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
          (preimageSectionsRestrictSourceCompUnit p V hW).app
              (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory.map
              ((derivedSectionsOverOpen X W).map ((derivedPushforwardUnit i).app K)) =
    (preimageSectionsCompRestrictSourceUnit i p V hW).app K ≫
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory.map
          ((lerayComparison i W).app (DerivedCategory.Qh.obj K)) := by
  have hnat : (sectionsRestrictScalars X hW ⋙
            preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.app
            (((preimageSections i W).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso i W)
              (ComplexShape.up ℤ)).inv.app K)) =
      DerivedCategory.Qh.map
          (((sectionsRestrictScalars X hW ⋙
              preimageRestrictScalars p V).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso i W)
              (ComplexShape.up ℤ)).inv.app K)) ≫
        (sectionsRestrictScalars X hW ⋙
            preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.app
          (((sectionsOverOpen X W).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((sectionsRestrictScalars X hW ⋙
      preimageRestrictScalars p V).mapDerivedCategoryFactorsh.inv.naturality
        ((Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso i W)
          (ComplexShape.up ℤ)).inv.app K)).symm
  dsimp only [preimageSectionsCompRestrictSourceUnit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  simp only [exactPostcomposeUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory.map_comp,
    lerayComparison_fac_app i W K]
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp]
  simp only [preimageSectionsRestrictSourceCompUnit, exactPostcomposeUnit, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  rfl


/-! ### The compatibility of the relative Leray comparison with restriction -/

/-- **The relative Leray comparison is compatible with shrinking the open downstairs.** For
morphisms `i : Z ⟶ X` and `p : X ⟶ Y` of ringed spaces, an open `V ⊆ Y` and an open `W ⊆ p⁻¹V` of
`X`, the relative Leray comparison for `i` over `p` at `V`, followed by the crossing of the two
models of `RΓ(p⁻¹V, -)` and the derived restriction of sections from `p⁻¹V` to `W`, equals the
derived restriction of sections from `(p ∘ i)⁻¹V` to `i⁻¹W` followed by the Leray comparison for
`i` at `W`. Both sides are transformations

`RΓ((p ∘ i)⁻¹V, -) ⟶ Ri_* ⋙ RΓ(W, -) ⋙ res` of functors `D(𝒪_Z) ⥤ D(Γ(V, 𝒪_Y))`,

where `res` is the composite of restriction of scalars along `Γ(p⁻¹V, 𝒪_X) ⟶ Γ(W, 𝒪_X)` and along
`p^♯ : Γ(V, 𝒪_Y) ⟶ Γ(p⁻¹V, 𝒪_X)`.

This is the compatibility that conclusion (c) of [Stacks, Tag 0EX3] uses where its `γ⁺` side reads
the inner morphism over the larger open and restricts afterwards while its `ψ` side is already at
the restricted morphism, and it holds with no hypothesis on `i`, on `p`, on `V` or on `W`. Both
sides come out of the total right derived functor `RΓ((p ∘ i)⁻¹V, -)`, so `lerayComparison_ext`
reduces the statement to the composites with the derived-functor unit, and those are compared
degreewise.

The two model comparisons are what makes the left-hand side's target match: the derived restriction
`Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison` starts at the model
`RΓ(p⁻¹V, -) ⋙ res.mapDerivedCategory`, while `lerayCompositeComparison` lands in the total
`derivedPreimageSections p V`, and `Stacks.EdgeCompat.preimageSectionsModelComparison` is the
crossing between them. -/
theorem lerayCompositeComparison_restrictSource :
    lerayCompositeComparison i p V ≫
        Functor.whiskerLeft (derivedPushforward i)
          (preimageSectionsModelComparison p V ≫
            preimageSectionsRestrictSourceModelComparison p V hW) =
      derivedPreimageSectionsCompRestrictSource i p V hW ≫
        Functor.whiskerRight (lerayComparison i W)
          (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars p V).mapDerivedCategory := by
  apply (derivedPreimageSections (i ≫ p) V).rightDerived_ext
    (derivedPreimageSectionsUnit (i ≫ p) V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [lerayCompositeComparison_fac_app_comp i p V K,
    derivedPreimageSectionsCompRestrictSource_fac_app_comp i p V hW K]
  exact (lerayCompositeUnit_comp_restrictSourceModelComparison_app i p V hW K).trans
    (restrictSourceCompUnit_pushforward_eq_unit_comp_lerayComparison_app i p V hW K)

end Stacks.Cohomology.DerivedSectionsLeray

end
