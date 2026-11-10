module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerivedLE
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives

/-!
# The open-subscheme crossing at the preimage open itself is invertible

`LerayOpenSubschemeDerivedLE.lean` builds, for a morphism of schemes `f : X ⟶ S`, an open
`V ⊆ S` and an open `U ≤ f⁻¹V` of `X`, the derived crossing
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeSectionsComparisonLE` from
`RΓ(f⁻¹V, -)` to its open-subscheme reading at `U`, and records that at a proper `U < f⁻¹V` the
degreewise crossing is the restriction of sections and is **not** invertible. At `U = f⁻¹V` it
ought to be, and this file proves that it is — both for the crossing out of `RΓ(f⁻¹V, -)` and for
the crossing out of the Leray comparison's target `Rf_* ⋙ RΓ(V, -)`.

*Why this is needed, and why it is not automatic.* The tail of conclusion (c) of
[Stacks, Tag 0EX3] matches its factor (1) at the restricted morphism `f' ∣_ V` over the whole of
the open subscheme `f'⁻¹V`, while the `γ⁺` side reads the same factor at the unrestricted `f'`
over `V`. The passage between those two instantiations is the `LE` family at `U = f'⁻¹V` and
`e = le_rfl`, taken in the inverted direction, so the match needs exactly the invertibility proved
here. None of the three steps —
`IsIso (…DerivedSectionsLeray.sectionsOverOpenRestrictLE X (le_refl U))`,
`IsIso (…preimageSectionsOpenSubschemeLE f V (le_refl (f ⁻¹ᵁ V)))` and
`IsIso (…openSubschemeSectionsComparisonLE f V (le_refl (f ⁻¹ᵁ V)))` — is found by `inferInstance`
(each reports `failed to synthesize`), for the reason the implementation notes record.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.isIso_sectionsOverOpenRestrict_le_refl` — **restriction
  of sections from an open to itself is an isomorphism.** Not `𝟙`: the target is read over
  `Γ(U, 𝒪_X)` along `…DerivedSectionsLeray.sectionsRingRestrict X le_rfl`, a ring map equal to the
  identity but not syntactically `RingHom.id`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isKInjective_mapHomologicalComplex`
  `_openSubschemeRestrictionOf` — [Stacks, Tag 08BS] in this subtree's spelling of restriction to
  an open subscheme.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_preimageSectionsRestrictLE_le_refl` and
  `…isIso_preimageSectionsOpenSubschemeLE_le_refl` — the **degreewise** crossing at `U = f⁻¹V` is
  an isomorphism.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit` — **the general brick.** Whenever the
  degreewise crossing `α` is invertible and `RP` is a right derived functor of degreewise sections
  upstairs at `u`, the open-subscheme derived target
  `…openSubschemeDerivedTargetOf X U V RP` is a right derived functor of degreewise sections over
  `f⁻¹V` at `…openSubschemeUnitOfNatTransUnit f V e α u`. Nothing is assumed of `f`, of `V`, of
  `U`, of `RP` or of `u` beyond that.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.isRightDerivedFunctor_openSubschemeSectionsUnitLE_le_refl`,
  `…isIso_openSubschemeSectionsComparisonLE_le_refl` and
  `…isIso_openSubschemeLerayComparisonLE_le_refl` — **the two derived crossings at `U = f⁻¹V` are
  isomorphisms**, with no hypothesis on `f` or on `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeUnitOfIsoUnit`,
  `…isRightDerivedFunctor_openSubschemeSectionsUnit`, `…isIso_openSubschemeSectionsComparison` and
  `…isIso_openSubschemeLerayComparison` — **the same four statements at the
  `AlgebraicGeometry.Scheme.Hom.morphismRestrict` spelling of the restricted morphism**, which is
  the spelling the match of conclusion (c) of [Stacks, Tag 0EX3] actually consumes; see the
  implementation note on why that is a second statement and not a transport.

## Implementation notes

*Which of the two spellings the match needs.* Factor (1) of [Stacks, Tag 089W] is matched at
`q := f' ∣_ V` — that is the morphism
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` is instantiated at, and the one
`…TopDegreeBaseChange.restrictScalars_singleCompDerivedSectionsTop_inv_app_eq` and
`…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` carry. So the crossing between the
`((f' ∣_ V), ⊤)` and `(f', V)` readings of the `γ⁺` prefix is
`…TopDegreeBaseChange.openSubschemeSectionsComparison`, the **non-`LE`** crossing of
`LerayOpenSubschemeDerived.lean`, and not `…openSubschemeSectionsComparisonLE` at `e = le_rfl`. The
two differ by `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`, which is not `rfl`, so
neither is an instance of the other and both are proved here — the second by the same six lines at
the other spelling, the one duplication this file contains and the cheapest available: a shared
brick would have to restate the unit and the homotopy splitting generically, duplicating three
existing `def`s instead of one proof.

*Why none of the three steps is `inferInstance`.*
`…DerivedSectionsLeray.sectionsOverOpenRestrictLE X h` is
`CategoryTheory.PresheafOfModules.restriction` along `(homOfLE h).op`, whiskered by the forgetful
functor, and its target is read over `Γ(U, 𝒪_X)` through
`CategoryTheory.ModuleCat.restrictScalars (…DerivedSectionsLeray.sectionsRingRestrict X h)`. At
`h = le_rfl` that ring map is the identity *mathematically* and not `RingHom.id` *syntactically*,
so neither the component nor the scalars layer is the identity to instance search. What closes the
step is that `(homOfLE h).op` **is** `𝟙 (op U)` — `Opens X` is a poset, so `homOfLE` of any proof
of `U ≤ U` is the identity by proof irrelevance — together with Mathlib's
`CategoryTheory.PresheafOfModules.map_id`, which says that the restriction map along `𝟙` is the
inverse of `CategoryTheory.ModuleCat.restrictScalarsId'`, an isomorphism. That is the
presheaf-functoriality-at-`(𝟙).op` step, and it is three lines.

*Why the composite of the three degreewise factors cannot be left to instance search either.*
`…preimageSectionsRestrictLE` declares its target at the
`AlgebraicGeometry.Scheme.Hom.appLE` spelling of the scalars while the factor composed after it
presents them as the restriction map after `f^♯`, and `sectionsOverOpen X (U.ι ''ᵁ ⊤)` against
`sectionsOverOpen X U`; both crossings are definitional, and `CategoryTheory.IsIso.comp_isIso`
is keyed on the composite's *middle object*, so synthesis does not cross them: `IsIso`
of each factor alone is found and `IsIso` of the two-factor composite is not. The fix is
`CategoryTheory.IsIso.comp_isIso'` with the three factors supplied by hand, where the unification
runs at default transparency.

*Why the brick takes its invertibility hypothesis explicitly and not as an instance.* The same
spelling pair. `…preimageSectionsOpenSubschemeLE` declares its target with
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, while the brick's `α` is typed with
`…openSubschemeRestrictionOf` — the recorded pair that is definitionally equal and not
interchangeable for instance synthesis. With `[IsIso α]` the instance argument is asked for at the
brick's spelling and `IsIso (preimageSectionsOpenSubschemeLE f V ⋯)` is reported unsynthesisable;
with `(hα : IsIso α)` the available instance is passed by name and the crossing is made
once, by `exact`.

*What the brick's proof actually checks.* The K-injective criterion
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective`
reduces it to the invertibility of `…openSubschemeUnitOfNatTransUnit`'s component at a K-injective
complex, and that transformation has four factors: `α` on the homotopy category, the splitting of
the two exact factors, `u`, and the comparison of restriction to the open subscheme with
localization. The first, second and fourth are invertible formally; the third needs the
**restriction of a K-injective complex to the open subscheme to be K-injective**, which is
[Stacks, Tag 08BS], formalized as `ExtensionByZeroModules.isKInjective_jStar`. No precomposition
counterpart of `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` is
declared and none is needed: the criterion is applied directly.

*A duplicate.* That an isomorphism of
additive functors stays an isomorphism on the homotopy category is proved in the tree already, as
the `private` `mapHomotopyCategory_iso_app`
(`Homology/DerivedCategory/InverseSystem/ModuleInverseLimitGlobalSections.lean:640`), by the same
`change`-to-`NatIso.mapHomologicalComplex` step used here. It is `private`, hence unusable from
another module. De-privatizing it, or stating it beside
`CategoryTheory.NatTrans.mapHomotopyCategory`, is a candidate.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 0D5W] carries its attribute where the Leray
comparison is proved invertible and [Stacks, Tag 08BS] where restriction is proved to preserve
K-injectivity; conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (isRightDerivedFunctor_of_isIso_app_isKInjective exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen preimageSections derivedPreimageSectionsUnit sectionsOverOpenRestrictLE
    lerayComparison isIso_lerayComparison)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedSectionsLeray

/-- **Restriction of sections from an open to itself is an isomorphism.** For a ringed space `Z`
and an open `W ⊆ Z`, the transformation
`…DerivedSectionsLeray.sectionsOverOpenRestrictLE Z (le_refl W)` is invertible.

It is not the identity transformation: its target reads the sections over `W` again, but over
`Γ(W, 𝒪_Z)` along `…DerivedSectionsLeray.sectionsRingRestrict Z le_rfl`, which is the identity ring
map only up to `CategoryTheory.Functor.map_id` and not syntactically. Componentwise the
transformation is the restriction map of a sheaf of modules along `(homOfLE le_rfl).op = 𝟙 (op W)`,
which Mathlib's `CategoryTheory.PresheafOfModules.map_id` identifies with the inverse of
`CategoryTheory.ModuleCat.restrictScalarsId'`. -/
instance isIso_sectionsOverOpenRestrict_le_refl (Z : RingedSpace.{u, u}) (W : Opens Z.carrier) :
    IsIso (sectionsOverOpenRestrictLE Z (le_refl W)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hf : RingCat.Hom.hom ((structureSheafRing Z).obj.map (𝟙 (op W))) = RingHom.id _ := by
    rw [CategoryTheory.Functor.map_id]; exact RingCat.hom_id
  have h : (sectionsOverOpenRestrictLE Z (le_refl W)).app M =
      ((SheafOfModules.forget (structureSheafRing Z)).obj M).map (𝟙 (op W)) := rfl
  rw [h, PresheafOfModules.map_id]
  exact Iso.isIso_inv (Iso.app (ModuleCat.restrictScalarsId' _ hf) _)

end Stacks.Cohomology.DerivedSectionsLeray

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### Restriction to an open subscheme preserves K-injectivity -/

/-- **[Stacks, Tag 08BS] in the spelling `…TopDegreeBaseChange.openSubschemeRestrictionOf`.** The
degreewise restriction to an open subscheme `U` of `X` of a K-injective complex of
`𝒪_X`-modules is K-injective.

Nothing is proved: `…TopDegreeBaseChange.openSubschemeRestrictionOf X U` is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace U` with its target
ascribed, and that functor **is** `ExtensionByZeroModules.jStar U (structureSheafRing _)` — both
are `CategoryTheory.SheafOfModules.pushforward` of the identity of the restricted sheaf of rings
along the image functor of the open embedding, so the identification is definitional (it holds by
`rfl`). The K-injectivity hypothesis is an explicit argument rather than an instance, because
instance search does not cross the two spellings of the target category. -/
theorem isKInjective_mapHomologicalComplex_openSubschemeRestrictionOf (X : Scheme.{u})
    (U : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((openSubschemeRestrictionOf X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  ExtensionByZeroModules.isKInjective_jStar U (structureSheafRing X.toRingedSpace) I

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-! ### The degreewise crossing at the preimage open itself -/

/-- **Restriction of sections from `f⁻¹V` to `f⁻¹V`, read over `Γ(S, V)`, is an isomorphism.** It
is `…DerivedSectionsLeray.sectionsOverOpenRestrictLE` at `le_rfl` whiskered by restriction of
scalars along `f^♯` at `V`, so this is
`…DerivedSectionsLeray.isIso_sectionsOverOpenRestrict_le_refl` and
`CategoryTheory.Functor.isIso_whiskerRight`. The `inferInstanceAs` is what re-types the
declared `AlgebraicGeometry.Scheme.Hom.appLE` spelling of the target scalars to the whiskered
one. -/
instance isIso_preimageSectionsRestrictLE_le_refl :
    IsIso (preimageSectionsRestrictLE f V (le_refl (f ⁻¹ᵁ V))) :=
  inferInstanceAs (IsIso (Functor.whiskerRight
    (sectionsOverOpenRestrictLE X.toRingedSpace (le_refl (f ⁻¹ᵁ V)))
    (ModuleCat.restrictScalars (f.app V).hom)))

/-- **The degreewise open-subscheme crossing at `U = f⁻¹V` is an isomorphism.** Its three factors
are the restriction of sections at `le_rfl`, the crossing
`…TopDegreeBaseChange.sectionsOnImageTopNatIso` of the two sections functors inverted, and the
identification `…TopDegreeBaseChange.restrictScalarsSquareIso` of the two readings of the scalars;
the last two are isomorphisms by construction and the first is
`isIso_preimageSectionsRestrictLE_le_refl`.

The three are composed by `CategoryTheory.IsIso.comp_isIso'` and not by instance search: the
composite's middle objects sit at definitionally equal but differently spelled functors, and
`CategoryTheory.IsIso.comp_isIso` is keyed on them (see the implementation notes). -/
instance isIso_preimageSectionsOpenSubschemeLE_le_refl :
    IsIso (preimageSectionsOpenSubschemeLE f V (le_refl (f ⁻¹ᵁ V))) := by
  have h2 : IsIso (Functor.whiskerRight (sectionsOnImageTopNatIso X (f ⁻¹ᵁ V)).inv
      (ModuleCat.restrictScalars (f.appLE V (f ⁻¹ᵁ V) (le_refl (f ⁻¹ᵁ V))).hom)) :=
    inferInstance
  have h3 : IsIso (Functor.whiskerLeft
      (moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V) ⋙
        sectionsOverOpen ((f ⁻¹ᵁ V : X.Opens) : Scheme).toRingedSpace ⊤)
      (restrictScalarsSquareIso _ _ _ _
        (appLE_comp_topIso_inv_hom f V (le_refl (f ⁻¹ᵁ V)))).hom) := inferInstance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h2 h3)

/-! ### The derived target is a right derived functor whenever the crossing is invertible -/

variable {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-- **The open-subscheme derived target is a right derived functor of degreewise sections over
`f⁻¹V`, whenever the degreewise crossing is invertible.** For a morphism of schemes `f : X ⟶ S`,
an open `V ⊆ S`, an open `U ≤ f⁻¹V` of `X`, an **invertible** degreewise crossing `α` of sections
over `f⁻¹V` with their open-subscheme reading at `U`, and a functor `RP` on the derived category
upstairs that is a right derived functor of degreewise sections over `(f.resLE V U e)⁻¹⊤` at `u`,
the composite `…TopDegreeBaseChange.openSubschemeDerivedTargetOf X U V RP` together with
`…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit f V e α u` satisfies the universal property
of the total right derived functor of `Γ(f⁻¹V, -)`.

By `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
`.isRightDerivedFunctor_of_isIso_app_isKInjective` it is enough that the unit be invertible at a
K-injective complex `I`, and there its four factors are: `α` on the homotopy category, which is
invertible because `α` is; the splitting of the two exact factors, an isomorphism; `u` at the
restriction of `I` to the open subscheme, which is invertible because that restriction is again
K-injective ([Stacks, Tag 08BS]) and `RP` is a right derived functor ([Stacks, Tag 070K]); and the
comparison of restriction to the open subscheme with localization, an isomorphism.

**Nothing is assumed** of `f`, of `V`, of `U`, of `RP` or of `u` beyond the two stated hypotheses.
The invertibility of `α` is an explicit argument and not an instance; see the implementation
notes. -/
theorem isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit
    (α : preimageSections f.toLRSHom.toShHom V ⟶
      openSubschemeRestrictionOf X U ⋙
        preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) (hα : IsIso α)
    {RP : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (U : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RP.IsRightDerivedFunctor u (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (structureSheafRing (U : Scheme).toRingedSpace)) (ComplexShape.up ℤ))] :
    (openSubschemeDerivedTargetOf X U V RP).IsRightDerivedFunctor
      (openSubschemeUnitOfNatTransUnit f V e α u)
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective X.toRingedSpace) DerivedCategory.Qh _ _ fun I hI => ?_
  have := hα
  have h1 : IsIso ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj I)) := by
    change IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((NatIso.mapHomologicalComplex (asIso α) (ComplexShape.up ℤ)).hom.app I))
    infer_instance
  have h3 : IsIso (u.app
      (((openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj I))) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace)).2
      (L := DerivedCategory.Qh) RP u _
      (isKInjective_mapHomologicalComplex_openSubschemeRestrictionOf X U I hI)
  dsimp only [openSubschemeUnitOfNatTransUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map]
  infer_instance

/-! ### The two derived crossings at the preimage open itself -/

/-- **The open-subscheme reading of `RΓ(f⁻¹V, -)` at `U = f⁻¹V` is a right derived functor of
degreewise sections over `f⁻¹V`**, at `…TopDegreeBaseChange.openSubschemeSectionsUnitLE`. It is
`isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit` at the degreewise crossing, which
`isIso_preimageSectionsOpenSubschemeLE_le_refl` makes invertible there, and at the unit of
`RΓ((f.resLE V (f⁻¹V) le_rfl)⁻¹⊤, -)`. -/
instance isRightDerivedFunctor_openSubschemeSectionsUnitLE_le_refl :
    (derivedPreimageSectionsOpenSubschemeLE f V (le_refl (f ⁻¹ᵁ V))).IsRightDerivedFunctor
      (openSubschemeSectionsUnitLE f V (le_refl (f ⁻¹ᵁ V)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit f V (le_refl (f ⁻¹ᵁ V))
    (preimageSectionsOpenSubschemeLE f V (le_refl (f ⁻¹ᵁ V)))
    (isIso_preimageSectionsOpenSubschemeLE_le_refl f V)
    (derivedPreimageSectionsUnit
      (f.resLE V (f ⁻¹ᵁ V) (le_refl (f ⁻¹ᵁ V))).toLRSHom.toShHom ⊤)

/-- **The derived crossing out of `RΓ(f⁻¹V, -)` is an isomorphism at `U = f⁻¹V`**, with no
hypothesis on `f` or on `V`. Both ends are right derived functors of the same degreewise functor —
the target by `isRightDerivedFunctor_openSubschemeSectionsUnitLE_le_refl` — and
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE` is the
`CategoryTheory.Functor.rightDerivedDesc` between them, so this is
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`.

This is the one place the `LE` crossing is invertible: at a proper `U < f⁻¹V` the degreewise
crossing is the restriction of sections from `f⁻¹V` to `U` and is not, which is the measurement
`LerayOpenSubschemeSectionsLE.lean` records. -/
instance isIso_openSubschemeSectionsComparisonLE_le_refl :
    IsIso (openSubschemeSectionsComparisonLE f V (le_refl (f ⁻¹ᵁ V))) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V) _ _
    (openSubschemeSectionsUnitLE f V (le_refl (f ⁻¹ᵁ V)))).1 inferInstance

/-- **The derived crossing out of the Leray comparison's target is an isomorphism at `U = f⁻¹V`**,
with no hypothesis on `f` or on `V`.

Nothing new is checked: `…openSubschemeSectionsComparisonLE_comp_lerayComparison_eq` presents
`lerayComparison f V ≫ openSubschemeLerayComparisonLE` as the crossing out of `RΓ(f⁻¹V, -)`
followed by the Leray comparison for the restricted morphism whiskered, and both of those are
invertible — the first by `isIso_openSubschemeSectionsComparisonLE_le_refl`, the second by
[Stacks, Tag 0D5W]. Cancelling the invertible `lerayComparison f V` on the left is
`CategoryTheory.IsIso.of_isIso_comp_left`. -/
instance isIso_openSubschemeLerayComparisonLE_le_refl :
    IsIso (openSubschemeLerayComparisonLE f V (le_refl (f ⁻¹ᵁ V))) := by
  have hcomp : IsIso (openSubschemeSectionsComparisonLE f V (le_refl (f ⁻¹ᵁ V)) ≫
      Functor.whiskerLeft (openSubschemeRestrictionOf X (f ⁻¹ᵁ V)).mapDerivedCategory
        (Functor.whiskerRight (lerayComparison
            (f.resLE V (f ⁻¹ᵁ V) (le_refl (f ⁻¹ᵁ V))).toLRSHom.toShHom ⊤)
          (ModuleCat.restrictScalars
            (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) := by
    have := isIso_lerayComparison
      (f.resLE V (f ⁻¹ᵁ V) (le_refl (f ⁻¹ᵁ V))).toLRSHom.toShHom (⊤ : Opens (V : Scheme))
    infer_instance
  rw [openSubschemeSectionsComparisonLE_comp_lerayComparison_eq] at hcomp
  have := isIso_lerayComparison f.toLRSHom.toShHom V
  exact IsIso.of_isIso_comp_left (lerayComparison f.toLRSHom.toShHom V) _

/-! ### The same at the `morphismRestrict` spelling, which is the one the match consumes -/

/-- **The same brick at the `morphismRestrict` spelling of the restricted morphism.** For a
morphism of schemes `f : X ⟶ S`, an open `V ⊆ S`, an **isomorphism** `α` presenting degreewise
sections over `f⁻¹V` as their open-subscheme reading, and a functor `RP` on the derived category
upstairs that is a right derived functor of degreewise sections over `(f ∣_ V)⁻¹⊤` at `u`, the
composite `…TopDegreeBaseChange.openSubschemeDerivedTarget f V RP` together with
`…TopDegreeBaseChange.openSubschemeUnitOfIsoUnit f V α u` satisfies the universal property of the
total right derived functor of `Γ(f⁻¹V, -)`.

The proof is `isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit`'s, six lines, at the
`AlgebraicGeometry.Scheme.Hom.morphismRestrict` spelling of the upstairs morphism; it is a second
statement and not a transport, because `f.resLE V (f⁻¹V) le_rfl = f ∣_ V` is
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` and **not** `rfl`, so the scalars
`(f ∣_ V)^♯` inside `…DerivedSectionsLeray.preimageSections` are a different term. The restriction
factor is shared on the nose: `…TopDegreeBaseChange.openSubschemeRestriction f V` **is**
`…openSubschemeRestrictionOf X (f ⁻¹ᵁ V)`, which `…openSubschemeRestriction_eq` records by `rfl`,
so the K-injectivity input is the same lemma at the same open.

This is the spelling the match of conclusion (c) of [Stacks, Tag 0EX3] consumes: factor (1) is
matched at `q := f' ∣_ V`, by `…TopDegreeBaseChange.restrictScalars`
`_singleCompDerivedSectionsTop_inv_app_eq` and
`…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv`, so the crossing to the `γ⁺` side's
reading at `(f', V)` is the one below and not the `LE` one at `e = le_rfl`.

No invertibility hypothesis is needed here: `α` is an `Iso`, so `CategoryTheory.Iso.isIso_hom`
supplies it. **Nothing is assumed** of `f`, of `V`, of `RP` or of `u` beyond `RP` being a right
derived functor at `u`. -/
theorem isRightDerivedFunctor_openSubschemeUnitOfIsoUnit
    (α : preimageSections f.toLRSHom.toShHom V ≅
      openSubschemeRestriction f V ⋙
        preimageSections (f ∣_ V).toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    {RP : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))}
    (u : (preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RP.IsRightDerivedFunctor u (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) (ComplexShape.up ℤ))] :
    (openSubschemeDerivedTarget f V RP).IsRightDerivedFunctor
      (openSubschemeUnitOfIsoUnit f V α u)
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective X.toRingedSpace) DerivedCategory.Qh _ _ fun I hI => ?_
  have h1 : IsIso ((NatTrans.mapHomotopyCategory α.hom (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)).obj I)) := by
    change IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom.app I))
    infer_instance
  have h3 : IsIso (u.app
      (((openSubschemeRestriction f V).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)).obj I))) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((preimageSections (f ∣_ V).toLRSHom.toShHom ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective (f ⁻¹ᵁ V : Scheme).toRingedSpace)).2
      (L := DerivedCategory.Qh) RP u _
      (isKInjective_mapHomologicalComplex_openSubschemeRestrictionOf X (f ⁻¹ᵁ V) I hI)
  dsimp only [openSubschemeUnitOfIsoUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map]
  infer_instance

/-- **The open-subscheme reading of `RΓ(f⁻¹V, -)` is a right derived functor of degreewise sections
over `f⁻¹V`**, at `…TopDegreeBaseChange.openSubschemeSectionsUnit`. It is
`isRightDerivedFunctor_openSubschemeUnitOfIsoUnit` at the `γ⁺` route's presentation
`…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso` of the degreewise crossing and at the unit
of `RΓ((f ∣_ V)⁻¹⊤, -)`.

By `…TopDegreeBaseChange.openSubschemeSectionsUnit_eq` the `ψ` route's unit is the same
transformation, so no second instance at
`…TopDegreeBaseChange.openSubschemePushforwardUnit` is declared. -/
instance isRightDerivedFunctor_openSubschemeSectionsUnit :
    (derivedPreimageSectionsOpenSubscheme f V).IsRightDerivedFunctor
      (openSubschemeSectionsUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_openSubschemeUnitOfIsoUnit f V
    (preimageSectionsOpenSubschemeIso f V)
    (derivedPreimageSectionsUnit (f ∣_ V).toLRSHom.toShHom ⊤)

/-- **The derived crossing of sections over `f⁻¹V` with their reading on the open subscheme is an
isomorphism**, with no hypothesis on `f` or on `V`. Both ends are right derived functors of the
same degreewise functor — the target by `isRightDerivedFunctor_openSubschemeSectionsUnit` — and
`…TopDegreeBaseChange.openSubschemeSectionsComparison` is the
`CategoryTheory.Functor.rightDerivedDesc` between them, so this is
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`.

**This is the crossing the tail of conclusion (c) of [Stacks, Tag 0EX3] needs between the two
readings of its `γ⁺` prefix**, at `(f', V)` on `X'` and at `((f' ∣_ V), ⊤)` on the open subscheme.
Being invertible it may be taken in either direction; the equation that transports factor (1)'s
match across it is a separate step and is not performed here. -/
instance isIso_openSubschemeSectionsComparison :
    IsIso (openSubschemeSectionsComparison f V) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V) _ _
    (openSubschemeSectionsUnit f V)).1 inferInstance

/-- **The derived crossing out of the Leray comparison's target is an isomorphism**, with no
hypothesis on `f` or on `V`. It is `isIso_openSubschemeLerayComparisonLE_le_refl`'s argument at
the `morphismRestrict` spelling: `…openSubschemeSectionsComparison_comp_lerayComparison_eq`
presents `lerayComparison f V ≫ openSubschemeLerayComparison` as two invertible factors, and the
invertible `lerayComparison f V` cancels on the left. [Stacks, Tag 0D5W] is not re-proved. -/
instance isIso_openSubschemeLerayComparison :
    IsIso (openSubschemeLerayComparison f V) := by
  have hcomp : IsIso (openSubschemeSectionsComparison f V ≫
      Functor.whiskerLeft (openSubschemeRestriction f V).mapDerivedCategory
        (Functor.whiskerRight (lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤)
          (ModuleCat.restrictScalars
            (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) := by
    have := isIso_lerayComparison (f ∣_ V).toLRSHom.toShHom (⊤ : Opens (V : Scheme))
    infer_instance
  rw [openSubschemeSectionsComparison_comp_lerayComparison_eq] at hcomp
  have := isIso_lerayComparison f.toLRSHom.toShHom V
  exact IsIso.of_isIso_comp_left (lerayComparison f.toLRSHom.toShHom V) _

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
