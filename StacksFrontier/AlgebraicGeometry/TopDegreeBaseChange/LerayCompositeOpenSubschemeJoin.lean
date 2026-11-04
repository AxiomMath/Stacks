module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayCompositeAbsolute
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerivedLE

/-!
# Brick (ii) of the 2b(B) match joined to the `LE` Leray compatibility

The Leray half of the 2b(B) match of [Stacks, Tag 0EX3] (c) has two proved bricks and the
absolute Leray comparison of `i` over `p⁻¹V` standing between them:

* **brick (ii)**, `Stacks.Cohomology.DerivedSectionsLeray`
  `.derivedPreimageSectionsCompIso_hom_comp_lerayComparison` (`LerayCompositeAbsolute.lean`), which
  identifies the relative Leray comparison inverted — the form the `γ⁺` side carries it in, as the
  second leading factor of `Stacks.Cohomology.DerivedBaseChange`
  `.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` — with
  `Stacks.EdgeCompat.preimageSectionsModelComparison p V` whiskered, through
  `…DerivedSectionsLeray.lerayComparison i ((opensMap p).obj V)`;
* the **`LE` Leray compatibility**,
  `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_lerayComparison_eq`
  (`LerayOpenSubschemeDerivedLE.lean`), which carries that same absolute Leray comparison to
  `…DerivedSectionsLeray.lerayComparison (i.resLE (p⁻¹V) U e) ⊤` on the open subscheme — which is
  the Leray comparison the `ψ` side's factor (3) is a left inverse of, `i.resLE (p⁻¹V) U e` being
  `h'.resLE (f'⁻¹V) (f''⁻¹W)` at the match's own data.

This file eliminates the absolute Leray comparison between them, leaving the open-subscheme Leray
comparison on one side and `preimageSectionsModelComparison p V` on the other.

## Main results

* `…TopDegreeBaseChange.lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq` — **the
  join.** For morphisms of schemes `i : Z ⟶ X` and `p : X ⟶ Y`, an open `V ⊆ Y` and an open
  `U ≤ i⁻¹(p⁻¹V)` of `Z`,

  > the comparison of the two models of `RΓ((p ∘ i)⁻¹V, -)`, then
  > `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE i (p⁻¹V) e` followed by the Leray
  > comparison on the open subscheme, both whiskered by restriction of scalars along `p^♯`, is the
  > relative Leray comparison inverted, then `preimageSectionsModelComparison p V` whiskered by
  > `Ri_*`, then `…TopDegreeBaseChange.openSubschemeLerayComparisonLE i (p⁻¹V) e` whiskered by the
  > scalars.

  Nothing is assumed of `i`, of `p`, of `V`, of `U` or of the module — no affineness, no
  acyclicity, no boundedness and no quasi-coherence.

## Implementation notes

*No inverse is taken that was not already available.* The only inversion is of
`…DerivedSectionsLeray.derivedPreimageSectionsCompIso`, which brick (ii) already writes in the
inverted direction and which is unconditionally invertible by
`…DerivedSectionsLeray.isIso_lerayCompositeComparison`; in particular neither
`derivedPreimageSectionsCompModel` nor `openSubschemeLerayComparisonLE` nor either model comparison
is inverted anywhere. The move is: postcompose brick (ii) by
`openSubschemeLerayComparisonLE` whiskered, so that the two Leray factors fuse by
`CategoryTheory.Functor.whiskerRight_comp`, and then substitute the `LE` compatibility for the
fused pair.

*The splice is a private lemma at variables of an abstract category*, so that the one definitional
crossing the statement makes — `(opensMap p).obj V` against `p ⁻¹ᵁ V`, which is `rfl` — is not
re-made by the proof. The `γ⁺`-side spelling is written first, that being where brick (ii) lives.

*What this does not do.* The `ψ` side's factor (3) is a **left inverse** of the degree-`d`
cohomology of the open-subscheme Leray comparison, handed in as a hypothesis by
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`, and it is
read under `Hᵈ` rather than at the level of transformations. Transposing this join through that
left inverse and through `Hᵈ` is a further step and is not performed here.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file, and [Stacks, Tag 0D5W] carries its own where it is proved.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (lerayComparison derivedPreimageSectionsCompModel
  derivedPreimageSectionsCompIso derivedPreimageSectionsCompIso_hom_comp_lerayComparison)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsModelComparison)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Splicing a known factorisation of a middle factor into a composite.** From `s = u ≫ v` and
`m ≫ u = w₁ ≫ w₂` one gets `m ≫ s = w₁ ≫ w₂ ≫ v`. Nothing is assumed of any of the morphisms, so
no inverse is taken. Stated at variables of an abstract category, where the reassociation is free
and no definitional crossing is made. -/
private theorem splice {C : Type*} [Category* C] {A B₀ B₁ T P : C}
    {m : A ⟶ B₀} {s : B₀ ⟶ T} {u : B₀ ⟶ B₁} {v : B₁ ⟶ T} (hs : s = u ≫ v)
    {w₁ : A ⟶ P} {w₂ : P ⟶ B₁} (hw : m ≫ u = w₁ ≫ w₂) :
    m ≫ s = w₁ ≫ w₂ ≫ v := by
  rw [hs, ← Category.assoc, hw, Category.assoc]

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Y.Opens) {U : Z.Opens}
  (e : U ≤ i ⁻¹ᵁ (p ⁻¹ᵁ V))

/-- **Brick (ii) joined to the `LE` Leray compatibility.** For morphisms of schemes `i : Z ⟶ X`
and `p : X ⟶ Y`, an open `V ⊆ Y` and an open `U ≤ i⁻¹(p⁻¹V)` of `Z`,

> `…DerivedSectionsLeray.derivedPreimageSectionsCompModel i p V` — the comparison of the two models
> of `RΓ((p ∘ i)⁻¹V, -)` — followed by
> `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE i (p⁻¹V) e` and the Leray comparison of
> [Stacks, Tag 0D5W] for `i.resLE (p⁻¹V) U e` over the whole of the open subscheme, whiskered by
> restriction of scalars along `p^♯`, is
> `…DerivedSectionsLeray.derivedPreimageSectionsCompIso i p V` **inverted**, then
> `Stacks.EdgeCompat.preimageSectionsModelComparison p V` whiskered by `Ri_*`, then
> `…TopDegreeBaseChange.openSubschemeLerayComparisonLE i (p⁻¹V) e` whiskered by the scalars.

The absolute Leray comparison `lerayComparison i (p⁻¹V)`, which both of the two bricks name and
which the match does not want, is eliminated: brick (ii) is postcomposed by
`openSubschemeLerayComparisonLE` whiskered, the two Leray factors fuse by
`CategoryTheory.Functor.whiskerRight_comp`, and the `LE` compatibility replaces the fused pair. The
only inverse taken is `derivedPreimageSectionsCompIso`'s, which brick (ii) already writes inverted
and which is unconditional.

**Nothing is assumed** of `i`, of `p`, of `V`, of `U` or of the module; in particular no
affineness, no acyclicity, no boundedness and no quasi-coherence. -/
theorem lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq :
    derivedPreimageSectionsCompModel i.toLRSHom.toShHom p.toLRSHom.toShHom V ≫
        Functor.whiskerRight
            (openSubschemeSectionsComparisonLE i (p ⁻¹ᵁ V) e ≫
              Functor.whiskerLeft (openSubschemeRestrictionOf Z U).mapDerivedCategory
                (Functor.whiskerRight
                  (lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤)
                  (ModuleCat.restrictScalars
                    (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom).mapDerivedCategory))
            (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory =
      (derivedPreimageSectionsCompIso i.toLRSHom.toShHom p.toLRSHom.toShHom V).inv ≫
        Functor.whiskerLeft (derivedPushforward i.toLRSHom.toShHom)
            (preimageSectionsModelComparison p.toLRSHom.toShHom V) ≫
          Functor.whiskerRight (openSubschemeLerayComparisonLE i (p ⁻¹ᵁ V) e)
            (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory :=
  splice
    ((congrArg
      (fun z => Functor.whiskerRight z
        (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory)
      (openSubschemeSectionsComparisonLE_comp_lerayComparison_eq i (p ⁻¹ᵁ V) e)).trans
        (Functor.whiskerRight_comp _ _ _))
    ((Iso.eq_inv_comp _).mpr
      (derivedPreimageSectionsCompIso_hom_comp_lerayComparison
        i.toLRSHom.toShHom p.toLRSHom.toShHom V))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
