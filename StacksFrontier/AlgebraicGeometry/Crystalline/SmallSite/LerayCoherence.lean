module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayCoherenceSquare
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiPushforwardLeray
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso

/-!
# The coherence of the four Leray comparisons across the crystalline–Zariski square

For a morphism of global crystalline situations, `RΓ(Cris(X'/S), -)` is identified with
`Ru_{X'/S, *} ⋙ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)` in two ways, by composing Leray comparisons and the
derived square of topoi. The edges are the following isomorphisms of functors, in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`:

* `derivedCrisGlobalSectionsIso`: `RΓ(Cris(X'/S), -) ≅ Rf_{cris, *} ⋙ RΓ(Cris(X/S), -)`;
* `derivedGlobalSectionsIsoDerivedZariskiDirectImage`, at the target and at the source
  situation: `RΓ(Cris(X/S), -) ≅ Ru_{X/S, *} ⋙ RΓ(X_Zar, -)`, and the same for `u_{X'/S}`;
* `derivedZariskiGlobalSectionsIsoPushforward`: `RΓ(X'_Zar, -) ≅ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`;
* `derivedZariskiSquare` at `crisZariskiSquare`: the derived square of topoi
  `Rf_{cris, *} ⋙ Ru_{X/S, *} ≅ Ru_{X'/S, *} ⋙ Rf_{Zar, *}`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrisZariskiLerayCoherence`: the proposition
  that the two routes around the square agree.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiLerayCoherence_of_underived`:
  the coherence follows from the coherence of the underived comparisons of global sections.
* In `Crystalline.GlobalCrystallineSituation.SmallSite`,
  `derivedZariskiGlobalSections_map_derivedZariskiComparison`: under the coherence,
  `RΓ(X_Zar, -)` applied to the derived Zariski comparison is `derivedCrisPullbackMap`, read
  through the Leray factorizations.

## References

* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- The coherence of the four Leray comparisons across the square of topoi, as a proposition.

Going round one way, `RΓ(Cris(X'/S), -)` is factored along `f_{cris}` and then the inner
`RΓ(Cris(X/S), -)` along `u_{X/S}`, and the result is carried across the derived square of
topoi; going round the other way it is factored along `u_{X'/S}` and the inner
`RΓ(X'_Zar, -)` along `f_{Zar}`. Both routes are isomorphisms

`RΓ(Cris(X'/S), -) ≅ Ru_{X'/S, *} ⋙ Rf_{Zar, *} ⋙ RΓ(X_Zar, -)`,

and the proposition is that they agree. -/
def CrisZariskiLerayCoherence : Prop :=
  (derivedCrisGlobalSectionsIso S S' fS fX hf).hom ≫
      Functor.whiskerLeft (derivedCrisDirectImageFunctor S S' fS fX hf)
        (derivedGlobalSectionsIsoDerivedZariskiDirectImage S').hom ≫
      Functor.whiskerRight (derivedZariskiSquare S S' fS fX hf
        (crisZariskiSquare S S' fS fX hf)).hom (derivedZariskiGlobalSectionsFunctor S') =
    (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom ≫
      Functor.whiskerLeft (derivedZariskiDirectImageFunctor S)
        (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom

/-- The derived coherence square follows from the underived one: if the two routes

`Γ(X_Zar, u_{X/S, *}f_{cris, *}ℋ) ⟶ Γ(Cris(X'/S), ℋ)`

agree for every abelian sheaf `ℋ` on `Cris(X'/S)` — one going through
`zariskiGlobalSectionsDirectImageIso` and `crisGlobalSectionsIso`, the other through the `2`-cell
of the square of topoi, the comparison for `f_{Zar}` and the comparison for `u_{X'/S}` — then
`CrisZariskiLerayCoherence` holds. -/
theorem crisZariskiLerayCoherence_of_underived
    (hund : ∀ H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1},
      (zariskiGlobalSectionsDirectImageIso S').hom.app
            ((crisDirectImage S S' fS fX hf).obj H) ≫
          (crisGlobalSectionsIso S S' fS fX hf).hom.app H =
        (zariskiGlobalSections S').map ((crisZariskiSquare S S' fS fX hf).hom.app H) ≫
          (zariskiPushforwardGlobalSectionsIso S S' fX).hom.app
            ((zariskiDirectImage S).obj H) ≫
          (zariskiGlobalSectionsDirectImageIso S).hom.app H) :
    CrisZariskiLerayCoherence S S' fS fX hf :=
  Stacks.DerivedFunctor.LeraySquare.derived_coherence
    (crisZariskiSquare S S' fS fX hf) (crisGlobalSectionsIso S S' fS fX hf)
    (zariskiGlobalSectionsDirectImageIso S') (zariskiGlobalSectionsDirectImageIso S)
    (zariskiPushforwardGlobalSectionsIso S S' fX) hund

/-- If `CrisZariskiLerayCoherence` holds, then the map

`RΓ(X_Zar, -)` applied to `Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'`

is `derivedCrisPullbackMap`, read through the Leray factorization of `RΓ(Cris(X/S), -)` along
`u_{X/S}` on the source and through the two factorizations along `u_{X'/S}` and `f_{Zar}` on the
target. -/
theorem derivedZariskiGlobalSections_map_derivedZariskiComparison
    (hcoh : CrisZariskiLerayCoherence S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    (derivedGlobalSectionsIsoDerivedZariskiDirectImage S').hom.app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (derivedZariskiGlobalSectionsFunctor S').map
          (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F) =
      derivedCrisPullbackMap S S' fS fX hf F ≫
        (derivedGlobalSectionsIsoDerivedZariskiDirectImage S).hom.app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
              (crisPullback S S' fS fX hf F)) ≫
        (derivedZariskiGlobalSectionsIsoPushforward S S' fX).hom.app
          ((derivedZariskiDirectImageFunctor S).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
                (crisPullback S S' fS fX hf F))) := by
  have hnat := (derivedGlobalSectionsIsoDerivedZariskiDirectImage S').hom.naturality
    (derivedCrisUnit S S' fS fX hf F)
  have hat := NatTrans.congr_app hcoh
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
        (crisPullback S S' fS fX hf F))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hat
  simp only [Functor.comp_map] at hnat
  dsimp only [derivedZariskiComparison, derivedCrisPullbackMap,
    derivedZariskiDirectImage, derivedGlobalSections, Functor.comp_obj]
  rw [← hat]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp, ← Category.assoc, ← hnat, Category.assoc]

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
