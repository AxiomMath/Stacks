module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CohomologySheavesOfADerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayRestrictionSquareProof
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionSquareProof
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RestrictionOfDerivedSections

/-!
# Restriction in the open, on the values of the preimage cohomology presheaf

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `V' ⊆ V` be opens of `Y` and
let `K` be an object of `D(𝒪_X)`.  The presheaf `V ↦ H^i(f⁻¹ V, K)` of [Stacks, Tag 0D5X] is
built as the degree-`i` cohomology of derived sections of `Rf_* K` taken on all opens of `Y` at
once, so its restriction maps come from the presheaf of modules and not from any identification
with hypercohomology over an inverse image; the identification of its values,
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso`, is therefore not
*a priori* compatible with restricting from `V` to `V'`.  This file proves that it is.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrictHomology`: restriction
  in the open on degree-`i` cohomology of derived sections over an inverse image,
  `H^i(f⁻¹ V, -) ⟶ H^i(f⁻¹ V', -) ⋙ Res_ρ`.

## Main results

* `Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso_restrict`: the
  restriction square of `preimageCohomologyEvaluationIso`, object-wise in `K`.

## References

* [Stacks Project, Tag 0D5X](https://stacks.math.columbia.edu/tag/0D5X)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Restriction in the open, on degree-`i` cohomology of derived sections over an inverse
image.**  `H^i(f⁻¹ V, -) ⟶ H^i(f⁻¹ V', -) ⋙ Res_ρ`, where `ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`: the
derived restriction `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrict`, read
on homology through the commutation of the exact functor `Res_ρ` with homology. -/
def derivedPreimageSectionsRestrictHomology {V V' : Opens Y.carrier} (hV : V' ≤ V) (i : ℤ) :
    derivedPreimageSections f V ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i ⟶
      (derivedPreimageSections f V' ⋙
          DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))) i) ⋙
        ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom :=
  Functor.whiskerRight (derivedPreimageSectionsRestrict f hV)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i) ≫
    Functor.whiskerLeft (derivedPreimageSections f V')
      (Stacks.Homology.derivedHomologyIso
        (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i).hom

end Stacks.Cohomology.DerivedSectionsLeray

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

attribute [local instance] isGrothendieckAbelian_moduleSheaves

/-- **Four squares pasted along a common factorization of the top edge.**  The top path `q ≫ r`
of the outer square refactors as `q' ≫ r'`; `r'` fits into a square with `s`, and the two
resulting halves are the squares `F3` and `F4`. -/
theorem square_paste_four {Z : Type*} [Category* Z] {a b c d e g₁ g₂ g₃ : Z}
    {p : a ⟶ b} {q : b ⟶ c} {r : c ⟶ d} {s : d ⟶ e}
    {q' : b ⟶ g₁} {r' : g₁ ⟶ d} {s' : g₁ ⟶ g₂} {v : g₂ ⟶ e}
    {t : a ⟶ g₃} {w : g₃ ⟶ g₂} {u : g₃ ⟶ e}
    (F1 : q ≫ r = q' ≫ r') (F2 : r' ≫ s = s' ≫ v) (F3 : p ≫ q' ≫ s' = t ≫ w)
    (F4 : w ≫ v = u) : (p ≫ q) ≫ r ≫ s = t ≫ u := by
  simp only [Category.assoc, reassoc_of% F1, F2, reassoc_of% F3, F4]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The restriction square of the value identification of [Stacks, Tag 0D5X].**  Evaluating the
presheaf `V ↦ H^i(f⁻¹ V, K)` of `Rf_* K` and identifying the value with hypercohomology over the
inverse image commutes with restricting from `V` to `V'`: the identification at `V` followed by
restriction on the cohomology of derived sections over `f⁻¹ V` is the restriction map of the
presheaf of modules followed by the identification at `V'`, read through restriction of scalars
along `ρ : Γ(V, 𝒪_Y) ⟶ Γ(V', 𝒪_Y)`. -/
theorem preimageCohomologyEvaluationIso_restrict {V V' : Opens Y.carrier} (hV : V' ≤ V) (i : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (preimageCohomologyEvaluationIso f V i).hom.app K ≫
        (Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrictHomology
          f hV i).app K =
      (PresheafOfModules.restriction (structureSheafRing Y).obj hV.hom.op).app
          ((DerivedCategory.homologyFunctor
              (PresheafOfModules.{u} (structureSheafRing Y).obj) i).obj
            ((Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf
                (structureSheafRing Y)).obj
              ((derivedPushforward f).obj K))) ≫
        (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((preimageCohomologyEvaluationIso f V' i).hom.app K) := by
  have F1 : (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso
            f V).hom.app K) ≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsRestrict
            f hV).app K) =
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrict Y hV).app
            ((derivedPushforward f).obj K)) ≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
          ((Stacks.Cohomology.DerivedSectionsLeray.restrictScalarsDerived Y hV).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso
              f V').hom.app K)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso_restrict f hV K]
  have F2 : (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
          ((Stacks.Cohomology.DerivedSectionsLeray.restrictScalarsDerived Y hV).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso
              f V').hom.app K)) ≫
        (Stacks.Homology.derivedHomologyIso
            (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i).hom.app
          ((Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V').obj K) =
      (Stacks.Homology.derivedHomologyIso
            (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i).hom.app
          ((derivedPushforward f ⋙
            Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Y V').obj K) ≫
        (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))) i).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso
              f V').hom.app K)) :=
    (Stacks.Homology.derivedHomologyIso
      (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i).hom.naturality _
  have F3 : (Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso
            (structureSheafRing Y) V i).hom.app ((derivedPushforward f).obj K) ≫
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenRestrict Y hV).app
              ((derivedPushforward f).obj K)) ≫
          (Stacks.Homology.derivedHomologyIso
              (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom) i).hom.app
            ((derivedPushforward f ⋙
              Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Y V').obj K)) =
      (PresheafOfModules.restriction (structureSheafRing Y).obj hV.hom.op).app
          ((DerivedCategory.homologyFunctor
              (PresheafOfModules.{u} (structureSheafRing Y).obj) i).obj
            ((Stacks.Cohomology.HypercohomologyEdge.derivedSectionsPresheaf
                (structureSheafRing Y)).obj
              ((derivedPushforward f).obj K))) ≫
        (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso
            (structureSheafRing Y) V' i).hom.app ((derivedPushforward f).obj K)) :=
    Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict
      (structureSheafRing Y) hV.hom i ((derivedPushforward f).obj K)
  have F4 : (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso
            (structureSheafRing Y) V' i).hom.app ((derivedPushforward f).obj K)) ≫
        (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V'))) i).map
            ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso
              f V').hom.app K)) =
      (ModuleCat.restrictScalars ((structureSheafRing Y).obj.map hV.hom.op).hom).map
          ((preimageCohomologyEvaluationIso f V' i).hom.app K) :=
    (CategoryTheory.Functor.map_comp _ _ _).symm
  exact square_paste_four F1 F2 F3 F4

end Stacks.Cohomology.UnboundedHigherDirectImage

end
