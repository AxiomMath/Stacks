module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleBoundedBelowEquivalence

/-!
# `La^*` is an equivalence `D⁺(O_X) ≌ D⁺_𝒜(O)` for a hypercovering of an object

Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of `C`,
let `O_C` be a sheaf of commutative rings on `C` and let `K` be a hypercovering of `X`
(Stacks 01G5). With `O_X = O_C|_{C/X}`, `O = a⁻¹O_X` on the total site `(C/K)_total` and
`a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)` the ringed augmentation of Remarks 0D9V and 0D9X,
**Stacks 0DA7** asserts that the cartesian `O`-modules form a weak Serre subcategory
`𝒜 ⊂ Mod(O)` and that `La^*` defines an equivalence

`D⁺(O_X) ⟶ D⁺_𝒜(O)`

with quasi-inverse `R a_*`.

The source deduces it from Stacks 0DA2 applied to the site `C/X`, which has a final object and
fibre products. Here the argument of Stacks 0DA2 is run directly over `C/X`, in
`HypercoveringObjectModuleBoundedBelowEquivalence.lean` in this directory: the weak Serre
property is Stacks 0D7J (2) for the cartesian structure sheaf `O = a⁻¹O_X`
(`isWeakSerreClass_isModuleFiberTransitionIso_over`), and the equivalence is the restriction of the
derived adjunction `La^* ⊣ R a_*` (`derivedPullbackEquivalenceOfIsHypercovering`), with unit
invertible by Stacks 0DA5 and counit invertible on `D⁺_𝒜(O)` by Stacks 0DA4. This file states the
lemma for an arbitrary hypercovering `K` of `X`; Stacks 0DAE is its special case for a
hypercovering by a simplicial object of `C`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.exists_derivedPullbackEquivalence_isHypercovering`:
  **Stacks 0DA7**.

## References

* [Stacks Project, Tag 0DA7](https://stacks.math.columbia.edu/tag/0DA7)
* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0D9V](https://stacks.math.columbia.edu/tag/0D9V)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of
`C`, let `O_C` be a sheaf of commutative rings on `C` and let `K` be a hypercovering of `X`
(Stacks 01G5: a simplicial object of `SR(C, X)` whose degree-zero family covers `X` and
whose matching maps `K_{n+1} ⟶ (cosk_n sk_n K)_{n+1}` are covering). Let `O_X = O_C|_{C/X}`, let
`O = a⁻¹O_X` on the total site `(C/K)_total` and let `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)`
be the ringed augmentation of Remarks 0D9V and 0D9X. Then

* the cartesian `O`-modules form a weak Serre subcategory `𝒜 ⊂ Mod(O)`, and
* the functor `La^*` defines an equivalence `D⁺(O_X) ⟶ D⁺_𝒜(O)` with quasi-inverse `R a_*`:
  there is an equivalence of categories whose functor, followed by the inclusion of `D⁺_𝒜(O)`, is
  `La^*` on `D⁺(O_X)`, and whose inverse, followed by the inclusion of `D⁺(O_X)`, is `R a_*` on
  `D⁺_𝒜(O)`.

Here `D⁺(O_X)` is the full subcategory of bounded below objects of `D(O_X)`, and `D⁺_𝒜(O)` that of
bounded below objects of `D(O)` all of whose cohomology modules are cartesian. Nothing is assumed
beyond the hypotheses of the source; the equivalence is
`derivedPullbackEquivalenceOfIsHypercovering`. -/
@[stacks 0DA7]
theorem exists_derivedPullbackEquivalence_isHypercovering (hK : IsHypercovering P K) :
    ObjectProperty.IsWeakSerreClass
        ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P K OC).O) ∧
      ∃ e : (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).FullSubcategory ≌
          (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
            ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
              (hypercoveringObjectRingedAugmentation P K OC).O)).FullSubcategory,
        e.functor ⋙ (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
            ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
              (hypercoveringObjectRingedAugmentation P K OC).O)).ι =
          (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).ι ⋙
            (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp (X := totalTopos P K OC)
              (Y := sliceTopos P K OC) (augmentationHom P K OC)).functor ∧
        e.inverse ⋙ (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).ι =
          (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
            ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
              (hypercoveringObjectRingedAugmentation P K OC).O)).ι ⋙
            Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := totalTopos P K OC)
              (Y := sliceTopos P K OC) (augmentationHom P K OC) :=
  ⟨isWeakSerreClass_isModuleFiberTransitionIso_over P K OC,
    derivedPullbackEquivalenceOfIsHypercovering P K OC hK,
    derivedPullbackEquivalenceOfIsHypercovering_functor P K OC hK,
    derivedPullbackEquivalenceOfIsHypercovering_inverse P K OC hK⟩

end CategoryTheory.SimplicialSemiRepresentable

end
