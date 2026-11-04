module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The projection of a fibred category as a 1-morphism of fibred categories

Let `(D, O_D)` be a ringed site and `p : C ⥤ D` a fibred category over its underlying site, the
standing data of Stacks 08P8. The base `D` is a fibred category over itself by the identity
functor, and `p` is a 1-morphism of fibred categories over `D` from `p : C ⥤ D` to `𝟭 D`. So the
standing data of Stacks 08PA is available with the target fibred category taken to be `D` and the
1-morphism taken to be `p`, and then the morphism of topoi `g : Sh(C) ⟶ Sh(D)` of Stacks 08PA is
the projection `π` of Stacks 08P8: the two are built from the same functor `p` between the same
two sites, the topology `D` inherits from itself along the identity being its own topology.

This is the reduction of Stacks 09CY. Under it the lower-shriek functors of Stacks 08PC become
the `π_!`, `π_!^{Ab}`, `Lπ_!` and `Lπ_!^{Ab}` of Stacks 08P8.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.toMorphismSituation`: the standing data of
  Stacks 08PA obtained from that of Stacks 08P8.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.toMorphismSituation_u`,
  `.toMorphismSituation_sourceTopology` and `.toMorphismSituation_totalTopology`: the three data
  from which Stacks 08PA builds `g` are the three from which Stacks 08P8 builds `π`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianInverseImage_toMorphismSituation`
  and `.abelianLowerShriek_toMorphismSituation`: `g^{-1}` and `g_!^{Ab}` of the reduced situation
  are `π^{-1}` and `π_!^{Ab}`.

## Where the four functors of Stacks 09CY are

Remark 09CY reads off from Lemma 08PC four functors for Situation 08P8 and two equalities. All are
proved for Situation 08P8, under its hypotheses alone:

* `π_!^{Ab}` is `FibredCategorySituation.abelianLowerShriek`, identified with the reduced
  situation's `g_!^{Ab}` by `abelianLowerShriek_toMorphismSituation` below;
* `π_!` on sheaves of modules, left adjoint to `π^*`, is
  `FibredCategorySituation.moduleLowerShriekAdjunction` in `ProjectionModuleLowerShriek.lean`;
* `Lπ_!^{Ab}`, left adjoint to `π^{-1}`, is
  `FibredCategorySituation.derivedAbelianLowerShriekAdjunctionUnconditional` in
  `ProjectionLowerShriekAcyclic.lean`;
* `Lπ_!` on sheaves of modules, left adjoint to `π^*`, is
  `FibredCategorySituation.derivedModuleLowerShriekAdjunctionAtBaseModuleRing` in
  `ProjectionModuleDerivedLowerShriek.lean`;
* `forget ∘ π_! = π_!^{Ab} ∘ forget` is
  `FibredCategorySituation.isIso_moduleLowerShriekForgetComparison`, the canonical comparison of
  Stacks 0798 being an isomorphism;
* `forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget` is
  `FibredCategorySituation.isIso_derivedModuleLowerShriekForgetComparison`, the canonical
  comparison of Stacks 07AE being an isomorphism.

These are the statements of Lemma 08PC for the reduced situation, proved directly at Situation
08P8 rather than transported along the reduction: the reduced target ringed topos is
`(Sh(D), π_D⁻¹O_D)` for the identity-induced `π_D`, which is isomorphic but not equal to
`(Sh(D), O_D)`, so its categories of modules are not the ones Situation 08P8 speaks of. The proofs
follow the source's: the section of Stacks 08P9 — the case of Stacks 08PB at hand — makes the
comparison maps `(π_U)_!^{Ab} O_U ⟶ O_{p(U)}` invertible, which by Stacks 0798 gives the
underived equality, and makes the underlying abelian sheaves of the `j_{U!} O_U` acyclic for
`π_!^{Ab}`, which gives `Lπ_!` and, by Stacks 07AE, the derived equality.

## A slip in the source

Stacks 09CY reads "setting `C' = D` and `u` equal to the structure functor of `C`". Those two
clauses are inconsistent: Situation 08PA has `u : C' ⥤ C`, while the structure functor of `C` is
`p : C ⥤ D`, so taking `u = p` forces `C' = C` and `C = D`, not `C' = D`. The second clause is the
one that fixes the content — it is what makes `g` equal to `π`, which is what the rest of the
remark is about — so the reduction formalized here is `C' = C`, `C = D`, `u = p`.

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w

namespace FibredCategorySituation

section Reduction

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- **Stacks 09CY, the reduction.** The standing data of Stacks 08PA obtained from that of
Stacks 08P8: the same ringed base site, the target fibred category taken to be the base itself
fibred over itself by the identity functor, the source fibred category taken to be `C`, and the
1-morphism taken to be the structure functor `p`. -/
@[stacks 09CY "the reduction of Situation 08P8 to Situation 08PA, by `C = D` and `u = p`"]
def toMorphismSituation : MorphismSituation.{uD, uD, uC, vD, vD, vC, w} where
  base := s.base
  total := s.base.C
  source := s.C
  p := 𝟭 s.base.C
  p' := s.p
  u := s.p
  pFibered := CategoryTheory.Functor.isFiberedInGroupoids_id.isFibered
  isFibredOneMorphism := CategoryTheory.Functor.isFibredOneMorphism_id s.p

/-- The reduced situation has the same ringed base site. -/
@[simp] theorem toMorphismSituation_base : s.toMorphismSituation.base = s.base := rfl

/-- The source fibred category of the reduced situation is `C`. -/
@[simp] theorem toMorphismSituation_source : s.toMorphismSituation.source = s.C := rfl

/-- The target fibred category of the reduced situation is the base category `D`. -/
@[simp] theorem toMorphismSituation_total : s.toMorphismSituation.total = s.base.C := rfl

/-- The target's structure functor in the reduced situation is the identity of `D`. -/
@[simp] theorem toMorphismSituation_p : s.toMorphismSituation.p = 𝟭 s.base.C := rfl

/-- The source's structure functor in the reduced situation is `p`. -/
@[simp] theorem toMorphismSituation_p' : s.toMorphismSituation.p' = s.p := rfl

/-- The 1-morphism of the reduced situation is the structure functor `p`. This is the clause of
Stacks 09CY that fixes the reduction. -/
@[simp] theorem toMorphismSituation_u : s.toMorphismSituation.u = s.p := rfl

/-- The topology the source fibred category inherits in the reduced situation is the topology `C`
inherits from `D` in Stacks 08P8. -/
@[simp] theorem toMorphismSituation_sourceTopology :
    s.toMorphismSituation.sourceTopology = s.topology := rfl

/-- The topology the target fibred category inherits in the reduced situation is the topology of
the base site itself: the topology a category inherits from its own topology along the identity
functor is that topology. -/
@[simp] theorem toMorphismSituation_totalTopology :
    s.toMorphismSituation.totalTopology = s.base.J :=
  CategoryTheory.Functor.inheritedTopology_id s.base.J

end Reduction

section Functors

variable (s : FibredCategorySituation.{uD, vD, uC, vC, max w uD vD uC vC})

/-- Abelian sheaves can be sheafified for the topology the target of the reduced situation
inherits, that topology being the topology of the base site. Instance search does not see that
identification, so the instance is restated here. -/
instance hasWeakSheafifyToMorphismSituationTotalTopology :
    HasWeakSheafify s.toMorphismSituation.totalTopology AddCommGrpCat.{max w uD vD uC vC} := by
  rw [s.toMorphismSituation_totalTopology]
  exact s.hasSheafifyBaseTopology.isRightAdjoint

/-- `g^{-1}` of the reduced situation is `π^{-1}`: both are restriction of abelian sheaves along
`p` between the same two sites. -/
@[stacks 09CY "the reduced situation's `g^{-1}` is the `π^{-1}` of Situation 08P8"]
theorem abelianInverseImage_toMorphismSituation :
    HEq s.toMorphismSituation.abelianInverseImage s.abelianInverseImage := by
  have key : ∀ (K : GrothendieckTopology s.base.C) [inst : s.p.IsContinuous s.topology K],
      K = s.base.J →
      HEq (s.p.sheafPushforwardContinuous AddCommGrpCat.{max w uD vD uC vC} s.topology K)
        s.abelianInverseImage := by
    intro K inst hK
    subst hK
    rfl
  exact key s.toMorphismSituation.totalTopology (inst := s.toMorphismSituation.uContinuous)
    s.toMorphismSituation_totalTopology

/-- `g_!^{Ab}` of the reduced situation is `π_!^{Ab}`: both are the chosen left adjoint of
restriction of abelian sheaves along `p` between the same two sites. -/
@[stacks 09CY "the reduced situation's `g_!^{Ab}` is the `π_!^{Ab}` of Situation 08P8"]
theorem abelianLowerShriek_toMorphismSituation :
    HEq (@MorphismSituation.abelianLowerShriek.{uD, uD, uC, vD, vD, vC, w} s.toMorphismSituation
        s.hasWeakSheafifyToMorphismSituationTotalTopology) s.abelianLowerShriek := by
  have key : ∀ (K : GrothendieckTopology s.base.C) [inst : s.p.IsContinuous s.topology K]
      [instK : HasWeakSheafify K AddCommGrpCat.{max w uD vD uC vC}],
      K = s.base.J →
      HEq (s.p.sheafPullback AddCommGrpCat.{max w uD vD uC vC} s.topology K)
        s.abelianLowerShriek := by
    intro K inst instK hK
    subst hK
    rfl
  exact key s.toMorphismSituation.totalTopology (inst := s.toMorphismSituation.uContinuous)
    (instK := s.hasWeakSheafifyToMorphismSituationTotalTopology)
    s.toMorphismSituation_totalTopology

end Functors

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
