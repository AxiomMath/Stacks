module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.CategoryTheory.Subobject.NoetherianObjectOfEssentiallyConstant
public import StacksCore.Tactic.StacksAttribute

/-!
# Ascending chains of subsheaves of a constructible étale sheaf

Let `X` be a Noetherian scheme and `Λ` a Noetherian ring. Every ascending chain
`F₁ ⊂ F₂ ⊂ F₃ ⊂ ⋯ ⊂ F` of subsheaves of a constructible sheaf on the small étale site of `X`
stabilizes: for some `n` one has `Fₙ = Fₙ₊₁ = Fₙ₊₂ = ⋯`. This is stated in the equivalent form
that `F` is a Noetherian object of the ambient sheaf category, which by
`CategoryTheory.isNoetherianObject_iff_monotone_chain_condition` is exactly the ascending chain
condition on the subobjects of `F`. There are three cases: sheaves of sets, sheaves of abelian
groups, and sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleSetSheaf` — sheaves of sets.
* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleAbelianSheaf` — sheaves of abelian
  groups.
* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleModuleSheaf` — sheaves of modules over
  a Noetherian ring.

## Implementation notes

The three proofs are one categorical argument, `Stacks.Subobject`
`.isNoetherianObject_of_subobject_essentiallyConstant`, applied to the constructibility
predicate; what each case supplies is AB5 for its coefficient category, which transfers to the
sheaf category.

Two inputs of the argument are themselves Stacks results that this library does not yet prove,
and each is carried as an explicit hypothesis rather than reproved: `hsub` is Stacks 09BH, that
a subsheaf of a constructible sheaf is constructible, and `hess` is Stacks 095P, that a filtered
system of constructible sheaves whose colimit is constructible is essentially constant. Only the
countable case of `hess` is asked for, since only chains indexed by `ℕ` occur.

For abelian coefficients the sheafification needed for AB5 is the instance
`AlgebraicGeometry.hasSheafify_smallEtale_addCommGrp`; for module coefficients it is a
hypothesis, as it is for `AlgebraicGeometry.isConstructibleModuleSheaf_zero`, because the
coefficient and site universes are independent there.

## References

* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Subobject

universe u w r

namespace AlgebraicGeometry

/-- Presheaves of sets on the small étale site of a scheme admit a sheafification: the site is
essentially small, and on a small site sheafification exists. -/
public theorem SmallEtale.hasSheafify_type (B : BigEtaleSite.{u}) (X : B.Scheme) :
    HasSheafify (SmallEtale.topology B X.obj X.property) (Type (u + 1)) := by
  let J := SmallEtale.topology B X.obj X.property
  let _ : HasSheafify
      ((equivSmallModel.{u + 1} (SmallEtale B X.obj X.property)).inverse.inducedTopology J)
      (Type (u + 1)) := inferInstance
  exact hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} J _

/-- **Stacks Project, Tag 09YV** for sheaves of sets. On a Noetherian scheme every ascending
chain of subsheaves of a constructible sheaf of sets stabilizes. -/
@[stacks 09YV "sheaves of sets, carrying Stacks 09BH (a subsheaf of a constructible sheaf of \
sets is constructible) as the explicit hypothesis hsub and Stacks 095P (a filtered system of \
constructible sheaves of sets whose colimit is constructible is essentially constant) as the \
explicit hypothesis hess"]
public theorem isNoetherianObject_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (hsub : ∀ {G H : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
      (i : G ⟶ H), Mono i → IsConstructibleSetSheaf B X H → IsConstructibleSetSheaf B X G)
    (hess : ∀ (M : ℕ ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
      (c : Cocone M), IsColimit c →
      (∀ n, IsConstructibleSetSheaf B X (M.obj n)) → IsConstructibleSetSheaf B X c.pt →
      ∃ (n : ℕ) (r : c.pt ⟶ M.obj n),
        EssentiallyConstantInd.IsEssentiallyConstantWith M c n r)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    IsNoetherianObject F := by
  let _ : HasSheafify (SmallEtale.topology B X.obj X.property) (Type (u + 1)) :=
    SmallEtale.hasSheafify_type B X
  let _ : AB5OfSize.{0, 0} (Type (u + 1)) := AB5OfSize_shrink (Type (u + 1))
  exact isNoetherianObject_of_subobject_essentiallyConstant F
    (IsConstructibleSetSheaf B X) (fun _ _ => hsub) (fun M => hess (monoOverDiagram M)) hF

/-- **Stacks Project, Tag 09YV** for sheaves of abelian groups. On a Noetherian scheme every
ascending chain of subsheaves of a constructible sheaf of abelian groups stabilizes. -/
@[stacks 09YV "sheaves of abelian groups, carrying Stacks 09BH (a subsheaf of a constructible \
sheaf of abelian groups is constructible) as the explicit hypothesis hsub and Stacks 095P (a \
filtered system of constructible sheaves of abelian groups whose colimit is constructible is \
essentially constant) as the explicit hypothesis hess"]
public theorem isNoetherianObject_of_isConstructibleAbelianSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
    (hsub : ∀ {G H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
      (i : G ⟶ H), Mono i →
      IsConstructibleAbelianSheaf B X H → IsConstructibleAbelianSheaf B X G)
    (hess : ∀ (M : ℕ ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (c : Cocone M), IsColimit c →
      (∀ n, IsConstructibleAbelianSheaf B X (M.obj n)) →
      IsConstructibleAbelianSheaf B X c.pt →
      ∃ (n : ℕ) (r : c.pt ⟶ M.obj n),
        EssentiallyConstantInd.IsEssentiallyConstantWith M c n r)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsNoetherianObject F := by
  let _ : AB5OfSize.{0, 0} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} AddCommGrpCat.{u + 1}
  exact isNoetherianObject_of_subobject_essentiallyConstant F
    (IsConstructibleAbelianSheaf B X) (fun _ _ => hsub) (fun M => hess (monoOverDiagram M)) hF

/-- **Stacks Project, Tag 09YV** for sheaves of modules. On a Noetherian scheme, and over a
Noetherian coefficient ring, every ascending chain of subsheaves of a constructible sheaf of
modules stabilizes. -/
@[stacks 09YV "sheaves of modules over a Noetherian ring, carrying Stacks 09BH (a subsheaf of \
a constructible sheaf of modules is constructible) as the explicit hypothesis hsub and Stacks \
095P (a filtered system of constructible sheaves of modules whose colimit is constructible is \
essentially constant) as the explicit hypothesis hess"]
public theorem isNoetherianObject_of_isConstructibleModuleSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (R : Type r) [CommRing R] [IsNoetherianRing R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)]
    (hsub : ∀ {G H : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)}
      (i : G ⟶ H), Mono i →
      IsConstructibleModuleSheaf B X R H → IsConstructibleModuleSheaf B X R G)
    (hess : ∀ (M : ℕ ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
      (c : Cocone M), IsColimit c →
      (∀ n, IsConstructibleModuleSheaf B X R (M.obj n)) →
      IsConstructibleModuleSheaf B X R c.pt →
      ∃ (n : ℕ) (r : c.pt ⟶ M.obj n),
        EssentiallyConstantInd.IsEssentiallyConstantWith M c n r)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsNoetherianObject F := by
  let _ : PreservesColimitsOfSize.{0, 0} (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{w, r, 0, 0} R
  let _ : AB5OfSize.{0, 0} AddCommGrpCat.{w} := AB5OfSize_shrink AddCommGrpCat.{w}
  let _ : AB5OfSize.{0, 0} (ModuleCat.{w} R) := ⟨fun I _ _ =>
    HasExactColimitsOfShape.domain_of_functor I (forget₂ _ AddCommGrpCat.{w})⟩
  exact isNoetherianObject_of_subobject_essentiallyConstant F
    (IsConstructibleModuleSheaf B X R) (fun _ _ => hsub) (fun M => hess (monoOverDiagram M)) hF

end AlgebraicGeometry

end
