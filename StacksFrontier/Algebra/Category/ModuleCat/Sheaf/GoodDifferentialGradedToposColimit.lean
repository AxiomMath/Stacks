module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit

/-!
# Colimits of good differential graded modules, at the topos reading of condition (3)

Let `Y` be a ringed topos and let `A` be a sheaf of differential graded `O_Y`-algebras on it.
A colimit of right differential graded `A`-modules which are good in the sense of
`SheafOfModules.IsGoodToposBaseChange` — conditions (1) and (2) of Tag 0FSA together with
condition (3) read over the source's own base changes, the morphisms of ringed topoi — is again
good, along any shape whose colimits of sheaves of modules are exact.

The three clauses are reached as follows.

* Conditions (1) and (2) for the colimit are the conditions (1) and (2) half of Tag 0FSD,
  `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_of_isColimit`.
* **Existence** of a base change of the colimit is free: `Functor.leftAdjointObjIsDefined` is
  stable under colimits, and `Functor.corepresentableByCompCoyonedaObjOfIsColimit` exhibits the
  corepresenting object of the colimit as the colimit of the corepresenting objects of the
  pieces. Nothing is assumed of a pullback functor, because there is none — the direct image of
  differential graded modules along a morphism of ringed topoi need have no global left adjoint,
  and the partial one of Mathlib's `CategoryTheory.Functor.partialLeftAdjoint` is exactly what
  condition (3) asserts to be defined.
* **Flatness** of that base change is Tag 0FSD again, now at the second ringed topos: the
  colimit there is a colimit of objects corepresenting the base changes of the pieces, and each
  of those is flat as a graded module and K-flat by the pieces' own condition (3).
* The conclusion is then pushed from the constructed corepresenting object to **every** chosen
  one by `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`, flatness and K-flatness
  transporting along an isomorphism by `SheafOfModules.RelativeTensor.IsGradedFlat.of_iso` and
  `SheafOfModules.RelativeTensor.IsKFlat.of_iso`.

## Main results

* `SheafOfModules.isGoodToposBaseChange_of_isColimit`: **a colimit of good right differential
  graded modules is good**, goodness being `SheafOfModules.IsGoodToposBaseChange`, along any
  shape in the module universe whose colimits of sheaves of modules are exact at the base ringed
  topos and at every ringed topos condition (3) quantifies over.
* `SheafOfModules.isGoodToposBaseChange_of_isColimit_nat`: the same for a colimit over `ℕ`,
  where the exactness hypothesis is discharged.

## Implementation notes

**The shape lies in the module universe and the exactness hypothesis is quantified.** Tag 0FSD
is stated for shapes `D : Type w` with `Category.{w} D`, `w` the module universe, because the
relative tensor product commutes with colimits of exactly that size; a shape such as `ℕ` is
transported along `SheafOfModules.DifferentialGradedModule.asSmallNatEquiv`, which is what
`isGoodToposBaseChange_of_isColimit_nat` does. Exactness of the colimits is needed at the second
ringed topos of condition (3) as well as at the first, and that topos is quantified over inside
the predicate, so the hypothesis cannot be an instance of the statement: it is carried as the
explicit argument `hD`, universally quantified over the ringed topoi condition (3) ranges over.
For a filtered shape — `AsSmall.{w} ℕ` in particular — it is discharged by AB5, which holds at
every site, and for a discrete shape by AB4; those are the two cases in which the hypothesis is
available at all.

**No pushout is covered by this lemma, and that is not an oversight.** Colimits over
`WalkingSpan` are not exact, so `hD` cannot be supplied for them; the flatness of the base change
of a pushout is not a colimit statement and comes instead from the admissible short exact
sequence the pushout sits in.

**The goodness readings stay incomparable.** `SheafOfModules.IsGoodToposBaseChange` is not
`SheafOfModules.DifferentialGradedModule.IsGood` with its binders rewritten, and neither
contains the other: `IsGood` quantifies bare functors of the two underlying categories, which
induce no morphism of topoi, and has no clause for a morphism of topoi not induced by a functor
of the two given sites (Tag 03CR). The site-indexed readings `IsGood`,
`IsGoodCocontinuousBaseChange` and `IsGoodSiteBaseChange`, and their colimit statements in
`GoodDifferentialGradedColimit.lean` and `GoodDifferentialGradedSiteColimit.lean`, are left
untouched.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

open DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

omit [HasSheafify Y.J (Type w)] in
/-- **A colimit of good right differential graded modules is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange`: conditions (1) and (2) of Tag 0FSA together with
condition (3) read over the morphisms of ringed topoi out of the base.

The shape `D` lies in the module universe, which is where Tag 0FSD applies, and `hD` supplies
exactness of its colimits at each ringed topos condition (3) quantifies over, exactness at the
base being an instance argument. Both are available for a filtered shape, by AB5, and for a
discrete one, by AB4.

Conditions (1) and (2) are Tag 0FSD at the base. For condition (3) at a base change
`(f, B, ψ)`: each piece's condition (3) says that the direct image of differential graded
modules has a partial left adjoint defined at that piece, so
`CategoryTheory.Functor.corepresentableByCompCoyonedaObjOfIsColimit` exhibits the colimit of
those partial values as an object corepresenting the base change of the colimit — which is the
existence half — and that colimit is flat as a graded module and K-flat by Tag 0FSD at the
second ringed topos, each of its pieces being so by the pieces' own condition (3). Every other
corepresenting object is isomorphic to it by
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`, and both conditions transport along an
isomorphism. -/
theorem isGoodToposBaseChange_of_isColimit {D : Type w} [Category.{w} D]
    [HasExactColimitsOfShape D (SheafOfModules.{w} (toRingCat Y.J Y.O))]
    (hD : ∀ (X : AlgebraicGeometry.RingedTopos.{v₁, u₁, w})
      [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
      [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}],
      HasExactColimitsOfShape D (SheafOfModules.{w} (toRingCat X.J X.O)))
    {K : D ⥤ DifferentialGradedModule.{w, w, w} A} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ d : D, IsGoodToposBaseChange.{w, v₁, u₁} (K.obj d)) :
    IsGoodToposBaseChange.{w, v₁, u₁} c.pt := by
  obtain ⟨h₁, h₂⟩ := isGradedFlat_and_isKFlat_of_isColimit hc fun d ↦ ⟨(hK d).1, (hK d).2.1⟩
  refine ⟨h₁, h₂, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  have := hD X
  set F := toposPushforward (toposDirectImageModules f) ψ hψ with hF
  have hdef : ∀ d : D, F.leftAdjointObjIsDefined (K.obj d) := by
    intro d
    obtain ⟨T, ⟨e⟩⟩ := ((hK d).2.2 f B ψ hψ).1
    exact e.isCorepresentable
  have e := Functor.corepresentableByCompCoyonedaObjOfIsColimit (F := F)
    (R := ObjectProperty.lift _ K hdef) hc (colimit.isColimit _)
  have hflat : RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
        (colimit (ObjectProperty.lift _ K hdef ⋙ F.partialLeftAdjoint))) ∧
      RelativeTensor.IsKFlat
        (colimit (ObjectProperty.lift _ K hdef ⋙ F.partialLeftAdjoint)) := by
    refine isGradedFlat_and_isKFlat_of_isColimit (colimit.isColimit _) fun d ↦ ?_
    have : (F ⋙ coyoneda.obj (Opposite.op (K.obj d))).IsCorepresentable := hdef d
    exact ((hK d).2.2 f B ψ hψ).2 _
      (F ⋙ coyoneda.obj (Opposite.op (K.obj d))).corepresentableBy
  refine ⟨⟨_, ⟨e⟩⟩, fun T eT ↦ ?_⟩
  have i : T ≅ colimit (ObjectProperty.lift _ K hdef ⋙ F.partialLeftAdjoint) :=
    eT.uniqueUpToIso e
  exact ⟨RelativeTensor.IsGradedFlat.of_iso (GradedModule.ofDifferentialGradedIso i).symm hflat.1,
    RelativeTensor.IsKFlat.of_iso i.symm hflat.2⟩

omit [HasSheafify Y.J (Type w)] in
/-- **A colimit over `ℕ` of good right differential graded modules is good**, goodness being
`SheafOfModules.IsGoodToposBaseChange`. This is
`SheafOfModules.isGoodToposBaseChange_of_isColimit` transported along
`SheafOfModules.DifferentialGradedModule.asSmallNatEquiv` to the shape `AsSmall.{w} ℕ`, which
lies in the module universe and is filtered, so the exactness hypothesis is an instance at every
ringed topos. -/
theorem isGoodToposBaseChange_of_isColimit_nat
    {K : ℕ ⥤ DifferentialGradedModule.{w, w, w} A} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ n : ℕ, IsGoodToposBaseChange.{w, v₁, u₁} (K.obj n)) :
    IsGoodToposBaseChange.{w, v₁, u₁} c.pt :=
  isGoodToposBaseChange_of_isColimit (D := AsSmall.{w} ℕ) (fun _ ↦ inferInstance)
    (K := asSmallNatEquiv.{w}.functor ⋙ K)
    (c := c.whisker asSmallNatEquiv.{w}.functor)
    (hc.whiskerEquivalence asSmallNatEquiv.{w}) fun _ ↦ hK _

end SheafOfModules

end
