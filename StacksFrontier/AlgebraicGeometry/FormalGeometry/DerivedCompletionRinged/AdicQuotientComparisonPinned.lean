module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit

/-!
# The comparison into a derived limit pinned by the universal property of the completion

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `K ↦ K^∧` a derived completion
functor. [Stacks, Tag 0CQH] builds a comparison map `K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)` by lifting the
cone of canonical factorizations through the Milnor triangle of the tower, and that lift is **not
unique**: its indeterminacy is `Hom(K^∧, (∏ₙ Tₙ)⟦-1⟧)`, the group whose `R¹lim` reading is the
obstruction recorded at `Stacks.MilnorTower.exists_lift_kInjectiveProj`. A map chosen that way
cannot be tested on a cover, because a chart-by-chart hypothesis about *some* lift says nothing
about any global map.

This file supplies the other way of pinning it, which that same docstring prescribes: *a consumer
needing a canonical map must pin it by a universal property of the source.* Given a
**derived-complete** `L` and **any** map `u : K ⟶ L`, the reflector adjunction produces exactly one
`c : K^∧ ⟶ L` with `(K ⟶ K^∧) ≫ c = u`. Nothing is chosen, so `c` restricts to the corresponding
map on every slice — that is
`AlgebraicGeometry.RingedSite.derivedCompletionRestrictIso_hom_app_comp_map_pinnedAdicComparison`
of `AdicMilnorComparisonSliceRestriction.lean`, for `ℐ` of finite type — and `IsIso c` is a local
question.

The pay-off is `AlgebraicGeometry.RingedSite.isIso_pinnedAdicComparison_of_bijective`: `c` is
invertible exactly when `u` is itself a derived-completion unit for `K`. **No amplitude hypothesis
appears in the statements of this file.** Compare the route through the Milnor triangle, where
matching two cones is turned into an isomorphism by a uniqueness statement for maps *into* a
derived limit — and such a statement is false without `IsLE`/`IsGE` bounds on the source and the
terms of the tower, the obstruction being the `R¹lim` of the `Ext⁻¹` groups. The uniqueness used
here is for maps *out of* a derived completion, which is the reflector adjunction and carries no
bound at all; the amplitude of `K` is never mentioned.

That is a statement about this file, not a removal of the amplitude condition from part (1) of
[Stacks, Tag 0A0K]. Pinning moves the question from *which* lift, to whether the pinned map is
invertible; answering the latter on a chart out of the chart's derived-limit presentations runs
into the same group, because matching projections leaves the third square of the morphism of
Milnor triangles undetermined. See the module documentation of
`AdicMilnorComparisonSliceRestriction.lean`.

What the universal property does *not* supply is `u` itself: a cone over the tower gives a map into
a derived limit only through the same non-unique lift. So the input this file needs is a map
`K ⟶ L` given by a *formula*, and
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/StrictAdicMilnorFibre.lean`
has one — `AlgebraicGeometry.RingedSite.strictAdicComparison`, the Milnor augmentation map of the
strictified tower.

## Main definitions

* `AlgebraicGeometry.RingedSite.pinnedAdicComparison`: the unique `c : K^∧ ⟶ L` through the
  completion unit, for `L` derived complete.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCompletionUnit_comp_pinnedAdicComparison` and
  `AlgebraicGeometry.RingedSite.eq_pinnedAdicComparison`: its defining property, and that it is
  the only map with it.
* `AlgebraicGeometry.RingedSite.pinnedAdicComparison_comp`: naturality in the target — composing
  with a map to a derived-complete object again gives a pinned comparison. At the terms of the
  adic reduction tower this says the composites of `c` with the projections are the canonical
  factorizations of [Stacks, Tag 0CQH], so `c` *is* a comparison map in the sense of that tag.
* `AlgebraicGeometry.RingedSite.isIso_pinnedAdicComparison_of_bijective`: **`c` is invertible as
  soon as precomposition with `u` is bijective on maps into derived-complete objects** — needed at
  the two objects `K^∧` and `L` only.
* `AlgebraicGeometry.RingedSite.isIso_pinnedAdicComparison_of_iso`: the form a descent consumes —
  `c` is invertible once `K^∧` and `L` are both identified with one derived-complete object,
  compatibly with the two maps out of `K`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedCompletion_of_isIso_pinnedAdicComparison`:
  from `IsIso c` and a derived-limit presentation of `L`, the derived completion is a derived
  limit of the tower. This is the shape of part (1) of [Stacks, Tag 0A0K].

## Implementation notes

`pinnedAdicComparison` is built from `derivedCompletionAdjunction` in exactly the way
`AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor` of `AdicQuotientFactorization.lean` is,
and specializes to it at `u = adicQuotientReduction X I K n`. It is stated here for an arbitrary
derived-complete target because the target that matters for part (1) of [Stacks, Tag 0A0K] is the
derived limit, not a term of the tower.

`isIso_pinnedAdicComparison_of_bijective` does not go through
`AlgebraicGeometry.RingedSite.bijective_precomp_derivedCompletionUnit_app`, whose statement carries
`HasWeakSheafify X.J CommRingCat`: surjectivity of precomposition with `u` at the single object
`K^∧` produces the inverse, and the two identities are then
`AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit` and injectivity at `L`. So no
hypothesis beyond the reflector is needed.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]
  {K L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}

/-- **The comparison `K^∧ ⟶ L` pinned by the universal property of the derived completion.** For
`L` derived complete, the reflector adjunction attaches to a map `u : K ⟶ L` the unique map out of
`K^∧` restricting to it along the completion unit.

Nothing is chosen: this is a formula in `u`, where a lift of a cone through the Milnor triangle of
a tower is determined only up to `Hom(K^∧, (∏ₙ Tₙ)⟦-1⟧)`. -/
def pinnedAdicComparison (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L) :
    (derivedCompletion X I).obj K ⟶ L :=
  (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map
    (((derivedCompletionAdjunction X I).homEquiv K ⟨L, hL⟩).symm u)

/-- The defining property: the completion unit followed by the pinned comparison is `u`. -/
@[reassoc]
theorem derivedCompletionUnit_comp_pinnedAdicComparison
    (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L) :
    (derivedCompletionUnit X I).app K ≫ pinnedAdicComparison X I hL u = u :=
  ((derivedCompletionAdjunction X I).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The pinned comparison is the only map out of `K^∧` restricting to `u`.** This is the
universal property `AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit` read as a
uniqueness statement. -/
theorem eq_pinnedAdicComparison (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L)
    {g : (derivedCompletion X I).obj K ⟶ L}
    (hg : (derivedCompletionUnit X I).app K ≫ g = u) :
    g = pinnedAdicComparison X I hL u :=
  hom_ext_derivedCompletionUnit X I hL
    (hg.trans (derivedCompletionUnit_comp_pinnedAdicComparison X I hL u).symm)

/-- **Naturality of the pinned comparison in the target.** Composing with a map into a further
derived-complete object gives the pinned comparison of the composite.

At `L` a derived limit of the adic reduction tower and `p` the `n`-th projection this identifies
`c ≫ p` with `pinnedAdicComparison` of `u ≫ p`; when `u ≫ p` is the derived reduction
`K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`, that is `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor`, so `c` is
a comparison map in the sense of [Stacks, Tag 0CQH]. -/
theorem pinnedAdicComparison_comp (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L)
    {T : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hT : IsDerivedComplete.{u, u, u, u} X I T) (p : L ⟶ T) :
    pinnedAdicComparison X I hL u ≫ p = pinnedAdicComparison X I hT (u ≫ p) :=
  eq_pinnedAdicComparison X I hT (u ≫ p) (derivedCompletionUnit_comp_pinnedAdicComparison_assoc ..)

/-- **The pinned comparison is invertible exactly when `u` is a derived-completion unit for `K`**,
and the hypothesis is needed at two objects only.

Surjectivity of precomposition with `u` at `K^∧` produces `d : L ⟶ K^∧` with `u ≫ d` the
completion unit; `c ≫ d = 𝟙` is then the universal property of `K^∧`, and `d ≫ c = 𝟙` is
injectivity of precomposition with `u` at `L`.

**No amplitude hypothesis enters.** The uniqueness used is for maps out of a derived completion;
the route that turns matching cones into an isomorphism instead needs maps *into* a derived limit
to be determined, which is false without `IsLE 0` on the source and `IsGE 0` on the terms of the
tower. -/
theorem isIso_pinnedAdicComparison_of_bijective (hL : IsDerivedComplete.{u, u, u, u} X I L)
    (u : K ⟶ L)
    (h : ∀ M : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      IsDerivedComplete.{u, u, u, u} X I M → Function.Bijective (fun g : L ⟶ M ↦ u ≫ g)) :
    IsIso (pinnedAdicComparison X I hL u) := by
  obtain ⟨d, hd'⟩ :=
    (h _ (isDerivedComplete_derivedCompletion_obj X I K)).2 ((derivedCompletionUnit X I).app K)
  have hd : u ≫ d = (derivedCompletionUnit X I).app K := hd'
  refine ⟨d, ?_, (h L hL).1 ?_⟩
  · refine hom_ext_derivedCompletionUnit X I (isDerivedComplete_derivedCompletion_obj X I K) ?_
    rw [Category.comp_id]
    exact (derivedCompletionUnit_comp_pinnedAdicComparison_assoc ..).trans hd
  · show u ≫ d ≫ pinnedAdicComparison X I hL u = u ≫ 𝟙 L
    rw [← Category.assoc, hd, derivedCompletionUnit_comp_pinnedAdicComparison, Category.comp_id]

/-- **The pinned comparison is invertible once both its source and its target are identified with
one derived-complete object, compatibly with the maps out of `K`.** This is the form a
local-to-global argument consumes: on a chart where `ℐ` is generated by finitely many sections the
derived completion is the Čech completion of [Stacks, Tag 099B] and the derived limit is a Milnor
fibre, and both identifications are available there with their units.

The proof is `AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit` applied to
`c ≫ θ.hom` and `γ.hom`, so again no amplitude input is used. -/
theorem isIso_pinnedAdicComparison_of_iso (hL : IsDerivedComplete.{u, u, u, u} X I L)
    (u : K ⟶ L)
    {T : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hT : IsDerivedComplete.{u, u, u, u} X I T)
    (γ : (derivedCompletion X I).obj K ≅ T) (θ : L ≅ T)
    (hγθ : (derivedCompletionUnit X I).app K ≫ γ.hom = u ≫ θ.hom) :
    IsIso (pinnedAdicComparison X I hL u) := by
  have key : pinnedAdicComparison X I hL u ≫ θ.hom = γ.hom :=
    hom_ext_derivedCompletionUnit X I hT
      ((derivedCompletionUnit_comp_pinnedAdicComparison_assoc ..).trans hγθ.symm)
  have hfactor : pinnedAdicComparison X I hL u = γ.hom ≫ θ.inv := by
    rw [← key, Category.assoc, θ.hom_inv_id, Category.comp_id]
  rw [hfactor]
  infer_instance

/-- **From an invertible pinned comparison, the derived completion is a derived limit of the
tower.** This is the shape of part (1) of [Stacks, Tag 0A0K]: the tower is the adic reduction
tower, `L` a named derived limit of it, and `u` the Milnor comparison map out of `K`.

`CategoryTheory.Pretriangulated.IsDerivedLimit` is a property of the object alone, so it transports
along the isomorphism; what the pinned comparison contributes is that the isomorphism exists and is
testable on a cover. -/
theorem isDerivedLimit_derivedCompletion_of_isIso_pinnedAdicComparison
    (hL : IsDerivedComplete.{u, u, u, u} X I L) (u : K ⟶ L)
    (F : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] (hF : IsDerivedLimit F L)
    (hc : IsIso (pinnedAdicComparison X I hL u)) :
    IsDerivedLimit F ((derivedCompletion X I).obj K) :=
  IsDerivedLimit.of_isoObj (asIso (pinnedAdicComparison X I hL u)).symm hF

end AlgebraicGeometry.RingedSite

end
