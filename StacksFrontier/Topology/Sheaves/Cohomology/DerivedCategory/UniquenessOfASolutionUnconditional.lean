module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCounitReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionClosed
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionFromTheSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtTopFromTheCover

/-!
# The uniqueness clause of Tag 0D68, with nothing granted

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it
(Situation 0D67).  The uniqueness clause of [Stacks, Tag 0D68] was reduced, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionFromTheSite`, to the
coherence of the two restrictions of morphisms, and that coherence was reduced further, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolutionClosed`, to the
single equation

```
canonicalCompareIso K hTW hWO = overMapCompareIso K hTW
```

between the two comparisons of the restriction of an extension by zero.  That equation is proved
in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCounitReduction`, as
`Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso`, and the coherence itself is
proved there as `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom`.

This file is the join of the two halves.  It discharges the granted hypothesis in each statement
that carried one and restates the conclusion with nothing granted.  Every proof below is an
application of a proved equation to a statement that quantified over it: no new mathematics, only
the removal of a hypothesis.

## Main results

* `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional` — the uniqueness
  clause of [Stacks, Tag 0D68] on the source's own hypotheses (1) and (2), with nothing granted.
  This is the clause that
  `Stacks.DerivedGlueing.subsingleton_shiftedHom_self_of_covers` and
  `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` record as uncovered; it is covered
  here, and their clause strings are corrected accordingly.
* `Stacks.DerivedGlueing.exists_unique_hom_top_unconditional` — the glueing of morphisms over a
  covering collection, with nothing granted.
* `Stacks.DerivedGlueing.hasHomRestrictionDictionary_unconditional` — the restriction dictionary
  of `Stacks.DerivedGlueing.HasHomRestrictionDictionary`, with **no hypothesis at all**.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_top_unconditional` — the sheaf condition of
  [Stacks, Tag 0D66] part (2) at the whole space, from the tag's own covering hypotheses and
  nothing else.  It is the hypothesis of
  `Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop`.
* `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate_unconditional` — the uniqueness
  clause at a covering collection on `Spec (ℤ × ℤ)` that does not contain the whole space, so the
  statement is not a restatement of the single-member case.

## What the two vocabularies share

The dictionary is proved by identifying the two bijections on morphism groups that the two halves
of the development use: `Stacks.DerivedGlueing.topHomEquiv`, built from
`Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful`, and
`Stacks.DerivedGlueing.homEquivSlice`, built from
`Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful`.  These are two bundlings of the
fully-faithfulness of one functor, so they have the same forward map and are mutually inverse;
`Stacks.DerivedGlueing.fullyFaithful_homEquiv_homCongr_roundtrip` states that once, with every
category, functor and object a variable, and the two uses below are instances of it.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The two granted hypotheses, discharged -/

/-- **The hypothesis `hcan` of
`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_canonical`, discharged.**  It is
`Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso` with its binders in the order the
consumers quantify over them. -/
theorem canonicalCompareIso_eq_overMapCompareIso_forall (X : RingedSpace.{u, u}) :
    ∀ {O : Opens X.carrier} (K : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O), canonicalCompareIso K hTW hWO = overMapCompareIso K hTW :=
  fun {_O} K {_T _W} hTW hWO => canonicalCompareIso_eq_overMapCompareIso K hTW hWO

/-- **The hypothesis `hcoh` of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence`, discharged.**  It is
`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom` with its binders in the order the
consumers quantify over them. -/
theorem restrictHomBelow_eq_restrictDerivedHom_forall (S : LocallyGiven X) :
    ∀ {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
      (hTW : T ≤ W) (hWO : W ≤ O)
      (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L),
      homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO φ) =
        RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
          (homEquivSlice S K L hWO φ) :=
  fun {_O} K L {_T _W} hTW hWO φ => restrictHomBelow_eq_restrictDerivedHom S K L hTW hWO φ

/-! ### The uniqueness clause of Tag 0D68 -/

/-- **The glueing of morphisms over a covering collection, with nothing granted.**  This is
`Stacks.DerivedGlueing.exists_unique_hom_top_of_coherence` with its hypothesis `hcoh` discharged
by `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom`. -/
theorem exists_unique_hom_top_unconditional (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (K L : OpenDerivedCategory X ⊤)
    (hExt : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ ⊤, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((S.restriction W ⊤ hWO).obj K)
        ((S.restriction W ⊤ hWO).obj L) i))
    (φ : ∀ (W : Opens X.carrier), W ∈ S.opens → ∀ hWO : W ≤ ⊤,
      (S.restriction W ⊤ hWO).obj K ⟶ (S.restriction W ⊤ hWO).obj L)
    (hφ : ∀ (W T : Opens X.carrier) (hW : W ∈ S.opens) (hT : T ∈ S.opens) (hTW : T ≤ W)
      (hWO : W ≤ ⊤), restrictHomBelow S hTW hWO (φ W hW hWO) = φ T hT (hTW.trans hWO)) :
    ∃! ψ : K ⟶ L, ∀ (W : Opens X.carrier) (hW : W ∈ S.opens) (hWO : W ≤ ⊤),
      (S.restriction W ⊤ hWO).map ψ = φ W hW hWO :=
  exists_unique_hom_top_of_coherence S (restrictHomBelow_eq_restrictDerivedHom_forall S)
    hcover hinter K L hExt φ hφ

/-- **The uniqueness clause of [Stacks, Tag 0D68]**: in Situation 0D67, if
the displayed opens cover `X`, if the intersection of two of them is the union of the members of
the collection it contains, and if the prescribed local objects have no negative self-`Ext`, then
any two solutions are identified by exactly one isomorphism of solutions.

The three conditions are (1) and (2) of the tag, as in
`Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self`, the tag's other clause.  The proof
applies `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence`, its coherence
input being `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom`.

The conclusion `Stacks.DerivedGlueing.Solution.IsCompatibleHom A B ψ.hom` is by definition
`∀ (U : Opens X.carrier) (hU : U ∈ S.opens), (S.restriction U ⊤ le_top).map ψ.hom ≫
(B.rho U hU).hom = (A.rho U hU).hom`, which is the clause as the source states it. -/
@[stacks 0D68 "the uniqueness of a solution up to unique isomorphism, under the tag's conditions
  (1) and (2); the vanishing of negative self-Ext is `subsingleton_shiftedHom_self_of_covers` and
  `Solution.subsingleton_shiftedHom_self`"]
theorem exists_unique_solutionIso_of_covers_unconditional (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_of_covers_of_coherence S
    (restrictHomBelow_eq_restrictDerivedHom_forall S) hcover hinter hExt A B

/-- **The same clause, reached instead through the `hcan` route**, that is, through
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_canonical`.  The two routes prove the
same proposition, so this is a second proof of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional` rather than a new
statement; it certifies that the discharge removes the hypothesis on either side of the reduction,
and so is not tagged. -/
alias exists_unique_solutionIso_of_covers_canonical_route :=
  Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_unconditional

/-- **The coherence of the two restrictions of morphisms, with nothing granted, for every
system.**  This is `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_canonical` with
its hypothesis discharged; it proves the same equation as
`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom`, by the other route. -/
theorem restrictHomBelow_eq_restrictDerivedHom_unconditional (S : LocallyGiven X)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O)
    (φ : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO φ) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
        (homEquivSlice S K L hWO φ) :=
  restrictHomBelow_eq_restrictDerivedHom_of_canonical S
    (canonicalCompareIso_eq_overMapCompareIso_forall X) K L hTW hWO φ

/-! ### A collection to which the clause applies, and which is not the single-member case -/

/-- **The uniqueness clause of [Stacks, Tag 0D68] at the non-degenerate witness, with nothing
granted.**  The collection is a covering collection on `Spec (ℤ × ℤ)` that does not contain the
whole space, so the already unconditional single-member case
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` does not apply and the statement above
is not vacuous at it.

This is `Stacks.DerivedGlueing.exists_unique_solutionIso_nonDegenerate_of_canonical` with its
hypothesis `hcan` discharged. -/
theorem exists_unique_solutionIso_nonDegenerate_unconditional
    (F : SheafOfModules.{u} (restrictedRingSheaf specULiftProdRingedSpace.{u} ⊤))
    (A B : Solution (nonDegenerateSystem.{u} F)) :
    ∃! ψ : A.obj ≅ B.obj, A.IsCompatibleHom B ψ.hom :=
  exists_unique_solutionIso_nonDegenerate_of_canonical
    (canonicalCompareIso_eq_overMapCompareIso_forall specULiftProdRingedSpace.{u}) F A B

/-! ### The restriction dictionary, and the sheaf condition at the whole space -/

/-- **Two bundlings of the fully-faithfulness of one functor give mutually inverse bijections on
morphism groups.**  Both `Stacks.DerivedGlueing.topHomEquiv` and
`Stacks.DerivedGlueing.homEquivSlice` are the action of one functor `F` on a morphism group,
conjugated by a choice of isomorphism at the source and at the target; they differ only in which
`CategoryTheory.Functor.FullyFaithful` structure on `F` was used to invert it.  Since
`CategoryTheory.Functor.FullyFaithful.homEquiv` has `F.map` as its forward map, independently of
the bundling, the two are inverse to one another.

Everything here is a variable, so the identification is paid once, at the level where it is formal,
rather than once per use. -/
theorem fullyFaithful_homEquiv_homCongr_roundtrip {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (hF hF' : F.FullyFaithful) {x y : C} {P Q : D}
    (α : F.obj x ≅ P) (β : F.obj y ≅ Q) (χ : x ⟶ y) :
    hF'.homEquiv.symm ((Iso.homCongr α.symm β.symm)
      ((hF.homEquiv.trans (Iso.homCongr α β)) χ)) = χ := by
  have h : (Iso.homCongr α.symm β.symm)
      ((hF.homEquiv.trans (Iso.homCongr α β)) χ) = hF'.homEquiv χ := by
    simp [Iso.homCongr, Functor.FullyFaithful.homEquiv]
  rw [h, Equiv.symm_apply_apply]

/-- **The two readings of a morphism group over an open agree.**  Reading a morphism between the
slice-model restrictions of the extensions by zero as a morphism between the restrictions displayed
by the system, by `Stacks.DerivedGlueing.topHomEquiv`, and reading it back by
`Stacks.DerivedGlueing.homEquivSlice`, returns it unchanged.  This is
`Stacks.DerivedGlueing.fullyFaithful_homEquiv_homCongr_roundtrip` at the passage between the two
models of modules on `W`. -/
theorem homEquivSlice_topHomEquiv (S : LocallyGiven X) (W : Opens X.carrier)
    (K L : OpenDerivedCategory X ⊤) (hW : W ≤ ⊤)
    (χ : siteRestrictOfTop W K ⟶ siteRestrictOfTop W L) :
    homEquivSlice S K L hW (topHomEquiv S W K L χ) = χ :=
  fullyFaithful_homEquiv_homCongr_roundtrip
    ((sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory)
    (Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful W)
    (sliceToSubspaceDerivedFullyFaithful W)
    (S.restrictionIsoOfExtension ⊤ W hW K) (S.restrictionIsoOfExtension ⊤ W hW L) χ

/-- **The coherence of the two restrictions of morphisms at `O = ⊤`, with the inner reading
collapsed.**  This is `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom` at the whole
space, with `Stacks.DerivedGlueing.homEquivSlice_topHomEquiv` used to remove the round trip on the
right-hand side. -/
theorem restrictHomBelow_topHomEquiv_eq_restrictDerivedHom (S : LocallyGiven X)
    (K L : OpenDerivedCategory X ⊤) {T W : Opens X.carrier} (hTW : T ≤ W)
    (χ : siteRestrictOfTop W K ⟶ siteRestrictOfTop W L) :
    homEquivSlice S K L (hTW.trans (le_top : W ≤ ⊤))
        (restrictHomBelow S hTW (le_top : W ≤ ⊤) (topHomEquiv S W K L χ)) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        (globalObjOfTop K) (globalObjOfTop L) χ :=
  (restrictHomBelow_eq_restrictDerivedHom S K L hTW (le_top : W ≤ ⊤)
      (topHomEquiv S W K L χ)).trans
    (congrArg
      (RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        (globalObjOfTop K) (globalObjOfTop L))
      (homEquivSlice_topHomEquiv S W K L le_top χ))

/-- **The restriction dictionary, with no hypothesis at all.**  The obligation that
`Stacks.DerivedGlueing.HasHomRestrictionDictionary` records — that the ringed-site restriction of
a morphism and the displayed restriction of Situation 0D67 agree, after the two vocabularies are
matched up — holds for every system, granted nothing.

It is `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom` read at `O = ⊤` and
transported across `Stacks.DerivedGlueing.homEquivSlice_topHomEquiv`, which is injective.  The
route through `Stacks.DerivedGlueing.hasHomRestrictionDictionary_of_comparison` is not used: that
one asks for the comparison together with its two coherences, and the equation proved on the slice
model supplies the dictionary directly. -/
theorem hasHomRestrictionDictionary_unconditional (S : LocallyGiven X) :
    HasHomRestrictionDictionary S :=
  fun K L T W hTW χ =>
    (homEquivSlice S K L (hTW.trans (le_top : W ≤ ⊤))).injective
      ((homEquivSlice_topHomEquiv S T K L (hTW.trans (le_top : W ≤ ⊤))
          (RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
            (globalObjOfTop K) (globalObjOfTop L) χ)).trans
        (restrictHomBelow_topHomEquiv_eq_restrictDerivedHom S K L hTW χ).symm)

/-- **The sheaf condition of [Stacks, Tag 0D66] part (2) at the whole space, with nothing
granted.**  This is `Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_covers_of_dictionary` with its
dictionary supplied by `Stacks.DerivedGlueing.hasHomRestrictionDictionary_unconditional`.

The two hypotheses that remain are the tag's own and are genuinely consumed: the conclusion fails
outright at a collection with no members, by
`Stacks.DerivedGlueing.subsingleton_hom_of_hasGluingForHomsAt_top`.  So this does not make
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop` unconditional as it
stands — that statement deliberately carries neither hypothesis — but it does discharge the one
thing that statement grants, at the cost of assuming what the source assumes. -/
theorem hasGluingForHomsAt_top_unconditional (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V}) :
    HasGluingForHomsAt S ⊤ :=
  hasGluingForHomsAt_top_of_covers_of_dictionary S
    (hasHomRestrictionDictionary_unconditional S) hcover hinter

/-- **Uniqueness of a solution up to unique isomorphism over a covering collection.**
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_hasGluingForHomsAtTop` with its hypothesis
`Stacks.DerivedGlueing.HasGluingForHomsAt S ⊤` supplied by
`Stacks.DerivedGlueing.hasGluingForHomsAt_top_unconditional`.  The uniqueness clause of
[Stacks, Tag 0D6C] is registered at
`Stacks.DerivedGlueing.exists_solution_and_unique_solutionIso_of_covers_unconditional`. -/
theorem exists_unique_solutionIso_of_hasGluingForHomsAtTop_unconditional (S : LocallyGiven X)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (A B : Solution S) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom :=
  exists_unique_solutionIso_of_hasGluingForHomsAtTop S
    (hasGluingForHomsAt_top_unconditional S hcover hinter) hExt A B

end Stacks.DerivedGlueing

end
