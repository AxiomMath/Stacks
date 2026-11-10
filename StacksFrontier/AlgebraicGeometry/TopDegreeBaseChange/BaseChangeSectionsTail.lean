module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsJoin
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrict
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryPullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeMate
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeHeadMatching
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeSectionsModelCrossing

/-!
# The head of the `ψ` side of [Stacks, Tag 0EX3] (c), split off from its tail

`BaseChangeSectionsJoin.lean` reduces the pure-tensor agreement of conclusion (c) of
[Stacks, Tag 0EX3] to one hypothesis, `join`, whose left-hand side is the `ψ` side of the
agreement as `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul` computes it. That composite
begins with two comparisons that cancel against the computation of
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` in
`OrdinaryPullbackUnitSections.lean`, and the unit it then carries is the unit of the **restricted**
adjunction, which `TopDegreeHeadMatching.lean` identifies with the restriction to `V` of the
ordinary unit of `(h')^* ⊣ (h')_*`.

This file performs those cancellations, so that the `ψ` side is read as the sections over `V` of
the degree-`d` higher direct image of the **ordinary** unit — which is exactly what the `γ⁺` side
carries, by `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus`
`_unit` — followed by a tail in which no unit occurs.

## Main results

* `…TopDegreeBaseChange.affineOpenCohomologyIsoSectionsOf_inv_eq` and
  `…TopDegreeBaseChange.affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology_hom_eq`: the two
  leading factors of the `ψ` side, read off their constructions.
* `…TopDegreeBaseChange.openSectionsModuleIso_hom_naturality`: the identification of the global
  sections of a restriction with the sections over the open is natural in the sheaf of modules.
* `…TopDegreeBaseChange.rightDerivedIso_inv_comp_restrictScalars_pullbackMap`: **the first
  cancellation.** The comparison of the two indexings of the right derived functors, inverted,
  followed by the pullback map on cohomology over the compatible pair of affine opens, is
  [Stacks, Tag 01XK] over `V`, then the sections over `V` of the degree-`d` higher direct image
  along `f' ∣_ V` of the unit of the restricted adjunction, and then the tail.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_id_obj`: the identity functor may be
  dropped from the coefficient of [Stacks, Tag 01E5]; split off as its own `rfl`.
* `…TopDegreeBaseChange.sections_pullbackMap_eq_unit_comp_tail`: **the second cancellation**, with
  the head matching hoisted onto variables.
* `…TopDegreeBaseChange.affineOpenCohomologyIsoSectionsOf_inv_comp_restrictBase_comp`: the
  bookkeeping of the two leading factors, with the geometry hoisted onto variables.
* `…TopDegreeBaseChange.psi_side_eq_sections_unit_comp_tail`: **the `ψ` side is the sections over
  `V` of the ordinary unit, followed by a tail in which no unit occurs.**
* `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail`: the
  pure-tensor agreement of conclusion (c), from the two sides' head-and-tail factorisations and
  the identification of their tails.
* `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE_of_id_obj`: the head matching with the
  identity functor dropped from the coefficient of its leading comparison.

## What remains

The `htail` argument of `baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail` — at the
`Θ` and `T` that `homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit` and
`psi_side_eq_sections_unit_comp_tail` name — and nothing else.

That theorem takes `Tgt`, `ξ`, `Θ` and `T` as its **own** implicit variables, fixed by
unification with the two factorisations it is handed, and asks for the tail identity at those
values only. Since an application of either tail to an element cannot be written out, the way to
supply it is to prove the **morphism-level** identity `T = Γ(V, Θ) ≫ (restriction to W)` and
apply it at `b`.

*Why the reduction is not stated with the tails quantified.*
A variant of `…_of_tail` whose hypothesis reads
`∀ {Tgt ξ Θ T}, (γ⁺ factorisation) → (ψ factorisation) → ∀ b, T b = …` — quantifying the four
*inside* the hypothesis, so that supplying it means proving the tail identity for **every**
quadruple satisfying the two factorisations — is **false**. The two factorisations constrain only
the composites `ξ ≫ Θ` and `ξ.app V ≫ T`, and `ξ.app V` is not epimorphic, so they do not
determine `Θ` and `T`. Given the
genuine quadruple `(Tgt₀, ξ₀, Θ₀, T₀)`, put `Tgt = Tgt₀ ⊞ Tgt₀`, `ξ = ξ₀ ≫ biprod.inl`,
`Θ = biprod.fst ≫ Θ₀` and `T = Γ(V, biprod.fst) ≫ T₀ + Γ(V, biprod.snd) ≫ T₀`. Both
factorisations still hold — `biprod.inl ≫ biprod.fst = 𝟙`, `biprod.inl ≫ biprod.snd = 0`, and
`Γ(V, -)` is additive — while the conclusion would force `Γ(V, biprod.snd) ≫ T₀ = 0`, which fails
as soon as `Γ(Tgt₀, V)` and `T₀` are nonzero. So such a theorem is vacuous: its hypothesis can
never be supplied.

Writing `A' = R^d f''_* ((h')^* F')`, the identity owed is

> `T = Γ(V, Θ)` followed by restriction to `W`,

between two maps `Γ(R^d f'_*((h')_*(h')^* F'), V) ⟶ Γ(A', W)`, where

* `Θ` is the `γ⁺` side's tail: the crossing of the two models of `Rf'_*` inverted, then
  `H^d(Rf'_*(-))` of the comparison of the two models of `Rh'_*` and of
  `Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare`, then the
  cohomology edge morphism
  `Stacks.Cohomology.DerivedPushforward.derivedPushforwardHomologyComparison` of `Rh_*`, then
  `h_*` of the crossing at `f''`;
* `T` is the `ψ` side's tail, as `psi_side_eq_sections_unit_comp_tail` displays it: the sections
  over `V` of the five comparisons of
  `…TopDegreeBaseChange.unit_resLE_eq_restrictFunctor_map_unit` conjugated by [Stacks, Tag 01E5],
  then [Stacks, Tag 01XK] over `V` inverted, the two indexings of the right derived functors
  crossed, the Leray comparison of [Stacks, Tag 089W] along the affine `h' ∣` inverted, the
  crossing of the two readings of the cohomology upstairs, the transport of the two readings of
  the scalars, and the identification of the right-hand end with the sections over `W`.

The chase is to be assembled from two results, **neither of which is used here**:
here**: `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
(`EdgeCompatCollapseMirror.lean`), which turns the edge morphism of `Rh_*` together with the two
model crossings into [Stacks, Tag 01XK]'s `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`,
and `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_comp_lerayComposite`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSections.lean`),
which is the comparison of the two
iterated derived pushforwards read on derived sections over the two intermediate opens `f'⁻¹(V)`
and `h⁻¹(V) ⊇ W`. This paragraph only names the ingredients; it does not perform the chase.

*The compatibility of the edge morphism with `Γ(V, -)`.* `Θ` is a composite of morphisms of
sheaves of modules on `Y'` whose factors are built in the unbounded model, and `T` is a composite
in the classical model over `f'⁻¹(V)` and `f''⁻¹(W)`. The crossings between the two models on
sections over an open are available —
`…TopDegreeBaseChange.derivedPreimageSectionsHomologyIso`
(`EdgeCompatPreimageSections.lean`) and
`…TopDegreeBaseChange.topDegreeSectionsModelCrossing` (`TopDegreeSectionsModelCrossing.lean`) —
and so is the compatibility of the **cohomology edge morphism**
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison` of
`Rh_*` with `Γ(V, -)`, in `EdgeCompatSectionsOverOpen.lean`:

* `Stacks.EdgeCompat.derivedPreimageSectionsHomologyComparison_eq` and its `…_app_eq`: the edge
  morphism of `RΓ(f⁻¹V, -)` is the degree-`q` cohomology of the Leray comparison of
  [Stacks, Tag 0D5W], then the edge morphism of `RΓ(V, -)` at `Rf_* -`, then `Γ(V, -)` of the
  edge morphism of `Rf_*`. No hypothesis on `f`, `V`, `q` or the object: it is
  `Stacks.EdgeCompat.derivedHomologyComparison_comp` — the edge morphism of a composite of two
  left exact functors splits — at the pair `(f_*, Γ(V, -))`, whose composite is
  `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` on the nose and whose characterising
  factorisation is `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac_app_refl`;
* `Stacks.EdgeCompat.map_sectionsOverOpen_derivedPushforwardHomologyComparison_app_eq`: the same
  solved for `Γ(V, -)` of the edge morphism of `Rf_*`, with the two inverses taken as left
  inverses of plain morphisms;
* `Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE`: the edge morphism of
  `RΓ(V, -)` is invertible at a bounded below object with `Γ(V, -)`-acyclic cohomology, which is
  what supplies one of those inverses (the other is unconditional,
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` being so).

*Where that compatibility comes from.* No declaration names the edge morphism together with
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` or a `leray` comparison; the content is
present at **full generality**, in `Stacks.EdgeCompat.derivedHomologyComparison_comp`
(`EdgeCompatComposition.lean`), which names neither the direct image nor sections because it is
stated for an arbitrary pair of left exact functors. Only the instantiation is needed, not new
mathematics.

*The two remaining dictionary entries.* The mirror
`Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
(`EdgeCompatCollapseMirror.lean`) is instantiated at the same pair, as
`Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`: the
crossing of the two models of the iterated derived functor of `Γ(V, -) ∘ f_*`, followed by
Grothendieck's comparison of [Stacks, Tag 01XK] inverted, is `H^n` of the Leray comparison, the
edge morphism of `RΓ(V, -)`, and `Γ(V, -)` of the crossing for `Rf_*`. And
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_comp_lerayComposite`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSections.lean`)
is the same for
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare`.

*What the chase still owes.* Every ingredient is available, but the identity itself is not
performed. Reading `Γ(V, Θ)` factor by factor:

* `Γ(V, -)` of the leading crossing `homologyFunctorDerivedPushforwardIso` inverted. That crossing
  is `H^d` of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso`
  inverted, which is `CategoryTheory.Functor.boundedDerivedIso` at the direct image; the mirror's
  crossing is `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, and the two
  are identified by `Stacks.DerivedFunctor`
  `.singleCompDerivedCompHomologyIsoRightDerived_hom_app` up to
`Stacks.DerivedIndexing.rightDerivedIso`, which is a factor `T` already carries. **That
identification is available at the direct image along a morphism of schemes**, as
`…TopDegreeBaseChange.singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq`
(`TopDegreeCrossingSingleModel.lean`), with the crossing of the
`AlgebraicGeometry.Scheme.Modules` / `SheafOfModules (structureSheafRing …)` divide in argument
position; so this factor is dictionary, not work. **In the sections model** it is
`…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerived`
`PushforwardIso_hom_eq` (`TopDegreeCrossingSections.lean`): the edge morphism of `RΓ(V, -)` at
`Rf_*((E Z)[0])` followed by `Γ(V, -)` of the crossing is the collapse factor of
[Stacks, Tag 01XK] and `Γ(V, -)` of `rightDerivedIso`, with only the unconditional Leray
inverse asked for. Postcomposing it with `Γ(V, -)` of the crossing **inverted** — where the
`γ⁺` side's tail starts — leaves the edge morphism of `RΓ(V, -)` alone, and that is the prefix
the next two factors consume.
* `Γ(V, H^d(Rf'_*(-)))` of the two crossings and of the Mate square: the naturality of the edge
  morphism of `RΓ(V, -)` moves each across, and `derivedPushforwardComparisonSquare_comp`
  `_lerayComposite` is what the Mate square becomes — the transport along
  `(h' ≫ f')⁻¹V = (f'' ≫ h)⁻¹V`.
* `Γ(V, -)` of the edge morphism of `Rh_*`. **The route through**
  `map_sectionsOverOpen_derivedPushforwardHomologyComparison_app_eq` **is not available here.**
  That form solves the splitting of the edge
  morphism of `RΓ(h⁻¹V, -)` for its last factor, so it must invert the edge morphism of
  `RΓ(V, -)` at `Rh_*(Rf''_*((h')^* F'[0]))`; and
  `Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE` supplies that only
  when the cohomology sheaves of `Rh_*(Rf''_* …)` are `Γ(V, -)`-acyclic. Over the affine `V` that
  is [Stacks, Tag 01XB], which needs them **quasi-coherent**, hence needs `h` quasi-compact and
  quasi-separated — and the situation places **no hypothesis at all** on `h`. (Restricting to `V`
  does not rescue it: `H^j(Rh_* Rf''_* …)|_V = H^j(R(h ∣_ V)_* …)` and `h⁻¹V` is not affine, only
  the smaller `W` is.) What is available, and is what this factor uses, is the same splitting
  solved for its last **two** factors:
  `Stacks.EdgeCompat.sectionsOverOpenHomologyComparison_comp_map_derivedPushforwardHomology`
  `Comparison_eq` asks only for the Leray inverse, which is unconditional by
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`. The pair it absorbs — the edge
  morphism of `RΓ(V, -)` at `Rh_* K` immediately in front of `Γ(V, -)` of the edge morphism of
  `Rh_*` — is exactly what the previous factor's prefix and the naturality of the edge morphism
  produce, and `Stacks.EdgeCompat.sectionsOverOpenHomologyComparison_comp_map_comp_derived`
  `PushforwardHomologyComparison_eq` performs that naturality step and the absorption in one, for
  an arbitrary morphism of `D(𝒪_{Y'})` landing on `Rh_* K`. So no boundedness and no acyclicity
  is needed anywhere in this factor, and `isLE_derivedPushforward_baseChange` is not used.
* `Γ(V, h_*(-))` of the crossing at `f''`, and the restriction from `h⁻¹V` to `W`:
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_restrict`
  (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean`) is
  the restriction of the Leray comparison, and the crossing at
  `f''` is the first factor again, at `f''` over `W`. The intermediate step it needs is as follows.
  What the previous three factors leave in front of this one is the edge morphism of `RΓ(h⁻¹V, -)`
  at `K`, and the crossing at `f''` over `W` meets the edge morphism of `RΓ(W, -)`; getting from
  one to the other needs the **cohomology edge morphism's** compatibility with restriction to a
  smaller open, which `lerayComparison_restrict` is *not* — that is the same compatibility for the
  **Leray comparison**, a different transformation. It is
  `Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict`
  (`EdgeCompatRestrictSections.lean`), with no hypothesis on the space, the opens or the degree.

  That compatibility is a specialisation of a statement with no sections in it at all: the edge
  morphism is natural in the **functor**, along any natural transformation of two left exact
  additive functors with compatible right derived functors. That chain is stated at the
  generality the edge morphism is defined at, in
 `StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismOnARingedSite.lean`
  —
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
  `.cyclesComparison_naturality_natTrans` and `.homologyComparison_naturality_natTrans`
  degreewise, `.homologyComparisonNatTrans_naturality_natTrans` at the transformation level,
  `.homologyComparisonOnHomotopy_naturality_natTrans` on the homotopy category,
  `.homotopyHomologyComparisonToDerived_naturality_natTrans` at the derived functor's universal
  property, and `.derivedHomologyComparison_naturality_natTrans` for the edge morphism itself.
  `Stacks.EdgeCompat.derivedHomologyComparison_comp` is about **composing** two functors rather
  than moving along a transformation between two of them, which is why those six are needed.

So all four factors have their sections-model reading available, and the **first three are
composed**, as
`…TopDegreeBaseChange.prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`
(`TopDegreeCrossingSections.lean`): the prefix, then `Γ(V, -)` of the leading crossing inverted
followed by the rest of the tail through the edge morphism of `Rh_*`, is `H^d(RΓ(V, β))`, the
Leray inverse, and the edge morphism of `RΓ(h⁻¹V, -)`. Nothing is assumed of `h` there.

*What "the first three are composed" does and does not say.* That lemma holds `β` as a
**variable** — any morphism
`Rf'_*((E Z)[0]) ⟶ Rh_* K` of `D(𝒪_{Y'})` — and carries it across by the naturality of the edge
morphism of `RΓ(V, -)`. So factor 2 is composed **as a variable**: the two crossings and the Mate
square, which is what `β` is at the instantiation the tail needs, are never looked inside, and
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_comp_lerayComposite` — the
reading of the Mate square on derived sections over the two intermediate opens, which is what
factor 2's bullet above assigns to it — is **not** used there. Unfolding `H^d(RΓ(V, β))` at the
genuine `β` is part of step 2, not of step 1.

*The factor-2 assignment and its use.*
`derivedPushforwardComparisonSquare_comp_lerayComposite` is exactly the Mate-square reading that
unfolding `β` needs, and it is what the unfolding uses:
`Stacks.Cohomology.DerivedBaseChange.homology_map_derivedPushforwardComparisonSquare_eq_leray`
`Composite` (
`…/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSectionsHomology.lean`),
through its
object-level form `…derivedPushforwardComparisonSquare_app_comp_lerayComposite`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSections.lean`,
the file's own `_app_comp_leray` one
step further along). See step 2a below.

What the tail owes, in order. Steps 1 and 2a are **performed**; steps 2b and 3 are not:

1. *Gluing the last factor onto that composite — **performed**, see the paragraphs below.*
   The composite ends at the edge morphism of
   `RΓ(h⁻¹V, -)` in the spelling `Stacks.Cohomology.DerivedSectionsLeray.preimageSections h V`,
   and factor 4, `Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict`, is
   stated for `…DerivedSectionsLeray.sectionsOverOpen` at two opens of one space.

   **The functor-level identification this needs is the definition.**
   `…DerivedSectionsLeray.preimageSections f V` *is*
   `sectionsOverOpen X ((opensMap f).obj V) ⋙ ModuleCat.restrictScalars (f^♯ at V)`, and
   `…DerivedSectionsLeray.pushforwardPreimageSectionsIso f V`, which identifies it with
   `f_* ⋙ Γ(V, -)`, is `Iso.refl`; declaring it separately would duplicate an `abbrev` already in
   the library. **`Iso.refl _` inhabits it**, and that is how it is already used:
   `…TopDegreeBaseChange.preimageSectionsRightDerivedIso` (`EdgeCompatPreimageSections.lean`)
   passes `Iso.refl _` as `rightDerivedCompIso`'s `e : F ⋙ G ≅ H` argument at exactly this
   triple. So no named iso is declared here; write `Iso.refl _`.

   *The one caveat, which decides the spelling.* Only
   `sectionsOverOpen Y'' ((opensMap h).obj V)` — `SheafOfModules.evaluation` at that open — is
   definitionally the first factor. The open-subscheme reading `Γ((h⁻¹V : Scheme), ⊤)` through
   `Stacks.Cohomology.AffineBase.moduleGlobalSections` is **not** defeq: it needs the
   `AlgebraicGeometry.Scheme.Opens.topIso` factor, which is what
   `…TopDegreeBaseChange.app_comp_topIso_inv` and `…preimageSectionsCohomologyIso`
   (`TopDegreeSectionsModelCrossing.lean`) supply — and the latter is at a **fixed** module and
   degree, so it is not a functorial statement and cannot stand in for one. Stay in the
   `sectionsOverOpen` spelling and the identification is free.

   So what the glue actually needs is the edge morphism of a **composite** of two functors, not
   of a transformation between two: `preimageSections h V` is `Γ(h⁻¹V, -)` followed by
   restriction of scalars along `h^♯`, so its edge morphism splits by
   `Stacks.EdgeCompat.derivedHomologyComparison_comp` (`EdgeCompatComposition.lean`) at the pair
   `(Γ(h⁻¹V, -), ModuleCat.restrictScalars (h^♯))` — the same lemma
   `…derivedPreimageSectionsHomologyComparison_eq` uses at `(h_*, Γ(V, -))`. Factor 4 then
   applies to the inner factor at `W ≤ h⁻¹V`, and the transformation it supplies, whiskered by
   restriction of scalars along `h^♯`, is restriction to `W` with scalars over `Γ(V, 𝒪_{Y'})` —
   which is the target `T` carries, modulo the `appLE`-versus-composite spelling of the ring map
   that `…appLE_eq_comp_topIso` and `ModuleCat.restrictScalarsComp'` handle.
   `…DerivedSectionsLeray.preimageSectionsRestrictLE` is **not** this: it restricts along `W ≤ V`
   in the **base**, not to an open of `Y''` inside `h⁻¹V`.

   *The edge-morphism compatibility across that identification* is in
   `EdgeCompatPreimageRestrict.lean`. No statement elsewhere names
   `…HomologyComparison.derivedHomologyComparison` together with `preimageSections`, `opensMap`
   or `⁻¹ᵁ`, and the two nearby statements do not supply it:
   `Stacks.EdgeCompat.derivedPreimageSectionsHomologyComparison_eq` splits along the pair
   `(h_*, Γ(V, -))` on the **base**, so its last factor is the edge morphism of `Γ(V, -)` on
   `Y'`, not of `Γ(h⁻¹V, -)` on `Y''`; and
   `Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict` is at two opens of
   **one** space along `…DerivedSectionsLeray.sectionsRingRestrict`, not along `h^♯`.

   The content is not the identification but that the two sides name **different right derived
   functors with different units**, and `EdgeCompatRestrictSections.lean` is the template
   one-for-one. What `EdgeCompatPreimageRestrict.lean` proves, with nothing assumed of the
   morphism, the open or the degree:

   * `Stacks.EdgeCompat.preimageRestrictScalars`: restriction of scalars along `h^♯`, with its
     source ring **ascribed**. Not cosmetic. `ModuleCat.restrictScalars` takes its source ring
     implicitly, and the type of `(structureSheafHom h).hom.app (op V)` presents that ring as the
     sections over `V` of the *pushforward* of `structureSheafRing Y''`; keyed on that spelling,
     `CategoryTheory.Limits.PreservesFiniteLimits` is **not** synthesised, so the functor cannot
     be derived at all. Ascribed to `Γ(h⁻¹V, 𝒪_{Y''})` — the spelling the composition inside
     `preimageSections` forces — all three of additivity and preservation of finite limits and
     colimits are found, and the two readings agree by `rfl`.
   * `Stacks.EdgeCompat.preimageSectionsCompUnit` and
     `…isRightDerivedFunctor_preimageSectionsCompUnit`: `RΓ(h⁻¹V, -)` followed by that
     restriction of scalars is a right derived functor of sections over `h⁻¹V` read over
     `Γ(V, 𝒪_{Y'})`, through
     `…DerivedSectionsLeray.isRightDerivedFunctor_of_isIso_app_isKInjective`.
   * `Stacks.EdgeCompat.preimageSectionsCompUnitComp` and
     `…isRightDerivedFunctor_preimageSectionsCompUnitComp`: the same transformation and instance
     at the spelling `h_* ⋙ Γ(V, -)` of the degreewise functor, through a `show`, which is the
     pattern `…DerivedSectionsLeray.isRightDerivedFunctor_derivedPreimageSections_comp` records.
     **Two facts make this re-registration necessary and force the unit to be *defined* at the
     other spelling.** `PreservesFiniteLimits (preimageSections h V)` is not
     synthesisable, while the instances at `h_* ⋙ Γ(V, -)` are the ones already in use, so every
     statement has to be at the latter; and a unit *defined* at that spelling cannot be `rw`n in
     its own instance proof, because the resulting target is not type-correct at `implicit`
     transparency. Defining at the `Γ(h⁻¹V, -) ⋙ res` spelling and re-typing avoids both.
   * `Stacks.EdgeCompat.preimageSectionsModelComparison` and `…_fac_app`: the comparison of the
     two right derived functors, by `CategoryTheory.Functor.rightDerivedDesc`, and the
     factorisation that characterises it.
   * `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsModelComparison`: **the edge
     morphism of `RΓ(h⁻¹V, -)` over `Γ(V, 𝒪_{Y'})` in the `derivedPreimageSections` model is the
     comparison followed by the edge morphism in the model `RΓ(h⁻¹V, -) ⋙ res`.** This is
     `…derivedHomologyComparison_naturality_natTrans` at the **identity** transformation; no
     iso-shaped variant of that lemma was needed and none was declared.

   *The glue to sections over `W`, by the second of two possible routes.* The left-hand side
   above is exactly the edge morphism
   `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` ends at, so the step
   was to get from the right-hand side's `edge(Γ(h⁻¹V, -) ⋙ res)` to sections over `W`.

   * **The general brick**, which is what decides the route.
     `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` and
     `…isRightDerivedFunctor_exactPostcomposeUnit`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismExactFunctor.lean`)
     are the one statement that for `F`
     additive with a right derived functor `RF` and `G` **exact**, `RF ⋙ G.mapDerivedCategory`
     is a right derived functor of `F ⋙ G`.
     `Stacks.EdgeCompat.sectionsOverOpenRestrictCompUnit` and
     `Stacks.EdgeCompat.preimageSectionsCompUnit` are each one application of it, and so is the
     third instantiation below. Nothing is
     assumed of `F` beyond additivity; the K-injective resolutions are an explicit argument,
     which is why it is a theorem and not an `instance` — each site registers its own one-line
     `instance` by supplying its own resolutions.

     *A more general private version.* That brick is also proved **at greater generality** —
     for an arbitrary functor `G` out of the derived category, not just an exact one — as
     `isRightDerivedFunctor_postcomp` in
     `CategoryTheory/Sites/Cohomology/MayerVietoris/DescentForAFamilyOfSquares.lean:189`, where it
     is declared `private` and is therefore unusable from any other module. It is stated for an
     arbitrary `RF : D(𝒜) ⥤ H` and an arbitrary `G : H ⥤ H'`, with the unit
     `Functor.whiskerRight unit G` reassociated, and its proof checks the pointwise universal
     property at a K-injective resolution, whose indexing category has a terminal object: nothing
     is assumed of `G` at all. At `G := G.mapDerivedCategory` that is
     `isRightDerivedFunctor_exactPostcomposeUnit` up to the one `mapDerivedCategoryFactorsh`
     factor the latter's unit carries — `IsRightDerivedFunctor` being indexed by the unit, the two
     are not literally the same instance, so reusing it here would cost a transport along that
     factor. Making it public, or moving it beside
     `CategoryTheory.Functor.isRightDerivedFunctor_postcomp`
     (`Algebra/Homology/DerivedCategory/ExactFunctorBoundedBelow.lean:141`), which is the bounded
     statement of the same thing, would remove the duplication.
   * **The route taken, and why.** `Stacks.EdgeCompat`
     `.derivedHomologyComparison_preimageSectionsRestrictSource`
     (`EdgeCompatPreimageRestrictSource.lean`) is the **second** instantiation of
     `…derivedHomologyComparison_naturality_natTrans`, at
     `Stacks.EdgeCompat.preimageSectionsRestrictSource` —
     `Functor.whiskerRight (sectionsOverOpenRestrictLE Y'' hW) (preimageRestrictScalars h V)`,
     with its target's two restrictions of scalars associated into one factor — whose source is
     definitionally `preimageSections h V`. Its `CompUnit` and instance are the general brick at
     the pair `(Γ(W, -), res_{W ≤ h⁻¹V} ⋙ res_{h^♯})`, two lines; then a `rightDerivedDesc`
     comparison, its `fac_app`, and the instantiation. Nothing is assumed of `h`, of `V`, of `W`
     or of the degree.

     *Why this route rather than whiskering factor 4 by `res`.* What matters is what each route
     leaves for the next step, which needs the edge morphism of `RΓ(W, -)` itself.
     Whiskering factor 4 ends at
     `Functor.whiskerRight (edge(Γ(W, -) ⋙ res_{W ≤ h⁻¹V})) res_{h^♯}`, which is not an edge
     morphism of anything: reaching `edge(RΓ(W, -))` from there needs the split applied to
     `Γ(W, -) ⋙ res_{W ≤ h⁻¹V}` **and** a reassociation identifying a twice-whiskered edge
     morphism with the edge morphism whiskered by the composite — two exact prefixes and a
     bookkeeping step. This route ends at `edge(Γ(W, -) ⋙ (res ⋙ res))`, a genuine edge
     morphism at a composite target, which the split takes to `edge(RΓ(W, -))` in one
     application, leaving **one** exact prefix. Its cost — the declarations re-run at a second
     pair — is three declarations, the brick being general. So factor 4,
     `Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict`, is **not consumed
     by this chain**; it remains the statement at two opens of one space, with no morphism of
     spaces in it.
   * **The splitting is itself one general lemma.**
     `Stacks.EdgeCompat.derivedHomologyComparison_exactPostcomposeUnit_eq`: the edge morphism of
     a model `RF ⋙ G.mapDerivedCategory` with unit `exactPostcomposeUnit F G RF unit` splits as
     the edge morphism of `G` followed by `G` of the edge morphism of `RF`, for `F` left exact
     and `G` **exact**. Both splittings this chain performs are that lemma at a pair:
     `…derivedHomologyComparison_preimageSectionsCompUnit_eq` at
     `(Γ(h⁻¹V, -), res_{h^♯})`, and
     `…derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq` at
     `(Γ(W, -), res_{W ≤ h⁻¹V} ⋙ res_{h^♯})`, which is where the route above ends and which
     reaches **the edge morphism of `RΓ(W, -)` over `Γ(W, 𝒪_{Y''})`** — the thing the crossing at
     `f''` over `W` meets. Its one exact prefix is disposed of by
     `Stacks.EdgeCompat.isIso_derivedHomologyComparison_restrictScalarsComp`.

     So the whole of step 1 is performed: the chain runs from the composite of the first three
     factors to the edge morphism of `RΓ(W, -)`, with one invertible prefix in between and
     nothing assumed of `h`.

     *The declaration carrying the chain.*
     `Stacks.EdgeCompat.derivedHomologyComparison_derivedPreimageSections_comp_restrictSource`
     (`EdgeCompatPreimageRestrictSource.lean`) is the four composed, in the order a chase meets
     them: the edge morphism of `RΓ(h⁻¹V, -)` in the total `derivedPreimageSections` model — the
     one `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` ends at —
     followed by restriction of sections to `W`, is the two model comparisons, the exact prefix,
     and the two restrictions of scalars applied to the edge morphism of `RΓ(W, -)` over
     `Γ(W, 𝒪_{Y''})`. Nothing new is proved and nothing is assumed of `h`, of `V`, of `W` or of
     the degree.
   * **The first splitting in detail.**
     `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsCompUnit_eq` is
     `Stacks.EdgeCompat.derivedHomologyComparison_comp` at the pair
     `(Γ(h⁻¹V, -), ModuleCat.restrictScalars h^♯)` with the comparison of the two iterated
     derived functors the **identity** — the second model is `RΓ(h⁻¹V, -)` followed by the
     functor restriction of scalars induces, on the nose, so the coherence datum the splitting
     asks for *is* the definition of `preimageSectionsCompUnit`. The `IsRightDerivedFunctor`
     instance it needs for `(preimageRestrictScalars h V).mapDerivedCategory` at
     `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv` is found unaided, and
     its `hB` argument is
     `Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian` in the module
     category over `Γ(h⁻¹V, 𝒪_{Y''})`.
     `…derivedHomologyComparison_preimageSectionsCompUnitComp_eq` crosses the two spellings of
     the degreewise functor at that edge morphism, and is `rfl`; it is split off as its own
     lemma for the transparency reason given above.
   * **The exact prefix a split leaves is invertible.**
     `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
     `.isIso_derivedHomologyComparison_of_exact` and
     `…isIso_derivedHomologyComparison_mapDerivedCategory` assert it at **every** object of
     the derived category, with exactness the only hypothesis: no K-injectivity, no
     boundedness, no acyclicity. The complex level input is
     `…isIso_homologyComparison_of_exact`, the unbounded case of
     `Stacks.BoundedBelowEdge.isIso_homologyComparison_of_isStrictlyGE` with the two short
     exactnesses that argument obtains by an induction on the degree supplied instead by
     `Stacks.BoundedBelowEdge.shortExact_homologySC` — which holds at every complex — and
     `CategoryTheory.ShortComplex.ShortExact.map_of_exact`.

     *What is still absent there.* The **identification** of that edge morphism with
     `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` — the canonical commutation of
     `H^q` with `Functor.mapDerivedCategory`, which does exist, in
     `Algebra/Homology/DerivedCategory/MapDerivedCategoryHomology.lean`. No declaration relates
     it to `derivedHomologyComparison`. Proving the identification needs the complex level
     statement that `…HomologyComparison.homologyComparison`, defined by descending through the
     cokernel presentation of homology, is the component of
     `CategoryTheory.Functor.mapHomologicalComplexHomologyIso`, i.e. of Mathlib's
     `CategoryTheory.ShortComplex.homologyFunctorIso`, and nothing relates the two
     presentations. Invertibility holds without it, so the identification is wanted only
     in order to **name** the inverse; a consumer that needs the inverse can take `inv` of the
     invertibility.
2. *Identifying the result with `T`.* `T`'s factors are the ones listed above. The step splits in
   two, and the first half is **performed**.

   a. *Reading `β` — **performed**.* The factor step 1 leaves in front of the edge morphism of
      `RΓ(h⁻¹V, -)` is `H^d(RΓ(V, β))` followed by the Leray inverse, with `β` a **variable**.
      `Stacks.Cohomology.DerivedBaseChange.homology_map_derivedPushforwardComparisonSquare_eq`
      `_lerayComposite` (
      `…/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSectionsHomology.lean`)
      reads it
      at the genuine `β` — `Rf'_*(c)` followed by the Mate square, where `c` is the comparison
      `(h'_*(h')^* F')[0] ⟶ Rh'_*(((h')^* F')[0])` of the two models of `Rh'_*` that
      `derivedAdjunction_unit_comp_map_derivedToOrdinary_eq_single_unit` exhibits. Prefixed by the
      Leray comparison for `f'` at `V`, that factor is the degree-`d` cohomology of

      > `RΓ(f'⁻¹V, c)`, the relative Leray comparison for `h'` over `f'⁻¹V` inverted
      > (`…DerivedSectionsLeray.derivedPreimageSectionsCompIso`), the transport along
      > `(h' ≫ f')⁻¹V = (f'' ≫ h)⁻¹V`, and the relative Leray comparison for `f''` over `h⁻¹V`.

      Its right-hand end is the source of the edge morphism of `RΓ(h⁻¹V, -)`, so step 1's chain
      composes straight onto it. The Mate-square half is
      `derivedPushforwardComparisonSquare_comp_lerayComposite`, through its object-level form
      `…_app_comp_lerayComposite`; the comparison `c` is
      carried across by the naturality of the Leray comparison for `f'`. The only inverses are
      `isIso_lerayCompositeComparison` and `isIso_lerayComparison`, both unconditional, so
      **nothing is assumed of `h`**; there is no hypothesis on the square beyond its
      commutativity, none on `V`, none on `c` and none on the degree.

      *What the assembly costs.* Composing
      `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` with that identity
      **elaborates** — the two sides' factors line up and the proof is the step's statement
      whiskered by the edge morphism — but written out at generic data the resulting term is a
      **kernel** timeout, the Mate square occurring four times in one statement. So the assembly
      must hoist the edge morphism and the geometry onto variables, the discipline the rest of
      this file already follows; it is not a new mathematical obstruction.

   b. *Translating out of the sections model into `T`'s classical-model factors* —
      `openSectionsModuleIso`, `moduleGlobalSections`, `topIso`, [Stacks, Tag 01XK],
      `rightDerivedIso`, [Stacks, Tag 089W], `topDegreeFunctorObjIso…`, `restrictScalarsCongr`.
      **Not done.** In particular the two leading factors of 2a's right-hand side —
      `RΓ(f'⁻¹V, c)` then the relative Leray comparison for `h'` inverted — are what `T`'s
      "[Stacks, Tag 089W] along the affine `h' ∣` inverted" factor must be matched against, and
      that match is here, not in 2a.

      *The 089W match itself, at global sections of the two schemes.*
      `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison`
      (`AffineCohomologyComparison/DerivedSectionsModel.lean`) is exactly those two factors: for
      an affine morphism of schemes and a quasi-coherent module, [Stacks, Tag 089W] **inverted**
      is the crossing of the two models of `RΓ(S, -)` inverted, the derived sections over `⊤` of
      a comparison `c` of the two models of `Rf_*` retracting
      `CategoryTheory.Functor.singleCollapse`, a left inverse of the degree-`n` cohomology of the
      Leray comparison of [Stacks, Tag 0D5W], the crossing of the two models of `RΓ(f⁻¹⊤, -)`,
      and restriction of scalars pulled out of the right derived functor.
      `…cohomologyIsoPushforward_hom_eq_lerayComparison` is the same uninverted. Both are
      instances of `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_hom_eq` — its
      `RF`, `RG`, `RFG` and `θ` are the derived direct image, derived
      sections over `⊤`, derived sections over `f⁻¹⊤` and the **Leray comparison**, and the
      coherence `hθ` it asks for is
      `…DerivedSectionsLeray.lerayComparison_fac_app_refl` on the nose. The two inverses are
      taken as left inverses of plain morphisms, as 2a takes the Leray one, so the two statements
      compose and nothing is assumed beyond the affineness and quasi-coherence 089W itself
      carries.

      *What 2b still owes.* That match is at `⊤` of the two schemes, and the tail meets
      089W at the **restricted** morphism `h'.resLE (f'⁻¹V) (f''⁻¹W)`. Two passages are therefore
      needed: from the open subscheme's global sections to the relative statement over the
      open `f'⁻¹V` of `X'` — the direction
      `…TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso` and
      `…preimageSectionsCohomologyIso` go — and the passage between the two upstairs opens the two
      sides read the `h'` factor at, `h'⁻¹(f'⁻¹V) = f''⁻¹(h⁻¹V)` against the smaller
      `f''⁻¹W`. **The second of those two is**
      `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource`
      (`LerayCompositeRestrictSource.lean`); and of the first, the transport of its two **ends** is
      `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen`
      (`AffineComparisonOverOpen.lean`). What that leaves is the first passage's **middle**, which
      the paragraphs below discuss. The remaining pieces of 2b —
      `openSectionsModuleIso`, `topIso`, [Stacks, Tag 01XK] over `V`, `rightDerivedIso`,
      `topDegreeFunctorObjIso…` and `restrictScalarsCongr` — are discussed further below.

      *The first passage: its two ends are a transport, its middle is a separate theorem.* The
      ψ side carries `cohomologyIsoPushforward` at the restricted morphism,
      an isomorphism between the **global** sections cohomologies of the two open subschemes; the
      `γ⁺` side speaks of derived sections over the open `f'⁻¹V` of `X'`. Carrying the two ends of
      that isomorphism into the relative model is pure dictionary, and all three entries it needs
      are available, so **nothing new is proved**:

      * upstairs, `…TopDegreeBaseChange.derivedPreimageSectionsIsoAffineOpenCohomology`
        (`TopDegreeSectionsModelCrossing.lean`) through the `ℕ`-versus-`ℤ` indexing of
        `…affineOpenCohomologyNatIso` — and `…affineOpenCohomologyNat f V F d` is, on the nose,
        `AlgebraicGeometry.Scheme.Opens.topIso`-restricted scalars applied to the **source** of
        `cohomologyIsoPushforward (f ∣_ V) (F|) d`, which is why no new comparison is needed there;
      * downstairs, `…TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso`
        (`DerivedSectionsModelCrossing.lean`);
      * and `AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`
        (`AffinePushforward/Basic.lean:95`), the identification `(f ∣_ V)_*(F|_{f⁻¹V}) ≅ (f_*F)|_V`
        the one the downstairs crossing produces.
        — `morphismRestrict` together with `pushforward` — and not by name.

      What `AffineComparisonOverOpen.lean` proves, with **no hypothesis beyond the two
      [Stacks, Tag 089W] itself carries at the restricted morphism** (`IsAffineHom (f ∣_ V)` and
      quasi-coherence of `F|_{f⁻¹V}`), and in particular nothing of `h`:
      `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen` —
      `H^n(RΓ(f⁻¹V, F[0])) ≅ H^n(RΓ(V, (f_*F)[0]))` over `Γ(S, V)` — its two readings `…_hom` and
      `…_inv`, and **the transported equation** `…_hom_eq_lerayComparison` and
      `…_inv_eq_lerayComparison`, which are
      `cohomologyIsoPushforward_hom_eq_lerayComparison` and `…_inv_eq_lerayComparison` carried
      through it, the inverse direction taking the same two left inverses of plain morphisms as the
      global-sections statement so that nothing is added.

      ***What the middle owes.*** The ends-transport is cheap — its proofs are one `rfl`, one
      `CategoryTheory.Iso.trans_inv` reassociation at variables, and two `congrArg`s — because the
      content sits in the three crossings above. The expensive half is the **middle**: the
      transported equation still names
      `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison (f ∣_ V) ⊤` and the two model
      crossings **on the open subschemes**, while the `γ⁺` side names
      `…lerayCompositeComparison h' f' V` on `X'` and `Y'`. So what is owed is the compatibility of
      the Leray comparison of [Stacks, Tag 0D5W] with **restriction to an open subscheme** —
      `lerayComparison (f ∣_ V) ⊤` against `lerayComparison f V`, and
      `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the two pairs
      likewise. `…DerivedSectionsLeray.lerayComparison_restrict`
    (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean:439`)
      is the compatibility at two opens of **one** base, not across an open immersion. *Of those
      two, the Leray one is available at both the `∣_` and the `resLE` shape and the
      `singleCompDerivedCompHomologyIsoRightDerived` one is still absent; step 2b.3 below
      discusses both.*

      ***The crossing at the Leray comparison's source.*** The compatibility itself is in
      `LerayOpenSubschemeDerived.lean` and `LerayOpenSubschemeDerivedLE.lean`, at the two shapes;
      `AffineComparisonOverOpen.lean` — the 2b(i) ends-transport — *names*
      `lerayComparison (f ∣_ V) ⊤` but says nothing about `lerayComparison f V`. What
      `LerayOpenSubschemeSections.lean` proves, with no hypothesis on the morphism, the open or
      the module:

      * `…TopDegreeBaseChange.restrictScalarsSquareIso` and `…_app`: restriction of scalars along
        either side of a commuting square of ring maps as an isomorphism of **functors**, the
        functorial form of `…TopDegreeBaseChange.restrictScalarsSquareObjIso`, which is stated at
        an object. The `_app` lemma says the two are the same comparison.
      * `…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso`: **the model crossing at the
        degreewise source of the Leray comparison** —
        `preimageSections f V ≅ (-)|_{f⁻¹V}` then `preimageSections (f ∣_ V) ⊤`, read over
        `Γ(S, V)` through `AlgebraicGeometry.Scheme.Opens.topIso` at `V`. This is the `γ⁺` side's
        route: the crossing `sectionsOnImageTopNatIso` of the two sections functors at the
        open `f⁻¹V`, and the square of the two readings of the scalars whose input is
        `app_comp_topIso_inv_hom`.
      * `…TopDegreeBaseChange.preimageSectionsRestrictPushforwardIso` and
        `…preimageSectionsOpenSubschemePushforwardIso`: **the same crossing by the `ψ` side's
        route** — sections over `V` of the direct image, restricted to the open subscheme `V`, and
        [Stacks, Tag 01E5] undervied
        (`…HigherDirectImage.modulePushforwardRestrictIso`) identifying that with the global
        sections of `(f ∣_ V)_*((-)|_{f⁻¹V})`.

      *Four `rfl`s, which is why the crossing costs two declarations and not a file.*
      With the **ringed-space** restriction `…HigherDirectImage.moduleRestriction` — not
      `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, for the reason below —
      `moduleRestriction X U ⋙ sectionsOverOpen (U : Scheme) ⊤` **is**
      `sectionsOverOpen X (U.ι ''ᵁ ⊤)`; `Stacks.Cohomology.SchemeOpenSections.imageTop X U` **is**
      `U.ι ''ᵁ ⊤`; `AlgebraicGeometry.sectionsOn X U` **is**
      `…DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace U`; and
      `modulePushforward (f ∣_ V) ⋙ sectionsOverOpen (V : Scheme) ⊤` **is**
      `preimageSections (f ∣_ V) ⊤`. So the whole crossing of the two sections functors is
      `sectionsOnImageTopNatIso` and nothing about sections is re-proved.

      ***The compatibility, in three parts.*** All three are performed:
      `…TopDegreeBaseChange.openSubschemeSectionsComparison_comp_lerayComparison_eq`
      (`LerayOpenSubschemeDerived.lean`) is the compatibility of the Leray comparison of
      [Stacks, Tag 0D5W] with restriction to an open subscheme, with nothing assumed of `f`, of `V`
      or of the module. Part 1 below is the degreewise half and part 2 the derived packaging;
      part 3 concerns the comparison of `Rf_*` with `R(f ∣_ V)_*`, which is [Stacks, Tag 08FE],
      and which the compatibility does not need.

      1. *The degreewise equality of the two routes.* The two isomorphisms above are
         transformations between the **same** pair of functors and they are equal — on sections
         both are the restriction map of the sheaf of modules along an equality of opens, since
         `…HigherDirectImage.modulePushforwardRestrictIso_hom_app_val_app` and
         `…TopDegreeBaseChange.openSectionsImageTopIso_hom_apply` are both `rfl` and the morphisms
         of `TopologicalSpace.Opens` between two equal opens agree. ***That equality is
         proved***, as `…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso_eq`
         (`LerayOpenSubschemeSections.lean`), with nothing assumed of `f` or of `V`.

         *Why the proof goes through `HEq`.* `rfl` on the two assembled natural transformations,
         `rfl` on their components at a module, `rfl` on the components of their **inverses**,
         and `ext M x` followed by `rfl` each exhaust 200,000 heartbeats at `whnf` or at
         `isDefEq`. The way through is **not** a shuffle at variables (as done by
         `LerayCompositeRestrictSource.lean`'s private `glue_two_naturalities`), nor a
         decomposition of either route into factors: **no factor of either route is ever
         unfolded and no reassociation is performed**. It is that each route's *inverse*, applied
         to a local section, is **heterogeneously equal to that section** — both are restriction
         maps of the sheaf of modules along an equality of opens of `X`, and
         `…HigherDirectImage.heq_val_map_eqToHom` says such a restriction is the identity up to
         `HEq`. Two maps with the same source and the same target that are each `HEq` the identity
         are equal, by `eq_of_heq`. The three `HEq`s are cheap exactly where the `rfl`s are not,
         because each is matched against a **named** restriction map instead of against the other
         route:

         * `…heq_preimageSectionsOpenSubschemeIso_inv_app` is one application of
           `heq_val_map_eqToHom`;
         * `…heq_modulePushforwardMorphismRestrictIso_hom_app_val_app` is
           `…HigherDirectImage.modulePushforwardRestrictIso_hom_app_val_app_heq` carried across
           the `eqToIso` of `…SchemeHigherDirectImage.toShHom_morphismRestrict` by the general
           `…TopDegreeBaseChange.heq_eqToIso_trans_val_app`;
         * `…heq_preimageSectionsOpenSubschemePushforwardIso_inv_app` composes that with
           `heq_val_map_eqToHom` at the direct image, **with the inner section supplied
           explicitly** — left as a metavariable, the unifier unfolds the whole route and times
           out.

         `…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` names the transport inside
         `preimageSectionsOpenSubschemePushforwardIso`. It is not a second copy of
         [Stacks, Tag 01E5] underived but the one `eqToIso` the ringed-space comparison has to be
         read through, and it carries a name because
         `heq_modulePushforwardMorphismRestrictIso_hom_app_val_app` must speak about it.

         *A private duplicate.*
         `heq_eqToIso_trans_val_app`'s content — `eqToHom` of an equality of sheaves of modules is
         the identity on local sections up to `HEq` — is also proved as
         `eqToHom_sheaf_app_heq`
         (`Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomC.lean`), declared `private` and
         stated for an `AlgebraicGeometry.RingedSite`. The one public relative,
         `Stacks.SheafOfModules.GradedAlgebra.heq_eqToHom_val_app`
         (`Algebra/Category/ModuleCat/Sheaf/TensorSheafWorldBridge.lean`), is for a family of
         sheaves indexed by `ℤ` and an equality of degrees, not an equality of sheaves.
      2. *The two `rightDerivedDesc`s — **performed**, in `LerayOpenSubschemeDerived.lean`.* Both
         Leray comparisons are `CategoryTheory.Functor.rightDerivedDesc`s of their units, so the
         comparison of their sources is an equality of two transformations out of
         `derivedPreimageSections f V` and `…DerivedSectionsLeray.lerayComparison_ext` applies.
         `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean`
         is the template one-for-one: a `…HomotopyIso` splitting the
         composite off the homotopy category, a `…Unit`, the `rightDerivedDesc`, and `…_fac_app`
         with its `…_fac_app_comp` form. Two are needed and both are proved, out of the two right
         derived functors of the **same** degreewise sections functor, and into the **same**
         derived target
         `…TopDegreeBaseChange.derivedPreimageSectionsOpenSubscheme` — derived restriction to the
         open subscheme, then `RΓ((f ∣_ V)⁻¹⊤, -)`, then derived restriction of scalars along
         `topIso`:

         * `…TopDegreeBaseChange.openSubschemeSectionsComparison` out of
           `derivedPreimageSections f V`, with unit from the `γ⁺` route, and
         * `…TopDegreeBaseChange.openSubschemePushforwardComparison` out of
           `derivedPushforward f ⋙ derivedSectionsOverOpen S V`, with unit from the `ψ` route;

         and a **third**, `…TopDegreeBaseChange.openSubschemeLerayComparison`, out of the same
         functor as the second but into
         `…TopDegreeBaseChange.derivedPushforwardSectionsOpenSubscheme` — the same target with the
         Leray comparison's own target upstairs — which is what the paragraph below the next one
         uses.

         With their `_fac_app` and `_fac_app_comp` forms, and
         `…TopDegreeBaseChange.openSubschemeSectionsComparison_eq`: **the first is the Leray
         comparison followed by the second.** Nothing is assumed of `f`, of `V` or of the module.
         The `IsRightDerivedFunctor` instance the second needs is **not** a re-proof of
         anything: `lerayComparison f V` *is* the `rightDerivedDesc` at
         `lerayUnit f V`, so `CategoryTheory.Functor`
         `.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` read right-to-left at
         `isIso_lerayComparison f V` supplies it, and that is all
         `…DerivedSectionsLeray.isRightDerivedFunctor_lerayUnit` is.

         *The two units are the same unit, which is why the compatibility is cheap.* Both are
         `…TopDegreeBaseChange.openSubschemeUnitOfIsoUnit` — the degreewise crossing on the
         homotopy category, the splitting of the two exact factors, a unit upstairs and
         `mapDerivedCategoryFactorsh` for the restriction — at a **variable** presentation of the
         degreewise crossing and a **variable** unit upstairs, so `openSubschemeSectionsUnit_eq`
         is `congrArg` on `preimageSectionsOpenSubschemeIso_eq` and no factor of either route is
         unfolded. The
         compatibility is then the two `_fac_app`s and `lerayComparison_fac_app_comp`.

         *The one instance crossing this costs.*
         `…HigherDirectImage.moduleRestriction X.toRingedSpace (f ⁻¹ᵁ V)` has declared target the
         modules on `…HigherDirectImage.restrictToOpen X.toRingedSpace (f ⁻¹ᵁ V)`, and
         `preimageSections (f ∣_ V) ⊤` has source the modules on
         `(f ⁻¹ᵁ V : Scheme).toRingedSpace`: the second spelling pair described below. The
         degreewise crossing is stated across them and elaborates, because no instance is asked
         for there; `Functor.mapHomotopyCategoryCompIso` does ask, and the `Functor.Additive`
         subgoal it generates carries (as `pp.explicit` shows) the `restrictToOpen`
         spelling, where neither `preimageSections_additive` nor `Functor.instAdditiveComp`
         applies — while `Functor.instAdditiveComp _ _` closes the same composite's additivity
         when it is asked for on its own, and an instance declared at the other spelling is not
         found. A type **ascription** does not fix it: `(e : T).Additive` elaborates `e` first and
         then reads its own type, so the ascription is dropped. The cure is a `def` —
         `…TopDegreeBaseChange.openSubschemeRestriction` — whose *declared* target is the open
         subscheme's own structure sheaf, with `Additive`, `PreservesFiniteLimits` and
         `PreservesFiniteColimits` carried over by `inferInstanceAs`, in term mode where the
         conversion runs at default transparency. It is deliberately not an `abbrev`: reducible,
         instance search unfolds it and lands back on the spelling it cannot use.

         ***And the compatibility 2b(i) owes — `lerayComparison (f ∣_ V) ⊤` against
         `lerayComparison f V` — is in the same file.***
         `openSubschemeSectionsComparison_eq` by itself compares the Leray comparison with the
         crossing of its **source** and does not mention `lerayComparison (f ∣_ V) ⊤` at all. The
         statement that does is
         `…TopDegreeBaseChange.openSubschemeSectionsComparison_comp_lerayComparison_eq`: the
         crossing of the source, followed by the Leray comparison for `f ∣_ V` over `⊤` whiskered
         by the derived restriction and the derived restriction of scalars, is
         `lerayComparison f V` followed by `…openSubschemeLerayComparison`, the **third**
         `rightDerivedDesc` out of `derivedPushforward f ⋙ derivedSectionsOverOpen S V`, into
         `Rres ⋙ R(f ∣_ V)_* ⋙ RΓ(V, ⊤) ⋙ res`, whose unit is the `ψ` route with
         `lerayUnit (f ∣_ V) ⊤` upstairs. Nothing is assumed of `f` or of `V`.

         *What that step costs.* One might expect the degreewise identity to need
         `mapDerivedCategoryFactorsh` and the naturality of the Leray comparison, because the
         left-hand side's component sits at `Rres(Qh K)` rather than at `Qh K'`. The
         component at all: the unit is built by `…TopDegreeBaseChange.openSubschemeUnitOfIsoUnit`
         from a **variable** upstairs unit, and
         `…TopDegreeBaseChange.openSubschemeUnitOfIsoUnit_comp` composes a transformation of the
         upstairs derived functors onto it once and for all, its whole content being that
         transformation's naturality at the one morphism `factorsh.inv.app K`. The two units are
         then identified by `lerayComparison_fac` at `(f ∣_ V, ⊤)` read backwards through that
         lemma, and `lerayComparison_ext` finishes. No factor of the crossing is unfolded.

         ***The third descent needs no [Stacks, Tag 08FE].***
         Part 3 below observes that the two Leray comparisons' targets are related by nothing in
         the sections vocabulary, which suggests that the comparison of `Rf_*` with `R(f ∣_ V)_*`
         across the restriction is required. What the universal property actually asks for is a
         **transformation** out of `Rf_* ⋙ RΓ(V, -)`, not an isomorphism of the two targets, and
         the degreewise `ψ` route together with `lerayUnit (f ∣_ V) ⊤` supplies one — which is
         exactly how `openSubschemePushforwardComparison` and `openSubschemeLerayComparison` are
         built, with no 08FE anywhere in either (axioms: `propext`, `Classical.choice`,
         `Quot.sound`). 08FE's instantiations are an alternative route to the same place, and the
         spelling bridge part 3 describes is the way to use them; it is not a prerequisite for
         anything here.
      3. ***The comparison of `Rf_*` with `R(f ∣_ V)_*` across the restriction, which is
         [Stacks, Tag 08FE].*** The two Leray comparisons' **targets** are
         `derivedSectionsOverOpen S V ∘ Rf_*` and
         `derivedSectionsOverOpen (V : Scheme) ⊤ ∘ R(f ∣_ V)_*` after the restriction, and no model
         crossing of **sections** relates them: what relates them is the comparison of `Rf_*` with
         `R(f ∣_ V)_*` across the restriction. That comparison is in the library three times over,
         each depending only on the axioms `propext`, `Classical.choice` and `Quot.sound`:

         * `Stacks.Cohomology.derivedPushforwardRestrictIso`
           (`Topology/Sheaves/Cohomology/CechAndResolutions/KInjectiveRestriction.lean:960`),
           carrying `@[stacks 08FE]`: for a cartesian square of ringed spaces whose two vertical
           edges are open immersions, `Rf ⋙ Rj ≅ Ri ⋙ Rg`, **fully parametric** in the four right
           derived functors and their units — so it is instantiated, not re-proved, at any choice
           of model for the restriction;
         * `AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`
           (`MoreMorphisms/PseudoCoherentThree/DerivedChowFourierMukai.lean:198`),
           which is exactly this comparison at an open of the target of a morphism of **schemes**:
           `Rq_* ⋙ L(V.ι)^* ≅ L((q ⁻¹ᵁ V).ι)^* ⋙ R(q ∣_ V)_*`, with the square supplied by
           Mathlib's `AlgebraicGeometry.isPullback_morphismRestrict` and
           `AlgebraicGeometry.isPullback_toShHom` (`DerivedAcyclic/Pushforward.lean:175`);
         * `…TorIndependence.derivedPushforwardRestrictIsoCanonical`
           (`AlgebraicGeometry/BaseChange/TorIndependence/DerivedBaseChangeGlobal.lean:339`), the
           same at the canonical derived pushforwards and pullbacks of ringed spaces.

         *Where it is filed.* It is filed under the **pullback** vocabulary and under the Stacks
         tag of "forming the total direct image commutes with localization", 08FE, rather than
         under the **sections** vocabulary or under names built from `derivedPushforward`
         together with `moduleRestriction`, `restrictFunctor` or `∣_`; its restriction functor is
         `derivedPullback` of [Stacks, Tag 079W], not a `mapDerivedCategory`. Two nearby
         declarations are not it: `…DerivedQCoh.OpenLift.openDerivedPushforwardRestrictionIso` is
         `Lj^*(Rj_* E) ≅ E` and `Duality/OpenImmersion/DerivedRestrictAdjunction.lean` is the
         adjunction.

         *So a route via `exactPostcomposeUnit` and a fourth `rightDerivedDesc` is not taken: it
         would be a second construction of 08FE.* What is needed is only the **spelling
         bridge**, because the Leray crossing of part 1 is written with
         `…HigherDirectImage.moduleRestriction` and 08FE's instantiations are written with
         `RingedSpaceModuleAdjunction.modulePullback`. The two are isomorphic by
         `Stacks.Cohomology.ClosedSupportPerfect.pullbackOpenRestrictionIso`
       (`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean:249`,
         both are left adjoint to the
         pushforward), and that file already carries the derived packaging at the `modulePullback`
         spelling — `derivedRestrictionAlongOpen`, `derivedRestrictionAlongOpenUnit` and
         `derivedRestrictionAlongOpen_isRightDerived`.

         ***The spelling bridge.*** `…TopDegreeBaseChange.derivedPushforwardMorphismRestrictIso`
         (`DerivedPushforwardOpenSubscheme.lean`) is 08FE at an open `V` of the target of a
         morphism of schemes with the restriction read as `mapDerivedCategory` of
         `…HigherDirectImage.moduleRestriction`:
         `Rf_* ⋙ D((-)|_V) ≅ D((-)|_{f⁻¹V}) ⋙ R(f ∣_ V)_*`, nothing assumed of `f` or of `V`
         (axioms: `propext`, `Classical.choice`, `Quot.sound`). It is the derived counterpart of
         the underived `…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso`, and it places
         no `@[stacks …]` attribute: 08FE carries its own where the comparison is built and where
         its scheme form is instantiated.

         *How the bridge is built.* No unit is transported: `derivedPushforwardRestrictIso` is
         not instantiated afresh with `Ri`, `Rj` the `mapDerivedCategory` of `moduleRestriction`
         and the units transported along `pullbackOpenRestrictionIso`. 08FE is **already**
         instantiated at the standard derived functors at exactly this square —
         `AlgebraicGeometry.DerivedChow.derivedPushforwardRestrictOpenIso`, which carries
         `@[stacks 08FE]` — so the restriction spelling is changed in the **statement** and not in
         the units, by whiskering an isomorphism of functors onto each side of it. Two
         `Functor.isoWhisker`s and nothing else; re-instantiating 08FE would be a second
         instantiation of a tagged theorem.

         *The isomorphism those two whiskerings use.*
         `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`
    (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/OpenImmersionRestriction.lean:157`)
         is
         `derivedPullback (X.ofRestrict U.isOpenEmbedding) ≅ (moduleRestriction X U)`
         `.mapDerivedCategory` — precisely the `modulePullback → moduleRestriction` bridge at the
         derived level, with the companion `…derivedPullbackOpenRestrictionIso` at the
         `ExtensionByZeroModules.resRing` spelling and `…derivedPullbackIsoMapDerivedCategory`
         for an arbitrary exact pullback. Its proof shows how to get past the instance problem
         described next: the three exactness arguments are written out and passed explicitly in a
         term-mode `exact`, where the conversion runs at default transparency, instead of being
         synthesised.

         *The instance problem.* The failure is the second spelling pair,
         `…HigherDirectImage.restrictToOpen X U` against `X.restrict U.isOpenEmbedding`: with
         `pp.explicit`, the subgoal `Functor.Additive` that `Functor.mapHomotopyCategoryCompIso`
         generates in `LerayOpenSubschemeDerived.lean` carries
         `Stacks.Cohomology.HigherDirectImage.restrictToOpen X.toRingedSpace`
         `((Opens.map f.base).obj V)` as the source category's space. A type **ascription** does
         not repair it — `(e : T).Additive`
         elaborates `e` first and reads its own type, so the ascription is dropped — and an
         instance declared at the other spelling is not found either. What works is to give the
         functor a name whose *declared* type is the wanted spelling and carry its instances over
         by `inferInstanceAs`, or to pass them explicitly in term mode, which is what the two
         declarations above do.

         *Three constructions that fail for this reason:*
         `CategoryTheory.Functor.mapHomotopyCategoryNatIso` at `pullbackOpenRestrictionIso`; the
         same with a `letI` supplying `Additive` at the `X.restrict U.isOpenEmbedding`
         ascription; and `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, which
         has its two functors explicit — all three report `failed to synthesize`
         `(moduleRestriction X U).Additive`, even though `(moduleRestriction X U).Additive` *is*
         found standalone, as are `PreservesFiniteLimits`, `PreservesFiniteColimits`, and
         `.mapDerivedCategoryFactorsh` itself.

         *Two free inputs, which the bridge does not need.*
         `V.ι.toLRSHom.toShHom = …HigherDirectImage.openSubspaceInclusion S.toRingedSpace V` by
         **`rfl`**, and the ringed-space cartesian square is the one line
         `AlgebraicGeometry.isPullback_toShHom (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι`
         `(isPullback_morphismRestrict f V).flip`, which elaborates. The scheme
         form of 08FE supplies that square itself, so the bridge passes neither.

         *A route not taken.* The same bridge at
         ringed-space generality — `derivedPushforwardRestrictIso` instantiated at
         `derivedRestrictionAlongOpen`, whose units and `IsRightDerivedFunctor` instance
         `StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/ClosedSupportPerfect.lean`
         already carries, then whiskered by
         `derivedRestrictionAlongOpen X U ≅ (moduleRestriction X U).mapDerivedCategory` — also
         elaborates, and so does its scheme instantiation, but the latter needs
         `attribute [local instance 10000] HasDerivedCategory.standard` (at the default priority
         the two `HasDerivedCategory` instances give `Functor.{u, u, …}` against
         `Functor.{u + 1, u + 1, …}`; import order is load-bearing here) and needs the
         `IsRightDerivedFunctor` of `derivedPushforward (f ∣_ V)` passed through `@` and
         `inferInstanceAs`, the `quasiIso` morphism property carrying the `X.restrict` spelling.
         It is a second instantiation of 08FE and is strictly more expensive than whiskering the
         existing one, so it is not used.

         ***A further instance of the same phenomenon.***
         `…HigherDirectImage.openSubspaceInclusion X U` is a `noncomputable abbrev` for
         `X.ofRestrict U.isOpenEmbedding`, and the two are **not** interchangeable for instance
         synthesis across the module boundary: `(modulePullback (X.ofRestrict
         U.isOpenEmbedding)).Additive` is found and `(modulePullback (openSubspaceInclusion X
         U)).Additive` is **not**, in the same file, with the same imports. Write `ofRestrict` in
         any position an instance has to be synthesised at.

         Collapsing `Rf_*(F[0])` to `(f_* F)[0]` instead would need `f_*`-acyclicity, i.e.
         affineness, which the statement does not carry; that route is a weakening and is not
         taken.

      *Two instance-synthesis pitfalls.* `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`
      and `…HigherDirectImage.moduleRestriction X.toRingedSpace V` are equal functors
      (`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`) and are **not**
      interchangeable for instance synthesis; the derived machinery needs the second, because
      `HasDerivedCategory X.Modules` is not synthesisable, while everything at the
      `SheafOfModules (structureSheafRing _)` spelling is found. And
      ascribing `moduleRestriction X.toRingedSpace U`'s target to `(U : Scheme).toRingedSpace`
      **loses** its `Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits` instances,
      so `restrictToOpen X.toRingedSpace U` and `(U : Scheme).toRingedSpace` are a
      second spelling pair to keep apart; a composite written across them is reported as a missing
      `Functor.Additive` instance even though both factors have one.

      *Two duplicates.*
      `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`
      (`TopDegreeBaseChange/SchemeRestriction.lean:151`) and
      `Stacks.LocalCohomology.schemeRestrictFunctor_eq_moduleRestriction`
      (`LocalCohomology/PushforwardCoherence/RestrictPushforward.lean:48`) are the same statement
      with the same four-line proof. And the undervied restriction-of-a-direct-image comparison
      exists at two spellings: `AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`
      (`AffinePushforward/Basic.lean:95`, the `Scheme.Modules` spelling) and
      `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`
    (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationComparison.lean:366`,
      the ringed-space spelling), each with
      its own four-factor construction; the second is the one the crossing above uses, because only
      it carries the characterising `…_hom_app_val_app`.

      *A route not taken, and why.* The alternative is to build a relative
      [Stacks, Tag 089W] **over the open `V`** directly, from the fully parametric
      `…AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`
      (`AffineCohomologyComparison/UnboundedModel.lean`) at the pair
      `(f_*, Γ(V, -))` — and every input of that brick exists at an arbitrary open:
      `Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic` takes the open as
      an argument, and `…DerivedSectionsLeray.lerayComparison_fac_app_refl f V` is its coherence
      `hθ` on the nose for every `V`. Two facts stop it. **`HasDerivedCategory S.Modules`
      is not synthesisable**, so the pair
      must be written at the `SheafOfModules` spelling with the instances passed inside an
      `@`-application; and there the acyclicity `…AffineComparison`
      `.rightAcyclic_pushforward_of_isAffineHom`, which is stated at the `Scheme.Modules` spelling,
      does **not** defeq-check against the expected type within 200,000 heartbeats, even though
      `Scheme.Modules.pushforward f = modulePushforward f.toLRSHom.toShHom` is `rfl` —
      the two spellings' `Abelian` and `HasDerivedCategory` instance terms are what differ, and
      `CategoryTheory.Functor.rightAcyclic` is indexed by them. And even built, that object would
      not discharge the passage: the ψ side carries the **classical** 089W at the restricted
      morphism, so the two would still have to be identified, which is a transport of
      `…AffineComparison.rightDerivedCollapseIso` across a change of the functor **pair** — nothing
      in the library supplies one, and the restriction enters by **pre**-composition, where an
      exact functor does not commute with a right derived functor for free.

      *Two elaboration pitfalls.* `Stacks.Cohomology.AffineBase.moduleGlobalSections` is
      ambiguous under `open AlgebraicGeometry` even without `open …AffineBase`, and must be written
      fully qualified — and it **is** `…DerivedSectionsLeray.sectionsOverOpen` at `⊤`
      by `rfl`, so a relative 089W in the `sectionsOverOpen` model would specialise to 089W itself.
      And proving the transported equation by
      `rw [cohomologyIsoPushforwardOverOpen_hom, cohomologyIsoPushforward_hom_eq_lerayComparison]`
      exhausts 200,000 heartbeats at `isDefEq`, while the same equation is proved in seconds by
      `congrArg` at an explicit lambda, the `_hom` reading being
      `rfl`. This is the same `rw`-versus-term phenomenon as above.

      *Where that second passage sits.* 2a's right-hand side does **not** end at
      `h'⁻¹(f'⁻¹V)`. Its last factor is `(lerayCompositeComparison f'' h V).app M`, and
      `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison i p V`
   (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayCompositeSections.lean:125`)
      has type
      `derivedPreimageSections (i ≫ p) V ⟶ derivedPushforward i ⋙ derivedPreimageSections p V`,
      so at `(i, p) = (f'', h)` its target is derived sections over `h⁻¹V` — **downstairs on
      `Y''`** — of `Rf''_* M`. That is what step 2a's own paragraph above says ("its right-hand
      end is the source of the edge morphism of `RΓ(h⁻¹V, -)`, so step 1's chain composes
      straight onto it"). The `h'⁻¹(f'⁻¹V)`
      spelling occurs **mid-chain**, as the source of the `eqToHom` transport along
      `(h' ≫ f')⁻¹V = (f'' ≫ h)⁻¹V`, and is consumed there by the relative Leray comparison for
      `f''`. So the end of 2a is already matched, by step 1; nothing is owed there.

      *What is owed instead, and the brick it needs.* The mismatch is between the two sides'
      **heads**. The `γ⁺` chain restricts **downstairs and late**: it reads the `h'` factor at the
      unrestricted `h' : X'' ⟶ X'` over the open `f'⁻¹V` of `X'`, whose upstairs open is
      `h'⁻¹(f'⁻¹V) = f''⁻¹(h⁻¹V)`, descends to `h⁻¹V` by the relative Leray comparison for `f''`,
      and only then restricts to `W`. The `ψ` chain restricts **upstairs and early**: its 089W
      factor is already at `h'.resLE (f'⁻¹V) (f''⁻¹W)`, upstairs open `f''⁻¹W`. Commuting the one
      into the other is the compatibility of the relative Leray comparison for `f''` with
      shrinking the open of `Y''` from `h⁻¹V` to `W`.

      The **absolute** form of that compatibility is available and unconditional:
      `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_restrict`
   (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean:439`),
      at `f := f''` and the opens `W ≤ h⁻¹V` of `Y''`, with no
      hypothesis on the morphism, the opens or the degree. Its **relative** form — the same
      statement for `lerayCompositeComparison i p V`, where the target's second factor is
      `preimageSections p V` read over `Γ(V, 𝒪_{Y'})` rather than `sectionsOverOpen Y'' (h⁻¹V)`
      read over `Γ(h⁻¹V, 𝒪_{Y''})`, so the open being shrunk is the **source** open of a
      preimage-sections functor and not the base open `V` — is
      `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource`
      (`LerayCompositeRestrictSource.lean`); see the paragraphs below for what it costs.

      Two things that are **not** that brick. Restricting `V` itself
      in `Y'` — the literal transliteration of `lerayComparison_restrict` to
      `lerayCompositeComparison` — is the wrong statement: `W` is an open of `Y''` and is not
      `h⁻¹(V')` for any open `V'` of `Y'`. And `lerayComparison_restrict` applied to `h'` is also
      the wrong statement: it would need an open `U ≤ f'⁻¹V` of `X'` with `h'⁻¹U = f''⁻¹W`, and
      `f''⁻¹W` is not the preimage of any open of `X'`. The shape to build is the one
      `EdgeCompatPreimageRestrictSource.lean` already uses for the **edge morphism** —
      `Stacks.EdgeCompat.preimageSectionsRestrictSource`, the source open of `preimageSections`
      shrunk by
      `Functor.whiskerRight (sectionsOverOpenRestrictLE _ hW) (preimageRestrictScalars _ _)`
      — transplanted to the Leray comparison. That file is the template, and as there the content
      is that the two sides name different right derived functors with different units.

      *Most of that cost is already paid.*
      `EdgeCompatPreimageRestrictSource.lean` builds exactly the source-open shrink, at an
      arbitrary `f : X ⟶ Y` of ringed spaces, an open `V` of `Y` and `hW : W ≤ f⁻¹V` with `W` an
      open of `X`, with nothing assumed of any of them:
      `Stacks.EdgeCompat.preimageSectionsRestrictSource` (degreewise),
      `…preimageSectionsRestrictSourceCompUnit` with
      `…isRightDerivedFunctor_preimageSectionsRestrictSourceCompUnit` (one application of
      `…HomologyComparison.exactPostcomposeUnit`), and the derived transformation
      `…preimageSectionsRestrictSourceModelComparison` with its `…_fac_app`. At `f := h` those
      are the restriction from `preimageSections h V` down to sections over `W` read over
      `Γ(V, 𝒪_{Y'})` — the very transformation the brick's left-hand side must whisker onto
      `lerayCompositeComparison f'' h V`. So the brick's **left-hand side** needs no new
      `CompUnit`, no new instance and no new `rightDerivedDesc`.

      ***The brick. Unlike its left-hand side, its right-hand side does need a new
      `rightDerivedDesc`; see below.***
      `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource`
      (`LerayCompositeRestrictSource.lean`) is the compatibility of the relative Leray comparison
      with shrinking the open of the middle space from `p⁻¹V` down to `W`, for arbitrary
      `i : Z ⟶ X` and `p : X ⟶ Y` of ringed spaces, an arbitrary open `V` of `Y` and an arbitrary
      open `W ≤ p⁻¹V` of `X`:

      > `lerayCompositeComparison i p V`, then `Ri_*` of `preimageSectionsModelComparison p V`
      > followed by `preimageSectionsRestrictSourceModelComparison p V hW`, is
      > `derivedPreimageSectionsCompRestrictSource i p V hW` followed by `lerayComparison i W`
      > whiskered by `res_{W ≤ p⁻¹V} ⋙ res_{p^♯}`.

      Nothing is assumed of `i`, of `p`, of `V` or of `W`; in particular nothing of `h`, and the
      only inverse taken anywhere is the one inside `lerayComparison_ext`.

      The crossing the brick drags in is the following: the source of
      `preimageSectionsRestrictSourceModelComparison p V hW` is the **second** model
      `derivedSectionsOverOpen X (p⁻¹V) ⋙ (preimageRestrictScalars p V).mapDerivedCategory`,
      while the target of `lerayCompositeComparison i p V` carries the **total** right derived
      functor `derivedPreimageSections p V`, and
      `Stacks.EdgeCompat.preimageSectionsModelComparison` (`EdgeCompatPreimageRestrict.lean`) is
      what crosses them.

      *What the right-hand side costs.* The other order needs a transformation out of the
      **total** right derived functor `RΓ((p ∘ i)⁻¹V, -)` landing in
      `RΓ(i⁻¹W, -) ⋙ res.mapDerivedCategory`, and no existing declaration inhabits that type.
      `preimageSectionsRestrictSource (i ≫ p) V` at the
      smaller open `i⁻¹W` is **not** it: its target reads the scalars as
      `res_{i⁻¹W ≤ (i≫p)⁻¹V} ⋙ res_{(i≫p)^♯}`, while `lerayComparison i W` whiskered by scalars
      forces `res_{i^♯ at W} ⋙ res_{W ≤ p⁻¹V} ⋙ res_{p^♯}`. The two are restriction of scalars
      along the **same** ring map `Γ(V, 𝒪_{Y}) ⟶ Γ(i⁻¹W, 𝒪_{Z})` — a composite of two
      `ModuleCat.restrictScalars` is `restrictScalars` of the composite by `rfl`, and
      `opensMap (i ≫ p) = opensMap p ⋙ opensMap i` and
      `RingedSpaceModuleAdjunction.structureSheafHom_comp` are `rfl` — but the two ring maps
      themselves are **not** equal by `rfl`, the remaining content being the
      naturality of `structureSheafHom i` along `W ≤ p⁻¹V`. So matching the two spellings would
      mean transporting along an equality of functors, i.e. `eqToHom` through the chase.

      *What avoids that, and is why the cost is three declarations rather than a refactor.*
      `preimageSections (i ≫ p) V` **is** `i_* ⋙ preimageSections p V` on the nose
      (`preimageSectionsPushforwardIso` is `Iso.refl`), and `i_* ⋙ sectionsOverOpen X W` **is**
      `preimageSections i W` on the nose (`pushforwardPreimageSectionsIso`). So
      `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompRestrictSource` —
      `preimageSectionsRestrictSource p V hW` whiskered on the **left** by `i_*` — has both its
      source and its target the intended functors definitionally, with the scalars read through
      `Γ(W, 𝒪_{X})` from the start. Both that definition and
      `…HomologyComparison.exactPostcomposeUnit` at the pair
      `(preimageSections i W, res_{W ≤ p⁻¹V} ⋙ res_{p^♯})` elaborate with no ascription and no
      transport. The new declarations are then
      `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompRestrictSourceUnit`,
      `…derivedPreimageSectionsCompRestrictSource` and its `…_fac_app` (with the `…_fac_app_comp`
      form a rewrite uses), and the identity itself is `lerayComparison_ext` on the composite
      with the three degreewise helpers
      `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayRestrictSections.lean`
      carries for the absolute
      case, one for one.

      *One elaboration pitfall.* Moving the two model comparisons past the image of the
      pushforward unit by `rw` fails — `preimageRestrictScalars` is keyed on the ascribed
      spelling of its source ring, so the motive `rw` builds for the **second** naturality square
      is not type-correct at `implicit` transparency. The private `glue_two_naturalities` of
      `LerayCompositeRestrictSource.lean` performs the same shuffle at variables, which is the
      workaround `derivedHomologyComparison_preimageSectionsModelComparison` also uses for
      `CategoryTheory.Category.comp_id`.

      *Where 2b can live.* `BaseChangeSectionsTail.lean` **cannot** host it: from this file
      `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`,
      `Stacks.EdgeCompat.derivedHomologyComparison_derivedPreimageSections_comp_restrictSource`
      (step 1), `…homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite` (step 2a) and
      `…AffineComparison.cohomologyIsoPushforward_hom_eq` are all `unknownIdentifier` — the
      closure is 1,652 modules and none of the four is in it. A file importing
      `BaseChangeSectionsTail`, `EdgeCompatPreimageRestrictSource`, `TopDegreeCrossingSections`,
      `AffineCohomologyComparison/UnboundedModel` and
      `DerivedPushforward/BaseChangeComparisonSectionsHomology` has all four, at 1,666 modules.
      And the 089W match itself needs only 341 modules, which is why it sits beside 089W's
      unbounded reading rather than in `TopDegreeBaseChange/`.

      ***The six remaining dictionary pieces are all available, and five of the six need nothing
      further:***

      * `openSectionsModuleIso` is `AlgebraicGeometry.openSectionsModuleIso`
        (`Modules/RestrictOpenSections.lean:157`), with `…_hom_apply` (:169, `rfl`) and — the one
        declaration anywhere naming it together with
        `Stacks.Cohomology.AffineBase.moduleGlobalSections` —
        `openSectionsModuleIso_hom_naturality` in this file. There is **no** `_inv` lemma
        and none is wanted: the ψ side's one inverted use, inside
        `psi_side_eq_sections_unit_comp_tail`, takes `inv_comp_of_comp_hom` of the
        `hom` naturality. *What is absent is not on 2b's path.* Nothing names
        `openSectionsModuleIso` together with `…DerivedSectionsLeray.sectionsOverOpen`,
        `sectionsOnImageTopNatIso` or `openSectionsImageTopIso`; its sections-model twin
        `…TopDegreeBaseChange.openSectionsImageTopIso` (`DerivedSectionsModelCrossing.lean:155`) is
        a **different object with the same `rfl` body** — both are the sheaf's restriction along
        `eqToHom (Scheme.Opens.ι_image_top _).symm` — and the identification of the two is
        undeclared. It is not owed here, because `psi_side_eq_sections_unit_comp_tail` has already
        cancelled `openSectionsModuleIso` against the head; it survives in `T` only as the leading
        factor the γ⁺ side's `ξ.val.app (op V)` is matched against, which that theorem performs.
      * `AlgebraicGeometry.Scheme.Opens.topIso` is Mathlib's, and all three of its bridges to the
        scalars are available: `…TopDegreeBaseChange.app_comp_topIso_inv` and `…_hom`
        (`TopDegreeSectionsModelCrossing.lean:135,146`), `…appLE_eq_comp_topIso`
        (`BaseChangeSectionsBijection.lean:505`), and `topIso_symm_ringEquiv_eq` in this file for
        the `rfl` crossing of its two spellings. Nothing is owed.

      * [Stacks, Tag 01XK] over `V` is `…TopDegreeBaseChange.affineOpenCohomologyIsoSections`
        (`AffineOpenSectionsCohomology.lean:113`) and `…affineOpenCohomologyIsoSectionsOf`
        (`SourceSectionsNormalisation.lean:93`), both over an affine `V` with no hypothesis on the
        base, and its **sections-model** reading is
        `Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`
        (`EdgeCompatSectionsOverOpen.lean:419`). Nothing is owed. *Three duplicates:* 01XK
        itself is in the library three times over — the tagged
        `Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward`
        (`AffineCohomologyVanishing/AffineBase.lean:264`), the tagged
        `…AffineBase.cohomologyIsoSectionsRightDerivedPushforward`
        (`Cohomology/AffineBase.lean:194`, at the `sectionsFunctor _ ⊤` spelling of the same
        statement), and the **untagged** `Stacks.AlgebraicGeometry.HigherDirectImageQcoh`
        `.cohomologyIsoGlobalSectionsRightDerivedPushforward`
        (`HigherDirectImageQcqs/AffineBaseSections.lean:326`), whose statement is the first's
        verbatim.
      * `Stacks.DerivedIndexing.rightDerivedIso` (`Homology/DerivedIndexing/Basic.lean:474`) has
        its crossing into the sections model twice — in general as
        `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp`
        `_rightDerivedIso`
        (`StacksFrontier/Algebra/Homology/DerivedCategory/SingleRightDerivedViaPlus.lean:282`), and
        at the direct image over an
        open as `…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map`
        `_homologyFunctorDerivedPushforwardIso_hom_eq` (`TopDegreeCrossingSections.lean:111`) — and
        its ℕ-versus-ℤ bridge at 01XK over `V` is `…affineOpenCohomologyNatIso`
        (`AffineOpenCohomologyIndexing.lean:105`), whose body is exactly this factor. Nothing is
        owed. (`…TopDegreeBaseChange.restrictScalarsRightDerivedIso` does **not** exist; the
        declaration is `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso`,
        `AffineCohomologyComparison/Basic.lean:170`, and only its naturality lemma sits in the
        `TopDegreeBaseChange` namespace.)
      * `topDegreeFunctorObjIso…` is exactly two declarations, both in
        `BaseChangeSectionsBijection.lean`: `…topDegreeFunctorObjIsoCohomologyUpstairs` (:625) and
        `…topDegreeFunctorObjIsoTargetSections` (:683), the second being the first followed by a
        scalars transport and 01XK over `W`. Neither has a sections-model reading, and that
        reading is what the **last two** factors of `T` will need — it is not part of 2b(B).
      * `ModuleCat.restrictScalarsCongr` is Mathlib's: zero declarations of that name exist in
        either tree. Nothing is owed.

      ***2b(B) — the ψ side's 089W factor against step 2a's two leading factors — does not close
      by the direct route, because that route needs a hypothesis on `h` that the source lacks.***
      Three facts decide it.

      1. *The tail's 089W is at a `resLE`, and it cannot be weakened to a `∣_`.*
         `IsAffineHom (h'.resLE (f'⁻¹V) (f''⁻¹W))` holds by
         `…TopDegreeBaseChange.isAffineHom_resLE_of_isPullback`
         (`AffineOpenCohomologyPullback.lean:109`) because the restricted square's bottom edge
         `h ∣ : W ⟶ V` is a morphism of **affine schemes** — the affineness comes from `V` and `W`
         being affine and from nothing else. With that very instance in scope,
         **`IsAffineHom (h' ∣_ (f'⁻¹V))` is not synthesisable**; and it cannot be, since
         `h' ∣_ (f'⁻¹V)` is a base change of `h` along `f'⁻¹V ↪ X' ⟶ Y'`, so at `f' = 𝟙` it *is*
         `h`, on which the situation places no hypothesis at all. Therefore
         `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen` — whose **first
         hypothesis is exactly `IsAffineHom (f ∣_ V)`** — **cannot be applied at `(h', f'⁻¹V)`**.
         The ends-transport is at a `∣_`, the tail meets 089W at a `resLE`, and the two are not
         one instantiation. Like the other direct routes, this one would need a hypothesis on `h`.
      2. *What is available instead, and it is unconditional.*
         `AlgebraicGeometry.Scheme.Hom.resLE f U V e` **is** `X.homOfLE e ≫ f ∣_ U` by definition
         (printed), and `Stacks.AlgebraicGeometry.RestrictionSections.resLE_toShHom`
         (`Duality/ResLEUnitSections.lean:103`) records that on the underlying morphisms of ringed
         spaces by `rfl`. So the tail's 089W morphism factors through an open immersion, and
         `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp`
   (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayCompositeSections.lean:335`)
         — the Leray comparison of a **composite**, with no
         hypothesis on either factor — applies at the pair
         `((f''⁻¹W ↪ h'⁻¹(f'⁻¹V)), h' ∣_ (f'⁻¹V))` over `⊤` of `(f'⁻¹V : Scheme)` **with its
         source displayed at the `resLE` spelling and no transport anywhere**: the statement so
         written is closed by `lerayComparison_comp` itself. Its right-hand side is
         the relative Leray comparison for the open immersion — which is the upstairs shrink from
         `h'⁻¹(f'⁻¹V) = f''⁻¹(h⁻¹V)` down to `f''⁻¹W` — followed by
         `lerayComparison (h' ∣_ (f'⁻¹V)) ⊤`, and that second factor is what
         `…TopDegreeBaseChange.openSubschemeSectionsComparison_comp_lerayComparison_eq` crosses to
         `lerayComparison h' (f'⁻¹V)`, which is step 2a's second leading factor. **No affineness
         enters that chain at all**: the affineness of the `resLE` is confined to the
         `CategoryTheory.Functor.singleCollapse` factor, which
         `…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` hands in as the
         variable `c` with its retraction `hc`.
      3. ***What that leaves: the γ⁺-route crossing at an arbitrary open, with its derived
         packaging.*** The two facts in point 2 name `lerayComparison (h' ∣_ (f'⁻¹V)) ⊤` in
         **incompatible whiskerings** — on the left by `derivedPushforward` of the open immersion
         in the first, on the left by
         `(openSubschemeRestriction h' (f'⁻¹V)).mapDerivedCategory` and on the right by
         `res_{topIso}` in the second — so they do not compose, and no reassociation makes them.
         What makes them compose is the γ⁺-route open-subscheme crossing of
         `LerayOpenSubschemeSections.lean` at an **arbitrary** open `U ≤ f⁻¹V` in place of
         `f⁻¹V` itself, with its derived packaging:

         * `…TopDegreeBaseChange.appLE_comp_topIso_inv_hom`
           (`LerayOpenSubschemeSectionsLE.lean`): the two routes from the functions on `V` to the
           functions on the open subscheme `U` agree, as ring homomorphisms. At `U = f⁻¹V` it is
           `…app_comp_topIso_inv_hom`. **It is Mathlib's `AlgebraicGeometry.arrowResLEAppIso`,
           which the library also repackages twice** — as
           `Stacks.Morphisms.appTop_resLE` and `…topIso_symm_hom_comp_appTop_resLE`
           (`AlgebraicGeometry/Morphisms/FiniteStratificationInvariant.lean:79,88`) and as
           `Stacks.AlgebraicGeometry.Slicing.resLE_appTop_topIso`
           (`AlgebraicGeometry/Groupoids/Slicing/FlatBaseChangeOnIntersection.lean:189`). It is
           stated here rather than imported: both of those sit in the Fitting-stratification and
           flat-descent subtrees, and only the ring-homomorphism form is what
           `CategoryTheory.ModuleCat.restrictScalars` consumes.
         * `…TopDegreeBaseChange.preimageSectionsRestrictLE` and
           `…preimageSectionsOpenSubschemeLE`: the degreewise crossing at an arbitrary
           `U ≤ f⁻¹V`, with nothing assumed of `f`, of `V`, of `U` or of the module.
         * `…TopDegreeBaseChange.openSubschemeRestrictionOf` with its three exactness instances,
           `…openSubschemeDerivedTargetOf`, the two homotopy splittings,
           `…openSubschemeUnitOfNatTransUnit` with `…_comp`, the two units, the two
           `rightDerivedDesc`s `…openSubschemeSectionsComparisonLE` and
           `…openSubschemeLerayComparisonLE` with their factorizations, and
           `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_lerayComparison_eq`
           (`LerayOpenSubschemeDerivedLE.lean`) — **the compatibility of the Leray comparison of
           [Stacks, Tag 0D5W] with restriction to a smaller open subscheme**: the crossing of the
           source, followed by `lerayComparison (f.resLE V U e) ⊤` whiskered by the derived
           restriction and the derived restriction of scalars, is `lerayComparison f V` followed by
           the crossing out of its target. Nothing is assumed of `f`, of `V`, of `U` or of the
           module (axioms: `propext`, `Classical.choice`, `Quot.sound`).

         *Three remarks on this generalisation.* First, the γ⁺ half does **not** generalise as it
         stands. The four `rfl`s do hold at every open —
         `moduleRestriction X U ⋙ sectionsOverOpen (U : Scheme) ⊤` *is*
         `sectionsOverOpen X (U.ι ''ᵁ ⊤)` for every `U` — but at `U < f⁻¹V` the crossing is the
         **restriction of sections** from `f⁻¹V` to `U` and is **not invertible**, so
         `…openSubschemeUnitOfIsoUnit`, which takes an `Iso`, cannot be reused;
         `…openSubschemeUnitOfNatTransUnit` takes a plain transformation, which is all the
         universal property of `RΓ(f⁻¹V, -)` asks for. Second, the generalisation does **not** make
         the two facts of point 2 compose: it **supersedes** them. It relates
         `lerayComparison (f.resLE V U e) ⊤` to `lerayComparison f V` in one step, and neither
         `…DerivedSectionsLeray.lerayComparison_comp` nor
         `…openSubschemeSectionsComparison_comp_lerayComparison_eq` is used anywhere in the two new
         files. Third, no second descent out of `Rf_* ⋙ RΓ(V, -)` is needed: the `U = f⁻¹V` file
         reaches its compatibility in two steps, through `…openSubschemePushforwardComparison`,
         and the `LE` statement is proved in one, `lerayComparison_ext` applying directly because
         both of its sides come out of `RΓ(f⁻¹V, -)`.

         *No duplicate restriction functor is introduced.*
         `…TopDegreeBaseChange.openSubschemeRestriction f V` **is**
         `…openSubschemeRestrictionOf X (f ⁻¹ᵁ V)`, which `…openSubschemeRestriction_eq` records by
         `rfl`. The other `U = f⁻¹V` declarations are the `LE` ones at `e := le_rfl` only up
         to `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`, which is not `rfl`, so they
         are not literal instances.

         The **ψ** half does not generalise: `(f.resLE V U e)_*(F|_U)` is not
         `(f_* F)|_V` once `U < f⁻¹V`, so `…HigherDirectImage.modulePushforwardRestrictIso` has no
         analogue there and `…preimageSectionsOpenSubschemePushforwardIso` with
         `…preimageSectionsOpenSubschemeIso_eq` stay special to `U = f⁻¹V`.

         ***2b(B) still does not close, though both of its bricks are proved — neither of them
         needing a hypothesis on `h`.*** With the crossing in hand the **Leray factor** of the
         match is settled; of the two further inputs, brick (ii) is performed (see its paragraph
         below) and brick (i) is performed as the general statement at a bare pair, in
         `Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`. What
         still blocks the match is the **instantiation** of brick (i) at the geometric pair, whose
         `θ` carries two factors brick (i)'s `hθ` has not; the paragraph "***The 2b(B) match
         does not follow from it***" below writes that gap out.

         (i) *The model crossings at the two ends.*
         `…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` instantiated at
         `h'.resLE (f'⁻¹V) (f''⁻¹W)` carries
         `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the two pairs on
         the **open subschemes** `(f'⁻¹V : Scheme)` and `(f''⁻¹W : Scheme)`, while 2a's statement
         is written at functors on `X'` and `Y'`. The compatibility of that crossing with
         restriction to an open subscheme is the **second half** of what is owed, the first half
         being the Leray compatibility above; no statement of the library names
         `singleCompDerivedCompHomologyIsoRightDerived` or `singleCompDerived` together with any
         of `topIso`, `Scheme.Opens`, `restrictFunctor`, `moduleRestriction`, `∣_`, `resLE`,
         `openSubscheme` or `imageTop`. The ends-transport
         `…AffineComparison.cohomologyIsoPushforwardOverOpen` is **not** a
         substitute and cannot be made one at a `resLE`: besides the unavailable
         `IsAffineHom (f ∣_ V)`, its third input is
         `AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`,
         `(f ∣_ V)_*(F|_{f⁻¹V}) ≅ (f_* F)|_V`, which has no analogue at `U < f⁻¹V` — the same
         obstruction that stops the ψ half.

         *The existing statements about this crossing.* Nothing in the library names
         `singleCompDerivedCompHomologyIsoRightDerived` or `singleCompDerived` together with the
         restriction vocabulary above, with the **pullback** vocabulary (`derivedPullback`,
         `openImmersion`, `extensionByZero`, `ofRestrict`, `localization`), or with the tags
         `089W`, `01E5`, `08FE` or `0D5W` (except one docstring line of
      `StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismExtend.lean`).
         Exactly five declarations carry the brick's name — the def
      (`StacksFrontier/Algebra/Homology/DerivedCategory/DerivedFunctorSingleRightDerived.lean:192`),
         `…_hom_app_res` (:221),
         `…_hom_app_comp_rightDerivedIso` and `…_hom_app`
         (`StacksFrontier/Algebra/Homology/DerivedCategory/SingleRightDerivedViaPlus.lean:282,326`)
         and `…_hom_app_eq`
         (`TopDegreeCrossingSingleModel.lean:89`) — and every one of them has a
         **single** `w`. The two two-functor statements that exist are both **post**composition,
         `w` being the inner factor of `F ⋙ G`:
         `…AffineComparison.singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`
         (`AffineCohomologyComparison/UnboundedModel.lean:257`) and its 01XK twin
         `Stacks.EdgeCompat.Mirror.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
         (`EdgeCompatCollapseMirror.lean:323`). (The `E : D ⥤ A` of the latter is **not** a
         precomposition: it appears only as `E.obj X` and is never pushed into a derived functor.)

         ***The mathematics the brick needs is available.*** Precomposition by the restriction asks
         for `(r ⋙ w).rightDerived n ≅ r ⋙ w.rightDerived n`, i.e. for `r` to carry an injective
         resolution to an injective resolution. All three inputs exist and are public:

         * `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`
           (`CategoryTheory/Sites/Cohomology/HigherDirectImage/CompositeRightDerivedFunctors.lean`
           `:172`) is exactly `(L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n` for `L` additive,
           exact and `L.PreservesInjectiveObjects` and `G` merely additive, through `mapInjRes`
           (:126); with the component lemmas `compRightDerivedNatIso_hom_app`,
           `…_hom_app_mapInjRes`, `…_hom_app_eq` and `…_hom_app_eq_of_desc`
           (`…/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeComparisonOnResolutions.lean`,
           lines 165, 322, 249, 342), the
           composition law `compRightDerivedNatIso_comp`
           (
        `…/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeRightDerivedTransitivity.lean:121`),
           and the two-engine
           transitivity `rightDerivedCompIso_comp_compRightDerivedNatIso_app`
      (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/TwoEngineTransitivity.lean:167`).
           **Mathlib has nothing of the kind**
           — no Grothendieck spectral sequence, no composition result for `Functor.rightDerived`
           — so this is the library's own.
         * `Stacks.Cohomology.HigherDirectImage.moduleRestriction_preservesInjectiveObjects`
 (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationIsomorphisms.lean:131`),
           carrying `@[stacks 01E1]`, is
           an **instance**: restriction of sheaves of modules to an open subspace preserves
           injectives, by the adjunction `j_! ⊣ j^*` with `j_!` preserving monomorphisms. Nothing
           is assumed of the space or the open. Its `OfLE` sibling is at
     `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationNaturality.lean:224`,
           and that one's own docstring says
           it exists in order to feed `compRightDerivedNatIso`.
         * `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` is **Mathlib's**
           (`Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:111`):
           `singleFunctor C₁ n ⋙ F.mapDerivedCategory ≅ F ⋙ singleFunctor C₂ n`.

         *Elaboration facts.* With one new instance,
         `(openSubschemeRestrictionOf X U).PreservesInjectiveObjects` by `inferInstanceAs` from
         `moduleRestriction_preservesInjectiveObjects` — **A** — all of the following
         elaborate in a file importing `LerayOpenSubschemeDerivedLE` and
         `HigherDirectImage/LocalizationIsomorphisms`: **B**, `compRightDerivedNatIso` at the pair
         `(openSubschemeRestrictionOf X U, …DerivedSectionsLeray.sectionsOverOpen (U : Scheme) ⊤)`;
         **C**, the degreewise composite of that pair *is*
         `sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)` by `rfl`; **D**,
         `mapDerivedCategorySingleFunctor` at `openSubschemeRestrictionOf X U`. One caveat:
         `Stacks.Cohomology.AffineBase.moduleGlobalSections (U : Scheme)` has **no** `Additive`
         instance findable at that spelling — `(… ⋙ moduleGlobalSections ↑U).Additive` and
         `(moduleGlobalSections ↑U).Additive` both report `failed to synthesize`, while the `rfl`-
         equal `sectionsOverOpen (U : Scheme).toRingedSpace ⊤` has one — so write the second
         spelling, or pass the instance through `@` and `inferInstanceAs`. And
         `Scheme.Modules.restrictFunctor` has **no** `PreservesInjectiveObjects` instance: only the
         ringed-space `moduleRestriction` does, which is why the derived machinery is written at
         that spelling.

         *So what brick (i) owes is the chase, not the mathematics* (it is performed; see the
         paragraph "***Brick (i) is proved***" below): the statement that the
         crossing at `(r ⋙ w, r.mapDerivedCategory ⋙ Rw)` corresponds, under
         `compRightDerivedNatIso`, to the crossing at `(w, Rw)` evaluated at `r(-)` — fully
         parametric in the two right-derived data with a coherence `hθ` for the transformation
         `RLw ⟶ r.mapDerivedCategory ⋙ Rw`, exactly as the two POSTcomposition mirrors above are
         written. `EdgeCompatCollapseMirror.lean` is the template one-for-one. The content is that
         the two sides read **different** injective resolutions of `r.obj X` — the chosen one, and
         `r` applied to the chosen resolution of `X` — so the chase goes through
         `InjectiveResolution.desc` and `compRightDerivedNatIso_hom_app_eq_of_desc`. Nothing in
         that needs a hypothesis on `h`, on `f'`, on `V` or on `W`.

         ***Most of the chase is already performed, in a third vocabulary.*** The precomposition
         comparison of this bullet exists in the library twice over, and the second copy carries
         the chase:

         * `Stacks.Cohomology.RightDerivedEdge.edge P Q n`
           (`Algebra/Homology/RightDerivedEdge.lean:209`) is the **edge morphism** of the pair,
           `P ⋙ Q.rightDerived n ⟶ (P ⋙ Q).rightDerived n`, for `P` additive and preserving
           injective objects, with **no** exactness hypothesis on `P`, built out of
           `…RightDerivedEdge.resolutionComparison` (:163) — which maps the chosen injective
           resolution of `P X` **into** `P` applied to the chosen resolution of `X`, the opposite
           direction to `mapInjRes` and `InjectiveResolution.desc` — and characterised through an
           arbitrary triple by `…RightDerivedEdge.edge_app_eq` (:256).
         * `Stacks.DerivedIndexing.edge_comp_rightDerivedIsoRes`
           (`Homology/DerivedIndexing/Composite.lean:587`) is **the residue of brick (i)**:
           the edge morphism, read through `rightDerivedIsoRes`, is the degree-`i` homology of `Q`
           applied to the extension by zero of the comparison of resolutions
           (`…DerivedIndexing.extendResolutionComparison`, :570). Nothing is assumed of `P` beyond
           additivity and preservation of injectives.
         * `Stacks.DerivedIndexing.edge_comp_rightDerivedIso` (:1314) and
           `…rightDerivedPlusEdge_comp_rightDerivedPlusIsoRes` (:1273) are the **derived half** in
           the `rightDerivedPlus` indexing: the edge morphism *is* the degreewise comparison built
           from `R(Q ∘ P) ≅ RQ ∘ RP` (`…rightDerivedPlusCompIso`, :324), whose unit factor
           `…rightDerivedPlusUnitSingle` (:332) is the `D⁺` counterpart of
           `mapDerivedCategorySingleFunctor`; and `…singleIsoResPlusQh_hom_app_comp`
           `_extendResolutionComparisonPlus` (:1006) is the `D⁺` counterpart of the `D(A)`-identity
           the chase needs, with `…resUnit_app_comp_quotient_map_extendResolutionComparison` (:968)
           its degreewise content and `…rightDerivedPlusUnitSingle_app_comp_map_singleIsoResPlusQh`
           (:1041) the key equation it feeds.

         *Why these are easy to miss.* `Homology/DerivedIndexing/Composite.lean` names neither
         `singleCompDerivedCompHomologyIsoRightDerived`/`singleCompDerived` nor
         `compRightDerivedNatIso`: its subject is the *edge morphism of a composite*, filed under
         [Stacks, Tag 015M] and [Stacks, Tag 05T2], and it speaks of `rightDerivedPlus` rather than
         of an unbounded `Rw`.

         ***The key that makes it available.*** The two families name each other nowhere else, so
         neither can be used in place of the other without the following.
         `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_inv_eq_edge`
         (`Topology/Sheaves/Cohomology/DerivedFunctors/CompositeEdgeComparison.lean:142`) is the
         identification: **where both exist, the edge morphism is the inverse of
         `compRightDerivedNatIso`**, with `…compRightDerivedNatIso_inv_app_eq_edge_app` (:122) and
         the two cancellations `…edge_app_comp_compRightDerivedNatIso_hom_app` (:93) and
         `…compRightDerivedNatIso_hom_app_comp_edge_app` (:132). Nothing is assumed beyond what the
         two constructions already carry (axioms: `propext`, `Classical.choice`, `Quot.sound`). The
         proof is the one-variable transport
         `…DerivedCompTransport.isoRightDerivedObj_hom_eq` between the two injective resolutions of
         `P X` the two families choose, along `resolutionComparison`, which descends the identity
         of `P X` by `…RightDerivedEdge.ι_f_zero_comp_resolutionComparison` together with
         `…DerivedCompTransport.mapInjRes_ι_f_zero`; no homotopy uniqueness of descents is used,
         and `compRightDerivedNatIso_hom_app_eq_of_desc` is not needed. The two constructions
         `edge` and `compRightDerivedNatIso` are duplicates; both are kept, and this lemma joins
         them.

         ***Brick (i) is proved. The reduction is kept below because it describes the proof.***
         Writing `scd F` for
         `…DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F`, `cRD` for
         `compRightDerivedNatIso r w n`, `u F` for `…DerivedFunctor.resCompUnitIso F`, `fh` for
         `DerivedCategory.homologyFunctorFactorsh`, `mdcf` for
         `CategoryTheory.Functor.mapDerivedCategoryFactorsh` and `mdcSF` for
         `…mapDerivedCategorySingleFunctor`, the statement to prove — which **elaborates**
         as written, in a file importing `DerivedFunctorSingleRightDerived`,
         `CompositeComparisonOnResolutions` and `Homology/DerivedIndexing/Composite` — is:

         > `(scd (r ⋙ w) Rrw αrw hresC n).hom.app X ≫ cRD.hom.app X`
         > `= Hⁿ(θ.app (X[0])) ≫ Hⁿ(Rw.map (mdcSF.hom.app X))`
         > `≫ (scd w Rw αw hresA n).hom.app (r X)`.

         Reading both sides by `…singleCompDerivedCompHomologyIsoRightDerived_hom_app_res`, taking
         `cRD.hom.app X` to be the inverse of the edge morphism by the new identification, and
         transposing the residue with `edge_comp_rightDerivedIsoRes` and the naturality of `fh`,
         the whole statement reduces — with no inverse taken anywhere except the two units and the
         edge morphism, all three invertible — to **two** things and nothing else:

         1. *the `D(A)`-identity* — **performed**, as
            `Stacks.Cohomology.DerivedCompTransport.mapDerivedCategory_map_singleIsoResCompQh_hom`
            `_app_comp_factorsh`
    (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`)
            —
            `r.mapDerivedCategory.map ((singleIsoResCompQh (A := C)).hom.app X)`
            `≫ mdcf.hom.app (resH.obj X) = mdcSF.hom.app X ≫ (singleIsoResCompQh (A := A)).hom.app`
            `(r.obj X) ≫ Qh.map (quotient.map (extendResolutionComparison r X))`. This is the
            `mapDerivedCategory` spelling of the `D⁺` statement
            `…DerivedIndexing.singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus`, so
            what it owed was the translation of `mapSingleFunctorCompQhIso` into `mdcSF` and of
            `mapHomotopyCategoryPlus` into `mapDerivedCategory` through `mdcf`;
         2. *the derived half* — **performed**, as
            `Stacks.Cohomology.DerivedCompTransport.map_singleIsoResCompQh_hom_app_comp`
            `_resCompUnitIso_inv_app` (same file) — which is `EdgeCompatCollapseMirror.lean`'s
            shuffle one-for-one: the
            naturality of `θ` at `(singleIsoResCompQh).hom.app X`, the coherence `hθ` at
            `resH.obj X` solved for `(u (r ⋙ w)).inv.app X`, and the naturality of `αw` at
            `quotient.map (extendResolutionComparison r X)`.

         *The one input the derived half needs beyond the template* is
         `Stacks.Cohomology.DerivedCompTransport.isIso_unit_app_mapHomotopyCategory_resH_obj`. The
         shuffle inverts the unit of `Rw` at `r`
         applied to the chosen extended resolution, i.e. needs
         `IsIso (αw.app ((r.mapHomotopyCategory (ComplexShape.up ℤ)).obj (resH.obj X)))`. This
         holds by
         `Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective` at
         the complex `(r.mapHomologicalComplex (ComplexShape.up ℤ)).obj`
         `(injectiveResolution X).cochainComplex` — which is `r.mapHomotopyCategory`'s value on
         `resH.obj X` by **`rfl`** — and that complex is K-injective by
         `CochainComplex.isKInjective_of_iso` along
         `…DerivedIndexing.mapExtendIso r ComplexShape.embeddingUpNat (injectiveResolution X)`
         `.cocomplex` from `CochainComplex.isKInjective_of_injective _ 0` at
         `(…CompositeRightDerived.mapInjRes r (injectiveResolution X)).cochainComplex`. **One
         elaboration caveat:** the `IsKInjective` instance has to be restated at the *unfolded*
         spelling
         `((r.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex)`
         `.extend ComplexShape.embeddingUpNat` before `isKInjective_of_iso` will find it —
         instance search does not unfold `mapInjRes`, and keyed on the `mapInjRes` spelling the
         synthesis times out at 20,000 heartbeats. Restating it by `haveI … := h₁` in term mode
         crosses the two spellings.

         *Three facts about the translation in point 1.* The
         translation goes through `(DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X`, and
         `rfl` on its closed form is **inconclusive**, reporting
         `HomologicalComplexUpToQuasiIso.quotientCompQhIso` as `not exposed`; `simp` and `dsimp`
         through `SingleFunctors.postcompIsoOfIso` fail on a target that is **not type-correct at
         `implicit` transparency**, which is the wall Mathlib itself papers over with
         `backward.isDefEq.respectTransparency false` inside that very definition. The cure needs
         neither: the closed form is **proved**, as
         `Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app`
         (`Homology/DerivedIndexing/SingleDegreeUnit.lean:136`), proved by `show … ≫ 𝟙 _ = _`
         followed by `Category.comp_id`. Beside it, Mathlib's
         `CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor`
         `_hom_app` and `…mapDerivedCategoryFactorsh_hom_app` read `mdcSF` and `mdcf` on complexes,
         and `CategoryTheory.Functor.mapCochainComplexSingleFunctor` **is**
         `HomologicalComplex.singleMapHomologicalComplex` by definition — which is the comparison
         `…DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app` (:884) and
         `…ι_map_mapSingleFunctorCompQhIso_inv_app` (:915) are already stated at.

         ***Point 1 reduces further.*** On
         paper — not in Lean — point 1 is
         `…DerivedIndexing.resUnit_app_comp_quotient_map_extendResolutionComparison` together with
         the naturality of `mdcf.hom` at `resUnit.app X` and one **purely Mathlib-level**
         statement, call it (★★):

         > `r.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X)`
         > `≫ mdcf.hom.app ((HomotopyCategory.singleFunctor C 0).obj X)`
         > `= mdcSF.hom.app X ≫ (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app (r.obj X)`
         > `≫ Qh.map (quotient.map`
         > `((HomologicalComplex.singleMapHomologicalComplex r (ComplexShape.up ℤ) 0).inv.app X))`,

         whose `singleMapHomologicalComplex` factor is in exactly the direction
         `resUnit_app_comp_quotient_map_extendResolutionComparison` and
         `…DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app` already carry it. (★★)
         **elaborates**, and three further facts say how to prove it and how not
         to. The two `Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app` rewrites **do** fire,
         leaving both single-functor comparisons as components of
         `DerivedCategory.quotientCompQhIso`. `Qh.map`
         `((r.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _` is
         `DerivedCategory.Qh.map_id _`, which is the factor that must be absorbed from
         Mathlib's `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app`, the same absorption
         `EdgeCompatCollapseMirror.lean`'s `hcid` performs for
         `Functor.mapHomotopyCategoryCompIso`. But **`rw [Functor`**
         **`.mapDerivedCategoryFactorsh_hom_app]` is refused** on that goal, reporting a target
         that is *not type-correct at `implicit` transparency*: so that step has to be a term, by
         the `congrArg`/`Eq.trans`-at-variables discipline this file and
         `Homology/DerivedIndexing/Composite.lean` both follow. What then remains of (★★) is
         Mathlib's `…mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`
         against `DerivedCategory.quotientCompQhIso_inv_naturality` at
         `singleMapHomologicalComplex`, and nothing else is needed.

         ***Brick (i) is proved, along the reduction above.*** It is
         `Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp`
         `_compRightDerivedNatIso_hom`
         (`Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`), stated
         exactly as the display above writes it and with the same `hθ` the two POSTcomposition
         mirrors take, together with the four results it is assembled from —
         `…mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app_comp_factorsh` ((★★), purely
         Mathlib-level), `…mapDerivedCategory_map_singleIsoResCompQh_hom_app_comp_factorsh`
         (point 1), `…isIso_unit_app_mapHomotopyCategory_resH_obj` and
         `…map_singleIsoResCompQh_hom_app_comp_resCompUnitIso_inv_app` (point 2). Nothing is
         assumed of `w` beyond additivity, nothing of the object, nothing of `h`, of `f'`, of `V`
         or of `W`; no acyclicity, no boundedness and no homotopy uniqueness of descents occurs,
         and `compRightDerivedNatIso_hom_app_eq_of_desc` is not used (axioms: `propext`,
         `Classical.choice`, `Quot.sound` throughout). As noted above, the `factorsh` step is a
         term, and the `haveI` at the unfolded `extend` spelling avoids the `IsKInjective`
         heartbeat timeout.

         *Two variable-level shapes are duplicated.*
    `StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`'s
         private `inv_comp_square` is
         `EdgeCompatCollapseMirror.lean`'s private `inv_comp_of_comp_eq`, and the `hz` argument of
         its private `derived_left` does what that file's private `id_comp_of_eq_id` does. Both
         originals are `private`, so neither is usable from another module; both shapes belong in
         the leaf `CategoryTheory/CompositeCancellation.lean`, which exists for exactly this.

         ***The 2b(B) match does not follow from it.*** Brick (i) is the
         statement at a **bare** pair `(r, w)` with a `θ : R(r ⋙ w) ⟶ r.mapDerivedCategory ⋙ Rw`
         whose coherence `hθ` has three factors: the crossing
         `Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ w))` inverted under `Qh`, `αw` at
         `r.mapHomotopyCategory`, and `Rw` of `mapDerivedCategoryFactorsh` inverted. The `θ` the
         tail has at the geometric pair
         `(openSubschemeRestrictionOf X' U, …DerivedSectionsLeray.sectionsOverOpen (U : Scheme) ⊤)`
         is `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE`, whose unit
         `…openSubschemeSectionsUnitLE` is `…openSubschemeUnitOfNatTransUnit` and carries **two
         factors brick (i)'s `hθ` has not**: the degreewise crossing
         `…preimageSectionsOpenSubschemeLE` — which at `U < f⁻¹V` is the restriction of sections
         and is **not** invertible, which is why that family takes a plain transformation —
         and the derived restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso`,
         which `…openSubschemeDerivedTargetOf` carries as a third functor on the right. So the
         instantiation is not a substitution: what it needs is a `θ` and an `hθ` at the bare pair
         — a unit, its `IsRightDerivedFunctor` instance, a `Functor.rightDerivedDesc` and its
         `_fac_app`, the shape `LerayOpenSubschemeDerivedLE.lean` has — and then the composition
         of brick (i) at that pair with the `α` and scalars layers. The one instance it also needs,
         `(openSubschemeRestrictionOf X U).PreservesInjectiveObjects` by `inferInstanceAs` from
         `…HigherDirectImage.moduleRestriction_preservesInjectiveObjects`, is fact **A** above.

         So no `@[stacks 0EX3 "(c)"]` is placed, the match does not close and neither does the
         composite identity.

         *A duplicate.* The object-level form of `compRightDerivedNatIso` is proved a second time
         in the library, as `rightDerivedCompIso_of_preservesInjectiveObjects`
         (`AlgebraicGeometry/EtaleCohomology/NormalSepClosedConstantDirectImage.lean:553`), with
         its own `mapInjectiveResolution` (:546) — both **`private`**, so neither is usable from
         another module, and the public `compRightDerivedNatIso` subsumes both. A third family,
         `Stacks.RightDerivedComp.objIso` (`Homology/CompositeCollapse.lean:192`), is the same
         object-level statement again, public but not functorial.

         (ii) ***2a's second leading factor is not `lerayComparison h' (f'⁻¹V)`, and the
         identification it therefore needs is proved.*** By the statement of
         `…DerivedBaseChange.homology_map_derivedPushforwardComparisonSquare_eq_lerayComposite`,
         that factor is `(derivedPreimageSectionsCompIso h' S.f' V).hom.app M`, the inverse of the
         **relative** Leray comparison `…DerivedSectionsLeray.lerayCompositeComparison h' S.f' V`.
         *The direction matters* (see the occurrence at
 `…/Topology/Sheaves/Cohomology/DerivedPushforward/BaseChangeComparisonSectionsHomology.lean:187:14`
         ). It is
         `derivedPreimageSectionsCompIso i p V`, not `lerayCompositeComparison i p V`, that has
         type `Rh'_* ⋙ derivedPreimageSections f' V ≅ derivedPreimageSections (h' ≫ f') V`; the
         comparison itself runs
         `lerayCompositeComparison i p V : derivedPreimageSections (i ≫ p) V ⟶`
         `derivedPushforward i ⋙ derivedPreimageSections p V`
  (`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayCompositeSections.lean:125`),
         and the iso is literally
         `(asIso (lerayCompositeComparison i p V)).symm` (:370). Both are valued in
         `D(ModuleCat Γ(Y', V))`. The **absolute** `lerayComparison h' (f'⁻¹V)` — which is what the
         compatibility above and point 2 produce — has type
         `derivedPreimageSections h' (f'⁻¹V) ⟶ Rh'_* ⋙ derivedSectionsOverOpen X' (f'⁻¹V)`, valued
         in `D(ModuleCat Γ(X', f'⁻¹V))`: a different source, a different target and a different
         base ring. Step 2a's own paragraph above names the factor correctly ("the relative Leray
         comparison for `h'` over `f'⁻¹V` inverted
         (`…DerivedSectionsLeray.derivedPreimageSectionsCompIso`)"). So the match needs, in
         addition, the identification of
         `lerayCompositeComparison i p V` with `lerayComparison i (p⁻¹V)` whiskered by restriction
         of scalars along `p^♯` at `V` and crossed by
         `Stacks.EdgeCompat.preimageSectionsModelComparison` — `rightDerivedDesc`s out of the
         same degreewise functor with different units, of the shape of
         `LerayCompositeRestrictSource.lean` and `EdgeCompatPreimageRestrictSource.lean`. None of
         the other statements about the relative Leray comparison (the nine listed above and
         `…lerayCompositeComparison_restrictSource`) compares it with the absolute one.

         ***It is proved in `LerayCompositeAbsolute.lean`, with nothing assumed of `i`, of `p`
         or of `V`*** (axioms: `propext`, `Classical.choice`, `Quot.sound` throughout):

         * `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsCompModelUnit` with
           `…isRightDerivedFunctor_preimageSectionsCompModelUnit`: `RΓ(i⁻¹(p⁻¹V), -)` over
           `Γ(p⁻¹V, 𝒪_X)`, followed by restriction of scalars along `p^♯`, is a right derived
           functor of sections over `(p ∘ i)⁻¹V` read over `Γ(V, 𝒪_Y)`. One application of
           `…HomologyComparison.exactPostcomposeUnit` at the pair
           `(preimageSections i (p⁻¹V), res_{p^♯})`, with the K-injective resolutions on `Z`.
         * `…derivedPreimageSectionsCompModel` with `…_fac_app` and `…_fac_app_comp`: the
           `rightDerivedDesc` comparison of the two models.
         * `…lerayCompositeComparison_eq_lerayComparison`: **the relative Leray comparison,
           followed by the crossing of the two models of `RΓ(p⁻¹V, -)`, is the crossing of the two
           models of `RΓ((p ∘ i)⁻¹V, -)` followed by `lerayComparison i (p⁻¹V)` whiskered by
           restriction of scalars along `p^♯`.**
         * `…derivedPreimageSectionsCompIso_hom_comp_lerayComparison`: the same solved for the
           inverse, which is the form a chase meets it in, 2a carrying
           `derivedPreimageSectionsCompIso`. The only invertibility used is the unconditional
         `isIso_lerayCompositeComparison`; neither model comparison is inverted anywhere, and
         no `isIso` of either is declared — none is needed and none exists in the library.

         *Why one `rightDerivedDesc` suffices.* At `W = p⁻¹V` **no degreewise
         comparison is needed at all**: `preimageSections (i ≫ p) V` *is*
         `preimageSections i (p⁻¹V) ⋙ preimageRestrictScalars p V` by `rfl`, by three
         identifications that are each `Iso.refl` — `preimageSectionsPushforwardIso`, the
         definition of `preimageSections`, and `pushforwardPreimageSectionsIso`. So the two ring
         maps `Γ(V, 𝒪_Y) ⟶ Γ(i⁻¹p⁻¹V, 𝒪_Z)` are never compared, and the naturality of
         `structureSheafHom i` along `W ≤ p⁻¹V` that `LerayCompositeRestrictSource.lean` identifies
         as the obstruction at a strictly smaller `W` does not arise. `lerayCompositeComparison_
         restrictSource` at `hW := le_rfl` is **not** this statement and is not used: it carries
         `preimageSectionsRestrictSourceModelComparison` and a `sectionsRestrictScalars X le_rfl`
         factor, neither of which is an identity on the nose.

         *Two elaboration caveats.* The naturality square of
         `preimageSectionsModelComparison` writes its component at the composite spelling
         `(Qh ⋙ Ri_*).obj K` while the goal has `Ri_*(Qh K)`, so `rw` is refused and the shuffle is
         done at variables (`glue_naturality_fac`); and `Category.assoc` is refused on the
         left-associated last factor — the target is not type-correct at `implicit` transparency,
         `preimageRestrictScalars` being keyed on the ascribed spelling of its source ring — so
         that reassociation is at variables too (`glue_map_fac`). The final step of the degreewise
         comparison needs a bare `rfl` after `simp only [Functor.map_comp, Category.assoc]`: simp
         leaves the two sides printing identically and does not close them.

         This does not complete 2b: brick (i)'s instantiation is still missing, so the
         match does not close and neither does the composite identity.
3. *Then* `htail` on `…_of_tail`; only with that is the pure-tensor agreement unconditional.

Steps 1 and 2a are done, and every claim about them above cites the declaration that carries it.
Of step 2b, three pieces are done and each cites its declaration: the 089W match at global
sections; the compatibility of the relative Leray comparison with shrinking the open downstairs,
`Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_restrictSource`; and the two
**ends** of the passage from the open subscheme's global sections to the relative statement over
`f'⁻¹V`, `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforwardOverOpen` with its
transported equation; and of that passage's **middle** — the compatibility of the Leray comparison
of [Stacks, Tag 0D5W] with restriction to an open subscheme — the **crossing at the comparison's
degreewise source** is available, by both of the two routes the two sides of (c) present it in,
as `…TopDegreeBaseChange.preimageSectionsOpenSubschemeIso` and
`…preimageSectionsOpenSubschemePushforwardIso` (`LerayOpenSubschemeSections.lean`), with
`…restrictScalarsSquareIso` beside them, **and the two routes are proved equal**,
`…preimageSectionsOpenSubschemeIso_eq`. Of the middle's other two parts: the comparison of `Rf_*`
with `R(f ∣_ V)_*` across the restriction is [Stacks, Tag 08FE]
(`Stacks.Cohomology.derivedPushforwardRestrictIso` and its two instantiations, cited in the
paragraphs above), so only a spelling bridge from `modulePullback` to `moduleRestriction` is
needed there and no new construction; and the two `rightDerivedDesc`s, with the compatibility
itself, are proved —
`…TopDegreeBaseChange.openSubschemeSectionsComparison_comp_lerayComparison_eq`
(`LerayOpenSubschemeDerived.lean`), at a `∣_`, with nothing assumed of `f`, of `V` or of the
module. So 2b(i)'s middle is closed **at the `∣_` shape**.

*The six remaining pieces of 2b are available, and 2b's conclusion is still owed.*
`openSectionsModuleIso`, `topIso`, [Stacks, Tag 01XK] over `V`,
`Stacks.DerivedIndexing.rightDerivedIso`, both `topDegreeFunctorObjIso…`s and
`ModuleCat.restrictScalarsCongr` are all in the library, cited above, and five of the six need
nothing further. What remains owed is **2b's actual conclusion** — the match of the ψ side's 089W
factor against step 2a's two leading factors — and it does **not** go through
`cohomologyIsoPushforwardOverOpen`: `IsAffineHom (h' ∣_ (f'⁻¹V))` is not available and
would force a hypothesis on `h`, while the tail's 089W sits at the `resLE`
`h'.resLE (f'⁻¹V) (f''⁻¹W)`, affine only because `V` and `W` are.

*The γ⁺-route crossing that route needs is proved, and the match still does not close.* The
crossing of `LerayOpenSubschemeSections.lean` at an arbitrary open `U ≤ f⁻¹V`, with its
derived packaging, is `LerayOpenSubschemeSectionsLE.lean` and `LerayOpenSubschemeDerivedLE.lean`,
ending at `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_lerayComparison_eq`, with
nothing assumed of `f`, of `V`, of `U` or of the module; step 2b.3 above lists it declaration by
declaration, together with the three remarks it forces. It **supersedes** the
two-step route sketched here rather than completing it: the two facts
(`…lerayComparison_comp` at the `resLE`'s factorisation, and
`…openSubschemeSectionsComparison_comp_lerayComparison_eq` at `(h', f'⁻¹V)`) are not used, and
neither is needed. 2b(B) needs two bricks, described in step 2b.3, and **both are proved**:

* **brick (i)**, the compatibility of
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` with precomposition by an
  exact functor preserving injectives — the second half of 2b(i)'s middle — is
  `Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp`
  `_compRightDerivedNatIso_hom`
  (`Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`), at a bare
  pair `(r, w)` with `r` exact, additive and preserving injectives and `w` merely additive, and
  with the same `hθ` the two postcomposition mirrors take (axioms: `propext`, `Classical.choice`,
  `Quot.sound`). ***Most of its chase is already performed, in the edge-morphism vocabulary.***
  `Homology/DerivedIndexing/Composite.lean` carries the residue
  (`Stacks.DerivedIndexing.edge_comp_rightDerivedIsoRes`, :587) and the derived half in the
  `rightDerivedPlus` indexing (`…edge_comp_rightDerivedIso`, :1314, and
  `…singleIsoResPlusQh_hom_app_comp_extendResolutionComparisonPlus`, :1006) for the **edge
  morphism** `Stacks.Cohomology.RightDerivedEdge.edge`, which is identified with
  `compRightDerivedNatIso`: `Stacks.Cohomology.DerivedCompTransport`
  `.compRightDerivedNatIso_inv_eq_edge`
  (`Topology/Sheaves/Cohomology/DerivedFunctors/CompositeEdgeComparison.lean:142`) says the edge
  morphism **is** the comparison's inverse, with nothing assumed beyond what the two
  constructions carry (axioms: `propext`, `Classical.choice`, `Quot.sound`). With that key, step
  2b.3 reduces the brick to exactly two things — the `mapDerivedCategory` spelling of the
  `D⁺` identity, and `EdgeCompatCollapseMirror.lean`'s shuffle one-for-one — and lists the
  facts each needs, including the invertibility of the unit of `Rw` at `r` applied to the
  chosen extended resolution. Both points are
  performed: (★★) as
  `…DerivedCompTransport.mapDerivedCategory_map_singleFunctorIsoCompQh_hom_app_comp_factorsh`,
  point 1 as `…mapDerivedCategory_map_singleIsoResCompQh_hom_app_comp_factorsh`, the
  invertibility as `…isIso_unit_app_mapHomotopyCategory_resH_obj`, and point 2 as
  `…map_singleIsoResCompQh_hom_app_comp_resCompUnitIso_inv_app`;
* **brick (ii)**, the identification of 2a's second leading factor — the **relative** Leray
  comparison `…DerivedSectionsLeray.lerayCompositeComparison h' S.f' V` inverted and **not** the
  absolute `lerayComparison h' (f'⁻¹V)` — with the
  absolute one whiskered by restriction of scalars along `f'^♯` and crossed by
  `Stacks.EdgeCompat.preimageSectionsModelComparison`, is
  `Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison_eq_lerayComparison` and its
  inverted form `…derivedPreimageSectionsCompIso_hom_comp_lerayComparison`
  (`LerayCompositeAbsolute.lean`), with nothing assumed of `i`, of `p` or of `V`.

**The composition of brick (i)'s bare-pair instantiation with the `α` and scalars layers is also
proved** — `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_eq_modelComposition`
(`OpenSubschemeModelCompositionGlue.lean`), see the paragraphs on the gluing below. So still owed:
**the match**, then the composite identity `T = Γ(V, Θ) ≫ res_W`
itself. Steps 2b and 3 are not complete, the match does **not** close, and no
`@[stacks 0EX3 "(c)"]` is placed anywhere.

*What the instantiation needs, which is more than a substitution.* Brick (i)'s
`hθ` has three factors — the crossing
`CategoryTheory.Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ w))` inverted under `Qh`, `αw`
at `r.mapHomotopyCategory`, and `Rw` of
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted. The `θ` the tail has at the pair
`(…TopDegreeBaseChange.openSubschemeRestrictionOf X' U,`
`…DerivedSectionsLeray.sectionsOverOpen (U : Scheme) ⊤)` is
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE`, and its unit
`…openSubschemeSectionsUnitLE` — an instance of `…openSubschemeUnitOfNatTransUnit` — carries two
factors that `hθ` has not: the degreewise crossing `…preimageSectionsOpenSubschemeLE`, which at
`U < f⁻¹V` is the restriction of sections and is **not** invertible, and the derived restriction
of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` that `…openSubschemeDerivedTargetOf`
carries as a third functor on the right. So what is owed is a `θ` and an `hθ` at the **bare**
pair — a unit, its `IsRightDerivedFunctor` instance, a `CategoryTheory.Functor.rightDerivedDesc`
and its `_fac_app`, the four-declaration shape of `LerayOpenSubschemeDerivedLE.lean` — and then
the composition of brick (i) at that pair with the `α` and scalars layers. Nothing in that
needs a hypothesis on `h`.

***The bare-pair instantiation.***
`OpenSubschemeSingleModelCrossing.lean` carries it, at an arbitrary scheme `X`, an arbitrary open
`U ⊆ X`, an arbitrary sheaf of modules and an arbitrary degree, with **nothing assumed of `h`, of
`f'`, of `V`, of `W` or of affineness** (axioms: `propext`, `Classical.choice`, `Quot.sound`
throughout):

* `…TopDegreeBaseChange.openSubschemeRestrictionOf_preservesInjectiveObjects` — fact **A**
  of step 2b.3, `…HigherDirectImage.moduleRestriction_preservesInjectiveObjects` carried across the
  ascription by `inferInstanceAs`;
* `…TopDegreeBaseChange.derivedSectionsImageTopOf` and `…derivedSectionsImageTopUnitOf` with
  `…isRightDerivedFunctor_derivedSectionsImageTopUnitOf` —
  `…DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)` and its unit,
  re-declared at the spellings `ModuleCat Γ(U, 𝒪_U)` and `r ⋙ w`, which the next paragraph explains
  is not optional;
* `…TopDegreeBaseChange.openSubschemeBareUnitOf`, `…openSubschemeBareComparisonOf` and
  `…openSubschemeBareComparisonOf_fac_app` — the three factors of brick (i)'s `hθ`, their
  `rightDerivedDesc`, and the factorisation, which **is** `hθ` with no further work: the `_fac_app`
  is `CategoryTheory.Functor.rightDerived_fac_app` itself, the three whiskerings' components being
  the three factors on the nose;
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom` —
  **brick (i) at the pair.** The crossing of the two models of `Rⁿ Γ(U.ι ''ᵁ ⊤, -)` on `X`,
  followed by `compRightDerivedNatIso` for `(restriction to U, Γ(U, ⊤, -))`, is `Hⁿ` of
  `openSubschemeBareComparisonOf` at `M[0]`, then of `RΓ(U, ⊤, -)` applied to
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, then the crossing on the open
  subscheme at the restricted module.

*One elaboration caveat, about a pair of spellings.* Passing
`…DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)` straight in as brick
(i)'s `Rrw` is **refused**: `HasDerivedCategory` is then reported `failed to synthesize` at
`ModuleCat Γ(U, 𝒪_U)` — the spelling `w`'s target carries — even though that very instance is found
by `inferInstance` standing alone in the same file, and even with it introduced into the local
context by `haveI` (also with all six universe levels of the brick written out explicitly: the
levels are not the cause). The crossing it is asked to make is
`ModuleCat Γ(U, 𝒪_U)` against `ModuleCat Γ(U.ι ''ᵁ ⊤, 𝒪_X)`, which are `rfl`-equal — fact
**C** of step 2b.3 — but the instance argument is synthesised rather than unified. The cure is the
same as for `openSubschemeRestrictionOf`: a `def` whose *declared* target
carries the wanted spelling, with the conversion run once in term mode at default transparency. The
same `def` is needed for the unit, `IsRightDerivedFunctor` being indexed by the unit term; that is
why the shape is four declarations and not two.

***What the composition with the `α` and scalars layers needs.*** The geometric
`openSubschemeSectionsComparisonLE f V e` runs
`derivedPreimageSections f V ⟶ Rres ⋙ RΓ((f.resLE V U e)⁻¹⊤, -) ⋙ res_{topIso}`, while the bare
comparison runs `RΓ(U.ι ''ᵁ ⊤, -) ⟶ Rres ⋙ RΓ(U, ⊤, -)`. Factor by factor the chain between them
is, in the order a chase meets it:

1. `Stacks.EdgeCompat.preimageSectionsModelComparison f V` — the total `derivedPreimageSections`
   model against `RΓ(f⁻¹V, -) ⋙ res_{f^♯}`. Available, and it elaborates at
   `f := f.toLRSHom.toShHom`.
2. `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison f V e` — the `α` layer,
   restriction of sections from `f⁻¹V` down to `U` read over `Γ(V, 𝒪_S)`. Available
   (`EdgeCompatPreimageRestrictSource.lean`), and it elaborates at the geometric data with
   `hW := e`. Its target reads the scalars as `res_{U ≤ f⁻¹V} ⋙ res_{f^♯}`.
3. the crossing of `derivedSectionsOverOpen X U` with `derivedSectionsOverOpen X (U.ι ''ᵁ ⊤)`, i.e.
   the **unbounded** derived form of `…TopDegreeBaseChange.sectionsOnImageTopNatIso`. The only
   other derived form of it is `…TopDegreeBaseChange.sectionsOnImageTopDerivedIso`
   (`DerivedSectionsModelCrossing.lean`), which is at Mathlib's **classical** `Functor.rightDerived
   n` through `…ModuleComparison.rightDerivedCompIso` — not a comparison of two unbounded right
   derived functors, and so not what the chain needs. It is proved in
   `OpenSubschemeDerivedSectionsImageTop.lean`, with nothing assumed of `X`, of `U` or of the
   module (axioms: `propext`, `Classical.choice`, `Quot.sound`): `…TopDegreeBaseChange`
   `.imageTopRestrictScalarsOf` with its three exactness instances, `…sectionsImageTopNatIsoOf`,
   `…imageTopCompUnit` with `…isRightDerivedFunctor_imageTopCompUnit`, and
   `…derivedSectionsImageTopIso` with `…derivedSectionsImageTopIso_hom_app_unit`. Its closure is
   348 modules, so it is cheap to import anywhere.

   *What made it three declarations rather than a file.* Both sides are right derived functors of
   the two **isomorphic** degreewise functors along the *same* localization `DerivedCategory.Qh`,
   so Mathlib's `CategoryTheory.Functor.rightDerivedNatIso` gives the comparison outright once the
   left-hand side is exhibited as a right derived functor — and that is one application of
   `…HomologyComparison.exactPostcomposeUnit` with its instance, restriction of scalars being
   exact. No chase, no `_fac_app` bookkeeping beyond `Functor.rightDerivedNatTrans_app`.

   *An alternative route, and an elaboration caveat.*
   `StacksDraft.DerivedModel.rightDerivedModelIso` (`Homology/DerivedCategory/`
   `StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`) is the general "a total
   right derived functor read at two
   models" and would also give it in one application — but it requires the comparison of the two
   **targets** to be an equivalence, and `ModuleCat.restrictScalars`
   `(Scheme.Opens.topIso U).inv.hom` carries no `.IsEquivalence` instance,
   restriction of scalars along a ring isomorphism having none registered; `rightDerivedNatIso`
   asks for no equivalence and is the cheaper route. And the composite
   `sectionsOverOpen X (U.ι ''ᵁ ⊤) ⋙ ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom`
   is reported as a missing `CategoryTheory.Functor.Additive` instance although **both factors have
   one standing alone** (at both the `sectionsOverOpen` and the
   `AlgebraicGeometry.sectionsOn` spelling of the first factor): `Functor.instAdditiveComp` is
   keyed on the intermediate category, and the two factors spell the ring `Γ(U, 𝒪_X)` as
   `(structureSheafRing X.toRingedSpace).obj.obj (op (U.ι ''ᵁ ⊤))` and as
   `(U : Scheme).presheaf.obj (op ⊤)`. The cure is the usual one —
   `imageTopRestrictScalarsOf` is a `def` with both ends declared at the
   `structureSheafRing` spelling and `inferInstanceAs` for the three instances.
4. the bare comparison, whiskered by the scalars.
5. `Stacks.EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` — the upstairs scalars
   layer, which elaborates; `(opensMap (f.resLE V U e)).obj ⊤ = ⊤` is `rfl`, so no transport of
   the upstairs open is needed.
6. the three spellings of the one ring map `Γ(V, 𝒪_S) ⟶ Γ(U, 𝒪_U)` reconciled:
   `res_{U ≤ f⁻¹V} ⋙ res_{f^♯}` from point 2, `res_{f.appLE V U e}` from
   `…preimageSectionsRestrictLE`, and `res_{(f.resLE V U e)^♯} ⋙ res_{topIso}` from
   `…openSubschemeDerivedTargetOf`. The degreewise reconciliations are available —
   `…TopDegreeBaseChange.appLE_comp_topIso_inv_hom` and `…restrictScalarsSquareIso` — and
   `ModuleCat.restrictScalarsComp'` associates the pairs. ***Their derived form*** is
   in `OpenSubschemeDerivedScalars.lean`, with nothing assumed of `f`, of `V`, of `U` or
   of the module (axioms: `propext`, `Classical.choice`, `Quot.sound`):
   `…TopDegreeBaseChange.derivedScalarsReconciliation`, which identifies
   `RΓ(U, ⊤, -) ⋙ D(res_{topIso at U}) ⋙ D(res_{U ≤ f⁻¹V} ⋙ res_{f^♯})` with
   `RΓ(U, ⊤, -) ⋙ D(res_{resLE^♯}) ⋙ D(res_{topIso at V})`, together with the equation
   `…derivedScalarsReconciliation_hom_app_unit` that characterises it. Four units and four
   instances come with it — `…openSubschemeTopUnit`, `…scalarsUnitA`, `…resLETopUnit`,
   `…scalarsUnitB` — two applications of
   `…HomologyComparison.exactPostcomposeUnit` on each side, after which the two sides are right
   derived functors along the same `DerivedCategory.Qh` of the two *isomorphic* degreewise
   functors and Mathlib's `CategoryTheory.Functor.rightDerivedNatIso` gives the comparison
   outright. No `mapDerivedCategoryCompIso` is used and none is needed; the route through
   `CategoryTheory.Functor.mapDerivedCategoryCompIso` is avoided because its
   characterisation over `DerivedCategory.Qh` names `mapDerivedCategoryFactorsh`, at which `rw`
   is refused (see above).

   *Three elaboration facts.* `scalarsChainA` and `scalarsChainB`
   each **are** `ModuleCat.restrictScalars` of a single ring homomorphism by `rfl` — a composite
   of two `ModuleCat.restrictScalars` being `restrictScalars` of the composite — so the two sides
   are `ModuleCat.restrictScalarsCongr` at `appLE_comp_topIso_inv_hom` and no
   `restrictScalarsComp'` reassociation occurs anywhere. `f ⁻¹ᵁ V` **is**
   `(opensMap f.toLRSHom.toShHom).obj V` by `rfl`, but the composite
   `sectionsRestrictScalars X e ⋙ preimageRestrictScalars f V` is reported as a missing
   `Functor.Additive` instance when the open is written in the **scheme** spelling and is found
   when it is written in the ringed-space one — `Functor.instAdditiveComp` keyed on the
   intermediate category, the same issue as above, at a third pair of spellings. And the
   same issue arises at `sectionsOverOpen (U : Scheme) ⊤ ⋙ imageTopRestrictScalarsOf X U`, whose
   `Functor.Additive` is **not** synthesisable although `(imageTopRestrictScalarsOf X U).Additive`
   is found by `inferInstance` in the same file and `Functor.instAdditiveComp _ _` is passed
   explicitly; the cure is the usual one, `…openSubschemeTopRestrictScalars` with its source
   *declared* at `Γ(U, 𝒪_U)`, equal to `imageTopRestrictScalarsOf X U` by `rfl`
   (`…openSubschemeTopRestrictScalars_eq`), so no second construction is hidden.

   *Two general transports of `exactPostcomposeUnit`*, in
   `…/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismExactFunctorTransport.lean`,
   are used because the gluing needs
   to move a transformation past that unit twice over:
   `…HomologyComparison.exactPostcomposeUnit_comp` — postcomposing a comparison `RF ⟶ RF'` of the
   two right derived functors upstairs, with `RF'` not assumed to be a right derived functor of
   anything — and `…HomologyComparison.exactPostcomposeUnit_whiskerRight` — pulling a degreewise
   prefix `δ : F ⟶ F'` out, which is the naturality of the comparison isomorphism
   `exactPostcomposeUnit` carries in its first argument. Nothing is assumed of `F`, `F'` beyond
   additivity or of `G` beyond exactness (axioms: `propext`, `Classical.choice`, `Quot.sound`).
   The second needs `…HomologyComparison.mapHomotopyCategoryCompIso_refl_inv_app`, a two-line
   statement that is also `private` in
   `Homology/DerivedCategory/InverseSystem/ModuleInverseLimitGlobalSections.lean`
   and in `Algebra/Homology/DerivedCategory/MapDerivedCategoryCompIsoOnHomotopyCategory.lean`;
   the one public relative,
   `CategoryTheory.mapHomotopyCategoryCompIso_hom_app`
   (`Algebra/Homology/HomotopyCategoryTransition.lean`), reads the comparison at an arbitrary `e`
   in the `hom` direction and does not specialise.
   *One elaboration caveat:* rewriting those identities
   away with `CategoryTheory.Category.id_comp` is **refused**, the target not being type-correct
   at `implicit` transparency, and the cancellation is a private lemma at variables.

*The engine for the identity itself is available and is not a new brick.*
`Stacks.RightDerivedDescent.comp_rightDerivedDesc_eq_rightDerivedDesc_iff` and
`…comp_rightDerivedDesc` (`CategoryTheory/Functor/Derived/RightDerivedDescTransport.lean`) reduce
an identity of two right derived descents to the identity of the two transformations they descend,
which for this chain is the *definition* of `…preimageSectionsOpenSubschemeLE` — it is already
`…preimageSectionsRestrictLE`, then `sectionsOnImageTopNatIso` inverted, then the scalars square.
That brick is **not** in `BaseChangeSectionsTail.lean`'s closure and must be imported.
`lerayComparison_ext` is the alternative and is what the `LE` file already uses.

So **every one of the composition's six factors is available** — point 6's derived form being
`…TopDegreeBaseChange.derivedScalarsReconciliation` — and what is left of it is
bookkeeping: the three model comparisons of points 1, 2 and 5, the crossing of point 3, the bare
comparison of point 4, and point 6's reconciliation of the three spellings of the one ring map,
glued by `rightDerived_ext` through the four `_fac_app`s. Nothing is assumed of `h` anywhere in
it. The gluing itself is performed below.

***The composition's statement.*** Written
out at the geometric data it is

> `openSubschemeSectionsComparisonLE f V e`, then
> `…EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` whiskered by the derived
> restriction on the left and by `D(res_{topIso at V})` on the right, equals
> `…EdgeCompat.preimageSectionsModelComparison f V`, then
> `…preimageSectionsRestrictSourceModelComparison f V e`, then
> `…TopDegreeBaseChange.derivedSectionsImageTopIso` **inverted** whiskered by the downstairs
> scalars, then `…TopDegreeBaseChange.openSubschemeBareComparisonOf` whiskered by the two scalars
> layers, then `…TopDegreeBaseChange.derivedScalarsReconciliation`,

and that statement elaborates in a file importing
`OpenSubschemeSingleModelCrossing`, `OpenSubschemeDerivedSectionsImageTop`,
`EdgeCompatPreimageRestrictSource` and `OpenSubschemeDerivedScalars` — the four
defeq crossings it makes (`derivedSectionsImageTopOf` against `derivedSectionsOverOpen X
(U.ι ''ᵁ ⊤)`, `imageTopRestrictScalarsOf` against `openSubschemeTopRestrictScalars`,
`(opensMap (f.resLE V U e)).obj ⊤` against `⊤`, and the two readings of the functor composition's
associativity) are all `rfl` and cost nothing.

***Both unit composites are computed, and what is left of the gluing is one coherence
identity, written out below.*** The reordering above is what makes that cheap: putting
`derivedScalarsReconciliation` **before** the bare comparison rather than after it keeps it a
transformation of functors out of `D(𝒪_X)`, so the naturality of the reconciliation at
`(openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv.app K`, i.e.
`…openSubschemeUnitOfNatTransUnit_comp` transplanted, **does not arise at all** and the
reconciliation is consumed by its own `rightDerivedNatTrans_fac`. That is also why point 6's
derived form is stated at `RΓ(U.ι ''ᵁ ⊤, -)` on `X` and not at `RΓ(U, ⊤, -)` on the open
subscheme.

`rightDerived_ext` at `derivedPreimageSections f V` reduces the gluing to the identity of the two
composites with `derivedPreimageSectionsUnit f V`, and both are proved in
`OpenSubschemeModelCompositionUnit.lean`, with nothing assumed of `f`, of `V`, of `U` or of the
module (axioms: `propext`, `Classical.choice`, `Quot.sound`):

* `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_upstairsModel_unit` — the **left**
  side is `…openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)`
  `(…EdgeCompat.preimageSectionsCompUnit (f.resLE V U e) ⊤)`. Three steps:
  `Functor.rightDerived_fac`, `…openSubschemeUnitOfNatTransUnit_comp` at
  `L := preimageSectionsModelComparison (f.resLE V U e) ⊤`, and that comparison's own
  `rightDerived_fac`. *One elaboration caveat:* `rw [← openSubschemeUnitOfNatTransUnit_comp]` is
  **refused** — the target is not type-correct at `implicit` transparency — so the lemma is
  applied to the already-rewritten hypothesis instead.
* `…TopDegreeBaseChange.modelComposition_unit` — the **right** side is three degreewise prefixes,
  `wR (mapHC (preimageSectionsRestrictSource f V e)) Qh`, then
  `wR (mapHC (wR (sectionsImageTopNatIsoOf X U).inv (downstairs scalars))) Qh`, then
  `wR (mapHC (wL (sectionsOverOpen X (U.ι ''ᵁ ⊤)) (scalarsReconciliation f V e).hom)) Qh`,
  followed by `exactPostcomposeUnit (secIT ⋙ resLEtop) baseT _`
  `(exactPostcomposeUnit secIT resLEtop _ (openSubschemeBareUnitOf X U))`. Five steps, each
  stated as its own lemma: two `rightDerived_fac`s, then
  `…preimageSectionsRestrictSourceCompUnit_comp_derivedSectionsImageTopIso_inv` (one
  `exactPostcomposeUnit_comp`, the inverse half `…derivedSectionsImageTopIso_inv_unit` of point 3's
  characterising equation, and one `exactPostcomposeUnit_whiskerRight`), then
  `…scalarsUnitA_comp_derivedScalarsReconciliation` (one `rightDerivedNatTrans_fac`), then
  `…scalarsUnitB_comp_openSubschemeBareComparisonOf` (two `exactPostcomposeUnit_comp`s and
  `openSubschemeBareComparisonOf_fac_app`).

***So the gluing is reduced to exactly one identity, and that identity and the gluing are
performed*** — `…TopDegreeBaseChange.modelComposition_coherence` and
`…openSubschemeSectionsComparisonLE_eq_modelComposition`
(`OpenSubschemeModelCompositionGlue.lean`); the paragraphs below describe the reduction. Writing
`r` for
`openSubschemeRestrictionOf X U`, the two sides' three degreewise prefixes agree — a composite of
two `ModuleCat.restrictScalars` is `restrictScalars` of the composite and
`AlgebraicGeometry.Scheme.Hom.appLE` is that composite, both by `rfl`, so
`preimageSectionsRestrictLE` against `preimageSectionsRestrictSource` and the two whiskered
crossings match factor for factor, and `moduleRestriction X U ⋙ sectionsOverOpen (U : Scheme) ⊤`
**is** `sectionsOverOpen X (U.ι ''ᵁ ⊤)`, which is why `scalarsReconciliation` is declared as
`restrictScalarsSquareIso` and not as the bare `ModuleCat.restrictScalarsCongr`: that makes the
third prefix the very factor `preimageSectionsOpenSubschemeLE` carries. What remains is the rest:

> `(preimageSectionsOpenSubschemeHomotopyIsoLE f V e).hom`, then
> `wL (r.mapHC) (wR (…EdgeCompat.preimageSectionsCompUnit (f.resLE V U e) ⊤)
> D(res_{topIso at V}))`, then `wR r.mapDerivedCategoryFactorsh.inv (…)`, equals
> `exactPostcomposeUnit (secIT ⋙ resLEtop) baseT _`
> `(exactPostcomposeUnit secIT resLEtop _ (openSubschemeBareUnitOf X U))`.

*What that identity is, on printing both sides.* After `ext K` and
`simp [preimageSectionsOpenSubschemeHomotopyIsoLE, preimageSectionsTopRestrictHomotopyIsoLE,`
`exactPostcomposeUnit, openSubschemeBareUnitOf, preimageSectionsCompUnit]`, both sides are flat
composites of the **same** factors in the **same** order — `baseT`'s
`mapDerivedCategoryFactorsh.inv`, then `resLEtop`'s, then `derivedSectionsOverOpenUnit (U, ⊤)` at
`r.mapHC K`, then `r.mapDerivedCategoryFactorsh.inv` — and differ only by (i) four occurrences of
`CategoryTheory.Functor.mapHomotopyCategoryCompIso (Iso.refl _) |>.inv.app`, which are identities
by `…HomologyComparison.mapHomotopyCategoryCompIso_refl_inv_app`, (ii) one
`CategoryTheory.Functor.associator` leg, also an identity, and (iii) the distribution of
`Functor.map` and of `whiskerLeft`/`whiskerRight` over those composites. **`simp` does not close
it**: it cannot cancel the identities, `CategoryTheory.Category.id_comp` being refused on a target
that is not type-correct at `implicit` transparency — the same issue as in
`exactPostcomposeUnit_whiskerRight`, handled there by a private lemma at variables. So the
step is the same cancellation discipline at four more places, and nothing mathematical is left in
it.

***The cancellation discipline, at variables and in full generality; the identity reduces to four
pieces.*** What the identity is, stripped of the
geometry: both tails are the *same* two-step postcomposition of the unit of `RΓ((f.resLE V U e)⁻¹⊤,
-)` by the two exact restrictions of scalars, taken in the two possible orders — precomposing the
restriction `r` to the open subscheme first, or postcomposing the scalars first. That is one
statement at variables of abstract categories, and it is proved in
`…/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismExactFunctorTransport.lean`
beside the two transports that file
already carried (axioms: `propext`, `Classical.choice`, `Quot.sound`):

* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit_precompose`: for
  `r` exact, `F` additive with a right derived functor `RF` presented by `unit`, and `G` exact,
  applying `exactPostcomposeUnit … G` to the transformation
  `wR (mapHomotopyCategoryCompIso (Iso.refl (r ⋙ F))).inv Qh ≫ wL (r.mapHC) unit ≫`
  `wR r.mapDerivedCategoryFactorsh.inv RF` — the shape every `rightDerivedDesc` out of a
  precomposition in this subtree is fed, `…TopDegreeBaseChange.openSubschemeBareUnitOf` included —
  gives the same transformation built from `exactPostcomposeUnit F G RF unit`. The proof is
  `ext K`, one `simp only` on the definition, and the private `glue_two_sides` cancelling the
  **four** `mapHomotopyCategoryCompIso (Iso.refl _)` identities at variables: exactly the
  discipline described above, carried out once instead of four times. Nothing is assumed of
  `r` or `G` beyond exactness, nothing of `F` beyond additivity, and `RF` is not assumed to be a
  right derived functor of anything.
* `…HomologyComparison.exactPostcomposeUnit_precompose_comp`: the same for two exact functors
  postcomposed in succession, with the result written out **left-associated**, which is the
  spelling `…openSubschemeUnitOfNatTransUnit`'s tail has, so that no reassociation is left at the
  call site. Two applications of the first and one `simp only`.

*The geometric pieces*, in `OpenSubschemeModelComposition.lean`, with nothing
assumed of `f`, of `V`, of `U` or of the module (axioms: `propext`, `Classical.choice`,
`Quot.sound` throughout):

* `…TopDegreeBaseChange.preimageSectionsOpenSubschemeLE_eq` — the degreewise crossing **is** the
  three degreewise prefixes `modelComposition_unit` produces, by `rfl`; and
  `…whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE`, the same read on the
  homotopy category and localized, where the two splittings are
  `CategoryTheory.NatTrans.mapHomotopyCategory_comp`. So the prefix half of the identity is
  closed.
* `…TopDegreeBaseChange.openSubschemeBareUnitOf_eq` — the two-fold `exactPostcomposeUnit` on
  `openSubschemeBareUnitOf X U`, read at the open subscheme's own spellings, by `rfl`.
* `…TopDegreeBaseChange.openSubschemeBareUnitOf_eq_precomposeTail` and `…_eq_precomposeTail'` —
  **that two-fold unit IS the tail of `openSubschemeUnitOfNatTransUnit`**, by
  `exactPostcomposeUnit_precompose_comp` at the geometric pair; the primed form reads the target
  at the open subscheme's spelling as well.
* `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit_eq_precomposeTail` — the left side's unit
  composite is the degreewise crossing followed by that tail, by `rfl`.

***What the composition costs.*** The two
sides spell the same functors differently at **five** places — `U.ι ''ᵁ ⊤` of `X` against `⊤` of
the open subscheme, `(opensMap (f.resLE V U e)).obj ⊤` against `⊤`, and the ascribed
`…resLETopRestrictScalars`/`…baseTopRestrictScalars` against
`Stacks.EdgeCompat.preimageRestrictScalars` and the bare `ModuleCat.restrictScalars` — and each
crossing is definitional but costs a large part of a declaration's 200,000 heartbeats: one factor
of the flattened component identity
(`baseT.mapDerivedCategoryFactorsh.inv.app` against `resV`'s, at the two spellings of the object)
is `rfl` in about five seconds. The five crossings the identity needs are the two-fold unit's
*term*, its *source* functor, its *target* functor, the prefix's target, and the model
composition's target; the four declarations above and the two restatements of
`modelComposition_unit` each pay exactly one, which is the only reason they are split. Composing
them does not need a sixth crossing in the composing declaration, provided the statement is
arranged as described below. The following arrangements exhaust the budget:

* the term built by `have` and discharged by `exact` — `timeout at isDefEq` on the `exact`;
* the same written in term mode — `timeout at whnf`;
* a `rw` chain — **refused outright** in the `←` direction, the motive not being type-correct at
  `implicit` transparency (`preimageRestrictScalars` keyed on the ascribed spelling of its source
  ring, reported as a mismatch of
  `Γ(⊤, (opensMap (f.resLE V U e))_* 𝒪_U)` against `Γ((opensMap (f.resLE V U e)).obj ⊤, 𝒪_U)`),
  and `timeout at isDefEq` in the forward direction;
* the component route — `CategoryTheory.NatTrans.ext (funext fun K => ?_)` followed by one
  `simp only` does flatten both sides to the same factors in the same order, but `simp only` leaves
  `Functor.whiskerRight_app` unapplied on the whiskered bare unit — **silently** — and
  `rw [Functor.whiskerRight_app]` is refused there too, `timeout at whnf`. `ext K` itself exhausts
  the heartbeats at `whnf` where `NatTrans.ext (funext fun K => ?_)` succeeds.

*Why one declaration holds the crossing.* In `theorem _ : A = B`
Lean elaborates `A`, then elaborates `B` **against `A`'s type**, so the equation's type index is
`A`'s and the crossing is made once, there. Written with the **open-subscheme** side first — the
spelling all three input lemmas already live at — the statement's one crossing is paid during its
elaboration and nothing in the proof crosses again: the proof is
`glue_prefix3_tail`, the reassociation at variables this subtree uses throughout, whose three
hypotheses fix every category and every object, so its application is syntactic. The statement
alone elaborates in about two seconds, and the coherence identity with its proof checks in about
six. Each of the failing arrangements above puts the crossing in the statement **and again** in
the proof — the `exact`'s `isDefEq`, the term's `whnf`, the `rw` motive — with the budget already
spent on the first. In particular no ascribed `def` for restriction of scalars along
`(f.resLE V U e)^♯` with its source at `Γ((U : Scheme), ⊤)` is needed, and
`modelComposition_unit` is not restated. (`exactPostcomposeUnit_precompose_comp` is refused at
`(sectionsOverOpen (U : Scheme) ⊤, resLETopRestrictScalars f V e)` —
`(resLETopRestrictScalars f V e).Additive` reported `failed to synthesize` where `inferInstance`
finds it standing alone — the instance-spelling issue at a sixth pair; it is not on the path.)

***So the gluing is proved***, in `OpenSubschemeModelCompositionGlue.lean`, with nothing assumed of
`f`, of `V`, of `U` or of the module (axioms: `propext`, `Classical.choice`, `Quot.sound`):

* `…TopDegreeBaseChange.modelComposition_coherence` — the coherence identity above, the four pieces
  of `OpenSubschemeModelComposition.lean` composed;
* `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_eq_modelComposition` — **the gluing**:
  `openSubschemeSectionsComparisonLE f V e` followed by
  `Stacks.EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` whiskered by the derived
  restriction and the derived restriction of scalars is the three model comparisons, the crossing
  of the two sections functors inverted, `…derivedScalarsReconciliation`, and
  `…openSubschemeBareComparisonOf` whiskered by the two scalars layers. Both sides come out of
  `…DerivedSectionsLeray.derivedPreimageSections f V`, so
  `…DerivedSectionsLeray.lerayComparison_ext` reduces it to the two unit composites with the
  coherence identity between them: three `Eq.trans` and nothing else.

***The 2b(B) match still does not close, nor does the composite identity; what the match needs is
a chase and no new general brick, and the inventory below is read off the two sides'
statements.***

The ψ side's 089W factor is
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` at
`g := h'.resLE (f'⁻¹V) (f''⁻¹W)` — a morphism of schemes
`(f''⁻¹W : Scheme) ⟶ (f'⁻¹V : Scheme)`, so **`g` is `f.resLE V U e` at
`(f, V, U) = (h', f'⁻¹V, f''⁻¹W)` and the whole `LE` family applies to it on the nose**. Printed
from that statement, its five factors are: (1)
`…DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the pair
`(sectionsOverOpen (f'⁻¹V : Scheme) ⊤, derivedSectionsOverOpen (f'⁻¹V : Scheme) ⊤)`, **inverted**;
(2) `Hᵈ` of `derivedSectionsOverOpen (f'⁻¹V : Scheme) ⊤` applied to a comparison `c` of the two
models of `Rg_*` retracting `CategoryTheory.Functor.singleCollapse`; (3) a left inverse of `Hᵈ` of
`lerayComparison g ⊤`; (4) the same crossing at the pair
`(modulePushforward g ⋙ sectionsOverOpen (f'⁻¹V : Scheme) ⊤, derivedPreimageSections g ⊤)` —
whose degreewise factor **is** `…DerivedSectionsLeray.preimageSections g ⊤`, by
`pushforwardPreimageSectionsIso` being `Iso.refl`; (5)
`…AffineComparison.restrictScalarsRightDerivedIso g F' d` inverted. Step 2a's two leading factors,
read off its statement, are `(derivedPreimageSections S.f' V).map c` and
`(derivedPreimageSectionsCompIso h' S.f' V).hom.app M`, on `X'` and `Y'`.

What matches what, and with which brick:

* factors (1) and (4) are the **model half**. Both are moved off the open subschemes by the
  bare-pair brick `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp`
  `_compRightDerivedNatIso_hom` (`OpenSubschemeSingleModelCrossing.lean`) at the pair
  `(openSubschemeRestrictionOf X U, sectionsOverOpen (U : Scheme) ⊤)` — at `(X', f'⁻¹V)` for (1)
  and at `(X'', f''⁻¹W)` for (4) — whose `openSubschemeBareComparisonOf` factor is exactly what the
  gluing above rewrites into `openSubschemeSectionsComparisonLE` and the three model comparisons.
  For (4) the brick is reached through `Stacks.EdgeCompat.preimageSectionsModelComparison g ⊤`,
  which is the gluing's own left-hand factor, so **no second instantiation of the brick at
  `w := preimageSections g ⊤` is needed** — a second instantiation would be four declarations
  (unit, `IsRightDerivedFunctor`, `rightDerivedDesc`, `_fac_app`) and is not on the path. The
  only consumer of brick (i) is `OpenSubschemeSingleModelCrossing.lean`, and the only other
  statement about `singleCompDerivedCompHomologyIsoRightDerived` together with
  `preimageSections` is in `EdgeCompatPreimageSections.lean`, where
  `…TopDegreeBaseChange.derivedPreimageSectionsRightDerivedIso` (:111) is the γ⁺ side's own reading
  of that crossing at `(preimageSections f V, derivedPreimageSections f V)` — the target of the
  move, not a duplicate of the brick. (But see the correction below: factor (4) is in fact moved
  by the collapse mirror, not by brick (i).)
* factor (3) is the **Leray half**, and it is settled: brick (ii)
  `…DerivedSectionsLeray.derivedPreimageSectionsCompIso_hom_comp_lerayComparison`
  (`LerayCompositeAbsolute.lean`) is already the inverted form 2a's second leading factor is
  written at, and `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_lerayComparison_eq`
  (`LerayOpenSubschemeDerivedLE.lean`) carries `lerayComparison g ⊤` to
  `lerayComparison h' (f'⁻¹V)`.
* factor (2) is 2a's first leading factor after the same model move, and factor (5) is the scalars.

*The one crossing the chase still has to make.* The bricks above are
natural transformations of functors on the derived categories, while the ψ side's factors are
`Hᵈ` of them with restrictions of scalars interleaved, so the chase must commute `Hᵈ` past
`ModuleCat.restrictScalars … |>.mapDerivedCategory`. That is
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`
(`Homology/DerivedCategory/MapHomologyIso.lean:35`), for any exact functor and any degree, with
`…mapHomologicalComplexHomologyIso` (:25) its degreewise content. It is built by
`CategoryTheory.Localization.liftNatIso` and therefore has **no component formula**, so a chase may
use only its **naturality**; that is all the moves above ask of it. (*A duplicate:*
`StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso`
(`Homology/PseudoCoherent/Basic.lean:198`) is the same statement for an exact functor of **module**
categories, with the same `Localization.liftNatIso` proof and the degreewise isomorphism inlined
rather than named; the general one subsumes it.)

So the match is a chase over the bricks at two instantiations, and it is not performed here.
No `@[stacks 0EX3 "(c)"]` is placed and conclusion (c) stays open.

***Two corrections to the inventory above: one of the two bricks it names is the wrong one.***
What is right: `g := h'.resLE (f'⁻¹V) (f''⁻¹W)` *is*
`f.resLE V U e` at `(h', f'⁻¹V, f''⁻¹W)`, so the whole `LE` family does apply to it; and the
five-factor reading of the ψ side's 089W factor is accurate factor for factor, as one sees by
elaborating `…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` at
`p.resLE (f ⁻¹ᵁ V) U' e` for variable `p : Z ⟶ X`, `f : X ⟶ S`, `V : S.Opens`,
`U' ≤ p⁻¹(f⁻¹V)`. What is wrong is the assignment of bricks and the modules.

1. *Factor (4) is **not** moved by the bare-pair brick (i), at any pair.*
   `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom`
   and the general statement behind it,
   `Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso`
   `_hom`, are **pre**composition statements: they move an *exact* functor `r` out of
   `Rⁿ(r ∘ w)` on the **left**, and they need `r` exact and injective-preserving. Factor (4)'s
   degreewise functor is `…DerivedSectionsLeray.preimageSections g ⊤`, which is `Γ(g⁻¹⊤, -)`
   followed by restriction of scalars along `g^♯`: the exact factor is on the **right**. At
   `r := sectionsOverOpen (f''⁻¹W : Scheme) ⊤` the exact slot would be the functor being derived,
   and `modulePushforward g` is not exact either, so no instantiation of brick (i) reaches it.
   The applicable general statement is the collapse **mirror**,
   `Stacks.EdgeCompat.singleCompDerived_hom_app_comp_rightDerivedCompNatIso_inv`
   (`EdgeCompatCollapseMirror.lean`), which moves the **outer** functor out; its instantiation at
   the scalars pair is in `PreimageSectionsCollapseMirror.lean`:
   `Stacks.EdgeCompat.singleCompDerivedPreimageSections_hom_app_comp_rightDerivedCompNatIso_inv`,
   with `…singleCompDerivedPreimageSectionsComp_hom_app_comp_rightDerivedCompNatIso_inv` the same
   at the `f_* ⋙ Γ(V, -)` spelling of the degreewise functor, which is the spelling factor (4) is
   printed at. Nothing is assumed of `f`, of `V`, of the degree or of the object beyond the
   pointwise homology-preservation hypothesis Grothendieck's comparison itself carries, and that
   one is `fun _ => inferInstance`, restriction of scalars being exact.

   *This is not a second bare-pair instantiation of brick (i).* Such an instantiation at
   `w := preimageSections g ⊤` would be four new
   declarations — a unit, an `IsRightDerivedFunctor`, a `rightDerivedDesc` and its `_fac_app`. None
   is needed: all three data the mirror consumes already sit in
   `EdgeCompatPreimageRestrict.lean` — `Stacks.EdgeCompat.preimageSectionsCompUnit` with
   `…isRightDerivedFunctor_preimageSectionsCompUnit`, and
   `…preimageSectionsModelComparison` with `…_fac_app` — and the inventory itself names
   `preimageSectionsModelComparison g ⊤` as the route. What `PreimageSectionsCollapseMirror.lean`
   application is two routine inhabitants (K-injective resolutions of complexes of
   `Γ(f⁻¹V, 𝒪_X)`-modules, and restriction of scalars being its own right derived functor) and one
   `rfl`-plus-reassociation reading of `…HomologyComparison.exactPostcomposeUnit` off its
   construction, which is the `hθ` the mirror asks for.

2. *Brick (i) does not apply to factor (1) "on the nose" either: the modules do not match.* Brick
   (i) is natural in a module **on the ambient scheme**, and its right-hand side's last factor —
   the one that is ψ's factor (1) — sits at `(openSubschemeRestrictionOf X U).obj M`. ψ's factor
   (1) sits at `(Scheme.Modules.pushforward g).obj N` and factor (4) at `N`, where in the genuine
   situation `N = g^*(F'|_{f'⁻¹V})`. Neither is syntactically a restriction from the ambient
   scheme. The ψ tail does carry the two transports that fix this — `Stacks.Modules`
   `.restrictPullbackObjIso` inside `…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`
   upstairs, and the five comparisons of `…unit_resLE_eq_restrictFunctor_map_unit` downstairs — so
   the chase must move them across the crossings by naturality first; that is a step the inventory
   does not account for. And for factor (1) the downstairs transport is **not** available from the
   `resLE` data alone: the observation above that the ψ half does not generalise —
   `(f.resLE V U e)_*(F|_U)` is not `(f_* F)|_V` once `U < f⁻¹V`, so
   `…HigherDirectImage.modulePushforwardRestrictIso` has no analogue there — applies verbatim to
   `g_* N`. So factor (1)'s move consumes the **pullback square** `hsq`, not just the `LE` family,
   and the sentence "the whole `LE` family applies on the nose" is true of `g` and of the Leray
   half and false as a claim about the module factor (1) sits at.

These two corrections do not bring the match closer than the inventory says; the first
replaces one named brick by another, the second adds a step the inventory omitted.

***The dictionary needed by the five-step order.*** Steps 2 and 3 of that order need the
dictionary between the
mirror's `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` and the `ψ` side's factor (5)
`Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso`.
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_eq_rightDerivedCompIso`
(`AffineCohomologyVanishing/AffineBaseComposition.lean`) supplies half of it for a `G` with
`PreservesHomology`, which restriction of scalars has — and the
`sectionsOverOpen`-versus-`moduleGlobalSections` crossing **on top** of it is free.

*A near-miss.* No other statement names
`rightDerivedCompNatIso` together with `restrictScalarsRightDerivedIso`. The closest is
`CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismExtend.lean:62`, whose notes
*assert* the identification in prose — "the two tags share their first factor exactly …
`rightDerivedCompIso` at `sectionsRestrictionIsoTop`, which is `restrictScalarsRightDerivedIso`
whiskered" — without a theorem a chase could rewrite with.

*All four halves of the crossing are `rfl`, each on its own:*
`Stacks.Cohomology.AffineBase.asRingedSpaceHom g = g.toLRSHom.toShHom`;
`moduleGlobalSections X = sectionsOverOpen X ((opensMap g).obj ⊤)`;
`ModuleCat.restrictScalars g.appTop.hom = Stacks.EdgeCompat.preimageRestrictScalars g ⊤`, the
ascription of the source ring being invisible to `rfl`; and
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop g = Iso.refl _`, that comparison being
`NatIso.ofComponents (fun _ => Iso.refl _)`. The mirror's pointwise homology-preservation
hypothesis is `fun _ => inferInstance`, so it survives in none of the statements.

***What is proved***, in `PreimageSectionsCollapseMirrorScalars.lean`, with nothing assumed of `g`,
of the degree or of the object, and no affineness anywhere (axioms: `propext`, `Classical.choice`,
`Quot.sound`):

* `Stacks.EdgeCompat.rightDerivedCompIsoTop_app_eq_restrictScalarsRightDerivedIso` — the one
  crossing, made between two **isomorphisms**, where it is `rfl` in about a second;
* `Stacks.EdgeCompat.rightDerivedCompNatIsoTop_inv_app_eq_restrictScalarsRightDerivedIso` — the
  dictionary in the direction 089W inverted carries it;
* `Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
  `_restrictScalarsRightDerivedIso_inv` — **089W's factors (4) and (5) composed**: they are `Hᵈ` of
  `Stacks.EdgeCompat.preimageSectionsModelComparison`, the edge morphism of restriction of scalars,
  and restriction of scalars applied to the crossing of the two models of `RΓ(g⁻¹⊤, -)` on `X`
  alone — the place the `γ⁺` side reads, with the scalars **outside**.

*Two arrangements that time out.* The dictionary stated as
an equality of the two **isomorphisms** and proved by `Iso.ext`, and the dictionary stated at the
`hom` **component** and proved from `rightDerivedCompNatIso_hom_app_eq_rightDerivedCompIso` by one
`congrArg`: both `timeout at whnf`. The statement alone elaborates in about five seconds, so the
crossing is affordable exactly once; `Iso.ext` unifies the two isomorphism **types** a second time,
and the `congrArg`'s result type makes the same crossing again at a `whnf` on `.hom.app` of two
large terms. The general principle: a definitional crossing is paid in the
statement it is written into, and **no proof step may be asked to make it again**. The route that
works pays it once, between isomorphisms, and reaches the component by `congrArg Iso.inv`.

***Brick (i)'s instantiation, solved for the factor the chase consumes, and a remark on
invertibility.*** The chase meets the crossing of the two
models of `RⁿΓ(U, -)` on the open subscheme **twice** — positively as factor (4), inverted as
factor (1) — so brick (i)'s instantiation
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom` has
to be solved for its last factor. The cheap way is the inverted one:

* solving for it **uninverted** needs `…TopDegreeBaseChange.openSubschemeBareComparisonOf` to be
  invertible, and that is **not available**: the instance
  `((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙ RΓ(U, ⊤, -)).IsRightDerivedFunctor`
  `(openSubschemeBareUnitOf X U)` is reported `failed to synthesize`, and the **pre**composition
  counterpart of `…HomologyComparison.exactPostcomposeUnit` that would supply it does not exist in
  the library. It could be built: its one nontrivial input, that restriction to an open carries a
  K-injective complex to a K-injective complex, is available at ringed-space generality as
  `Stacks.PseudoCoherence.isKInjective_restrictComplex`. It is simply **not needed**;
* solving for the crossing **inverted** needs none of it.
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` and
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` are isomorphisms by
  construction, so transposing brick (i) at its three isomorphism factors moves the two `Hⁿ`
  prefixes to the right with **no inverse of either taken**. A chase that meets the crossing
  positively transposes its own equation instead of inverting a prefix.

So `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction`
(`OpenSubschemeSingleModelCrossing.lean`) is proved, with nothing assumed of `X`, of `U`, of the
module or of the degree (axioms: `propext`, `Classical.choice`, `Quot.sound`): the crossing on `U`
inverted, at the restricted module, is `compRightDerivedNatIso` inverted, the crossing on `X`
inverted, `Hⁿ` of `openSubschemeBareComparisonOf` at `M[0]`, and `Hⁿ` of derived global sections of
`U` applied to `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. Its
`openSubschemeBareComparisonOf` factor is exactly where the gluing
`…openSubschemeSectionsComparisonLE_eq_modelComposition` enters.

***What steps 1 to 5 still owe, and the one place the five-step order is optimistic.***
Step 1 — moving the two module transports across the crossings by naturality — needs a
spelling crossing. By the statement of
`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`
(`RestrictPullbackTopDegreeBridge.lean`), the upstairs transport is
`Stacks.Modules.restrictPullbackObjIso h' hle F'` (`PullbackInvertible/Basic.lean:116`), an
isomorphism
`(Scheme.Modules.restrict ((Scheme.Modules.pullback h').obj F') (f''⁻¹W).ι) ≅`
`(Scheme.Modules.pullback (h'.resLE (f'⁻¹V) (f''⁻¹W) hle)).obj (F'|_{f'⁻¹V})` — exactly ψ's module
`N` against `((h')^*F')|_{f''⁻¹W}`, so that assignment is right. But it is written with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, and brick (i)'s solved form sits at
`…TopDegreeBaseChange.openSubschemeRestrictionOf`, which is the ringed-space
`…HigherDirectImage.moduleRestriction` ascribed. Those two are **equal functors** and **not
interchangeable for instance synthesis** —
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` — so step 1 carries a crossing the
five-step order does not mention. It is in **argument position**, which is where this subtree pays
such a crossing affordably (`…singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq` is the
precedent), but it is a step and not a substitution.

Steps 2 and 3 are therefore: the 089W factors (4)+(5) composite, then
`singleCompDerivedOpenSubscheme_inv_app_restriction` transposed for factor (4) and applied directly
for factor (1), with `restrictPullbackObjIso` carried across by naturality and
`openSubschemeBareComparisonOf` rewritten through the gluing — and with `Hᵈ` commuted past
`restrictScalars.mapDerivedCategory` by the **naturality** of
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`, which has no component
formula. Factor (1)'s module half involves the pullback square `hsq` (but see the correction
below). The match does not close, the composite identity
`T = Γ(V, Θ) ≫ res_W` is not proved, and **no `@[stacks 0EX3 "(c)"]` is placed anywhere**.

*The two tails cannot be applied to an element in a written-out statement.* Doing so exhausts the
elaborator's recursion budget, which is why `…_of_tail` carries them as variables fixed by the two
factorisations rather than written out. The morphism-level identity is what must be proved, and
then applied at `b`.

***Step 1 at both factors, and what the pullback square buys at factor (1).*** In
`OpenSubschemeModelCrossingTransport.lean`, with
nothing assumed of the schemes, the opens, the modules, the degree or the transport (axioms:
`propext`, `Classical.choice`, `Quot.sound`):

* `…TopDegreeBaseChange.openSubschemeRestrictionOf_eq_restrictFunctor` — the spelling pair, crossed
  once. It is `…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` inverted,
  `openSubschemeRestrictionOf` being the ringed-space `moduleRestriction` ascribed. **It is a
  transport and not a substitution**: passing
  `Stacks.Modules.restrictPullbackObjIso h' hle F'` where the `openSubschemeRestrictionOf` reading
  of its source is expected is a reported type mismatch, so the two spellings are not
  interchangeable for the elaborator either, and not only for instance synthesis.
* `…TopDegreeBaseChange.openSubschemeRestrictionPullbackIso` — the **upstairs** transport at brick
  (i)'s spelling: `restrictPullbackObjIso` with its source read at `openSubschemeRestrictionOf`,
  the crossing made once by `CategoryTheory.eqToIso` on the functor equality, which is the pattern
  `…SchemeHigherDirectImage.higherDirectImageRestrictIso` already uses.
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction` — **brick (i)
  at the module factor (4) sits at.** The crossing on `U''` inverted, read at
  `(h'.resLE U' U'' hle)^*(F'|_{U'})`, is the classical right derived functor of sections applied
  to the transport inverted, then brick (i)'s four factors, then derived sections of `U''` applied
  to the transport. The transport being an isomorphism there, the naturality square solves for the
  component at the `ψ` side's own module.
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_rightDerived_map_comp_inv_app` — **brick (i)
  carried across an arbitrary morphism of the module**, which is the form factor (1) consumes, with
  no inverse of the transport taken anywhere.

*Read off the statement of `…unit_resLE_eq_restrictFunctor_map_unit`:* factor
(1)'s downstairs transport is **not an isomorphism**, and `hsq` does not make it one. The five
comparisons' third factor is `(h' ∣_{U'})_*` of the unit of
`(X''.homOfLE e)^* ⊣ (X''.homOfLE e)_*` for the inclusion `f''⁻¹W ≤ (h')⁻¹(f'⁻¹V)`; that unit is
restriction to a smaller open and is invertible only when the inclusion is an equality. The square
gives `(h')⁻¹(f'⁻¹V) = (f'')⁻¹(h⁻¹V)` and `W` is a *proper* affine open of `h⁻¹V`, so the inclusion
stays proper and the unit stays non-invertible. What `hsq` buys at factor (1) is the `≤` itself —
the situation's `e` is `preimage_le_preimage_of_isPullback hsq hWV` — and in fact less than that:
`…TopDegreeBaseChange.preimage_le_preimage_of_isPullback` (`BaseChangeAffineOpenSquare.lean`) uses
only `hsq.w`, the square's commutativity, and nothing cartesian. So factor (1)'s module half does
not obtain an isomorphism from `hsq`; the right move is naturality in the direction that needs no
inverse, which the fourth declaration above is, and which is available because the `ψ` tail
carries the transport in exactly the position in front of the crossing that naturality consumes.

***Step 5's crossing of `Hᵈ` past the scalars is proved generically, and needs no
instantiation.*** `StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map`
(`Homology/DerivedCategory/MapHomologyIso.lean`) is the naturality of
`mapDerivedCategoryHomologyIso` solved for the one factor a calculation meets: for `F` exact and
`φ` a morphism of `D(C)`, `F` of `Hⁱ(φ)` is the comparison inverted, `Hⁱ` of `F` read on derived
categories applied to `φ`, and the comparison again. No hypothesis on `φ`, on the degree or on the
objects, and no component of the comparison is named — which is all that transformation allows,
being built by `CategoryTheory.Localization.liftNatIso`. **It applies at the chase's own exact
functor directly**: `Stacks.EdgeCompat.preimageRestrictScalars g V` has every instance the brick
asks for synthesised — additivity, both exactness halves, and `HasDerivedCategory` on the two
module categories under `HasDerivedCategory.standard` — and the application elaborates in about a
fifth of a second. So no instantiation at the scalars is declared, and none is needed.

*Two duplicates.*
`AlgebraicGeometry.ProjectiveCoherentImage.restrictFunctorIso`
(`ProjectiveCoherentImage/Basic.lean`) is the comparison of the same two spellings of restriction
as an **isomorphism**, built by `SheafOfModules.pushforwardCongr`, where
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` (`SchemeRestriction.lean`) proves
them **equal**; the equality subsumes it. And
`AlgebraicGeometry.ProjectiveCoherentImage.restrictedMorphism_eq` in that same file is
`…SchemeHigherDirectImage.toShHom_morphismRestrict` (`SchemeRestriction.lean`) inverted, the two
proofs differing only in which side is cancelled against the monomorphism.

***Factor (1) does not need its transport inverted; what blocks it is a different step.*** Two
questions arise for factor (1), and the answers are: the invertibility is **not**
needed, and what is unavailable is the **naturality of [Stacks, Tag 01XK] at the transport**.

*The invertibility is not needed.* Write `μ` for the transport — the five comparisons of
`…unit_resLE_eq_restrictFunctor_map_unit`, from
`(Scheme.Modules.restrictFunctor (f'⁻¹V).ι).obj ((h')_*(h')^* F')` to `g_* N`. The `ψ` tail meets
`μ` in the **forward** direction: `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE`
(`TopDegreeHeadMatching.lean`) fixes the `v` of `psi_side_eq_sections_unit_comp_tail` as
`…SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` inverted followed by
`R^d(f' ∣_ V)_*(μ)`, so `μ` occurs applied and never inverted; and
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_rightDerived_map_comp_inv_app` takes the
transport as an **arbitrary** morphism. So the non-invertibility above is irrelevant to
factor (1), and no inverse of `μ` is needed anywhere.

*What is needed, and it is not a library gap.* That lemma's left-hand side is
`((sectionsOverOpen (f'⁻¹V : Scheme) ⊤).rightDerived d).map μ` followed by the crossing — `μ` under
the **upstairs** cohomology of `f'⁻¹V`. The `ψ` tail has it under the **downstairs**
`Γ(V, R^d(f' ∣_ V)_*(-))`, and the bridge between those two readings is [Stacks, Tag 01XK],
`…AffineBaseSections.cohomologyIsoGlobalSectionsRightDerivedPushforward`. Its naturality is proved
in both directions — `…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward`
`_hom_naturality` and `…_inv_naturality` (`AffineOpenCohomologyNaturality.lean`) — but **only for a
morphism of the full subcategory of quasi-coherent modules**, and `μ`'s source is not known
quasi-coherent: `(h')_*` preserves quasi-coherence by [Stacks, Tag 01XJ] only for a quasi-compact
quasi-separated `h'`, and the situation assumes **nothing** of `h`, hence nothing of its base
change `h'`, and assuming `h` quasi-compact and quasi-separated would change the statement.
**The missing input is not a missing declaration**: the degeneration
`…AffineBaseSections.preservesLeftHomologyOf_moduleGlobalSections` says that `Γ(V, -)` kills the
higher cohomology of the pushforwards of an injective resolution, which over an affine `V` is
[Stacks, Tag 01XB] applied to the higher direct images and needs them quasi-coherent. At a
non-quasi-coherent coefficient the Leray spectral sequence does not degenerate and the comparison
is false.

*The blocker localises to exactly one of 01XK's two halves, as their statements show.*
`…AffineBaseSections.rightDerivedModuleGlobalSectionsIso` — the first half,
`R^n Γ(X, -) ⋙ res_{f^♯} ≅ R^n(f_* ⋙ Γ(S, -))` — carries **no** hypothesis at all: not
quasi-coherence, not quasi-compactness, not quasi-separatedness, not affineness of the target, and
it is a natural isomorphism on all modules. So `μ` crosses that half for free, and what degenerates
is only Grothendieck's half, `…AffineBaseSections.rightDerivedCompositionNatIso` at
`(qcohInclusion X', (f' ∣_ V)_*, Γ(V, -))`. So the refusal is sharp: factor (1) can be moved by
brick (i) only at a coefficient where that one comparison is available, and `μ`'s source is not
such a coefficient. **Nothing is assumed to get past this** — not that
`f''⁻¹W = (h')⁻¹(f'⁻¹V)`, not `W = h⁻¹V`, and no hypothesis on `h`, on `h'` or on the opens. The
alternative is to arrange the match with `μ` left **downstairs**, crossing
01XK only at `g_* N`, where the `ψ` tail already crosses it and where the quasi-coherence is
`inferInstance` from `isAffineHom_resLE_of_isPullback`; that would put brick (i)'s application for
factor (1) at a different coefficient from the one the inventory names (see below).

*A `private` declaration blocking reuse.* All three of
`rightDerivedModuleGlobalSectionsIso`, `preservesLeftHomologyOf_moduleGlobalSections` and
`rightDerivedCompositionNatIso` are `private` in
`HigherDirectImageQcqs/AffineBaseSections.lean`, so the hypothesis-free first half of 01XK cannot
be named from another module even though it is exactly what a chase at a non-quasi-coherent
coefficient would use.

***What the match and the composite identity still owe.*** Step 1 and step 5's scalars crossing are
performed; **steps 2, 3 and 4 are not**, and neither is the composite identity. What is left is the
chase itself: the 089W factors (4)+(5) composite of
`PreimageSectionsCollapseMirrorScalars.lean` — whose degreewise functor is brick (i)'s on the nose,
four `rfl`s, so that no crossing is owed between them — then brick (i) at factor (4) with
the chase's own equation transposed, the crossing being an isomorphism there so that no inverse of
`openSubschemeBareComparisonOf` is taken, then factor (1) once the question above is settled, with
`openSubschemeBareComparisonOf` rewritten through
`…openSubschemeSectionsComparisonLE_eq_modelComposition`
(`OpenSubschemeModelCompositionGlue.lean`), and factors (2), (3) and (5) settled against step 2a,
brick (ii) and the LE Leray compatibility. The match does not close, the composite identity
`T = Γ(V, Θ) ≫ res_W` is not proved, and **no `@[stacks 0EX3 "(c)"]` is placed anywhere**.

***Factor (4) of the match is performed, and factor (5) with it.***
`…TopDegreeBaseChange.factorFourFive_comp_openSubschemeCrossing_eq`
(`OpenSubschemeFactorFourJoin.lean`), with nothing assumed of `h'`, of the two opens, of `F'` or of
the degree (axioms: `propext`, `Classical.choice`, `Quot.sound`): the 089W factors (4)+(5)
composite, then the restriction of scalars along `g^♯` applied to brick (i)'s six factors, is `Hᵈ`
of `Stacks.EdgeCompat.preimageSectionsModelComparison g ⊤` at the module's single complex followed
by the edge morphism of that restriction of scalars. Factor (5) is one of the two factors the
composite joins, so 2b(B)'s factor (5) is closed by the same declaration.

*How it is proved.* The mirror's standing crossing is brick (i)'s on the nose, by **six** `rfl`s,
each holding on its own: `(f''⁻¹W : Scheme).toRingedSpace` against
`…toSheafedSpace`; `(opensMap g).obj ⊤` against `⊤`; and `…DerivedSectionsLeray.sectionsOverOpen`,
`…derivedSectionsOverOpen`, `…derivedSectionsOverOpenUnit` and the whole
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` built out of them. The join
**transposes the chase's own equation**, as described above: brick (i) factorises
the crossing's *inverse* and the `ψ` side meets the crossing *forward*, so brick (i)'s six factors
are postcomposed and cancel against it by a private cancellation at variables of abstract
categories, and **no inverse of `openSubschemeBareComparisonOf` is taken**. The collapse mirror's
index functor `E` — which it carries only because
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` does — is instantiated at `𝟭 _` with `Z` the
module, where `E.obj Z` is the module by definition and no transport arises. Following the
ordering principle, the crossing's own spellings are written first, and the statement and proof
check together in about six seconds.

***Factor (1): the `μ`-downstairs route is the arrangement the `ψ` side already has, and it is
blocked too.*** By `psi_side_eq_sections_unit_comp_tail`, keeping `μ` downstairs and crossing
[Stacks, Tag 01XK] only at `g_* N` **is not a rearrangement to be made: it is the arrangement the
`ψ` side is stated at.** `T`'s leading factors there are
`(…AffineBase.moduleGlobalSections (V : Scheme)).map v`, then
`(cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app`
`⟨g_* N, inferInstance⟩`, then the restriction of scalars along `(f' ∣_ V)^♯` of
`Stacks.DerivedIndexing.rightDerivedIso` inverted and the 089W block. So 01XK is crossed at exactly
**two** coefficients in the whole `ψ` side — `(Scheme.Modules.restrictFunctor (f'⁻¹V).ι).obj F'` at
the head, in `affineOpenCohomologyIsoSectionsOf_inv_eq`, and `g_* N` in the tail — both with
quasi-coherence `inferInstance`, and **`μ` never crosses 01XK**. The obstruction above,
01XK at a non-quasi-coherent coefficient, therefore does **not** arise on this route.

What arises instead is the same blocker from the other side. With `μ` downstairs, factor (1)'s
crossing is met at the coefficient `g_* N` preceded only by factors at that same coefficient, and
**neither form of brick (i) reaches it**:

* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction`
  (`OpenSubschemeSingleModelCrossing.lean`) needs the coefficient to be
  `(openSubschemeRestrictionOf X' (f'⁻¹V)).obj M'`, and `g_* N` is not: the fact
  that `(f.resLE V U e)_*(F|_U)` is not `(f_* F)|_V` once `U < f⁻¹V` applies verbatim;
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_rightDerived_map_comp_inv_app`
  (`OpenSubschemeModelCrossingTransport.lean`) needs
  `((…DerivedSectionsLeray.sectionsOverOpen (f'⁻¹V : Scheme) ⊤).rightDerived d).map μ`
  **immediately in front of** the crossing — `μ` read *upstairs* — and getting `μ` there from
  downstairs is exactly the naturality of 01XK at `μ`.

**So the two routes are mutually exclusive.** The `μ`-upstairs route reaches brick (i) and needs
01XK's naturality at `μ`; the `μ`-downstairs route never needs 01XK at `μ` and *for that very
reason* cannot reach brick (i). The morphism named is `μ` itself — what
`unit_resLE_eq_restrictFunctor_map_unit` (`TopDegreeHeadMatching.lean`) leaves after its leading
`(Scheme.Modules.restrictFunctor (f'⁻¹V).ι).map` of the ordinary unit, from
`(restrictFunctor (f'⁻¹V).ι).obj ((h')_*(h')^* F')` to `g_* N` — and in the situation's own
variable context:

* `((Scheme.Modules.pullback h').obj F').IsQuasicoherent` **is** `inferInstance`;
* `SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward h').obj`
  `((Scheme.Modules.pullback h').obj F'))` is **`failed to synthesize`**;
* so is the same for its restriction along `(S.f' ⁻¹ᵁ V).ι`, which is `μ`'s source;
* and `…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality` and
  `…_inv_naturality` (`AffineOpenCohomologyNaturality.lean`) are stated for `φ : A ⟶ B` with
  `A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory`, so **both** ends must be
  quasi-coherent, not just the target.

Nothing is assumed to get past this: no hypothesis on `h`, on `h'` or on the opens, not
`W = h⁻¹V`, not `f''⁻¹W = (h')⁻¹(f'⁻¹V)`. *There is no third position for `μ`:* brick (i) is a
**pre**composition statement, so the crossing its right-hand side carries is intrinsically at a
coefficient in the image of the restriction functor; the only way to a coefficient outside that
image is the crossing's naturality along a morphism out of it, and the only such morphism the
situation supplies is `μ`. **So factor (1) cannot be reached by brick (i) at all.** The remaining
possibility is to make the match at factor (1) **without brick (i)** — the crossing at `g_* N`
matched against the `γ⁺` side's own factors — which is what is done below.

***The bare comparison through the gluing: the gluing cannot be solved for it, and one factor
stops it.*** `…openSubschemeSectionsComparisonLE_eq_modelComposition` reads
`A ≫ B = C₁ ≫ C₂ ≫ C₃ ≫ C₄ ≫ D` with `D` the bare comparison whiskered by the two scalars layers.
Of the four prefix factors, `C₃` (`…derivedSectionsImageTopIso` inverted, whiskered) and `C₄`
(`…derivedScalarsReconciliation`) are isomorphisms by construction, and `C₁`
(`Stacks.EdgeCompat.preimageSectionsModelComparison f V`) is one **unconditionally** —
`Stacks.EdgeCompat.isIso_preimageSectionsModelComparison`
(`OpenSubschemeBareComparisonThroughGluing.lean`), by
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` at the registered
`Stacks.EdgeCompat.isRightDerivedFunctor_preimageSectionsCompUnitComp`, the comparison being a
`rightDerivedDesc` between two right derived functors of the *same* degreewise functor
(`inferInstance` does not find it). But `C₂`, the `α` layer
`Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison f V e`, is **not** invertible —
it is `CategoryTheory.Functor.rightDerivedNatTrans` along the degreewise
`Stacks.EdgeCompat.preimageSectionsRestrictSource f V e`, the restriction of sections from `f⁻¹V`
down to `U`, which at a proper `U < f⁻¹V` is not invertible (as for
`…preimageSectionsOpenSubschemeLE`), and `IsIso` of it is `failed to synthesize`.
**And the match meets the gluing at a proper `U`**: its instance is
`(f, V, U, e) := (h', f'⁻¹V, f''⁻¹W, hle)`, whose `f''⁻¹W ⊊ (h')⁻¹(f'⁻¹V)` is the very thing that
makes the transport of the match a morphism and not an isomorphism.

So what is proved is the gluing solved for its last **four** factors,
`…TopDegreeBaseChange.alphaLayer_comp_openSubschemeBareComparisonOf_eq`, taking only the one
available inverse and leaving `C₂`, `C₃`, `C₄` and `D` in the order the gluing writes
them, with nothing assumed of `f`, of `V`, of `U` or of the module (axioms: `propext`,
`Classical.choice`, `Quot.sound`). **A chase that wants the bare comparison must carry the `α`
layer with it, in the forward direction**; "rewrite the bare comparison through the gluing" is not
a substitution and cannot be made one.

***What the match still owes.*** Factors (4) and (5) are performed and factor
(3)'s two bricks are joined at the level of transformations; factors (1) and (2) are not performed,
factor (3)'s passage to `Hᵈ` and its left inverse is not, and neither is the composite identity.
The shape the remaining chase has is
as follows: the join's right-hand side ends at `Hᵈ` of
`Stacks.EdgeCompat.preimageSectionsModelComparison g ⊤` at a component, the gluing's left-hand side
carries that same transformation whiskered, and brick (ii)
`…DerivedSectionsLeray.derivedPreimageSectionsCompIso_hom_comp_lerayComparison`
(`LerayCompositeAbsolute.lean`) delivers `preimageSectionsModelComparison S.f' V` whiskered on the
`γ⁺` side — so the three meet at one transformation at two instances, and the crossing between `Hᵈ`
of a component and the whiskered transformation is
`StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map`, proved generically and needing no
instantiation.

*Factor (3)'s two bricks are joined, at the level of transformations*, in
`…TopDegreeBaseChange.lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq`
(`LerayCompositeOpenSubschemeJoin.lean`), with nothing assumed of the two morphisms, of the opens
or of the module (axioms: `propext`, `Classical.choice`, `Quot.sound`). What stood between brick
(ii) and the `LE` Leray compatibility was the **absolute** Leray comparison
`…DerivedSectionsLeray.lerayComparison h' (f'⁻¹V)`, which both of them name and the match wants in
neither form; it is eliminated by postcomposing brick (ii) with
`…openSubschemeLerayComparisonLE` whiskered, so that the two Leray factors fuse by
`CategoryTheory.Functor.whiskerRight_comp` and the `LE` compatibility replaces the fused pair. The
only inverse taken is `…DerivedSectionsLeray.derivedPreimageSectionsCompIso`'s, which brick (ii)
already writes inverted and which is unconditional; neither model comparison and neither
`rightDerivedDesc` is inverted. What is left of factor (3) is the transposition of that join
through `Hᵈ` and through the **left inverse** of `Hᵈ(lerayComparison g ⊤)` that
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` hands in as a hypothesis — the
`ψ` side reads factor (3) only in that form — and that transposition is not performed here.

The match does not close, the composite identity `T = Γ(V, Θ) ≫ res_W` is not proved, and **no
`@[stacks 0EX3 "(c)"]` is placed anywhere**.

***Factor (1) is matched, without brick (i).*** The match can be made at factor (1) with no
brick (i) at all. The exact functor factor (1)'s own surroundings supply is the
restriction of scalars along `(f' ∣_ V)^♯`, which the `ψ` side applies to the **whole** of
[Stacks, Tag 089W] inverted, so it sits on the **outside** of factor (1) — which is the collapse
mirror's shape and not brick (i)'s. The mirror already used for factor (4),
`Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
`_restrictScalarsRightDerivedIso_inv` (`PreimageSectionsCollapseMirrorScalars.lean`), applies to
factor (1) verbatim at the morphism `q := f' ∣_ V` **out of** the open subscheme and the open `⊤`
of its target, where `moduleGlobalSections (f'⁻¹V : Scheme)` is `sectionsOverOpen` at
`(opensMap q).obj ⊤` and `ModuleCat.restrictScalars (f' ∣_ V).appTop.hom` is
`Stacks.EdgeCompat.preimageRestrictScalars q ⊤`, both `rfl`. So the brick-(i) obstruction comes
only from looking for a **pre**composition statement at a factor whose exact functor is
postcomposed; this route needs no hypothesis on `h`.

*What is proved*, in `FactorOneCollapseMirror.lean`:

* `…TopDegreeBaseChange.restrictScalars_singleCompDerivedSectionsTop_inv_app_eq` — **the mirror
  solved for factor (1).** Restriction of scalars along `q^♯` applied to the crossing of the two
  models of `RⁿΓ(Sq, ⊤, -)` **inverted** at `M` is
  `…AffineComparison.restrictScalarsRightDerivedIso q M n` — which is 089W's own factor (5) —
  then the crossing of the two models of `Rⁿ(q_* ⋙ Γ(B, ⊤, -))` inverted, then `Hⁿ` of
  `Stacks.EdgeCompat.preimageSectionsModelComparison q ⊤` and the edge morphism of the
  restriction of scalars. `M` is **arbitrary**: it is not assumed to be a restriction from an
  ambient scheme, which is the hypothesis both forms of brick (i) need at this factor and
  neither gets. Nothing is assumed of `q`, of `M` or of `n` (axioms: `propext`,
  `Classical.choice`, `Quot.sound`). The transposition takes `.inv` of the two crossings and of
  nothing else, so **neither `preimageSectionsModelComparison` nor the edge morphism of the
  restriction of scalars is inverted** and the two invertibility results for them —
  `Stacks.EdgeCompat.isIso_preimageSectionsModelComparison` and
  `…HomologyComparison.isIso_derivedHomologyComparison_mapDerivedCategory` — are not used.
* `…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` — **factor (1)
  against the `γ⁺` side's own factors.** The crossing of the two models of
  `Rⁿ(q_* ⋙ Γ(B, ⊤, -))` is the factor the `γ⁺` prefix
  `sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq`
  (`TopDegreeCrossingSections.lean`) is written at — the same term, the two units at that
  spelling being one (`Stacks.EdgeCompat.derivedPreimageSectionsUnitComp` is an `abbrev` for
  `…DerivedSectionsLeray.derivedPreimageSectionsUnit`) — so composing the two **eliminates it**:
  the edge morphism of `RΓ(B, ⊤, -)` at `Rq_*((E Z)[0])` followed by `Γ(B, ⊤, -)` of the crossing
  of the two models of `Rq_*` is the Leray left inverse, the two mirror factors, factor (1)
  forward, factor (5), Grothendieck's comparison at `(q_*, Γ(B, ⊤, -))` inverted, and
  `Γ(B, ⊤, -)` of the comparison of the two indexings. Nothing is assumed of `q`, of `E`, of `Z`
  or of `n` (same three axioms); the two hypotheses are its inputs' own — `hpl` and the
  unconditional Leray left inverse.

***The degeneration `hpl` is available at the coefficient the `ψ` side crosses 01XK at, in the
situation's own variable context.*** This is what makes the route usable rather
than merely available. `hpl` is Grothendieck's pointwise homology-preservation hypothesis at the
pair `((f' ∣_ V)_*, Γ(V, ⊤, -))`, and
`Stacks.Cohomology.AffineBase.preservesLeftHomology_pushforward_injectiveResolution (S.f' ∣_ V)`
`(g_* N) S.d` inhabits it **at exactly the `sectionsOverOpen (V : Scheme).toSheafedSpace ⊤` /
`modulePushforward (S.f' ∣_ V).toLRSHom.toShHom` spelling the statement asks for**. Its
three instances are all present: `QuasiCompact (S.f' ∣_ V)` and `QuasiSeparated (S.f' ∣_ V)` are
`inferInstance` from `S.quasiCompact_f'` and `S.quasiSeparated_f'`,
`IsAffine (V : Scheme)` is the situation's hypothesis, and `(g_* N).IsQuasicoherent` is the
`inferInstance` `psi_side_eq_sections_unit_comp_tail` already passes to 01XK. **So no hypothesis
on `h`, on `h'` or on the opens is added, and `μ`'s source is never visited**: the route asks for
no naturality of 01XK along `μ`, which is the step the obstructions above turn on.

*Four possible routes for factor (1), compared.*

1. *Bringing the `γ⁺` side to `g_* N` so both sides meet where quasi-coherence is free:* **this is
   what the pair above does**, in the only sense available. The `γ⁺` prefix
   `sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` is
   stated at an arbitrary `(f, V)` and an arbitrary coefficient, so it instantiates at
   `((f' ∣_ V), ⊤)` and at `g_* N` — the open subscheme read as a scheme in its own right and the
   coefficient the `ψ` side already crosses 01XK at. What is **not** available
   is reading `Γ(V, Θ)` in the derived-sections model at the `γ⁺` side's own coefficient
   `(h')_*(h')^*F'` on `X'`: that needs the prefix `Pre` of
   `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` **inverted**, hence the
   edge morphism of `RΓ(V, -)` invertible at `Rf'_*(((h')_*(h')^*F')[0])`, which is the same
   degeneration as 01XK there and needs `h'` quasi-compact and quasi-separated. The pair above
   never inverts `Pre`; it instantiates the prefix at the other pair instead.
2. *Factoring `μ` through a quasi-coherent object, or deferring its crossing:* **this does not
   work, and it is not needed.** A factorisation `μ = α ≫ β` through a quasi-coherent `Q` moves `β`
   upstairs by
   01XK's naturality at `β` and leaves `Γ(V, R^d(f' ∣_ V)_*(α)) ≫ 01XK⁻¹[Q]`, whose own step is
   01XK's naturality at `α` — at the unchanged, unchanged-able source `μ`'s source. The source is
   fixed, so no factorisation reaches it; the deferral is a deferral and not an elimination.
   What the pair above does instead is leave `μ` exactly where
   `psi_side_eq_sections_unit_comp_tail` puts it, in front of 01XK, and match everything **after**
   01XK.
3. *The collapse mirror:* **this is the route.** See above.
4. *The match at the level of the units, before either side's `rightDerivedDesc`:* **not needed,
   and the pair above is cheaper.** Both of factor (1)'s crossings and both of Grothendieck's
   comparisons are isomorphisms by construction, so the whole match is transposition; descending
   to the units would re-derive their characterising factorisations, which is what the mirror's
   own `hθ` already consumed once.

*On the `private` copy of 01XK.* The `private` declarations of
`HigherDirectImageQcqs/AffineBaseSections.lean` noted above do not prevent naming the
hypothesis-free half of [Stacks, Tag 01XK]. The
copy the `ψ` side actually uses is `Stacks.Cohomology.AffineBase`'s — this file opens that
namespace and not `Stacks.AlgebraicGeometry.HigherDirectImageQcoh` — and in
`AffineCohomologyVanishing/AffineBase.lean` **all four of the pieces are `public`**:
`sectionsRestrictionIsoTop` (which is [Stacks, Tag 01EZ] over the whole space, and is declared
*before* the `QuasiCompact`/`QuasiSeparated`/`IsAffine` variables, so it carries no hypothesis at
all), `rightDerivedCompNatIso`, `preservesLeftHomology_pushforward_injectiveResolution` and
`affineBaseHigherDirectImageIso`. The private triple is the **duplicate** copy. So 01XK's two
halves are both nameable, which is what the pair above uses: the free half appears as
`…AffineComparison.restrictScalarsRightDerivedIso` (089W's factor (5)) and Grothendieck's half as
`rightDerivedCompNatIso` with `hpl` carried as a hypothesis.

***What the match still owes.*** Factors (1), (4) and (5) are performed and factor
(3)'s two bricks are joined at the level of transformations; **factor (2) is not performed**,
factor (3)'s passage to `Hᵈ` and through the left inverse
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` hands in is not, and neither
is the composite identity `T = Γ(V, Θ) ≫ res_W`. What factor (1)'s match leaves standing: the
pair above matches factor (1) against the `γ⁺` prefix **at
`((f' ∣_ V), ⊤)`**, while step 2a and
`prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` read the `γ⁺` side at
`(f', V)` on `X'`; the crossing between those two instantiations is the `LE` family at
`U = f'⁻¹V`, `e = le_rfl`, where the degreewise crossing is the restriction of sections from
`f⁻¹V` to itself — the one place the `LE` crossing ought to be an isomorphism, since it fails to
be one exactly at `U < f⁻¹V`.

*That invertibility is not found by instance search, at any of three steps.* At
`e := le_refl (f ⁻¹ᵁ V)` none of
`IsIso (…DerivedSectionsLeray.sectionsOverOpenRestrictLE X.toRingedSpace (le_refl U))`,
`IsIso (…TopDegreeBaseChange.preimageSectionsOpenSubschemeLE f V (le_refl (f ⁻¹ᵁ V)))` and
`IsIso (…TopDegreeBaseChange.openSubschemeSectionsComparisonLE f V (le_refl (f ⁻¹ᵁ V)))` is
synthesisable. The reason is visible in the construction and the statement is not hard:
hard: `sectionsOverOpenRestrictLE X h` is `PresheafOfModules.restriction` along `(homOfLE h).op`
whiskered by the forgetful functor, and its target is read over `Γ(U', 𝒪_X)` through
`ModuleCat.restrictScalars (sectionsRingRestrict X h)` — at `h = le_rfl` that ring map is the
identity *mathematically* and not `RingHom.id` *syntactically*, so neither the component nor the
scalars layer is the identity to instance search.

***All three steps are proved***, in `LerayOpenSubschemeCrossingInvertible.lean`, with
nothing assumed of `f` or of `V` (axioms: `propext`, `Classical.choice`, `Quot.sound`). The route
is the presheaf functoriality at
`(homOfLE le_rfl).op = (𝟙 _).op`, then
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`, which is what
`Stacks.EdgeCompat.isIso_preimageSectionsModelComparison`
(`OpenSubschemeBareComparisonThroughGluing.lean`) takes for a comparison between two right derived
functors of one degreewise functor — together with the K-injective
criterion:

* `Stacks.Cohomology.DerivedSectionsLeray.isIso_sectionsOverOpenRestrict_le_refl` — restriction of
  sections from an open to itself is invertible. The whole content is that `homOfLE` of any proof
  of `W ≤ W` **is** `𝟙 W` (proof irrelevance in a poset) together with Mathlib's
  `CategoryTheory.PresheafOfModules.map_id`, which says the restriction along `𝟙` is the inverse of
  `CategoryTheory.ModuleCat.restrictScalarsId'` — an isomorphism, not an identity, exactly because
  the scalars layer is not `RingHom.id`. Three lines.
* `…TopDegreeBaseChange.isIso_preimageSectionsRestrictLE_le_refl` and
  `…isIso_preimageSectionsOpenSubschemeLE_le_refl` — the degreewise crossing at `U = f⁻¹V`.
  *The composite of its three factors is not left to instance search:*
  `IsIso` of each factor alone is found and `IsIso` of the two-factor composite is **not**, because
  `CategoryTheory.IsIso.comp_isIso` is keyed on the composite's middle object and the middle
  objects here sit at definitionally equal but differently spelled functors — the `appLE`-versus-
  composite reading of the scalars, and `sectionsOverOpen X (U.ι ''ᵁ ⊤)` against
  `sectionsOverOpen X U`. `CategoryTheory.IsIso.comp_isIso'` with the three factors by hand runs
  at default transparency and closes it.
* `…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeUnitOfNatTransUnit` — **the general
  brick.** Inverting the derived
  crossing needs its *target* to be a right derived functor of degreewise sections over `f⁻¹V`,
  and the target has an exact functor **pre**composed, namely restriction to the open subscheme.
  The precomposition counterpart of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` is absent
  from the library, as noted in the paragraph on `openSubschemeBareComparisonOf` above, and it is
  not declared here: the K-injective criterion
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`
  `.isRightDerivedFunctor_of_isIso_app_isKInjective` is applied **directly**, and the one
  nontrivial input is the one named there — that restriction to an open carries a
  K-injective complex to a K-injective complex, [Stacks, Tag 08BS]. In this subtree's spelling that
  is `…TopDegreeBaseChange.isKInjective_mapHomologicalComplex_openSubschemeRestrictionOf`, and it
  is free: `…TopDegreeBaseChange.openSubschemeRestrictionOf X U` **is**
  `ExtensionByZeroModules.jStar U (structureSheafRing _)` by `rfl`, both being
  `SheafOfModules.pushforward` of the identity. The brick assumes nothing of `f`, of `V`, of `U`,
  of `RP` or of `u` beyond an invertible `α` and `RP` being a right derived functor at `u`.
  *Its invertibility hypothesis is an explicit argument and not an instance, and this is not
  cosmetic*: `preimageSectionsOpenSubschemeLE` declares its target with
  `…HigherDirectImage.moduleRestriction` and the brick types `α` with `openSubschemeRestrictionOf`
  — the first spelling pair noted above — so with `[IsIso α]` the instance is asked for at the
  brick's spelling and `IsIso (preimageSectionsOpenSubschemeLE f V ⋯)` is reported
  unsynthesisable.
* `…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeSectionsUnitLE_le_refl`,
  `…isIso_openSubschemeSectionsComparisonLE_le_refl` and
  `…isIso_openSubschemeLerayComparisonLE_le_refl` — **the two derived crossings at `U = f⁻¹V` are
  isomorphisms.** The second is the brick plus
  `isRightDerivedFunctor_iff_isIso_rightDerivedDesc`; the third is
  `…openSubschemeSectionsComparisonLE_comp_lerayComparison_eq` with the invertible
  `lerayComparison f V` cancelled on the left, so [Stacks, Tag 0D5W] is not re-proved.

*One duplicate.* That an isomorphism of
additive functors stays an isomorphism on the homotopy category — the brick's first factor — is
also proved as the `private` `mapHomotopyCategory_iso_app`
(`Homology/DerivedCategory/InverseSystem/ModuleInverseLimitGlobalSections.lean:640`), by the same
`change`-to-`NatIso.mapHomologicalComplex` step. Being `private` it is unusable from another
module.

***Which spelling the match consumes.*** The match does not meet the crossing as
"the `LE` family at `U = f'⁻¹V`, `e = le_rfl`". As the statements the match is made of show,
factor (1) is matched at `q := f' ∣_ V`: that is what
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` is instantiated at and what
`…TopDegreeBaseChange.restrictScalars_singleCompDerivedSectionsTop_inv_app_eq` and
`…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` carry, so the crossing to the `γ⁺`
side's reading at `(f', V)` is `…TopDegreeBaseChange.openSubschemeSectionsComparison` — the
**non-`LE`** crossing of `LerayOpenSubschemeDerived.lean`, at `f ∣_ V`. The two readings differ by
`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`, which is not
`rfl`, so neither is an instance of the other. Both are therefore proved, in the same file:

* `…TopDegreeBaseChange.isRightDerivedFunctor_openSubschemeUnitOfIsoUnit`,
  `…isRightDerivedFunctor_openSubschemeSectionsUnit`,
  `…isIso_openSubschemeSectionsComparison` and `…isIso_openSubschemeLerayComparison` — the same
  four statements at the `morphismRestrict` spelling, nothing assumed of `f` or of `V` (axioms:
  `propext`, `Classical.choice`, `Quot.sound`). The `α` there is an `Iso` by construction, so no
  invertibility hypothesis appears at all, and the degreewise step above is not even needed on
  this route; the restriction factor is shared on the nose, `…openSubschemeRestriction f V` being
  `…openSubschemeRestrictionOf X (f ⁻¹ᵁ V)` by `rfl`. The duplication is six lines of proof, and
  it is the cheapest available: a shared brick would have to restate the unit and the homotopy
  splitting at a variable upstairs morphism, duplicating three `def`s instead of one proof.
* By `…openSubschemeSectionsUnit_eq` the `ψ` route's unit is the same transformation as the `γ⁺`
  route's, so `…openSubschemePushforwardComparison` is invertible by the same instance and no
  second registration is made.

***The transport equation, in `FactorOnePrefixTransport.lean`, with nothing
assumed of `f`, of `V`, of the module or of the degree*** (axioms: `propext`, `Classical.choice`,
`Quot.sound`):

* `…TopDegreeBaseChange.homologyFunctor_map_openSubschemeSectionsComparison_eq` — **the crossing
  transport, at an arbitrary object `K` of `D(𝒪_X)`.** `Hⁿ` of the crossing out of `RΓ(f⁻¹V, -)`
  is `Hⁿ` of the Leray comparison of [Stacks, Tag 0D5W] for `f` over `V`, then of
  `…openSubschemeLerayComparison f V`, then the restriction of scalars along
  `AlgebraicGeometry.Scheme.Opens.topIso` crossed past `Hⁿ` and applied to a left inverse of
  `Hⁿ` of the Leray comparison for `f ∣_ V` over `⊤`, then that crossing inverted. The content is
  `…openSubschemeSectionsComparison_comp_lerayComparison_eq` read in degree `n` together with the
  naturality of `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`.
* `…TopDegreeBaseChange.homologyFunctor_map_openSubschemeSectionsComparison_single_eq` — the same
  at `K = M[0]`, with the Leray left inverse asked for at
  `((openSubschemeRestriction f V).obj M)[0]` instead of at
  `(openSubschemeRestriction f V).mapDerivedCategory.obj (M[0])`.
* `…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp` — **factor (1)'s
  match transported.** The `γ⁺` prefix at `((f ∣_ V), ⊤)`, read under the restriction of scalars
  along `topIso` and precomposed with the two Leray crossings and the single-functor crossing, is
  `Hⁿ` of `…openSubschemeSectionsComparison f V`, the single-functor crossing again,
  `mapDerivedCategoryHomologyIso`, and the restriction of scalars applied to everything
  `…FactorOneCollapseMirror`'s `prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` leaves
  after its Leray left inverse. Its two hypotheses are that lemma's own, `hpl` and `hl`.

*Three remarks on the transport, read off its statements.*

1. **The crossing is used in the forward direction on both sides, and its invertibility is not
   used at all.** The equation is not "the composition of the match with
   `openSubschemeSectionsComparison f' V` **inverted**": both statements name
   `openSubschemeSectionsComparison` with no `inv` anywhere, and
   `…isIso_openSubschemeSectionsComparison` is not among their dependencies. The four
   invertibility results of `LerayOpenSubschemeCrossingInvertible.lean` are therefore not
   used here; what they buy is that the transport may be *read* in either direction by a
   consumer, not anything the transport itself needs.
2. **The crossing that carries the source side is the Leray-target one**,
   `…openSubschemeLerayComparison f V`, not `…openSubschemeSectionsComparison f V`. The two are
   related by `…openSubschemeSectionsComparison_comp_lerayComparison_eq`, and that lemma — the
   compatibility, not either crossing alone — is the whole machinery of the transport. The only
   inverse taken anywhere is the Leray one for `f ∣_ V` over `⊤`, unconditional by
   `…DerivedSectionsLeray.isIso_lerayComparison`; it is handed in as a left inverse in the form
   `prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` asks for, and that it is also a
   right inverse — which the cancellation needs — is derived from that unconditional
   invertibility inside the proof and costs no hypothesis.
3. **An additional crossing is unavoidable here**:
   `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` at `openSubschemeRestriction f V`.
   `prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` takes a functor `E` into the
   **modules**, so every object it names is a single complex `(E.obj Z)[0]`, while
   `openSubschemeSectionsComparison f V` evaluated at `M[0]` lands at
   `(openSubschemeRestriction f V).mapDerivedCategory.obj (M[0])`. The match can therefore never
   be instantiated at a general object of `D(𝒪_X)`, and the passage between the two is the
   naturality of the Leray comparison at that isomorphism — which is what the `_single_eq` form
   above performs and what makes the two composable.

What the transport does **not** do: it relates the
two readings of the `γ⁺` **prefix**, and the `γ⁺` side's tail is read at `(f', V)` by
`prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`, whose own `Pre` is the
prefix at `(f', V)` fixed by `hPre`. Joining the two means instantiating that `hPre` from the
transport, which asks for the **target** crossing as well —
`Γ(V, Rᵈf'_* M) ⟶ res Γ(V, ⊤, Rᵈ(f' ∣_ V)_* (M|))`, the classical-model crossing that
`SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` is at the sheaf level.

***The target crossing and the edge-morphism passage the join runs on.*** Two of the three
inputs that paragraph asks for are available:

* the **target crossing**, as `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso`
  (`SectionsRestrictHigherDirectImage.lean`) — [Stacks, Tag 01E5] on sections over the open, with
  nothing assumed of `f`, of `V`, of `F` or of `d`. It also occurs welded to the
  [Stacks, Tag 01XK] factor, and so reachable only behind four hypotheses it does not need;
  `…affineOpenCohomologyIsoSections_eq` records that that identification is 01XK over `V`
  followed by it, so no second copy is made.
* the **edge-morphism passage**, as `…TopDegreeBaseChange.derivedHomologyComparison_lerayUnit_eq`
  (`OpenSubschemeLerayEdgeMorphism.lean`), with its two inputs
  `…isRightDerivedFunctor_openSubschemeLerayUnit` and `…openSubschemeLerayComparison_fac`: the
  edge morphism of the Leray comparison's target `Rf_* ⋙ RΓ(V, -)` is `Hᵈ` of
  `…openSubschemeLerayComparison f V` followed by the edge morphism of
  `…derivedPushforwardSectionsOpenSubscheme f V`. The two targets are right derived functors of
  **one** degreewise functor, `…DerivedSectionsLeray.preimageSections f V`, so this is
  `…HomologyComparison.derivedHomologyComparison_naturality_natTrans` at the **identity**
  transformation and costs no hypothesis (axioms: `propext`, `Classical.choice`, `Quot.sound`).
  It is the fourth instantiation of that brick in this subtree, at a new pair of models.

***The third input.*** The edge-morphism brick is not the only thing needed: `hPre` asks for the
composite

> the edge morphism of `RΓ(V, -)` at `Rf'_*(M[0])`, then `Γ(V, -)` of
> `…homologyFunctorDerivedPushforwardIso`.

Two routes compute it. Route 1, through the ambient collapse mirror, works once its hypothesis
`hpl` is seen to be inhabited (see the end of these notes); route 2 does not.

1. *Through the ambient collapse mirror.*
   `Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`, which
   `sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` is
   built from, computes exactly that composite — at the pair `(f'_*, Γ(V, -))` on the
   **ambient** `Y'`, and it carries `hpl` at that pair. At first sight the situation does not
   inhabit it: `…AffineBase.preservesLeftHomology_pushforward_injectiveResolution` asks `IsAffine`
   of the morphism's **target**, which for `f'` is `Y'` and not `V`, and `Y'` carries no
   hypothesis in (c). But the affineness is spent on the open over which sections are taken and
   not on the base, so the hypothesis generalises; see the end of these notes.
2. *Solving for the edge morphism out of the passage.* `Stacks.EdgeCompat`
   `.derivedHomologyComparison_comp` splits the edge morphism of the Leray target as the edge
   morphism of `RΓ(V, -)` at `Rf'_* -` followed by `Γ(V, -)` of the edge morphism of `Rf'_*`, so
   the passage determines that **composite** and not its first factor. Solving for the first
   factor needs `Γ(V, -)` of the edge morphism of `Rf'_*` invertible at `M[0]`, and it is not: at
   a single complex in degree `d > 0` its target is `f'_*(Hᵈ(M[0])) = 0` while its source is
   `Γ(V, Rᵈ f'_* M)`. And the edge morphism of `Rf'_*` is **not**
   `homologyFunctorDerivedPushforwardIso`, which is an isomorphism onto `Rᵈ f'_* M`; the two are
   different morphisms out of the same object, so no cancellation relates them.

An alternative to route 1 is the compatibility of Grothendieck's collapse
`…AffineBase.rightDerivedCompNatIso` at the two pairs — `(𝟭, f'_*, Γ(V, -))` on `Y'` and
`(openSubschemeRestriction f' V, (f' ∣_ V)_*, Γ(V, ⊤, -))` on the open subscheme — across
[Stacks, Tag 01E5] on sections, which would let the `((f' ∣_ V), ⊤)` collapse (whose `hpl`
*is* inhabited) stand in for the ambient one. No `rightDerivedCompNatIso` naturality in its
index functor `E` is otherwise declared, and `AffineOpenCohomologyNaturality.lean`'s two squares
are naturality of the **other** copy of 01XK,
`…AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward`, in the **coefficient**, which is
a different statement. That square is
`…AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square`
(`AffineCohomologyVanishing/RestrictionCollapseSquare.lean`) — see the end of these notes.

*The route that square takes, read off `rightDerivedCompNatIso`'s own construction; it is
**not** the `rightDerived_ext` pattern the rest of this subtree uses.*
`…AffineBase.rightDerivedCompNatIso` is built by `CategoryTheory.NatIso.ofComponents`, each
component being `CategoryTheory.ShortComplex.mapHomologyIso` for `G` on the degree-`n` short
complex of the image under `F` of the **chosen** injective resolution of `E.obj X` — there is no
universal property to extend along, so `CategoryTheory.Functor.rightDerived_ext` is unavailable
and the square has to be checked componentwise. The handle for that is
`…AffineBase.rightDerivedCompNatIso_hom_app`
(`StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBaseComposition.lean`) prints the
component
as that `mapHomologyIso` inverted, conjugated by
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` for `F` and for `F ⋙ G`. So the square
reduces to comparing `mapHomologyIso` on two short complexes built from **two different chosen
resolutions** — of `M` on `X'` and of `(openSubschemeRestriction f' V).obj M` on `f'⁻¹V` — and the
map between them is the uniqueness up to homotopy of injective resolutions, which needs:

> **restriction to an open preserves injective *objects*.**

The library otherwise has only the **complex**-level statement,
`ExtensionByZeroModules.isKInjective_jStar` ([Stacks, Tag 08BS]), which is about K-injectivity of
a complex and does not give injectivity of an object; the object-level statement is
`ExtensionByZeroModules.preservesInjectiveObjects_jStar`
(`StacksFrontier/Topology/Sheaves/Cohomology/ExtensionByZero/RestrictionOfKInjectives.lean`), with
nothing assumed of the space, the open or
the sheaf of rings (axioms: `propext`, `Classical.choice`, `Quot.sound`). It is one line:
`CategoryTheory.Functor.preservesInjectiveObjects_of_isExact` at the adjunction `j_! ⊣ j^*`, whose
exactness is available — `…jShriek_additive`, `…jShriek_preservesFiniteLimits`,
`…jShriek_preservesColimitsOfSize` — the same way
`RingedSpaceModuleAdjunction.modulePushforward_preservesInjectiveObjects`
(`Topology/Sheaves/Functors/Module/FlatPullback.lean`) is obtained for a flat pushforward. And
`…TopDegreeBaseChange.openSubschemeRestrictionOf X U` **is**
`ExtensionByZeroModules.jStar U (structureSheafRing _)` by `rfl`, so it applies to the match's own
restriction on the nose. This is the square's first brick; its
second — [Stacks, Tag 01E5] read at the two chosen resolutions — is described at the end of these
notes.

*The shape of factor (3)'s remaining passage, read off the join's type.* The join
`lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq`
(`LerayCompositeOpenSubschemeJoin.lean`) is an equation of transformations of functors
`D(𝒪_Z) ⥤ D(ModuleCat Γ(Y, V))`, and the factor the `ψ` side wants moved to the other side —
the open-subscheme Leray comparison — sits inside it as
`Functor.whiskerRight (Functor.whiskerLeft (openSubschemeRestrictionOf Z U).mapDerivedCategory
(Functor.whiskerRight (lerayComparison (i.resLE (p⁻¹V) U e) ⊤) res_topIso.mapDerivedCategory))
res_{p^♯}.mapDerivedCategory`, i.e. under **two** restriction-of-scalars layers, while
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` hands its left inverse in at
`Hᵈ` of the **bare** component. So the passage is `StacksDraft.DerivedCategoryHomology`
`.map_homologyFunctor_map` applied **twice**, at `res_topIso` and at
`Stacks.EdgeCompat.preimageRestrictScalars p V` — four
`…DerivedCategoryHomology.mapDerivedCategoryHomologyIso` factors in the resulting statement, that
transformation having no component formula — together with a single-functor crossing to reach the
module the `ψ` side's `lInv` sits at. `FactorOnePrefixTransport.lean`'s
`homologyFunctor_map_openSubschemeSectionsComparison_eq` is that calculation at **one** layer and
is the template.

***Factor (3)'s passage is performed***, in `FactorThreePassage.lean`, as
`…TopDegreeBaseChange.homologyFunctor_map_derivedPreimageSectionsCompModel_comp_eq`: the degree-`d`
cohomology of the join's right-hand side — `derivedPreimageSectionsCompIso` inverted,
`preimageSectionsModelComparison p V` at `Ri_*K`, and `openSubschemeLerayComparisonLE` under the
scalars — followed by the left inverse conjugated through the two restriction-of-scalars layers, is
the degree-`d` cohomology of the join's left-hand prefix. **Nothing is assumed** of `i`, of `p`, of
`V`, of `U`, of the object or of the degree (axioms: `propext`, `Classical.choice`, `Quot.sound`).
The one hypothesis is the Leray left inverse in the shape
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` supplies it; that it is also a
right inverse comes from the unconditional
`…DerivedSectionsLeray.isIso_lerayComparison` inside the proof. The whole conjugation is **one**
private lemma at variables of abstract categories — "a morphism conjugated by an iso pair inherits
the conjugated right inverse" — applied twice, the inner application's conclusion being the outer
one's `hv`; no factor of the join is unfolded and neither model comparison, neither
`rightDerivedDesc` and neither open-subscheme crossing is inverted.

*Three remarks on the passage, read off its statement.*

1. **The single-functor crossing is not part of it.** The description above says the passage
   needs "a single-functor crossing to reach the module the `ψ` side's `lInv` sits at".
   It does not: the passage is stated at an **arbitrary** object `K` of `D(𝒪_Z)`, where `lInv` is
   simply asked for
   at `(lerayComparison (i.resLE (p⁻¹V) U e) ⊤).app ((openSubschemeRestrictionOf Z U)`
   `.mapDerivedCategory.obj K)`, and no `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`
   appears anywhere in it. That crossing is needed where the passage meets
   `cohomologyIsoPushforward_inv_eq_lerayComparison`, whose coefficient is a **module**, exactly as
   `FactorOnePrefixTransport.lean`'s `_single_eq` form pays it for factor (1) — it belongs to the
   join with the `ψ` side, not to the passage.
2. **`simp only` at the join's component fails silently, which is why the hypothesis is spelled
   out.** `simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,`
   `Functor.map_comp, Category.assoc] at hc` leaves `hc` **unchanged and reports no error**
   (as `trace_state` shows), so the decomposition cannot be obtained that way even though the
   same incantation works at the shallower shape in `FactorOnePrefixTransport.lean`. What works is
   to give `NatTrans.congr_app` of the join an **explicit expected type** already in the decomposed
   spelling — every step of the decomposition being `rfl` — and to split the one genuine
   `Functor.map_comp` inside a private lemma at variables.
3. **Another spelling pair.** `Stacks.EdgeCompat.preimageRestrictScalars p V`
   declares its **source** as `ModuleCat Γ(X, (opensMap p).obj V)`, while
   `ModuleCat.restrictScalars (Scheme.Opens.topIso (p⁻¹V)).inv.hom` declares its **target** as
   `ModuleCat Γ(X, p⁻¹V)`. The two are `rfl`, and the join composes them without complaint; but
   `StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map` applied to
   `preimageRestrictScalars p V` at a morphism whose type carries the `p⁻¹V` spelling reports
   `failed to synthesize HasDerivedCategory (ModuleCat Γ(X, (opensMap p).obj V))` **and**
   `(preimageRestrictScalars p V).Additive`, even though `infer_instance` finds both standalone and
   the same application at a morphism whose type carries the `(opensMap p).obj V` spelling
   elaborates. An ascription does not fix it. The cure here is cheaper than a `def`: a
   local `have hgen : ∀ {A B : D(ModuleCat Γ(X, (opensMap p).obj V))} (φ : A ⟶ B), _ := fun φ =>`
   `map_homologyFunctor_map …`, which fixes the category **before** the morphism is seen, and the
   concrete morphism then goes in by defeq.

*One duplicate.* `FactorThreePassage.lean`
re-derives the three-line `comp_eq_id_of_comp_id` — a left inverse of an isomorphism is a right
inverse — that `FactorOnePrefixTransport.lean` declares `private`.

***Factor (2) is performed too***, in `FactorTwoNaturality.lean`, as
`…TopDegreeBaseChange.homologyFunctor_map_derivedPreimageSections_map_comp_eq`: for an arbitrary
morphism `c : K ⟶ L` of `D(𝒪_X)` and an arbitrary degree `n`, the degree-`n` cohomology of
`(derivedPreimageSections f V).map c` — step 2a's first leading factor — followed by
`openSubschemeSectionsComparison f V` at `L` and by
`Stacks.EdgeCompat.preimageSectionsModelComparison (f ∣_ V) ⊤` at the restriction of `L`, is the
same two crossings at `K` followed by **factor (2)** itself: the degree-`n` cohomology of
`derivedSectionsOverOpen (f⁻¹V : Scheme) ((opensMap (f ∣_ V)).obj ⊤)` applied to the restriction
of `c`, read under the two restrictions of scalars. **Nothing is assumed** of `f`, of `V`, of `c`
or of `n` (axioms: `propext`, `Classical.choice`, `Quot.sound`). The passage is **naturality and
nothing else**: no transformation is built, nothing is inverted and no `rightDerivedDesc` is taken.

*It uses one general brick.*
`StacksFrontier/Homology/DerivedCategory/MapHomologyIso.lean` carries two readings of
`mapDerivedCategoryHomologyIso`'s naturality
besides `map_homologyFunctor_map`:
`StacksDraft.DerivedCategoryHomology.homologyFunctor_map_mapDerivedCategory_map` — the same
naturality solved for the cohomology of the **image** rather than for the image of the cohomology,
which is the reading a calculation meeting the exact functor on the outside needs — and
`…homologyFunctor_map_comp_eq_of_square`, which reads a commuting square whose vertical edges are
an exact functor on derived categories in degree `i`. Neither assumes anything beyond exactness
(axioms: `propext`, `Classical.choice`, `Quot.sound`).

*The square is a hypothesis and `q` is an explicit morphism, and that is not cosmetic.* A version
of the brick taking a **functor** `Q` and a transformation `τ : P ⟶ Q ⋙ F.mapDerivedCategory`
and concluding about `Hⁱ(Q.map c)` would not do. At the composite `Q` this chase needs —
restriction, then sections, then the scalars upstairs — that forces the spelling
`(RD ⋙ Sov ⋙ Qs.mapDC).map c` on the conclusion, and the inner layer's own conjugation, which is
stated at the reduced `Qs.mapDC.map (Sov.map (RD.map c))`, then **cannot be substituted for it**:
`rw` at the concrete terms is a 200,000-heartbeat `isDefEq` timeout. Taking the square as a
hypothesis and `q` explicitly lets the consumer write `q` reduced and supply the square as
`(…).naturality c` **with its type given**.

*Rewriting at variables.* The substitution of the inner conjugation is done
inside a private lemma at variables of abstract categories, where it is a one-step rewrite of a
bound morphism; performed on the concrete goal the same `rw` times out in the same way.

***The join of the transport to `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomology`
`Comparison` is not written — but the "target crossing" it needs is available.*** The join
needs the **target** crossing `Γ(V, Rᵈf'_* M) ⟶ res Γ(V, ⊤, Rᵈ(f' ∣_ V)_* (M|))`, and the
classical-model crossing `SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` is at the
**sheaf** level; but a derived/sections-level form need not be built:
**that crossing is already written down, in this file**, as the first two
factors of `affineOpenCohomologyIsoSectionsOf_inv_eq`'s right-hand side —

> `(openSectionsModuleIso ((Rᵈ f'_*) F') V).inv`, then
> `ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom` applied to
> `Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)` of
> `SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F'` **inverted** —

whose source is `Γ(V, Rᵈf'_*F')` and whose target is
`res_{topIso} Γ((V : Scheme), ⊤, Rᵈ(f' ∣_ V)_*(F'|_{f'⁻¹V}))`, i.e. the owed type on the nose.
`AlgebraicGeometry.openSectionsModuleIso M V` (`Modules/RestrictOpenSections.lean`) is
`res_{topIso} (Γ((V : Scheme), ⊤, M|_V)) ≅ Γ(Y, V, M)` with no hypothesis at all, and 01E5 is
available both as a natural iso (`…SchemeHigherDirectImage.rightDerivedPlusRestrictIso`) and as
its component, with both naturalities. So nothing is to be **built** here: the sections-level
form is the two pieces composed, and the `ψ` side already carries that composite.

*The hypothesis-free form.* The same composite occurs a
second time, uninverted, in the definition of `…TopDegreeBaseChange.affineOpenCohomologyIsoSections`
(`AffineOpenSectionsCohomology.lean`) — and in both occurrences it is **welded to the
[Stacks, Tag 01XK] factor**, so that it is reachable only behind `QuasiCompact f`,
`QuasiSeparated f`, `IsAffine (V : Scheme)` and quasi-coherence of `F`, *none of which either of
its two factors needs*. So it is stated separately in
`SectionsRestrictHigherDirectImage.lean`:
`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso` — the global sections over the open
subscheme `V` of `Rᵈ(f ∣_ V)_*(F|_{f⁻¹V})`, read over `Γ(Y, V)` through `topIso`, are
`Γ(Rᵈ f_* F, V)`, with **nothing assumed** of `f`, of `V`, of `F` or of `d` (axioms: `propext`,
`Classical.choice`, `Quot.sound`) — together with
`…TopDegreeBaseChange.affineOpenCohomologyIsoSections_eq`, which says that the statement with
hypotheses is [Stacks, Tag 01XK] over `V` followed by it, so the two are the same morphism and no
second copy is hidden. Nothing new is proved there; only the hypotheses move.

*Related statements.* `StacksCore/` — the promoted tree
— has **no** occurrence of `rightDerivedPlusRestrict…`, `higherDirectImageRestrict…`,
`affineOpenCohomology…`, `openSectionsModuleIso` or `moduleGlobalSections`: all of this is draft
only. The 01E5 comparison is consumed at the **sheaf** level and nowhere else, by
`TopDegreeFiniteType/FinitePresentationAffineBase.lean:146`,
`ProperCohomologyFinite/Locality.lean:122` and
`FunctorsAndMorphisms/CoherentModuleFunctors/FinitenessCriterion.lean:414,424`. The near-miss
worth naming is `…TopDegreeBaseChange.affineOpenCohomologyIsoSectionsRightDerivedPlus`
(`BaseChangeMapAffineSections.lean:151`), which *is* 01XK followed by `moduleGlobalSections` of
01E5 — but with the **absolute** cohomology of `f⁻¹V` on the left rather than
`Γ(⊤, Rᵈ(f ∣_ V)_*(F|))`, and behind the same four hypotheses. And
`…TopDegreeBaseChange.sectionsOnRightDerivedRestrictIso` (`DerivedSectionsModelCrossing.lean:213`)
is the right *shape* at full generality — `RⁿΓ(U, -) ≅ restrictFunctor U.ι ⋙ RⁿΓ((U : Scheme), ⊤)`
`⋙ res_topIso` as functors, unconditional — but for the sections of **one** scheme, with no
morphism and no pushforward in it, so it is not this comparison.

*What the join needs, read off the two statements, with the brick named.* `Pre` is fixed by
`hPre` to the edge morphism of `RΓ(V, -)` at `Rf'_*((E Z)[0])` followed by `Γ(V, -)` of
`homologyFunctorDerivedPushforwardIso`, read at `(f', V)`; the transport
`prefix_transport_eq_openSubschemeSectionsComparison_comp` carries the same prefix at
`((f' ∣_ V), ⊤)`. Getting from the one to the other is **not** a new transport but
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans`
(
`…/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphismOnARingedSite.lean:579`)
at the **identity** transformation of
the degreewise functor — both `…DerivedSectionsLeray.lerayUnit f V` and
`…TopDegreeBaseChange.openSubschemeLerayUnit f V` are units of right derived functors of the
**same** degreewise `preimageSections f V`, the latter built through the degreewise iso
`…TopDegreeBaseChange.preimageSectionsOpenSubschemePushforwardIso` by
`openSubschemeUnitOfIsoUnit`. So `α := 𝟙`, `Rα := openSubschemeLerayComparison f V`, and the
`hRα` the brick asks for is that `rightDerivedDesc`'s own factorisation. This is the same shape as
`Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsModelComparison`, which is
that brick at the identity transformation. What remains after it is the
splitting of the open-subscheme model's edge morphism — `exactPostcomposeUnit` at the `topIso`
scalars, which is where the classical-model target crossing above enters through
`preimageSectionsOpenSubschemePushforwardIso`'s `ψ`-route half — and the two prefix
identifications on either side. **None of that is performed here.**

***The degeneration `hpl` at the ambient pair is inhabited, nothing is assumed of `Y'`, and the
square across [Stacks, Tag 01E5] is not needed to supply `hPre`.*** At first sight the ambient
route is closed, because
`…AffineBase.preservesLeftHomology_pushforward_injectiveResolution` asks `IsAffine` of the
morphism's **target** — `Y'` for `f'`, which carries no hypothesis in (c). That is accurate for
*that declaration*. But, as the three results the declaration's proof is assembled from show,
**none of them needs the base to be affine**:

* the terms. `Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic` takes the
  open of the base as an **argument**, and the existing proof passes it `⊤`. At an arbitrary open
  it says the direct image of an injective module has acyclic sections there, with no hypothesis
  on the morphism at all. ([Stacks, Tag 01EX] part (2).)
* the homology objects. Their quasi-coherence is [Stacks, Tag 01XJ], which mentions no open: it
  asks `f` quasi-compact and quasi-separated and the coefficient quasi-coherent, both of which
  the situation has (`S.quasiCompact_f'`, `S.quasiSeparated_f'`, `F'.IsQuasicoherent`).
* the vanishing. `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` asks
  `AlgebraicGeometry.IsAffineOpen` of the **open**, not `IsAffine` of the scheme, and
  `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` — which carries that
  vanishing back to the module-valued right derived functor — takes the open as an argument too.
  ([Stacks, Tag 01XB].)

So the whole use of affineness is at the open over which sections are taken. The generalisation
is in `AffineCohomologyVanishing/AffineOpenBase.lean`, both pieces with **nothing assumed
of the base scheme** (axioms: `propext`, `Classical.choice`, `Quot.sound`):

* `Stacks.Cohomology.AffineBase.rightAcyclic_sectionsOverOpen_of_isAffineOpen` — [Stacks,
  Tag 01XB] as acyclicity of module-valued sections over an affine open, the exact analogue of
  `…AffineBase.rightAcyclic_moduleGlobalSections` with the open left general;
* `Stacks.Cohomology.AffineBase.preservesLeftHomology_pushforward_injectiveResolution`
  `_of_isAffineOpen` — Grothendieck's pointwise hypothesis at the pair `(f_*, Γ(V, -))` for a
  quasi-compact quasi-separated `f : X ⟶ S`, an affine open `V ⊆ S`, a quasi-coherent coefficient
  and a degree `n`.

***Step 1(a) is therefore joined***, in `AmbientPrefixJoin.lean`, with the same three axioms
throughout:

* `…TopDegreeBaseChange.hpl_of_isAffineOpen` — the ambient degeneration in the spelling
  `sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` and
  `…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv`
  (`FactorOneCollapseMirror.lean`) ask for,
  for a functor `E : Dc ⥤ Mod(𝒪_X)` with quasi-coherent values; and
  `…TopDegreeBaseChange.hpl_isQuasicoherent_of_isAffineOpen`, the same at
  `E := (SheafOfModules.isQuasicoherent 𝒪_X).ι`, where the quasi-coherence is each object's own
  `property` and no coefficient need be named.
* `…TopDegreeBaseChange.collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`
  — **`hPre` supplied at `(f', V)`**: the prefix written out through [Stacks, Tag 01XK]'s
  collapse — the Leray left inverse at `f`, the crossing of the two models of
  `Rⁿ(f_* ⋙ Γ(V, -))`, Grothendieck's comparison inverted, and `Γ(V, -)` of
  `Stacks.DerivedIndexing.rightDerivedIso` — followed by `Γ(V, -)` of
  `…homologyFunctorDerivedPushforwardIso` inverted and the rest of the tail, is `Hⁿ` of
  `RΓ(V, β)`, the Leray left inverse at `g`, and the edge morphism of `RΓ(g⁻¹V, -)` at `K`. Its
  hypotheses are its two inputs' own: `hpl`, `hv`, and the two Leray left inverses, each
  unconditional by `…DerivedSectionsLeray.isIso_lerayComparison`. **Nothing is assumed of `g`,
  of `β`, of `K` or of `n`**, which is what (c) requires of the morphism of bases.

*A companion, which is not an input to any step of the chase.*
`Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE` carries its acyclicity
as a hypothesis, and its docstring says that acyclicity is [Stacks, Tag 01XB] "for an affine open
of an affine scheme" — the same hypothesis too many. So
`…TopDegreeBaseChange.isIso_sectionsOverOpenHomologyComparison_app_of_isAffineOpen`
(`AmbientPrefixJoin.lean`) is the edge morphism of `RΓ(V, -)` invertible at a cohomologically
bounded below object with quasi-coherent cohomology sheaves, over an affine open of an
**arbitrary** scheme (axioms: `propext`, `Classical.choice`, `Quot.sound`). It does **not**
reopen the third factor of the `Γ(V, Θ)` reading above: there the coefficient is
`Rh_*(Rf''_* …)`, whose cohomology sheaves are not quasi-coherent without `h` quasi-compact and
quasi-separated, and the situation places no hypothesis on `h`. So the factor continues to use
the splitting solved for its last two factors.

*What this does and does not settle.* The square
`…AffineBase.rightDerivedCompNatIso` at the two pairs across [Stacks, Tag 01E5] on sections is
still needed: joining the `γ⁺` prefix now read at `(f', V)` to the `ψ` side's
factor (1), which 089W forces to live at `((f' ∣_ V), ⊤)`, still crosses between the two
collapses. What has changed is that the square is **statable and usable** — both of its
`hpl`s are inhabited — and that it is not on the critical path for `hPre`. Its first brick is
`ExtensionByZeroModules.preservesInjectiveObjects_jStar`, used in the ψ-side join below, and the
square itself is proved.

*Two further facts.*

1. **Another spelling pair.** `preservesLeftHomology_pushforward_injectiveResolution`
   `_of_isAffineOpen` declares its coefficient as `X.Modules` with `[F.IsQuasicoherent]` an
   **instance** argument, while the comparison's index functor lands in
   `SheafOfModules (structureSheafRing X.toSheafedSpace)`. The two types are `rfl` and the
   coefficient goes in by defeq; but with a local `[(E.obj Z).IsQuasicoherent]` at the
   `SheafOfModules` spelling, the instance is reported unsynthesisable at the `X.Modules` one.
   An ascription fixes nothing. The cure here is cheaper than a `def`: take
   the quasi-coherence as an **explicit** family hypothesis and pass it positionally, where the
   elaborator checks it against the expected type at default transparency.
2. **Writing `Pre` out does elaborate**, which refines the implementation note of
   `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`. That note says both
   `Pre` and `v` are hoisted because "written out, the statement crosses the
   `AlgebraicGeometry.Scheme.Modules` / `SheafOfModules (structureSheafRing …)` divide twice and
   does not elaborate". With `Pre` replaced by the four factors the collapse identification names
   and `v` still hoisted, the statement elaborates and checks in 9 s. So the hoisting of `v` is
   what the elaboration problem is about, and the hoisting of `Pre` is bookkeeping.

***The ψ-side join: the square across [Stacks, Tag 01E5] is required, the two readings
do not match through `rightDerivedPlusRestrictSectionsIso` by themselves, and the two
formulations of the square are the same square.***
One might hope that the crossing between the `γ⁺` prefix computed at `(f', V)` and
the `ψ` side's factor (1) at `((f' ∣_ V), ⊤)` does not need that square, the two readings
already matching through the hypothesis-free
`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso`. The two statements show otherwise:
the comparison is required, and `rightDerivedPlusRestrictSectionsIso` is **one edge of
it**, not a way round it.
* *What the two statements actually end at.*
  `prefix_transport_eq_openSubschemeSectionsComparison_comp`'s right-hand side ends at
  `(sectionsOverOpen (V : Scheme) ⊤).map (Stacks.DerivedIndexing.rightDerivedIso …)` read under
  `ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom`, i.e. at
  `res_{topIso} Γ((V : Scheme), ⊤, Rⁿ(f ∣_ V)_*(M|_{f⁻¹V}))`;
  `collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`'s left-hand side ends
  at `(sectionsOverOpen Y V).obj (Rⁿ f_* (E Z))`, i.e. at `Γ(V, Rⁿf_*M)`. Those two objects are
  **different**, and the comparison between them is exactly
  `rightDerivedPlusRestrictSectionsIso f V n M`. So a crossing is needed, that declaration is it,
  and being hypothesis-free it is what lets the square be **stated** with nothing assumed beyond
  the two `hpl`s — but a statement is not a proof; the square is proved separately (see below).
* *The two formulations are one square.* The `γ⁺` prefix at `(f, V)` — the edge morphism of
  `RΓ(V, -)` at `Rf_*(M[0])` followed by `Γ(V, -)` of `homologyFunctorDerivedPushforwardIso` — and
  the same at `((f ∣_ V), ⊤)` are each identified with their collapse readings, by
  `sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` at the
  ambient pair and by `prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` at the restricted
  one, and **both of those identifications are proved with an inhabited `hpl`**. So the square
  stated on the two *primitive* prefixes and the square stated on the two
  `…AffineBase.rightDerivedCompNatIso` collapses are interderivable, and neither is cheaper for
  being stated the other way.
* *Where the restricted 01XK goes, and why the ambient collapse is still wanted.* The restricted
  collapse does **not** have to be crossed: `prefix_transport_eq_openSubschemeSectionsComparison`
  `_comp` has the restricted collapse on its right-hand side and the restricted *primitive* prefix
  on its left, so it cancels there. And `hPre` itself is not what the ambient collapse is for:
  `prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` hoists `Pre` with
  `hPre : edge ≫ Γ(V, -)(crossing) = Pre`, which is discharged by `rfl` at `Pre :=` the left-hand
  side. The ambient collapse is wanted **because the `ψ` side arrives in collapse form**, and the
  one 01XK that genuinely has to be crossed is therefore the ambient one against the restricted
  one — which is the square. `AmbientPrefixJoin.lean` is what makes that crossing statable on the
  ambient side; it does not remove it.
* *And the square meets [Stacks, Tag 01E5] at the CHOSEN injective resolutions, which is where
  `preservesInjectiveObjects_jStar` is spent.* `…AffineBase.rightDerivedCompNatIso_hom_app`
  (`StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBaseComposition.lean`) prints
  each collapse through
  `CategoryTheory.injectiveResolution (E.obj Z)` — on the ambient side the chosen resolution of
  `M` on `X`, on the open-subscheme side the chosen resolution of `(openSubschemeRestriction f V)`
  `.obj M` on `f⁻¹V`, those being the two index functors the two statements are written at
  (`𝟭`-like on the ambient side, `openSubschemeRestriction f V` on the other). 01E5's own
  resolution clause `Stacks.Cohomology.HigherDirectImage`
  `.higherDirectImageRestrictIso_injectiveResolution` is stated at an **arbitrary** triple
  `(I, J, φ)`, so what the square needs from it is the triple at the two chosen resolutions, and
  that is what the comparison of resolutions — hence restriction preserving injective **objects** —
  supplies. **Both bricks are proved**, with nothing assumed and axioms `propext`,
  `Classical.choice`, `Quot.sound` throughout:

  * `CategoryTheory.InjectiveResolution.mapOfPreservesInjectives`
    (`Algebra/Homology/Resolution/MapInjectiveResolution.lean`) — the image of an injective
    resolution under an additive functor preserving homology and injective objects is an injective
    resolution — together with `…mapOfPreservesInjectives_ι_f_zero` and
    `…desc_mapOfPreservesInjectives_f_zero`, which is the augmentation clause a chosen-resolution
    statement asks for. Nothing is assumed of the categories, the object or the resolution beyond
    what the functor is asked for; this is the first consumer of
    `ExtensionByZeroModules.preservesInjectiveObjects_jStar`, which applies to
    `…HigherDirectImage.moduleRestriction` because the latter *is*
    `ExtensionByZeroModules.jStar` at the structure sheaf (`infer_instance` finds it).
  * `Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison` and
    `…higherDirectImageRestrictIso_chosenResolution`
(`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/RestrictionOfChosenResolutions.lean`)
    — [Stacks, Tag 01E5] in degree `p`
    at the two chosen resolutions, with nothing assumed of `f`, of `V`, of `M` or of `p`. Its last
    factor is `CategoryTheory.ShortComplex.mapHomologyIso` for `moduleRestriction Y V` on the
    degree-`p` short complex of the image under `f_*` of the chosen resolution of `M` — which is
    **the middle factor of `rightDerivedCompNatIso_hom_app` at the pair `(f_*, Γ(V, -))`**. That
    coincidence is the key point: it is the single place where 01E5 and
    Grothendieck's collapse are the same expression, and so the only place the square can be
    checked componentwise.

  The square itself is proved; see the end of these notes.

***The source edge.*** The square's **source** edge — the
comparison between the two *sources* of the two collapses, as against
`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso`, which is its **target** edge — is a
`compRightDerivedNatIso`-family comparison, and it has a chosen-resolution formula. The family is
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`
(`CategoryTheory/Sites/Cohomology/HigherDirectImage/CompositeRightDerivedFunctors.lean`) —
`R ⁿ(L ⋙ G) ≅ L ⋙ R ⁿG` for `L` exact and injectives-preserving, [Stacks, Tag 01E1] — and its
chosen-resolution formulas are in
`Topology/Sheaves/Cohomology/DerivedFunctors/CompositeComparisonOnResolutions.lean`:
* `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app` reads the component off
  the chosen resolution of `X` and its image under `L`;
* `…DerivedCompTransport.compRightDerivedNatIso_hom_app_eq` reads it off an **arbitrary** triple
  — a resolution `I` of `X`, a resolution `J` of `L X`, and a comparison descending the identity —
  and `…_eq_of_desc` says the answer does not depend on the triple;
* `…DerivedCompTransport.compRightDerivedNatIso_hom_app_mapInjRes` is the same off `I` alone;
* `Stacks.Cohomology.HigherDirectImage.compRightDerivedNatIso_inv_app_eq`
  (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationOnResolutions.lean`) is
  that reading inverted.

What is additionally needed is the formula **at the
direction in which the comparison of chosen resolutions points**.
`compRightDerivedNatIso_hom_app_eq`'s comparison runs from `L(I)` **into** `J`, while
`CategoryTheory.InjectiveResolution.desc` — hence `restrictChosenResolutionComparison`, and the
clause `CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero` certifies — runs
**out of** the chosen `J`.
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationOnResolutions.lean`'s own
implementation note describes
the route for that direction, `compRightDerivedNatIso_inv_app_eq` together with
`…DerivedCompTransport.isoRightDerivedObj_hom_eq`, and performs it inside a proof rather than as a
declaration a chase could rewrite with.

*What is proved, with nothing assumed* (axioms `propext`, `Classical.choice`, `Quot.sound`
throughout):

* `Stacks.Cohomology.HigherDirectImage.restrictChosenResolutionComparison_ι_f_zero` and
  `…HigherDirectImage.compRightDerivedNatIso_inv_app_chosenResolution`
  (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/SourceEdgeChosenResolutions.lean`)
  — **the source edge at the two chosen
  resolutions, in the spelling [Stacks, Tag 01E5] is itself built from.** For an additive `P` out
  of the modules on `V`, the component at `M` of 01E1's collapse at the pair
  `((-|_{f⁻¹V}), (f ∣ V)_* ⋙ P)`, inverted, is the computation on the chosen resolution of
  `M|_{f⁻¹V}`, the degree-`p` homology of `(f ∣ V)_* ⋙ P` applied to
  `restrictChosenResolutionComparison`, and the computation on the chosen resolution of `M`
  inverted. Nothing is assumed of `f`, of `V`, of `M`, of `p`, or of `P` past additivity. It is
  the two existing results composed; nothing new is proved.
* `Stacks.RightDerivedComp.objIso_inv_eq` (`Homology/CompositeCollapseChosenResolution.lean`) and
  `Stacks.Cohomology.HigherDirectImage.restrictCollapse_inv_eq` with
  `…HigherDirectImage.isZero_rightDerived_moduleRestriction`
  (
  `…/Topology/Sheaves/Cohomology/HigherDirectImage/RestrictionCollapseChosenResolutions.lean`)
  — the same at the **objectwise,
  acyclic** family `Stacks.RightDerivedComp.objIso`, where the formula in that direction was
  for the same reason: `Stacks.RightDerivedComp.objIso_hom_eq` is the mirror with the
  comparison the other way, exactly as `compRightDerivedNatIso_hom_app_eq` is. `objIso` asks only
  for pointwise acyclicity where `compRightDerivedNatIso` asks for exactness of `L`, so neither is
  an instance of the other without discharging the stronger hypothesis; at this pair it is
  discharged, restriction to an open being exact, which is
  `isZero_rightDerived_moduleRestriction`. **These two re-derive, for a second family, content
  the four results above already carry.**

*A duplicate.* `CategoryTheory.InjectiveResolution.mapOfPreservesInjectives`
(`Algebra/Homology/Resolution/MapInjectiveResolution.lean`) is
`Stacks.Cohomology.CompositeRightDerived.mapInjRes` (
`…/CategoryTheory/Sites/Cohomology/HigherDirectImage/CompositeRightDerivedFunctors.lean`)
— **the
same `cocomplex`, the same `injective`, the same `ι`, and equal by `rfl`** — differing
only in asking `[L.PreservesHomology]` where `mapInjRes` asks for the two exactness instances,
which `CategoryTheory.Functor.preservesHomologyOfExact` supplies.
`Stacks.RightDerivedComp.mapOfAcyclic` (`Homology/CompositeCollapse.lean`) is a third copy, with
the injectivity of the terms got from pointwise acyclicity instead and a different `ι`. And
`…DerivedCompTransport.mapInjRes_ι_f_zero` is `…mapOfPreservesInjectives_ι_f_zero`. `mapInjRes`
is public; it names neither restriction nor any direct image and lives under
`CategoryTheory/Sites/Cohomology/HigherDirectImage/`.

*What the square needs, side by side.* **All four of its sides have a
chosen-resolution formula**, which is what turns the square from a construction into an assembly:

* the source edge — `compRightDerivedNatIso_inv_app_chosenResolution`, above;
* the target edge — `…HigherDirectImage.higherDirectImageRestrictIso_chosenResolution`
  (
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/RestrictionOfChosenResolutions.lean`),
  at the **sheaf** level, so a step applying `P` and
  `CategoryTheory.ShortComplex.mapHomologyIso` for `P` is owed before the two meet;
* the two collapses — `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app`
  (`StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBaseComposition.lean`) at the
  ambient pair and at the restricted one, both `hpl`s
  inhabited, by `hpl_of_isAffineOpen` (`AmbientPrefixJoin.lean`) and by the open-subscheme one;
* the transport between the two sources that 01E5 itself bundles —
  `…HigherDirectImage.rightDerivedPushforwardRestrictIso`, whose chosen-resolution reading is
  `…DerivedCompTransport.rightDerivedCompIso_hom_app_eq`.

The agreement of the middle factors is the reason it closes: the source edge's is the degree-`p`
homology of `restrictChosenResolutionComparison` under `(f ∣ V)_* ⋙ P`, and the target edge's is
the homology of the same comparison under `(f ∣ V)_*` alone, the two differing by the
`mapHomologyIso` factor `rightDerivedCompNatIso_hom_app` carries. ***The square is proved; see
the end of these notes.***

*Two further facts that decide the assembly's shape.*

1. **The two edges are at the same triple and the same direction.**
   `…HigherDirectImage.higherDirectImageRestrictIso_injectiveResolution`
   (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationInDegreeZero.lean`)
   holds at **every** degree — not only positive: the
   positive-degree half is `…_succ` in
   `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationOnResolutions.lean` and
   the degree-zero branch
   is discharged where the all-degree statement is proved — and its `φ` runs
   `J.cocomplex ⟶ (restriction).mapHomologicalComplex.obj I.cocomplex` with
   `hφ : J.ι.f 0 ≫ φ.f 0 = (restriction).map (I.ι.f 0)`, which is the direction
   `restrictChosenResolutionComparison` points and the one the source edge is read at. So no
   reorientation of either edge is needed; the direction, and not the formula, is what matters.
2. **The hinge is in Mathlib, and it is what the two `hpl`s are spent on.** The step relating the
   two middle factors — `P` of the degree-`p` homology of a map of complexes against the homology
   of its image under `P` — is `CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality`
   (`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`), with
   `…mapHomologyIso_inv_naturality` beside it. Its hypotheses are
   `[P.PreservesLeftHomologyOf S₁]` and `[P.PreservesLeftHomologyOf S₂]` at the **two** short
   complexes — the degree-`p` short complex of the image under `f_*` of the chosen resolution of
   `M`, and the one under `(f ∣ V)_*` of the chosen resolution of `M|` — which are exactly the two
   `hpl`s the square's two collapses already carry, the ambient one inhabited by
   `hpl_of_isAffineOpen` (`AmbientPrefixJoin.lean`) and the restricted one by the open-subscheme
   form. So the square needs **no** hypothesis beyond the two `hpl`s, and in particular nothing of
   `h`; and nothing new has to be proved about homology.

   *A near-miss.* The same hinge is also packaged
   **complex-level and functorially**, as
   `Stacks.Cohomology.ModuleComparison.homologyMapFunctorIso`
   (`StacksFrontier/Topology/Sheaves/Cohomology/ModuleComparison/SectionsOverAnOpen.lean`), whose
   component at a complex `K` is
   `(K.sc n).mapHomologyIso` — the very factor `rightDerivedCompNatIso_hom_app` carries — and
   whose naturality is literally `ShortComplex.mapHomologyIso_hom_naturality` whiskered along
   `HomologicalComplex.shortComplexFunctor`. It is **not usable here**: it asks
   `[P.PreservesHomology]`, i.e. exactness of `P`, and the `P` the square is instantiated at is
   sections over an affine open, which is not exact — the pointwise `hpl` is precisely the
   weakening that makes Grothendieck's collapse available at all, and it is the reason
   `…AffineBase.rightDerivedCompNatIso` exists beside
   `…ModuleComparison.rightDerivedCompIso`. So the hinge must be taken at the two short complexes
   from Mathlib directly, not through its functorial packaging.

***The square's hinge is two compatibilities, not one, and both are available.*** Point 2 above
names the hinge as Mathlib's `CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality` and says
that nothing new has to be proved about homology. Both halves are true, but the hinge is **two**
compatibilities and the one point 2 does not name is not a naturality:

* *naturality in the short complex* — the Mathlib lemma named there, whose `inv` companion
  `…ShortComplex.mapHomologyIso_inv_naturality` reads
  `F.map (homologyMap φ) ≫ (S₂.mapHomologyIso F).inv =`
  `(S₁.mapHomologyIso F).inv ≫ homologyMap (F.mapShortComplex.map φ)`; and
* *functoriality in the FUNCTOR* — `S.mapHomologyIso (R ⋙ P)` against
  `(S.map R).mapHomologyIso P` and `S.mapHomologyIso R`. The square cannot avoid it: the target
  edge's last factor is `CategoryTheory.ShortComplex.mapHomologyIso` for `moduleRestriction Y V`
  **alone** (`higherDirectImageRestrictIso_chosenResolution`,
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/RestrictionOfChosenResolutions.lean`),
  while the ambient collapse at a general additive `P`
  carries `mapHomologyIso` for the **composite** `moduleRestriction Y V ⋙ P`
  (`…AffineBase.rightDerivedCompNatIso_hom_app`,
  `StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBaseComposition.lean`). Mathlib
  has no such
  lemma: enumerating the environment of `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
  gives only the two naturalities, their `_assoc` forms, the primed pair,
  `…LeftHomologyData.mapHomologyIso_eq`, `…LeftHomologyData.mapCyclesIso_eq`,
  `…mapLeftHomologyIso_eq` and `…RightHomologyData.mapHomologyIso'_eq`.

The composition law **is in the library**, at exactly the pointwise hypotheses the square carries
and not at exactness: `CategoryTheory.ShortComplex.mapHomologyIso_comp_hom` and
`…ShortComplex.mapHomologyIso_comp_inv` (`Algebra/Homology/ShortComplex/MapHomologyComp.lean`),
asking `[R.PreservesLeftHomologyOf S]`, `[P.PreservesLeftHomologyOf (S.map R)]` and
`[(R ⋙ P).PreservesLeftHomologyOf S]` and nothing else; that file's own module docstring says it
belongs upstream beside the naturality. That file also explains the elaboration caveat: `rw` and
`simp` match at `instances` transparency and find **nothing** between
the two spellings `S.map (R ⋙ P)` and `(S.map R).map P` of one short complex, nor between
`(h.map (R ⋙ P)).H` and `(R ⋙ P).obj h.H`, so every step there has to be an explicit
`Category.assoc` / `congrArg` / `Eq.trans`.

*A duplicate pair.*
`Stacks.Homology.mapHomologyIso_comp_hom`
(`Algebra/Homology/HomotopyCategory/ExactFunctorHomologyComposition.lean`) is the same statement
under `[PreservesFiniteLimits]` and `[PreservesFiniteColimits]` on both functors, i.e. the
exactness specialisation of `CategoryTheory.ShortComplex.mapHomologyIso_comp_hom`; the two differ
only in hypotheses and in namespace — the names are otherwise identical — and the pointwise one
subsumes the exact one. Its two consumers there are `…Homology.exactHomologyIso_comp_hom_app` and
`…DerivedFunctor.complexHomologyIso_comp_hom_app`.

*Two clarifications about the square's ingredients.*

1. **The two `hpl`s are not two declarations.** `hpl_of_isAffineOpen` and
   `hpl_isQuasicoherent_of_isAffineOpen` (`AmbientPrefixJoin.lean`) are **both** at the ambient
   pair — the second is the first at the index functor [Stacks, Tag 01XK] whiskers by. The square's
   restricted `hpl` is `hpl_of_isAffineOpen` **again**, at `((f ∣_ V), ⊤)`, `⊤` being an affine
   open of `(V : Scheme)` because `V` is affine; it is not a second declaration, and the
   open-subscheme form named above is that instantiation.
2. **At a general `P` the transport is not `rightDerivedPushforwardRestrictIso`.** That comparison
   is `R ᵖ f_* ⋙ (-|_V) ≅ R ᵖ((-|_{f⁻¹V}) ⋙ (f ∣ V)_*)`, i.e. the `P = 𝟭` case, and it is already
   spent **inside** the target edge: `…HigherDirectImage.higherDirectImageRestrictIsoSucc` is
   `(rightDerivedPushforwardRestrictIso ≪≫ compRightDerivedNatIso).symm`
   (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/LocalizationIsomorphisms.lean`),
   so the source edge and that transport *are* the target edge
   in positive degree. What the square needs beside its two edges and two collapses is the derived
   transport **at `P`**, between `R ᵖ(f_* ⋙ (-|_V) ⋙ P)` and `R ᵖ((-|_{f⁻¹V}) ⋙ (f ∣ V)_* ⋙ P)`
   along `Functor.whiskerRight (modulePushforwardRestrictIso f V).inv P`. Hoisted onto a variable
   `τ` whose defining hypothesis is its chosen-resolution reading, that hypothesis is
   `rfl`-dischargeable, exactly as `hPre` is.

*The reduction, computed in full.* Write
`L = (-|_{f⁻¹V})`, `F = f_*`, `F' = (f ∣ V)_*`, `R = (-|_V)`,
`e = …HigherDirectImage.modulePushforwardRestrictIso f V`, `I` for the chosen resolution of
`M = E Z` and `J` for that of `L M`, `c = …HigherDirectImage.restrictChosenResolutionComparison`,
`Φ[K]` for `Φ.mapHomologicalComplex (ComplexShape.up ℕ)` at `K`, `H ᵖ` for the degree-`p` homology
functor, and `S = (F[I]).sc p`, `S' = (F'[J]).sc p`, `S'' = ((L ⋙ F')[I]).sc p`. Expand the two
paths by the four chosen-resolution formulas. The leading `P.map (J.isoRightDerivedObj F' p).hom`
and the trailing `(I.isoRightDerivedObj (L ⋙ F' ⋙ P) p).inv` are common to both, and the two
`isoRightDerivedObj (F' ⋙ P)` and the two `isoRightDerivedObj (F ⋙ R ⋙ P)` cancel in pairs. What is
left is

> `(S'.mapHomologyIso P).inv ≫ H ᵖ((F' ⋙ P)[c])`
> `= P.map (H ᵖ(F'[c])) ≫ P.map (H ᵖ(e.hom[I])) ≫ P.map (S.mapHomologyIso R).hom`
> `≫ (S.mapHomologyIso (R ⋙ P)).inv ≫ H ᵖ((Functor.whiskerRight e.inv P)[I])`,

and that closes in three steps, each by an existing lemma, with no new content:

* `mapHomologyIso_comp_inv` collapses the third and fourth factors on the right to
  `((S.map R).mapHomologyIso P).inv`;
* `mapHomologyIso_inv_naturality` at the short-complex map induced by `e.hom[I]` turns
  `P.map (H ᵖ(e.hom[I])) ≫ ((S.map R).mapHomologyIso P).inv` into
  `(S''.mapHomologyIso P).inv ≫ H ᵖ(P[e.hom[I]])`, whose second factor cancels against the
  trailing `H ᵖ((Functor.whiskerRight e.inv P)[I])`;
* `mapHomologyIso_inv_naturality` at the map induced by `F'[c]` is then literally the remaining
  identity.

So the square needs **no hypothesis beyond the two `hpl`s** and nothing of `h`, of `h'` or of the
opens. In particular it needs **neither** of the instances
`[P.PreservesLeftHomologyOf (S.map R)]` and `[P.PreservesLeftHomologyOf S'']` at the
intermediate complexes as hypotheses; the paragraphs below say why.

***The square.*** `Stacks.Cohomology.AffineBase`
`.rightDerivedCompNatIso_restrictChosenResolution_square`
(`AffineCohomologyVanishing/RestrictionCollapseSquare.lean`), at `{X Y : RingedSpace}`, an
arbitrary open `V ⊆ Y`, an arbitrary additive `P` out of the modules on `V`, an arbitrary index
functor `E : Dc ⥤ Mod(𝒪_X)`, an arbitrary object `Z` and an arbitrary degree `p`, with **nothing
assumed of `f`** and nothing of `P` beyond additivity (axioms: `propext`, `Classical.choice`,
`Quot.sound`). Its hypotheses are exactly `hamb`, `hres`, their two instance copies at the `Z` in
question, and `τ` hoisted with its `rfl`-dischargeable `hτ`. Closure 249 modules.

The proof follows the reduction computed above, with three refinements.

1. **The second naturality is not needed, and neither is the instance at `S''`.** Applying
   `mapHomologyIso_inv_naturality` at the **composite** `a ≫ b` of the two short-complex maps — the
   one induced by `F'[c]` and the one induced by `e.hom[I]` — does in one step what the display's
   second and third bullets do in two, and it never names `S''`. So the glue asks the pointwise
   hypothesis at `S.map R` and at `S'` only.
2. **The remaining instance at `S.map R` is not a hypothesis either**, and that matters: nothing in
   the library inhabits it at the geometric data, the available degenerations being at the two
   *chosen resolutions* and not at the restriction of a short complex, so as a hypothesis it would
   have made the square unusable at the pair (c) needs. It follows from `hamb`, by
   `CategoryTheory.ShortComplex.preservesLeftHomologyOf_map`
   (`StacksFrontier/Algebra/Homology/ShortComplex/MapHomologyComp.lean`): for `R`
   preserving homology, the pointwise hypothesis on `R ⋙ P` at `S` gives the one on `P` at
   `S.map R`. The content is the converse of `CategoryTheory.Limits.comp_preservesLimit` —
   `R` carries the kernel fork of `S.g` to a limit fork, `R ⋙ P` carries it to a limit fork, and
   `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` turns the pair into preservation
   by `P` of the limit of the **image** diagram, transported along the two diagram isomorphisms
   `parallelPair φ 0 ⋙ R ≅ parallelPair (R.map φ) 0` that `preservesHomology_comp` also uses.
   Restriction to an open is exact, so `R.PreservesHomology` is free.
3. **`simp only [Functor.map_comp]` on the goal after the four chosen-resolution rewrites is
   refused with no progress**, the target not being type-correct at `implicit` transparency: the
   target edge writes the degree-`p` short complex of `F[I]` **restricted to `V`** as `(S.map R)`
   while the factor in front of it is `H ᵖ((L ⋙ F')[I])`, and the two objects are definitionally
   equal and distinct keys. So every step after the four rewrites is a **term**, and the expensive
   crossing is paid at variables: `CategoryTheory.ShortComplex`
   `.mapHomologyIso_glue_mapHomologicalComplex`
   (`StacksFrontier/Algebra/Homology/ShortComplex/MapHomologyGlueComplex.lean`) is the glue stated
   at the degree-`p` short complexes of the images of two complexes, in exactly the spellings the
   goal has, so that the consumer matches it syntactically. Written with the short-complex glue
   instantiated directly at the geometric data instead, the `exact` is a 200,000-heartbeat `whnf`
   timeout. Stating the glue at variables first avoids it.

*What the square is assembled from, and the two new segment lemmas.* The four chosen-resolution
readings are `…AffineBase.rightDerivedCompNatIso_hom_app` at the two pairs,
`…HigherDirectImage.compRightDerivedNatIso_inv_app_chosenResolution` for the source edge and
`…HigherDirectImage.higherDirectImageRestrictIso_chosenResolution` for the target edge. After them
the two paths differ by one `isoRightDerivedObj` cancellation on each side, the four-fold splitting
of `P` applied to the target edge, and the glue — and the bookkeeping is done at variables of an
abstract category by two additions to the designated leaf
`StacksFrontier/CategoryTheory/CompositeCancellation.lean`: `CategoryTheory.map_comp₄` and
`CategoryTheory.comp_square_cancel`. Both depend on **no axioms at all**. Two same-named
`private` declarations elsewhere do not collide: `comp_square_cancel` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeSingleModelCrossing.lean`
(which imports the leaf) and `map_comp₄` in
`StacksFrontier/Topology/Sheaves/Cohomology/CechRefinements/CohomologyCompatibility.lean`; they
duplicate the new public shapes.

***What the ψ-side join still owes.*** The square is the brick the join waits on; the join itself
— `prefix_transport_eq_openSubschemeSectionsComparison_comp` against
`collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`, across
`…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso`, with the square supplying the crossing
of the two collapses — is **not written**, and neither is anything downstream of it.

*What the join's instantiation of the square will and will not have to cross.* The square is
stated at `{X Y : RingedSpace}` with `P` out of the
modules on `…HigherDirectImage.restrictToOpen Y V`, while the restricted prefix
`prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` reads the collapse at
`(modulePushforward q.toLRSHom.toShHom, …DerivedSectionsLeray.sectionsOverOpen B.toSheafedSpace ⊤)`
for `q = f' ∣_ V` and `B = (V : Scheme)`, and the ambient prefix
`sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` reads it
at `(modulePushforward f', sectionsOverOpen Y' V)`. Four of the five crossings are free and the
fifth is **not**, and it is the one that decides the shape of the join:

* `restrictToOpen Y.toRingedSpace V = (V : Scheme).toRingedSpace` is **`rfl`**, so the square's
  `P` may be written at either spelling;
* both `(sectionsOverOpen (restrictToOpen Y.toRingedSpace V) ⊤).Additive` and
  `(sectionsOverOpen (V : Scheme).toRingedSpace ⊤).Additive` are found by `infer_instance`. The
  instance loss noted above for `moduleRestriction`'s three exactness instances under an
  ascription does **not** occur for the sections functor at the two spellings of the open
  subscheme;
* `moduleRestriction Y V ⋙ sectionsOverOpen (V : Scheme).toRingedSpace ⊤` **is**
  `sectionsOverOpen Y.toRingedSpace (V.ι ''ᵁ ⊤)` by **`rfl`** — fact **C** above, at the
  `Y.toRingedSpace` spelling;
* but `moduleRestriction Y V ⋙ sectionsOverOpen (V : Scheme) ⊤ = sectionsOverOpen Y V` is a
  reported **type mismatch**, not a failed `rfl`: the two functors' *targets* are
  `ModuleCat Γ(V.ι ''ᵁ ⊤, 𝒪_Y)` and `ModuleCat Γ(V, 𝒪_Y)`, different rings. So the square's
  ambient `G = (-|_V) ⋙ P` lands at `sectionsOverOpen Y (V.ι ''ᵁ ⊤)` and the ambient prefix's at
  `sectionsOverOpen Y V`; the join must carry
  `…TopDegreeBaseChange.sectionsOnImageTopNatIso` — **and the transport is of the base ring as
  well as of the functor**, so it is not a substitution and no ascription reaches it;
* `modulePushforward (restrictedMorphism f.toLRSHom.toShHom V) =`
  `modulePushforward (f ∣_ V).toLRSHom.toShHom` is **not** closed by `rfl` (the report is the
  inconclusive "definition is not exposed", at `getLimitCone` and `inv`).
  `…SchemeHigherDirectImage.toShHom_morphismRestrict` is the bridge, and
  `…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` is the `eqToIso` it is read
  through.

***The join's fifth crossing is two statements about the collapse and its outer functor.*** The
crossing the paragraph above calls "the hard one" — the square's ambient outer functor against the
`γ⁺` prefix's — is not a substitution and not an ascription, and it is not one step but **two**.
The square is stated at an arbitrary additive
`P : Mod(𝒪_{restrictToOpen Y V}) ⥤ W`, so its ambient outer functor is `(-|_V) ⋙ P` and its
restricted one is `P` itself; the `γ⁺` side's is `sectionsOverOpen Y V` and the `ψ` side's is
`sectionsOverOpen (V : Scheme) ⊤` with a restriction of scalars applied **outside** it. At
`P := sectionsOverOpen (V : Scheme) ⊤ ⋙ ModuleCat.restrictScalars (topIso V).inv.hom` — the one
choice that makes the ambient side isomorphic to `sectionsOverOpen Y V`, by
`sectionsOnImageTopNatIso` — the two steps needed are:

* **postcomposition**: the collapse at `G ⋙ R` against `R` of the collapse at `G`, which is what
  moves the `ψ` side's outer `ModuleCat.restrictScalars (topIso V).inv.hom` inside the collapse;
* **transport along an isomorphism of the outer functor**: the collapse at `G` against the
  collapse at `G'` for `α : G ≅ G'`, which is the `V.ι ''ᵁ ⊤`-versus-`V` crossing itself.

Nothing else in the library relates the comparison's values at two outer functors. Both are in
`AffineCohomologyVanishing/CollapseOuterFunctor.lean`, with **nothing assumed** of the index
functor, the object or the degree, nothing of the three functors beyond additivity and in
particular no exactness of the outer one (axioms: `propext`, `Classical.choice`, `Quot.sound`):

* `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_postcomp_square` — besides the two
  collapses' own pointwise hypotheses it asks only the pointwise hypothesis for `R` at the image
  short complex, which is free for an exact `R`, and its content is the composition law
  `CategoryTheory.ShortComplex.mapHomologyIso_comp_inv`;
* `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_natIso_square` — it asks **only** the two
  collapses' own pointwise hypotheses.

*The hinge of the second one, and the one Mathlib generalisation it needed.* The reduction is the
naturality of `CategoryTheory.ShortComplex.mapHomologyIso` in the **functor**, which Mathlib has as
`CategoryTheory.ShortComplex.homologyMap_mapNatTrans` — but in a section whose `variable` block
also asks that both functors preserve the **right** homology of the short complex. Only the left
ones are used, and only the left ones are available here: the degenerations
`hpl_of_isAffineOpen` and `preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen`
give `PreservesLeftHomologyOf` and nothing about right homology, and the two are genuinely
independent (one asks the kernel of `g` to be preserved, the other the cokernel of `f`). So
`CategoryTheory.ShortComplex.mapHomologyIso_inv_natTrans` is proved in the Mathlib-only
leaf `Algebra/Homology/ShortComplex/MapHomologyComp.lean`, read off Mathlib's
`LeftHomologyMapData.natTransApp` directly — it needs only the left hypotheses — and in the
`inv` arrangement the square meets it at. The companion under exactness of both functors is
`CategoryTheory.ShortComplex.mapHomologyIso_hom_natTrans`
(`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequenceSecondPage.lean`), mentioned in
the new lemma's notes;
it is **not** usable here for the same reason the functorial packaging
`…ModuleComparison.homologyMapFunctorIso` is not.

*And one further degeneration lemma the instantiation needs.* The
ambient outer functor the crossing goes through is `sectionsOverOpen Y (V.ι ''ᵁ ⊤) ⋙ res`, a
**composite**, and nothing in Mathlib or elsewhere in the library carries the pointwise homology
hypothesis across
a postcomposition: `…ShortComplex.preservesLeftHomologyOf_map`
(`StacksFrontier/Algebra/Homology/ShortComplex/MapHomologyComp.lean`) is the
opposite direction, and `CategoryTheory.Limits.comp_preservesLimit` is a lemma, so instance search
does not compose the two preservation hypotheses a left homology datum asks for.
`CategoryTheory.ShortComplex.preservesLeftHomologyOf_comp` is proved beside it, with nothing
assumed of the first functor beyond preservation of zero morphisms and homology-preservation asked
only of the second (axioms: `propext`, `Classical.choice`, `Quot.sound`). With it, `hamb` at the
composite follows from `hpl_of_isAffineOpen` at the open `V.ι ''ᵁ ⊤` — which is an affine open
because it **is** `V` — and the exactness of restriction of scalars; no second degeneration is
needed.

*Two bookkeeping shapes added to the leaf.* `CategoryTheory.comp_conj_cancel_square` and
`CategoryTheory.map_comp₃_cancel_mid` (`StacksFrontier/CategoryTheory/CompositeCancellation.lean`,
beside `comp_square_cancel` and `map_comp₄`, which the restriction square added). They are needed
for the same reason: after the two `rightDerivedCompNatIso_hom_app` rewrites the goal
carries `(((F[I]).sc n).map G).homology` and `Hⁿ((F ⋙ G)[I])` side by side, which are
definitionally equal and distinct keys, so the goal is not type-correct at `implicit` transparency
and `simp only` on it is refused with no progress.

*What these two do and do not do.* They are the
crossing's two **general** steps, stated at variables of abstract categories with the derived
transport hoisted onto a variable whose `rfl`-dischargeable reading on the chosen resolution is its
defining hypothesis — the discipline the restriction square follows for `τ`. **Neither is
instantiated at the geometric data, the square still has no consumer, and the ψ-side join is still
not written.**

*What the instantiation will and will not have to pay, at the geometric data
of (c), at `P := sectionsOverOpen (V : Scheme) ⊤ ⋙ ModuleCat.restrictScalars (topIso V).inv.hom` —
the one choice of the square's `P` that makes the ambient side meet the `γ⁺` prefix's outer
functor.* Seven facts:

* `restrictToOpen Y.toSheafedSpace V = (V : Scheme).toRingedSpace` is **`rfl`**, so `P` may be
  written at the open-subscheme spelling and handed to the square at the `restrictToOpen` one.
* `moduleRestriction Y.toSheafedSpace V ⋙ P` **is**
  `sectionsOverOpen Y.toSheafedSpace (V.ι ''ᵁ ⊤) ⋙ ModuleCat.restrictScalars (topIso V).inv.hom`
  by **`rfl`** — the square's ambient outer functor, at the spelling the crossing starts from.
* **`…TopDegreeBaseChange.sectionsOnImageTopNatIso Y V` typechecks on the nose as
  `moduleRestriction Y.toSheafedSpace V ⋙ P ≅ sectionsOverOpen Y.toSheafedSpace V`.** So the
  crossing's isomorphism is the existing one by defeq and **no new comparison of sections functors
  is needed**; the reading of this crossing above as needing a transport of the base ring "that no
  ascription reaches" is about the **functor equality**, which is indeed a type mismatch, and the
  iso is what stands in for it.
* **A spelling pair that matters.** `(P).Additive` — the square's one hypothesis on `P`
  — is **not** synthesised when `P` is typed at the `restrictToOpen Y.toSheafedSpace V` spelling,
  while `(sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙ ModuleCat.restrictScalars …).Additive`
  is found by `infer_instance`. The cure is `inferInstanceAs` at the unascribed spelling, the
  pattern `openSubschemeRestriction` already uses; an ascription does not fix it.
* `IsAffineOpen (V.ι ''ᵁ ⊤)` follows from `IsAffineOpen V` by `rw [Scheme.Opens.ι_image_top]`, so
  `hpl_of_isAffineOpen` applies at the open the composite outer functor takes sections over, and
  `preservesLeftHomologyOf_comp` then gives the square's `hamb`.
* `(ModuleCat.restrictScalars (topIso V).inv.hom).PreservesHomology` is found by
  `infer_instance`, so the postcomposition square's one extra pointwise hypothesis is free and so
  is the input to `preservesLeftHomologyOf_comp`.
* `(E ⋙ moduleRestriction X.toSheafedSpace (preimageOpen f V)).obj Z` **is**
  `(openSubschemeRestriction f V).obj (E.obj Z)` by **`rfl`**, so the two restricted index
  functors need no transport: `rightDerivedCompNatIso_hom_app` mentions the index only through
  `E.obj Z`, and the crossing between the two index spellings is that lemma applied twice. **No
  index-functor naturality for the collapse is needed.**
* `modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)` against
  `modulePushforward (f ∣_ V).toLRSHom.toShHom` is **not `rfl`** (the inconclusive
  "definition is not exposed", at `getLimitCone` and `inv`); but
  `congrArg modulePushforward (…SchemeHigherDirectImage.toShHom_morphismRestrict f V)` **is** the
  equality, so no `eqToIso` has to be built — what remains is that
  rewriting with it inside the collapse must carry the pointwise hypothesis `hres` along, which is
  what `…TopDegreeBaseChange.modulePushforwardMorphismRestrictIso` is read through.

***The three squares instantiated at the geometric data, and the crossing of the two
collapses.*** In `CollapseCrossingGeometric.lean`, at the one choice of the square's `P`
the paragraphs above identify,

> `P = …TopDegreeBaseChange.openSubschemeTopSections V = Γ((V : Scheme), ⊤, -) ⋙ res_{topIso V}`,

with nothing assumed of `f`, of `V`, of `E`, of `Z` or of the degree beyond the three pointwise
homology hypotheses the three collapses carry (axioms `propext`, `Classical.choice`, `Quot.sound`
throughout):

* `…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` — **the crossing.** The `ψ` side's
  collapse at `((f ∣ V)_*, Γ(V, ⊤, -))`, read under the restriction of scalars and followed by the
  comparison that moves it inside and by [Stacks, Tag 01E1]'s source edge inverted, is
  [Stacks, Tag 01E5] under `P`, the `V.ι ''ᵁ ⊤`-versus-`V` crossing of the ambient outer functor,
  **the collapse at `(f_*, Γ(V, -))` that the `γ⁺` side reads**, and the two derived transports.
* `…TopDegreeBaseChange.collapse_crossing_restrictOuterFunctor` — the same with the ambient
  collapse still at `(-|_V) ⋙ P`: the postcomposition square and the restriction square glued.
* `…TopDegreeBaseChange.ambient_outer_collapse_square` — the third square, at
  `…TopDegreeBaseChange.restrictCompSectionsIso V` inverted.
* `…TopDegreeBaseChange.hpl_imageTop_of_isAffineOpen`, `…hamb_openSubschemeTopSections` and
  `…hres_openSubschemeTopSections` — the squares' pointwise hypotheses from the two degenerations
  the join's own two sides carry; and `…restrictCollapseTransport_app`,
  `…ambientCollapseTransport_app` for the squares' `hτ` and `hρ`.

*Six facts about these.*

1. **The hoisted transports do not have to be written out: all three are canonical.** `τ` and `ρ`
   are `CategoryTheory.NatTrans.rightDerived` of the two comparisons of degreewise functors, whose
   `hτ`/`hρ` are `CategoryTheory.InjectiveResolution.rightDerived_app_eq`; `σ` is
   `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the **identity** comparison, whose
   `hσ` is `Stacks.Cohomology.AffineBase.rightDerivedCompIso_refl_hom_app_mapHomologyIso`, proved
   beside the postcomposition square (it is
   `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app`, which is `rfl`, with its
   middle factor replaced by `…AffineBase.mapComplexHomologyIso_refl_hom_app`). Written out as
   hypotheses instead, the three readings are a 200,000-heartbeat timeout in the statement.
2. **The crossing is three declarations, not one, and that is forced.** The glued statement
   elaborates; the three square applications inside one declaration do not, at any arrangement.
   So the first two are glued and the third joined on by the new
   `CategoryTheory.comp_glue_mid_square` (beside `…comp_glue_two_squares` and
   `…comp_glue_three_squares`, all three in the leaf
   `StacksFrontier/CategoryTheory/CompositeCancellation.lean`, none depending on any axioms).
3. **The one reassociation must be paid before `rightDerived`.**
   `CategoryTheory.Functor.whiskerRight` produces `(f_* ⋙ (-|_V)) ⋙ P` where the square asks for
   `f_* ⋙ (-|_V) ⋙ P`; crossing the two *after* `CategoryTheory.Functor.rightDerived` is a
   200,000-heartbeat `isDefEq` timeout at either placement, and at the level of a transformation of
   degreewise functors it costs nothing. Hence `…TopDegreeBaseChange.restrictCollapseNatTrans`.
4. **The spelling pair above matters in three further places, each with the same cure.**
   `(sectionsOverOpen (V : Scheme).toRingedSpace ⊤).Additive` is **not** synthesised as the
   collapse's outer functor, the intermediate category there being spelled through
   `restrictToOpen` — hence `…TopDegreeBaseChange.sectionsOnOpenSubschemeTop`, the same functor
   with its source declared. `(ModuleCat.restrictScalars (topIso V).inv.hom)`
   `.PreservesZeroMorphisms` is found standing alone and **not** as the second factor in
   `CategoryTheory.ShortComplex.preservesLeftHomologyOf_comp` at the pair the ambient hypothesis
   needs; the cure is to write it at the `structureSheafRing (V.ι ''ᵁ ⊤)` spelling of its source
   ring, which is `…TopDegreeBaseChange.imageTopRestrictScalarsOf`. And
   `…TopDegreeBaseChange.sectionsImageTopNatIsoOf` has to be re-ascribed, as
   `…TopDegreeBaseChange.restrictCompSectionsIso`, before `CategoryTheory.Functor.whiskerLeft` of
   it is affordable — unascribed it is a `whnf` timeout.
5. **The `hres` transport along `toShHom_morphismRestrict` is `simp only`, not `rw`.** `rw` leaves
   a motive that is not type correct, the additivity instance that fires at the restricted
   morphism being the bespoke `…HigherDirectImage.modulePushforwardRestrictedMorphism_additive`;
   `attribute [local instance 2000]` on the generic `modulePushforward_additive` does **not** fix
   it. `simp only` discharges it, the dependency being on a proof of a `Prop`-valued
   class — as also noted in `AlgebraicGeometry/ProjectiveCoherentImage/Basic.lean`.
6. **The degeneration route of the seven facts above holds.**
   `IsAffineOpen (V.ι ''ᵁ ⊤)` by `rw [Scheme.Opens.ι_image_top]`, then `hpl_of_isAffineOpen`, then
   `preservesLeftHomologyOf_comp`, gives the square's `hamb`; and
   `moduleRestriction Y V ⋙ openSubschemeTopSections V` **is**
   `Γ(V.ι ''ᵁ ⊤, -) ⋙ imageTopRestrictScalarsOf` by `rfl`, stated as
   `…TopDegreeBaseChange.moduleRestriction_comp_openSubschemeTopSections`.

***What the ψ-side join still owes.*** The crossing above is the brick the join waits
on and it is **not** the join. Three things remain:

* the crossing is stated at `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, the spelling
  the three squares are stated at, and the transport of the **whole equation** to Mathlib's
  `f ∣_ V` — which is what both `prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` and
  `prefix_transport_eq_openSubschemeSectionsComparison_comp` are stated at — is not performed.
  Only the pointwise hypothesis is carried across, in `hres_openSubschemeTopSections`;
* the two transports `…ambientCollapseTransport` and `…restrictCollapseTransport` are canonical
  and are **not** yet matched against the derived-transport factors the two sides actually carry,
  `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso` and
  `Stacks.DerivedIndexing.rightDerivedIso` read under the two outer functors. By point 1 above
  the squares' own readings are free, and what is owed is the identification of the canonical
  transports with those factors;
* the join itself — `prefix_transport_eq_openSubschemeSectionsComparison_comp` against
  `collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`, across
  `rightDerivedPlusRestrictSectionsIso`, with the crossing above supplying the crossing of the two
  collapses.

The composite identity `T = Γ(V, Θ) ≫ res_W` is not proved, and **no `@[stacks 0EX3 "(c)"]` is
placed anywhere**.

***The index half of the second remaining point; the morphism half is open.*** In
`CollapseCrossingTransport.lean`, with nothing assumed of `f`, of
`V`, of `E`, of `Z` or of the degree beyond the collapse's own pointwise hypothesis asked at both
index functors (axioms `propext`, `Classical.choice`, `Quot.sound` for both):

* `…TopDegreeBaseChange.collapse_index_crossing_morphismRestrict` — **the index passage.** The
  component at `Z` of Grothendieck's collapse at the pair `((f ∣_ V)_*, Γ(V, ⊤, -))` indexed by
  `E ⋙ …TopDegreeBaseChange.openSubschemeRestriction f V` is its component at `E.obj Z` when it
  is indexed by `openSubschemeRestriction f V` alone — which is the index
  `prefix_transport_eq_openSubschemeSectionsComparison_comp` carries.
* `…collapse_index_crossing_morphismRestrict_inv` — the same inverted, which is the direction the
  `ψ` side consumes it in, by `CategoryTheory.Iso.inv_eq_inv`.
* `…collapse_index_crossing_restrictedMorphism` — the same passage at the **other** spelling of
  the restricted morphism, the one `collapse_crossing_restrictedMorphism` is stated at, so that
  the crossing's own `ψ`-side collapse can be read at the single module `E.obj Z`. Stating it at
  both spellings rather than one is forced by point 2 below. **With these two, the only
  difference between the crossing's left-hand side and the factor the `ψ` side carries that is
  not a `def` unfolded is the spelling of the restricted morphism**, which is the first remaining
  point, discussed below. The other three — `openSubschemeRestriction f V` against
  `moduleRestriction X (preimageOpen f … V)`, `sectionsOnOpenSubschemeTop V` against
  `Γ((V : Scheme), ⊤, -)`, and `baseTopRestrictScalars V` against its `ModuleCat.restrictScalars`
  — are each the `def` and its body, so they unify in term position and are invisible to an `Eq`;
  they are *not* invisible to instance search, which is exactly point 2. The `hom`-versus-
  `inv` difference is likewise none: the crossing is an equation and the collapse an isomorphism.

*Three facts about this.*

1. **The index passage cannot be a general lemma, and `…AffineBase.rightDerivedCompNatIso_hom_app`
   is the whole of its general content.** The two components' types are
   `G(Rᵖ F (E'.obj Z)) ⟶ Rᵖ(F ⋙ G)(E'.obj Z)` at the two index readings; at variables of abstract
   categories those two objects are unrelated terms, so the equation does not typecheck at all
   without an `eqToHom` transport, and a lemma carrying one would move the cast rather than
   discharge it. At the geometric data they are the same term, and the proof is `_hom_app` twice
   joined by `Eq.trans` — the second application needing `haveI` to re-seat its pointwise instance
   at the second spelling of the object, instance search being syntactic. So "the crossing between
   the two index spellings is that lemma applied twice", and this is it.
2. **The two spellings of the restricted morphism cannot be mixed inside one statement — in both
   directions the failure is one of instance synthesis.** Written with the
   index functor spelled `E ⋙ moduleRestriction X.toSheafedSpace (preimageOpen f … V)` — the
   spelling the three squares and `collapse_crossing_restrictedMorphism` use — and the pushforward
   at Mathlib's `f ∣_ V`, the ambient category is pinned at the `restrictToOpen` spelling and
   `(modulePushforward (f ∣_ V).toLRSHom.toShHom).Additive` is **not** synthesised. And
   written with the index functor at `openSubschemeRestriction f V` — whose declared target is
   `(f ⁻¹ᵁ V : Scheme).toRingedSpace` — and the pushforward at
   `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`,
   `(modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).Additive` is **not** synthesised,
   the bespoke `…HigherDirectImage.modulePushforwardRestrictedMorphism_additive` being
   keyed on the `restrictToOpen` spelling of its source. Hence the index passage above is stated
   wholly at the `f ∣_ V` spelling, where it meets the `ψ` side, and **it does not compose with
   `collapse_crossing_restrictedMorphism`**, which is wholly at the other.
3. **So the first remaining point is not a `simp only` away.**
   `congrArg modulePushforward (…toShHom_morphismRestrict f V)` does typecheck and
   `…TopDegreeBaseChange.hres_openSubschemeTopSections` transports a *pointwise hypothesis* across
   it by `simp only`. But the crossing's equation, with its own transports, cannot be **written**
   at the `f ∣_ V` spelling: its two ends and its last factor
   `(restrictCollapseTransport f V p).app (E.obj Z)` are terms whose types name
   `modulePushforward (restrictedMorphism …)`, and that functor is only propositionally equal to
   the one at `f ∣_ V` (the instance failures of point 2 reject each spelling's statement before
   any proof). A statement at `f ∣_ V` therefore needs either
   `eqToHom` conjugation at three places — source, target and the transport — or a second
   instantiation of the three squares at `f ∣_ V`-ascribed spellings, i.e. `f ∣_ V` analogues of
   `restrictCollapseNatTrans`, `restrictCollapseTransport` and its `_app` reading, and of the
   ascribed outer functors. `simp only [toShHom_morphismRestrict f V]` is not what produces such
   a statement. (The paragraphs below show that the second option is the one that works.)

*The match the third remaining point needs against `rightDerivedPlusRestrictSectionsIso` turns
on one specific identification.* `rightDerivedPlusRestrictSectionsIso f V d F` is
`res_{topIso V}` of `Γ((V : Scheme), ⊤, -)` of `…SchemeHigherDirectImage`
`.rightDerivedPlusRestrictObjIso f V d F`, followed by `AlgebraicGeometry.openSectionsModuleIso`;
and the first two factors of `collapse_crossing_restrictedMorphism`'s right-hand side are
`openSubschemeTopSections V` of the **ringed-space** [Stacks, Tag 01E5]
`…HigherDirectImage.higherDirectImageRestrictIso` followed by `restrictCompSectionsIso`. So the
match is factor-for-factor, with two dictionary entries needed: the `ℕ`-versus-`ℤ`-indexed 01E5,
and `restrictCompSectionsIso` against `openSectionsModuleIso`. **The second is not definitional.**
`(restrictCompSectionsIso V).hom.app G = (openSectionsModuleIso G V).hom` does not typecheck: the
elaborator reports the two sources as `(moduleRestriction Y.toSheafedSpace V ⋙`
`openSubschemeTopSections V).obj G` against
`res.obj (ModuleCat.of Γ(↑V, ⊤) Γ(G.restrict V.ι, ⊤))`, and
`…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` — the identification of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` with the ringed-space restriction — is a
theorem proved by `unfold`/`congr 1`/`ext`, **not** `rfl`.

*The route for that match, read off the construction.* The cast is already
packaged where it is needed: `…SchemeHigherDirectImage.higherDirectImageRestrictIso f V p`
(`SchemeRestriction.lean:215`) **is** `eqToIso (higherDirectImageRestrictIso_source f V p) ≪≫`
the ringed-space 01E5 `≪≫ eqToIso (higherDirectImageRestrictIso_target f V p).symm`, and
`higherDirectImageRestrictIso_target` is exactly the `restrictFunctor`-versus-`moduleRestriction`
crossing the failed identification above lacks, while `higherDirectImageRestrictIso_source`
carries the `f ∣_ V`-versus-`restrictedMorphism` transport of the first remaining point. So both
missing casts are components of the scheme-level 01E5, and the match is assembled by unfolding
that definition rather than by building any new comparison. `rightDerivedPlusRestrictObjIso` is
the component of `…rightDerivedPlusRestrictIso`, which is that iso whiskered by
`Stacks.DerivedIndexing.rightDerivedIso` on both sides, so the `ℕ`-versus-`ℤ` entry is that
definition unfolded too.

***The crossing can be stated at `f ∣_ V`.*** Three facts, and the vocabulary they turn on.

1. *The route above is available.*
   `…SchemeHigherDirectImage.higherDirectImageRestrictIso f V p` is at
   `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SchemeRestriction.lean:215`, with
   `…_source` at `:184` and `…_target` at `:199`, and it **is**
   `eqToIso (…_source f V p) ≪≫` the ringed-space 01E5 `≪≫ eqToIso (…_target f V p).symm`: both
   casts are packaged. (There is no such family under `AlgebraicGeometry/HigherDirectImage/`.)
   One refinement: `…_source` is an equality of the *composites*
   `restrictFunctor (f ⁻¹ᵁ V).ι ⋙ (pushforward (f ∣_ V)).rightDerived p` and
   `moduleRestriction X (preimageOpen f V) ⋙ (modulePushforward (restrictedMorphism f V))`
   `.rightDerived p`, so it is the shape the **third** remaining point's match needs, not the
   atomic cast the first remaining point needs. That atomic cast is stated on its own, in
   `CollapseCrossingMorphismRestrict.lean`, as
   `…TopDegreeBaseChange.rightDerived_modulePushforward_morphismRestrict`, with
   `…TopDegreeBaseChange.higherDirectImageRestrictIsoMorphismRestrict` the ringed-space 01E5
   transported along it — 01E5 at `f ∣_ V` for `Functor.rightDerived`, with no `eqToHom` in its
   statement — and `…restrictCollapseNatTransMorphismRestrict`,
   `…restrictCollapseTransportMorphismRestrict` and its `_app` reading the `f ∣_ V` forms of the
   restriction square's transport.
2. *The statement is writable, in the vocabulary the `ψ` side actually carries.* The instance
   failures of point 2 above stand, and re-ascribing the missing additivity
   does not cure them: `RingedSpaceModuleAdjunction.modulePushforward` determines its own source
   and target from the morphism, so neither a type ascription nor `(C := …)` moves the instance's
   key. But the equation can be written at `f ∣_ V`. Written wholly in the pure `f ∣_ V`
   vocabulary
   (`openSubschemeRestriction f V`, `modulePushforward (f ∣_ V).toLRSHom.toShHom`,
   `sectionsOverOpen (V : Scheme).toRingedSpace ⊤`, `baseTopRestrictScalars V` — which is exactly
   what `prefix_transport_eq_openSubschemeSectionsComparison_comp` is stated in) every category is
   the one the pushforward names itself, every instance is found, and the whole crossing equation
   elaborates. The only instance that had to be added is
   `(openSubschemeRestriction f V).PreservesInjectiveObjects`.
3. *But the transport of the equation is not a rewrite.* `simp only [toShHom_morphismRestrict f V]`
   does **not** move the restricted morphism in that statement — it reports progress when the
   definitions involved are unfolded alongside, which makes the failure quiet, and the goal it
   leaves reads `f ∣_ V` throughout. `rw` is
   a motive failure, at a named position: `(openSubschemeTopSections V).obj` applied to an object
   spelled at `(V : Scheme).toSheafedSpace` while that functor's ascription pins its source at
   `restrictToOpen Y.toSheafedSpace V`. Writing that one factor unascribed removes that obstruction
   and exposes the next — the two `eqToIso` proof terms mention the equality being rewritten, and
   abstracting the morphism under an `eqToIso` is not type correct. And matching the transported
   crossing by `exact` is a 200,000-heartbeat `whnf` timeout whose mismatch cannot be
   pretty-printed.

***The transport, by substitution.*** The cast is handled at **variables**, but not by a
cancellation: a cancellation in
`StacksFrontier/CategoryTheory/CompositeCancellation.lean` taking the equation and the two
`eqToHom` conjugations to the conjugated one would *move* the cast onto the other side of the
equation, whereas hoisting the restricted pushforward onto a variable and **substituting**
discharges it. The declarations:

* `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq`
  (`AffineCohomologyVanishing/RestrictionCollapseSquareTransport.lean`) — the restriction-collapse
  square with the restricted pushforward on a variable `Q`, taking `Q = (f ∣ V)_*` and the two
  composite equalities it does *not* imply as **separate** hypotheses: `subst` is refused if the
  equality substituted along occurs in another hypothesis's type, and
  `CategoryTheory.Functor.rightDerived` takes additivity as an instance argument so the derived
  equality is not the underived one's `congrArg`. The proof is `subst`, then
  `CategoryTheory.eqToIso_refl` and `CategoryTheory.Iso.refl_trans`, then the restriction square.
* `…TopDegreeBaseChange.restrictCollapseSquare_morphismRestrict`
  (`CollapseCrossingMorphismRestrict.lean`) — **the square at Mathlib's `f ∣_ V`**: that transport
  instantiated at `Q = …TopDegreeBaseChange.openSubschemePushforward f V`, the pushforward along
  `f ∣_ V` *declared* at the ringed-space spellings of its source and target, with the three
  equalities and the ascribed transport `…restrictCollapseTransportAscribed` and its `_app`.

Three further facts about this route.

* Instantiating the transport directly at the pure `f ∣_ V` vocabulary elaborates and is then a
  **`(kernel) deterministic timeout`** — a harder wall than an elaborator timeout, which no
  raised heartbeat limit could have reached. Hoisting the pushforward into
  `openSubschemePushforward`, so that the two spellings of the two restricted spaces meet in that
  declaration alone and nowhere inside the equation, makes both the elaborator and the kernel
  accept the term.
* Restating that term's conclusion by hand is then **one** `isDefEq`: `exact` is a
  200,000-heartbeat `whnf` timeout, while `convert … using 2`, which splits it factor by factor,
  closes it. The hand-written statement on its own, and each of its three factors on its own,
  elaborate in seconds — so the cost is never the type identification, it is paying it at every
  implicit argument of the equation simultaneously.
* The four spelling defeqs are each `rfl`, and a module carrying all four checks in under a
  second: `restrictToOpen Y.toSheafedSpace V = (V : Scheme).toRingedSpace`,
  `restrictToOpen X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V)`
  `= (f ⁻¹ᵁ V : Scheme).toRingedSpace`,
  `moduleRestriction X.toSheafedSpace (preimageOpen f.toLRSHom.toShHom V)`
  `= openSubschemeRestriction f V`, and `openSubschemeTopSections V`
  `= sectionsOverOpen (V : Scheme).toRingedSpace ⊤ ⋙ baseTopRestrictScalars V`.

**Still owed, and no `@[stacks 0EX3 "(c)"]` is placed anywhere.** The square at `f ∣_ V` is a
brick not yet consumed. The join proper, and the tail identity `T = Γ(V, Θ)` followed by
restriction to `W`, remain; the match of the third remaining point is the next paragraph.

***The match of the third remaining point, and the one identification it turns on, which costs
exactly one `eqToHom`.*** In
`SectionsRestrictMatch.lean`, with **nothing assumed** of `f`, of `V`, of `M` or of the degree
(axioms `propext`, `Classical.choice`, `Quot.sound` for all twelve declarations):

* `…TopDegreeBaseChange.rightDerivedPlusRestrictObjIso_hom_eq` — **the `ℕ`-versus-`ℤ` index
  entry.** The sheaf-level 01E5 for `CategoryTheory.Functor.rightDerivedPlus` is
  `…SchemeHigherDirectImage.higherDirectImageRestrictIso` with
  `Stacks.DerivedIndexing.rightDerivedIso` at `f ∣_ V` inverted in front and `rightDerivedIso` at
  `f` read under the restriction to `V` behind. This is
  `…SchemeHigherDirectImage.rightDerivedPlusRestrictIso`'s two whiskerings unfolded and nothing
  else.
* `…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_eq` — **the cast entry**, at the level of
  natural transformations: the scheme-level 01E5 is the ringed-space one conjugated by
  `…higherDirectImageRestrictIso_source` and `…_target`. So the assembly is the definition
  unfolded.
* `…TopDegreeBaseChange.openSubschemeTopSections_map` and `…_map_comp` — the readings of the `ψ`
  side's outer functor on a **variable** morphism and a variable composite. Not cosmetic: see the
  kernel facts below.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq` — 01E5 on sections is the
  sheaf-level comparison read under `openSubschemeTopSections V`, then
  `AlgebraicGeometry.openSectionsModuleIso`.
* `…TopDegreeBaseChange.restrictCompSectionsIso_hom_app_eq` and
  `…openSectionsModuleIso_hom_eq` — **the second dictionary entry, in both directions.** Since
  `(restrictCompSectionsIso V).hom.app G = (openSectionsModuleIso G V).hom` does not typecheck,
  the two are compared up to transport: they differ by **one** `eqToHom`, the transport along
  `…SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` at the module, and by nothing
  else. The three ingredients are `…heq_restrictCompSectionsIso_hom_app`,
  `…heq_openSectionsModuleIso_hom` — one application of
  `Stacks.Cohomology.HigherDirectImage.heq_val_map_eqToHom` each, both maps being the restriction
  along `V.ι ''ᵁ ⊤ = V` — and `…heq_eqToHom_transport_app`, the transport moving no section.
  **The module structure via `restrictAppIso` causes no further obstruction**:
  `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` in Mathlib, so
  `openSectionsIso`'s leading factor contributes nothing and the two maps are the same restriction
  map; only the module **instance** on the sections differs, which is what the one `eqToHom`
  carries.
* `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq_restrictCompSectionsIso` —
  **the match**: the two index comparisons, the scheme-level sheaf comparison under
  `openSubschemeTopSections V`, the one cast, and `restrictCompSectionsIso`. Its last factor is
  the second of the two the right-hand side of `collapse_crossing_restrictedMorphism` begins with,
  and the first of those two is `higherDirectImageRestrictIso_hom_eq` away from its second factor.

*What decided every proof there, which is the same obstruction met elsewhere in these notes.*
`rfl` on the assembled equations **elaborates** and is then a `(kernel) deterministic timeout`:
01E5-on-sections with the outer functor applied to the whole composite, the cast entry with
`.app M` on both sides, and the five-factor form of the index entry naming both `eqToIso` casts
and the ringed-space comparison at `M` in one equation — while each of that form's factors on its
own, and the composite of its first two, check in seconds. Hoisting onto variables is the cure, and
it is why the two readings of the outer functor are declared. Separately, `simp only` and `rw` do
not find their patterns at these spellings: `CategoryTheory.Iso.trans_hom` and `Iso.trans_refl` in
`(eqToIso _ ≪≫ ringed 01E5 ≪≫ eqToIso _).hom.app M`, `Functor.map_comp` in
`(openSubschemeTopSections V).map (a ≫ b ≫ c)`, `Category.assoc` in `(a ≫ b ≫ c) ≫ (d ≫ e)`, and
`ModuleCat.comp_apply` after `ext x` — each reporting "did not find an occurrence" with the subterm
printed in the goal, and `rw [openSubschemeTopSections_map_comp]` failing instead with "the target
expression is not type-correct under the `implicit` transparency level". So the splitting and the
reassociation are `congrArg` at an explicit lambda, and the two dictionary entries are
`ModuleCat.hom_ext (LinearMap.ext …)`.

*Why `…heq_eqToIso_trans_val_app` does not serve the transport, although it is the obvious
candidate.* That lemma is the same content for `eqToIso e ≪≫ α`; reaching
`heq_eqToHom_transport_app` from it at `α := Iso.refl _` needs `Iso.trans_refl`, which is the
second of the four pattern failures above. The transport is proved instead by `subst` under a
`suffices` that quantifies over the functor and the equality — the equality
`restrictFunctor V.ι = moduleRestriction Y V` has no free variable on either side, so `subst` does
not reach it directly. `Stacks.TensorSheafWorld.heq_eqToHom_val_app` is the same statement for a
family indexed by `ℤ`, and the family here is indexed by a functor category, so nothing is
duplicated.

**What the third remaining point still leaves, and no `@[stacks 0EX3 "(c)"]` is placed
anywhere.** The join proper — `prefix_transport_eq_openSubschemeSectionsComparison_comp` against
`collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`, across
`rightDerivedPlusRestrictSectionsIso`, with the square of
`restrictCollapseSquare_morphismRestrict` supplying the crossing of the two collapses — is **not**
performed, and neither is the tail identity `T = Γ(V, Θ)` followed by restriction to `W`. The
match is a dictionary between two readings of 01E5 on sections; it is not the join.

***The join's identification; the one `Eq.trans` that welds it onto
`rightDerivedPlusRestrictSectionsIso` hits a kernel timeout.*** In
`CollapseCrossingSectionsJoin.lean`, with **nothing assumed** of `f`, of `V`, of `M` or of the
degree (axioms `propext`, `Classical.choice`, `Quot.sound` for all twelve declarations, three of
them depending on none):

* `…TopDegreeBaseChange.higherDirectImageRestrictIso_hom_app_comp_restrictCompSectionsIso_eq` and
  `…TopDegreeBaseChange.schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq` — **the
  identification the join is made of, in both orientations.** The source cast of the scheme-level
  [Stacks, Tag 01E5] and the **ringed-space** 01E5, both read under `openSubschemeTopSections V`,
  then `restrictCompSectionsIso` at `Rᵖ f_* M` and the sections over `V` of
  `Stacks.DerivedIndexing.rightDerivedIso` at `f`, are the scheme-level 01E5 read under the outer
  functor followed by the three factors the match carries after it. The second and third factors
  on the left are **exactly** the two the right-hand side of `collapse_crossing_restrictedMorphism`
  begins with, so this is the adjacency the paragraph above calls the join.
* `…TopDegreeBaseChange.whiskerRight_higherDirectImageRestrictIso_hom_eq` and
  `…openSubschemeTopSections_map_higherDirectImageRestrictIso_hom_app` — the split of the
  scheme-level 01E5 under the outer functor, paid at the **transformation** level.
* `…TopDegreeBaseChange.restrictCompSectionsIso_hom_app_naturality_of_eq` and its instantiation
  `…_rightDerivedIso` — the step that moves `restrictCompSectionsIso` to the front, with the
  conjugating casts as variables; `…moduleRestriction_map_eq_restrictFunctor_map`,
  `…eqToIso_higherDirectImageRestrictIso_target_hom_app` and
  `…higherDirectImageRestrictIso_target_app_comp_restrictFunctor_map` are the cast readings it is
  applied with.

*What is still owed, and it is one step.* With the identification in hand the join is one
`Eq.trans` with the match and one cancellation of `rightDerivedIso` at `f` against its inverse.
**Six routes to that `Eq.trans` are each a `(kernel) deterministic timeout`** on a term that
elaborates with no error: all four combinations of the orientations of the identification and of
the conclusion; the same with the match re-elaborated right-hand side first in its own declaration,
so that both sides' implicit arguments come from one elaboration; and `refine … ?_` closed by
`exact (match).symm` — which the elaborator accepts and the kernel rejects — or by
`convert (match).symm using 2` and `using 3`, which leave an unsolved goal. So the obstruction is
not the orientation discipline, not the association and not a missing mathematical step.

***Nor is it the match: re-proving the match in the target factors does not help, and the
obstruction is located as follows.*** One might expect the cost to be the
`Eq.trans` whose middle term is the match's five-factor right-hand side, so that a match re-proved
in the crossing's own factors would avoid it; this is **not** so. Write `a` for the leading
factor — `openSubschemeTopSections V` of `Stacks.DerivedIndexing.rightDerivedIso` at `f ∣_ V`
inverted — and `L`, `R` for the two sides of
`schemeHigherDirectImageRestrictIso_hom_app_comp_tail_eq`.

* **The match re-proved directly in the target factors is the same timeout.** The statement
  `(01E5 on sections).hom = a ≫ R`, proved by a term-level segment lemma out of
  `rightDerivedPlusRestrictSectionsIso_hom_eq`, the split of the sheaf-level comparison and
  `openSectionsModuleIso_hom_eq` — so that the five-factor composite is never the middle term of
  any `Eq.trans` — is a `(kernel) deterministic timeout`. So is the same chase run from the new
  `…TopDegreeBaseChange.rightDerivedPlusRestrictSectionsIso_hom_eq_cast_comp`, which unfolds
  `rightDerivedPlusRestrictSectionsIso` one step further before the chase: that declaration
  **checks in seconds**, and the weld built on it does not.
* **The statement is not the cost.** `a ≫ R = a ≫ L`, `a ≫ L = a ≫ L` and `(R = L) = (R = L)` all
  check, the three together in 23 s.
* **The match is not the cost.** `L = R` restated in a fresh declaration and proved from the
  stored one checks, the whole module in 24 s.
* **The head is the cost.** `a ≫ R = a ≫ L` is a timeout under every proof tried:
  `comp_congr_right _ identification` at either orientation of the identification and of the
  conclusion; a five-factor term segment lemma `comp_congr_right a (comp₄_split_head_absorb …)`
  fed the identification's own two ingredients, at either orientation, so that the identification
  is rebuilt inline rather than compared against a stored statement; and the same with `a` in the
  whiskered spelling `(Functor.isoWhiskerLeft _ (rightDerivedIso _ p).symm).hom.app M`, which makes
  the junction `target a = source R` syntactic — the uncomposed `.obj` of
  `CategoryTheory.Functor.comp` against the composite one — and changes nothing.

So the wall is **precomposing this identification with one further factor**, where neither
composite, nor the proposition equating them, nor the identification itself is expensive on its
own. A route that is to move it must avoid ever holding `a ≫ L` and `a ≫ R` in one proof term;
avoiding only the five-factor middle term, which is what all four routes above do, is not enough.

*Four further elaboration facts.*

1. **Carrying the module-level cast entry under `openSubschemeTopSections V` is a kernel timeout in
   every form.** `congrArg (fun t => (openSubschemeTopSections V).map t)` at the cast entry; the
   same with that `congrArg` hoisted into a lemma at variable morphisms; `openSubschemeTopSections`
   `_map_comp` against the composite spelled `(higherDirectImageRestrictIso f V p).hom.app M`,
   relying on the definitional unfolding instead of an equation, at one split and at the full
   three-way split; and a generic `G.map (a ≫ b ≫ c) = G.map a ≫ G.map b ≫ G.map c` as a term.
   What is **cheap** is the same `…map_comp` at the same morphisms with the composite written out,
   and the cast entry itself at a module — so the cost is identifying the comparison with the
   explicit composite *underneath* the outer functor, and whiskering the cast entry and taking the
   component afterwards avoids that identification entirely.
2. **The orientation decides whether the identification can be proved at all.** With the crossing's
   own factors first it checks in seconds; with the match's factors first the **same** term is a
   kernel timeout, and `simp only` and `rw` fail at either orientation. The match-first orientation
   is then reached by `Eq.symm` **in its own declaration**, where it checks; inside a larger term
   it does not.
3. **A segment lemma proved by `rw`/`simp only` at variables is not interchangeable with the same
   lemma proved as a term.** `comp₅_split_mid_absorb`, nine variables and a two-line tactic proof,
   is a kernel timeout when instantiated at these composites, because a rewrite's `Eq.mpr` motives
   are then type-checked at the concrete objects; the term-proved `comp₄_split_head_absorb` is not.
   That is why the segment rewrites in that file are terms.
4. **Naming an instantiation is not cosmetic.** Writing the naturality step inline inside the
   gluing makes the unifier solve for its six implicit arguments together with the gluing's nine,
   which is a kernel timeout; with the instantiation declared, both check in seconds.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)


/-- **[Stacks, Tag 01XK] over the affine open `V`, inverted and read off its construction.** The
identification of the degree-`d` cohomology of `F'` over `f'⁻¹(V)` with the sections of
`R^d f'_* F'` over `V` is, inverted, the identification of those sections with the global sections
of the restriction to `V`, then [Stacks, Tag 01E5] inverted and [Stacks, Tag 01XK] inverted. The
equality holds by definition. -/
theorem affineOpenCohomologyIsoSectionsOf_inv_eq :
    haveI := S.quasiCompact_f'
    haveI := S.quasiSeparated_f'
    (affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
        (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv =
      (openSectionsModuleIso
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') V).inv ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map
              (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').inv ≫
            (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
              ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩) := rfl

/-- **The crossing to the module conclusion (b) tensors with, read off its construction.** It is
the comparison of the two indexings of the right derived functors, inverted, followed by the
transport along `…TopDegreeBaseChangeSituation.restrictBase_appTop_eq_algebraMap`. The equality
holds by definition. -/
theorem affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology_hom_eq :
    (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom =
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
          ((ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
            ((Stacks.DerivedIndexing.rightDerivedIso
                (Stacks.Cohomology.AffineBase.moduleGlobalSections
                  (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))) ≫
        eqToHom (congrArg
          (fun φ : (S.restrictBase V).affineBaseRing →+*
                Γ(((S.restrictBase V).affineBaseOver).left, ⊤) =>
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
              ((ModuleCat.restrictScalars φ).obj
                (((Stacks.Cohomology.AffineBase.moduleGlobalSections
                    (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).obj
                  ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))))
          (S.restrictBase_appTop_eq_algebraMap V).symm) := rfl


/-! ### Generic cancellations, at variables -/

/-- **A head factor cancelled against the leading factor of a known factorisation.** If
`p ≫ p' = 𝟙` and `q` factors as `p' ≫ r`, then `p ≫ q` is `r`. At variables, with the
invertibility given on plain morphisms. -/
private theorem cancel_comp_head {C : Type*} [Category* C] {A B D : C} {p : A ⟶ B} {p' : B ⟶ A}
    (hp : p ≫ p' = 𝟙 A) {q : B ⟶ D} {r : A ⟶ D} (hq : q = p' ≫ r) : p ≫ q = r := by
  rw [hq, ← Category.assoc, hp, Category.id_comp]

/-- **A five-fold factorisation through a functor, extended by one more factor inside the
functor.** If `m` factors as `(p ≫ x ≫ y) ≫ z ≫ G.map t`, then `m ≫ G.map n` factors the same
way with `t ≫ n` in the last place. Stated at variables, where the reassociation is free. -/
private theorem comp_map_glue {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₁ A₂ A₃ : C} {B₀ B₁ B₂ B₃ : D} {m : B₀ ⟶ G.obj A₂}
    {p : B₀ ⟶ B₁} {x : B₁ ⟶ B₂} {y : B₂ ⟶ B₃} {z : B₃ ⟶ G.obj A₁} {t : A₁ ⟶ A₂}
    (hm : m = (p ≫ x ≫ y) ≫ z ≫ G.map t) {nn : A₂ ⟶ A₃} {t' : A₁ ⟶ A₃}
    (ht : t ≫ nn = t') :
    m ≫ G.map nn = p ≫ x ≫ y ≫ z ≫ G.map t' := by
  rw [hm, ← ht, G.map_comp]
  simp only [Category.assoc]

/-- **The first cancellation of the `ψ` side.** The comparison of the two indexings of the right
derived functors at `F'|`, inverted, followed by the pullback map on cohomology over the
compatible pair of affine opens and by the crossing of the two readings of the cohomology
upstairs, is [Stacks, Tag 01XK] over `V`, then the sections over `V` of the degree-`d` higher
direct image along `f' ∣_ V` of the unit of `(h' ∣)^* ⊣ (h' ∣)_*`, then [Stacks, Tag 01XK]
inverted, the two indexings crossed back, the Leray comparison of [Stacks, Tag 089W] along the
affine `h' ∣` inverted, and the crossing of the two readings upstairs.

The leading comparison of `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_eq_sections`
`_rightDerivedPlus_unit` is what cancels; nothing else is touched. -/
theorem rightDerivedIso_inv_comp_restrictScalars_pullbackMap :
    haveI := S.quasiCompact_f'
    haveI := S.quasiSeparated_f'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV (preimage_le_preimage_of_isPullback hsq hWV)
    haveI := AffineBaseChange.isQuasicoherent_pullback
      (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
      ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
    (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
          ((Stacks.DerivedIndexing.rightDerivedIso
              (Stacks.Cohomology.AffineBase.moduleGlobalSections
                (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) ≫
        (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
          (affineOpenCohomologyPullbackMap hsq hWV
              (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
            (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
              (restrictPullbackRightDerivedPlusIso h'
                (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) =
      (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).hom.app
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩ ≫
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map
            (((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                  (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                    (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))) ≫
          (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
              ⟨(Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV))).obj
                ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                    (preimage_le_preimage_of_isPullback hsq hWV))).obj
                  ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')), inferInstance⟩ ≫
            (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                    (Stacks.Cohomology.AffineBase.moduleGlobalSections
                      (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
                  ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV))).obj
                    ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                        (preimage_le_preimage_of_isPullback hsq hWV))).obj
                      ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))) ≫
                (cohomologyPullbackIsoPushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV))
                    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
                    (Scheme.Modules.isQuasicoherent_restrictFunctor
                      (S.f' ⁻¹ᵁ V).ι F') S.d).inv ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have := isAffineHom_resLE_of_isPullback hsq hWV (preimage_le_preimage_of_isPullback hsq hWV)
  have := AffineBaseChange.isQuasicoherent_pullback
    (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
  refine cancel_comp_head
    (map_comp_cancel _ ((Stacks.DerivedIndexing.rightDerivedIso
      (Stacks.Cohomology.AffineBase.moduleGlobalSections
        (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv_hom_id_app _)) ?_
  exact (Functor.map_comp _ _ _).trans
    (comp_map_glue (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom)
      (affineOpenCohomologyPullbackMap_eq_sections_rightDerivedPlus_unit hsq hWV
        (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d)
      (Category.assoc _ _ _))


/-- **A head factor split off under a functor.** If `a ≫ d` factors as `u ≫ v`, then
`G.map a ≫ G.map d ≫ t` is `G.map u ≫ G.map v ≫ t`. At variables, where the functoriality and the
reassociation are free. -/
private theorem split_head_map {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {T : D} {a : A₀ ⟶ A₁} {d : A₁ ⟶ A₂} {u : A₀ ⟶ A₃} {v : A₃ ⟶ A₂}
    (h : a ≫ d = u ≫ v) (t : G.obj A₂ ⟶ T) :
    G.map a ≫ G.map d ≫ t = G.map u ≫ G.map v ≫ t := by
  rw [← Category.assoc, ← G.map_comp, h, G.map_comp, Category.assoc]

/-- **A cancelling pair in the second and third places of a composite.** At variables, with the
invertibility given on plain morphisms. -/
private theorem cancel_inner {C : Type*} [Category* C] {A B D E : C} (a : A ⟶ B) {b : B ⟶ D}
    {c : D ⟶ B} (hbc : b ≫ c = 𝟙 B) (d : B ⟶ E) : (a ≫ b) ≫ c ≫ d = a ≫ d := by
  rw [Category.assoc, ← Category.assoc b c d, hbc, Category.id_comp]

omit [F'.IsQuasicoherent] [IsAffine (V : Scheme)] in
/-- **The identity functor may be dropped from the coefficient of [Stacks, Tag 01E5].** The
comparison of the restricted higher direct image with the restriction of the higher direct image
at `(𝟭 _).obj F'` and at `F'` is one and the same isomorphism. Split off as its own `rfl` so that
the definitional step is checked once, here, and not inside a chase: inside one it makes the
kernel unfold the comparison underneath `CategoryTheory.Functor.rightDerivedPlus`. -/
theorem rightDerivedPlusRestrictObjIso_id_obj :
    SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d
        ((𝟭 (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace))).obj F') =
      SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F' := rfl

/-- **The `ψ` side read as the ordinary unit followed by a tail.** With the head matching of
`…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE` supplied as the hypothesis `hr` — which
fixes `u` as the restriction to `V` of the degree-`d` higher direct image of the ordinary unit of
`(h')^* ⊣ (h')_*` and `v` as the comparisons that follow it — the two leading comparisons of the
`ψ` side cancel and what is left is `u`, then `v`, then a tail in which no unit occurs:
[Stacks, Tag 01XK] over `V` inverted, the two indexings of the right derived functors crossed
back, the Leray comparison of [Stacks, Tag 089W] along the affine `h' ∣` inverted, and the
crossing of the two readings of the cohomology upstairs.

Stated with `u` and `v` as variables carrying `hr`: the comparisons the head matching produces are
long, and nothing here depends on their shape. -/
theorem sections_pullbackMap_eq_unit_comp_tail
    {Tgt : S.Y'.Modules}
    {ξ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F' ⟶ Tgt}
    {v : (Scheme.Modules.restrictFunctor V.ι).obj Tgt ⟶
      ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))).obj
          ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).obj
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')))}
    (hr : ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').hom ≫
          (Scheme.Modules.restrictFunctor V.ι).map ξ ≫ v) :
    haveI := S.quasiCompact_f'
    haveI := S.quasiSeparated_f'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV (preimage_le_preimage_of_isPullback hsq hWV)
    haveI := AffineBaseChange.isQuasicoherent_pullback
      (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
      ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').inv ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩) ≫
      ((ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
            ((Stacks.DerivedIndexing.rightDerivedIso
                (Stacks.Cohomology.AffineBase.moduleGlobalSections
                  (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) ≫
          (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
            (affineOpenCohomologyPullbackMap hsq hWV
                (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
              (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                (restrictPullbackRightDerivedPlusIso h'
                  (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv)) =
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map
          ((Scheme.Modules.restrictFunctor V.ι).map ξ) ≫
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map v ≫
          (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
              ⟨(Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV))).obj
                ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                    (preimage_le_preimage_of_isPullback hsq hWV))).obj
                  ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')), inferInstance⟩ ≫
            (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                    (Stacks.Cohomology.AffineBase.moduleGlobalSections
                      (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
                  ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV))).obj
                    ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                        (preimage_le_preimage_of_isPullback hsq hWV))).obj
                      ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))) ≫
                (cohomologyPullbackIsoPushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV))
                    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
                    (Scheme.Modules.isQuasicoherent_restrictFunctor
                      (S.f' ⁻¹ᵁ V).ι F') S.d).inv ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have := isAffineHom_resLE_of_isPullback hsq hWV (preimage_le_preimage_of_isPullback hsq hWV)
  have := AffineBaseChange.isQuasicoherent_pullback
    (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
  refine (congrArg (fun z => ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (V : Scheme)).map
          (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').inv ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩) ≫ z)
      (rightDerivedIso_inv_comp_restrictScalars_pullbackMap S F' h' f'' h hsq hWV)).trans ?_
  refine (cancel_inner _
    ((cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv_hom_id_app
      ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩) _).trans ?_
  exact split_head_map _
    (cancel_comp_head
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').inv_hom_id hr) _

/-- **A commuting square solved for the inverse of its left edge.** At variables of an abstract
category. -/
private theorem inv_comp_of_comp_hom {C : Type*} [Category* C] {A B D E : C} {i₁ : A ≅ B}
    {i₂ : D ≅ E} {f : A ⟶ D} {g : B ⟶ E} (hfg : f ≫ i₂.hom = i₁.hom ≫ g) :
    i₁.inv ≫ f = g ≫ i₂.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hfg, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Restriction of scalars along two equal ring maps, with the transport moved across a
morphism.** At variables of the three rings, where the substitution is free. -/
private theorem eqToHom_restrictScalars_chase {R T A : Type u} [Ring R] [Ring T] [Ring A]
    (a : R →+* T) {φ χ : T →+* A} (hφ : φ = χ) {M N : ModuleCat.{u} A} (Z : M ⟶ N)
    {Q : ModuleCat.{u} T} (Y : (ModuleCat.restrictScalars χ).obj N ⟶ Q) :
    eqToHom (congrArg (fun ρ : T →+* A =>
          (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars ρ).obj M)) hφ) ≫
        (ModuleCat.restrictScalars a).map ((ModuleCat.restrictScalars χ).map Z ≫ Y) =
      (ModuleCat.restrictScalars a).map ((ModuleCat.restrictScalars φ).map Z) ≫
        eqToHom (congrArg (fun ρ : T →+* A =>
            (ModuleCat.restrictScalars a).obj ((ModuleCat.restrictScalars ρ).obj N)) hφ) ≫
          (ModuleCat.restrictScalars a).map Y := by
  subst hφ
  simp

/-- **Two factors of a three-fold composite substituted.** At variables of an abstract
category. -/
private theorem comp_congr₂ {C : Type*} [Category* C] {A B D T : C} {a a' : A ⟶ B}
    (ha : a = a') {b b' : B ⟶ D} (hb : b = b') (t : D ⟶ T) :
    a ≫ b ≫ t = a' ≫ b' ≫ t := by
  rw [ha, hb]

/-- **Three factors through a functor collected, with what follows them given by a known
factorisation.** At variables of abstract categories, where every reassociation and every use of
functoriality is free. -/
private theorem collect_three_map {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₀ E T : D} {B₁ B₂ B₃ B₄ : C} (o : A₀ ⟶ G.obj B₁) (c₁ : B₁ ⟶ B₂) (c₂ : B₂ ⟶ B₃)
    {ee : G.obj B₃ ⟶ E} {m : E ⟶ T} {m₁ : B₃ ⟶ B₄} {rest : G.obj B₄ ⟶ T}
    (hm : ee ≫ m = G.map m₁ ≫ rest) :
    (o ≫ G.map c₁) ≫ (G.map c₂ ≫ ee) ≫ m = o ≫ G.map (c₁ ≫ c₂ ≫ m₁) ≫ rest := by
  simp only [Category.assoc]
  rw [hm, G.map_comp, G.map_comp]
  simp only [Category.assoc]

/-- **The two leading factors of the `ψ` side, with the transport pushed past the geometry.** For
any morphism `Z` out of the degree-`d` cohomology of `F'|` over `f'⁻¹(V)` and any `Y` out of its
target with the scalars restricted, [Stacks, Tag 01XK] over `V` inverted, the crossing to the
module conclusion (b) tensors with, and `Z` then `Y` read over `Γ(Y', V)` are: the global sections
of the restriction read as the sections over `V`, inverted; then [Stacks, Tag 01E5] and
[Stacks, Tag 01XK] inverted, the two indexings crossed and `Z`, all read over `Γ(Y', V)`; then the
transport along `…restrictBase_appTop_eq_algebraMap`; then `Y`.

Both `Z` and `Y` are variables: this is the bookkeeping of the two leading factors, and nothing in
it depends on the geometry they carry. -/
theorem affineOpenCohomologyIsoSectionsOf_inv_comp_restrictBase_comp
    {NN : ModuleCat.{u} Γ((S.f' ⁻¹ᵁ V : Scheme), ⊤)}
    (Z : ((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).obj
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ⟶ NN)
    {Q : ModuleCat.{u} Γ((V : Scheme), ⊤)}
    (Y : (ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
        Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).obj NN ⟶ Q) :
    haveI := S.quasiCompact_f'
    haveI := S.quasiSeparated_f'
    (affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
          (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
        (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map Z ≫ Y) =
      (openSectionsModuleIso
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') V).inv ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            (((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map
                  (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').inv ≫
                (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
                  ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩) ≫
              ((ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
                  ((Stacks.DerivedIndexing.rightDerivedIso
                      (Stacks.Cohomology.AffineBase.moduleGlobalSections
                        (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
                    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) ≫
                (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map Z)) ≫
          eqToHom (congrArg
              (fun ρ : (S.restrictBase V).affineBaseRing →+*
                    Γ((((S.restrictBase V).affineBaseOver)).left, ⊤) =>
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
                  ((ModuleCat.restrictScalars ρ).obj NN))
              (S.restrictBase_appTop_eq_algebraMap V).symm) ≫
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map Y := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  exact (comp_congr₂ (affineOpenCohomologyIsoSectionsOf_inv_eq S F')
      (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology_hom_eq S F') _).trans
    (collect_three_map (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) _ _ _
      (eqToHom_restrictScalars_chase _ (S.restrictBase_appTop_eq_algebraMap V).symm Z Y))

/-! ### The sections of a restriction, naturally -/

section OpenSections

variable {Z : Scheme.{u}} (U : Z.Opens) {M N : Z.Modules}

/-- **The global sections of a restriction are the sections over the open, naturally in the sheaf
of modules.** `AlgebraicGeometry.openSectionsModuleIso` is the restriction map of the module along
the equality `U.ι ''ᵁ ⊤ = U` of opens, so its naturality is the naturality of the underlying map
of presheaves of abelian groups. -/
theorem openSectionsModuleIso_hom_naturality (ξ : M ⟶ N) :
    (ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).map
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections (U : Scheme)).map
            ((Scheme.Modules.restrictFunctor U.ι).map ξ)) ≫
        (openSectionsModuleIso N U).hom =
      (openSectionsModuleIso M U).hom ≫ ξ.val.app (op U) := by
  ext x
  exact (ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf ξ).naturality
      (eqToHom (Scheme.Opens.ι_image_top U).symm).op) x).symm

/-- The two spellings of the comparison of the functions on `V` with the global sections of the
open subscheme — as the inverse of `AlgebraicGeometry.Scheme.Opens.topIso` and as the ring
equivalence its inverse determines — are one ring map. -/
theorem topIso_symm_ringEquiv_eq {Z : Scheme.{u}} (U : Z.Opens) :
    (((Scheme.Opens.topIso U).symm.commRingCatIsoToRingEquiv : Γ(Z, U) →+* Γ((U : Scheme), ⊤))) =
      (Scheme.Opens.topIso U).inv.hom := rfl

end OpenSections

/-! ### The `ψ` side as the ordinary unit followed by a tail -/

/-- **The first factor of a composite substituted.** At variables of an abstract category. -/
private theorem comp_congr_left {C : Type*} [Category* C] {A B D : C} {a a' : A ⟶ B}
    (ha : a = a') (b : B ⟶ D) : a ≫ b = a' ≫ b := by
  rw [ha]

/-- **A head factor shifted across a reassociation.** At variables of an abstract category. -/
private theorem assoc_shift {C : Type*} [Category* C] {A B D E T : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : D ⟶ E) (d : E ⟶ T) : (a ≫ b) ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

/-- **The argument of a functor substituted inside a four-fold composite.** At variables of
abstract categories. -/
private theorem map_arg_congr {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₀ T₁ T₂ T₃ : D} {B₁ B₂ : C} (i : A₀ ⟶ G.obj B₁) {z z' : B₁ ⟶ B₂} (hz : z = z')
    (ee : G.obj B₂ ⟶ T₁) (mm : T₁ ⟶ T₂) (rsc : T₂ ⟶ T₃) :
    (i ≫ G.map z ≫ ee ≫ mm) ≫ rsc = (i ≫ G.map z' ≫ ee ≫ mm) ≫ rsc := by
  rw [hz]

/-- **A leading isomorphism moved out of a composite by a naturality square.** At variables of
abstract categories, with the square given on plain morphisms. -/
private theorem push_iso_out {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A₀ A₁ T₁ T₂ T₃ : D} {B₁ B₂ B₃ : C} {i : A₀ ⟶ G.obj B₁} {g : A₀ ⟶ A₁}
    {j : A₁ ⟶ G.obj B₂} {u : B₁ ⟶ B₂} (hn : i ≫ G.map u = g ≫ j) (w : B₂ ⟶ B₃)
    (ee : G.obj B₃ ⟶ T₁) (mm : T₁ ⟶ T₂) (rsc : T₂ ⟶ T₃) :
    (i ≫ G.map (u ≫ w) ≫ ee ≫ mm) ≫ rsc = g ≫ j ≫ G.map w ≫ ee ≫ mm ≫ rsc := by
  rw [G.map_comp]
  simp only [← Category.assoc]
  rw [hn]

/-- **The `ψ` side of the pure-tensor agreement of [Stacks, Tag 0EX3] (c) is the sections over `V`
of the ordinary unit, followed by a tail.** With the head matching of
`…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE` supplied as `hr` — which fixes `ξ` as the
degree-`d` higher direct image along `f'` of the ordinary unit of `(h')^* ⊣ (h')_*` and `v` as the
comparisons that follow its restriction to `V` — the `ψ` side computed by
`…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul` is the sections over `V` of `ξ` followed by
a composite in which **no unit occurs**: `v`, then [Stacks, Tag 01XK] over `V` inverted, the two
indexings of the right derived functors crossed, the Leray comparison of [Stacks, Tag 089W] along
the affine `h' ∣` inverted, the crossing of the two readings of the cohomology upstairs, the
transport of the two readings of the scalars, the identification of the right-hand end with the
sections over `W`, and the transport of `CategoryTheory.ModuleCat.restrictScalarsCongr`.

Since the `γ⁺` side is, by
`…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit`, the
sections over `V` of that same `ξ` followed by its own tail, what the pure-tensor agreement still
owes is the identification of the two tails. -/
theorem psi_side_eq_sections_unit_comp_tail
    {Tgt : S.Y'.Modules}
    {ξ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F' ⟶ Tgt}
    {v : (Scheme.Modules.restrictFunctor V.ι).obj Tgt ⟶
      ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))).obj
          ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).obj
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')))}
    (hr : ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').hom ≫
          (Scheme.Modules.restrictFunctor V.ι).map ξ ≫ v) :
    haveI := S.quasiCompact_f'
    haveI := S.quasiSeparated_f'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV (preimage_le_preimage_of_isPullback hsq hWV)
    haveI := AffineBaseChange.isQuasicoherent_pullback
      (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) (preimage_le_preimage_of_isPullback hsq hWV))
      ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
    ((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
            (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
          (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
                (affineOpenCohomologyPullbackMap hsq hWV
                    (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
              (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
          (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
            (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W)) =
      ξ.val.app (op V) ≫
        (openSectionsModuleIso Tgt V).inv ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
              ((Stacks.Cohomology.AffineBase.moduleGlobalSections (V : Scheme)).map v ≫
                (cohomologyIsoGlobalSectionsRightDerivedPushforward (S.f' ∣_ V) (S.d : ℤ)).inv.app
                    ⟨(Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                        (preimage_le_preimage_of_isPullback hsq hWV))).obj
                      ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                          (preimage_le_preimage_of_isPullback hsq hWV))).obj
                        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')),
                      inferInstance⟩ ≫
                  (ModuleCat.restrictScalars (S.f' ∣_ V).appTop.hom).map
                    ((Stacks.DerivedIndexing.rightDerivedIso
                          (Stacks.Cohomology.AffineBase.moduleGlobalSections
                            (S.f' ⁻¹ᵁ V : Scheme)) S.d).inv.app
                        ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                            (preimage_le_preimage_of_isPullback hsq hWV))).obj
                          ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                              (preimage_le_preimage_of_isPullback hsq hWV))).obj
                            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F'))) ≫
                      (cohomologyPullbackIsoPushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                            (preimage_le_preimage_of_isPullback hsq hWV))
                          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
                          (Scheme.Modules.isQuasicoherent_restrictFunctor
                            (S.f' ⁻¹ᵁ V).ι F') S.d).inv ≫
                        (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                            (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                          (restrictPullbackRightDerivedPlusIso h'
                            (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv)) ≫
            eqToHom (congrArg
                (fun ρ : (S.restrictBase V).affineBaseRing →+*
                      Γ((((S.restrictBase V).affineBaseOver)).left, ⊤) =>
                  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).obj
                    ((ModuleCat.restrictScalars ρ).obj
                      ((ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                          (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).obj
                        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
                            (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
                          ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
                            ((Scheme.Modules.pullback h').obj F'))))))
                (S.restrictBase_appTop_eq_algebraMap V).symm) ≫
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
                ((topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                  (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
                (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
                  (ModuleCat.of Γ(Y'', W)
                    Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                      ((Scheme.Modules.pullback h').obj F'), W)) := by
  refine (assoc_shift _ _ _ _).trans ?_
  refine (comp_congr_left
    (affineOpenCohomologyIsoSectionsOf_inv_comp_restrictBase_comp S F' (V := V) _ _) _).trans ?_
  refine (map_arg_congr (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) _
    (sections_pullbackMap_eq_unit_comp_tail S F' h' f'' h hsq hWV hr) _ _ _).trans ?_
  exact push_iso_out (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    (inv_comp_of_comp_hom (openSectionsModuleIso_hom_naturality V ξ)) _ _ _ _

/-! ### The pure-tensor agreement, granted the tail identification -/

/-- **A map applied to an element, through a known factorisation.** At variables of a category of
modules. -/
private theorem apply_comp_of_eq {R : Type u} [Ring R] {M N P : ModuleCat.{u} R} {f : M ⟶ P}
    {g : M ⟶ N} {k : N ⟶ P} (hf : f = g ≫ k) (x : M) : f x = k (g x) := by
  rw [hf]
  rfl

/-- **A morphism of sheaves of modules read on sections, through a known factorisation.** At
variables. -/
private theorem sheaf_apply_comp_of_eq {Z : Scheme.{u}} {M N P : Z.Modules} {U : Z.Opens}
    {f : M ⟶ P} {g : M ⟶ N} {k : N ⟶ P} (hf : f = g ≫ k) (x : M.val.obj (op U)) :
    f.val.app (op U) x = k.val.app (op U) (g.val.app (op U) x) := by
  rw [hf]
  rfl

/-- **The pure-tensor agreement of [Stacks, Tag 0EX3] (c), granted the tail identification.** For
a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, the map `ψ` of `…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on the
pure tensor `1 ⊗ a`, as soon as the two sides' **tails** agree.

The three hypotheses are the two sides' head-and-tail factorisations and the identification of
their tails.

* `hΘ` is discharged by
  `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit`, which
  fixes `ξ` as the degree-`d` higher direct image along `f'` of the ordinary unit of
  `(h')^* ⊣ (h')_*` and `Θ` as the `γ⁺` side's tail.
* `hT` is discharged by `psi_side_eq_sections_unit_comp_tail` fed with the head matching
  `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE`, which fixes `T` as the `ψ` side's tail
  at that same `ξ` — its left-hand side is verbatim the `ψ` side of the agreement, as
  `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul` computes it.
* `htail` is then **the one geometric identity conclusion (c) still owes**: the `ψ` side's tail
  `T` is the sections over `V` of the `γ⁺` side's tail `Θ`, restricted to `W`.

*Why the tails are carried as variables.* Written out, each is a composite of a dozen named
comparisons, and an application of either to an element exhausts the elaborator's recursion
budget — the wall `…TopDegreeBaseChange.fromExtendScalarsComp_one_tmul_of_eq` records. With `T`
and `Θ` variables fixed by `hT` and `hΘ` the reduction is checked on its own, and `htail` is read
off those two results.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail
    {Tgt : S.Y'.Modules}
    {ξ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F' ⟶ Tgt}
    {Θ : Tgt ⟶ (Scheme.Modules.pushforward h).obj
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'))}
    (hΘ : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)) = ξ ≫ Θ)
    {T : ModuleCat.of Γ(S.Y', V) Γ(Tgt, V) ⟶
      (ModuleCat.restrictScalars (h.appLE V W hWV).hom).obj
        (ModuleCat.of Γ(Y'', W)
          Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'), W))}
    (hT : ((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
              (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
            (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
          (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
                (affineOpenCohomologyPullbackMap hsq hWV
                    (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
              (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
          (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
            (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W)) = ξ.val.app (op V) ≫ T)
    (htail : ∀ b : Γ(Tgt, V),
      T b = (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F')).val.map (homOfLE hWV).op
          (Θ.val.app (op V) b))
    (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)) :
    baseChangeSectionsMap S F' h' f'' h hsq hWV
        ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
      (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)).val.app (op W)
        (Scheme.Modules.pullbackSection h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
          V W hWV a) :=
  ((baseChangeSectionsMap_one_tmul S F' h' f'' h hsq hWV a).trans
      (((apply_comp_of_eq hT a).trans (htail _)).trans
        (congrArg (ConcreteCategory.hom
            ((((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F')).val.map (homOfLE hWV).op))
          (sheaf_apply_comp_of_eq hΘ a).symm))).trans
    (Scheme.Modules.pullbackSection_homEquiv h
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'))
      (topDirectImageBaseChangeMapPlus S F' h' f'' h
        (toShHom_comm_of_isPullback h' f'' h hsq)) V W hWV a).symm

omit [F'.IsQuasicoherent] [IsAffine (V : Scheme)] [IsAffine (W : Scheme)] in
/-- **The head matching, with the identity functor dropped from the coefficient of its leading
comparison.** `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE` states its leading factor at
`(𝟭 _).obj F'`; `psi_side_eq_sections_unit_comp_tail` asks for it at `F'`. The two comparisons are
one and the same, by `rightDerivedPlusRestrictObjIso_id_obj`, and the rest of the factorisation is
carried as the variable `r`, so that nothing of its shape enters here. -/
theorem rightDerivedPlus_map_unit_resLE_of_id_obj
    {r : (Scheme.Modules.restrictFunctor V.ι).obj
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') ⟶
        ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pushforward (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).obj
            ((Scheme.Modules.pullback (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV))).obj
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')))}
    (hr : ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
        (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d
            ((𝟭 (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace))).obj F')).hom ≫ r) :
    ((Scheme.Modules.pushforward (S.f' ∣_ V)).rightDerivedPlus (S.d : ℤ)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
              (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')) =
      (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso S.f' V S.d F').hom ≫ r :=
  (rightDerivedPlusRestrictObjIso_id_obj S F' (V := V)) ▸ hr


end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
