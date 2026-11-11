module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionDerivedDirectImage
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The higher direct image of a module, restricted to the small étale site of a chart

Let `S` be a scheme in a big fppf site, let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_{fppf}` — the source's quasi-compact, quasi-separated 1-morphism of
algebraic stacks representable by algebraic spaces — and let `y : V ⟶ 𝒴` be an object of `𝒴`.
Write `𝒱` for the category fibred in groupoids of that object, `𝒰 = 𝒱 ×_𝒴 𝒳` for the 2-fibre
product and `f' : 𝒰 ⥤ 𝒱` for the base change of `f`. Because `f` is representable by algebraic
spaces, `𝒰` is represented by an **algebraic space** `U` — not in general by a scheme — while
`𝒱` is represented by the scheme `V`, and `f'` induces a morphism `U ⟶ V` of algebraic spaces.
Stacks 0GQH asserts, for `ℱ` in `LQCoh^{fbc}(𝒪_𝒳)` and every `i`,

```text
(R^i f_* ℱ)|_{V_étale} = R^i f'_{small,*}(ℱ|_{U_étale}),
```

where `f'_{small,*}` is the direct image on the **small étale sites of algebraic spaces** and
`(-)|_{V_étale}`, `(-)|_{U_étale}` are the restrictions of Stacks 073M, i.e. `π_{V,*}` after
inverse image along `𝒱 ⥤ 𝒴`, resp. `π_{U,*}` after inverse image along `𝒰 ⥤ 𝒳`.

This file states and proves that identity, as an isomorphism of functors of the complex of
`𝒪_𝒳`-modules, from the source's own two ingredients: the **base change** of the higher direct
image along `y` (Stacks 075H), and **Stacks 075N**, the restricted total direct image of a
1-morphism between categories representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact_eq`: the functor induced on
  unbounded derived categories by an exact degreewise direct image of sheaves of modules is
  `CategoryTheory.Functor.mapDerivedCategory` of that direct image. This is true by
  definition, but `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact` is
  `irreducible`, so the equation has to be recorded.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExactCompHomologyFunctorIso`: **an
  exact direct image commutes with the cohomology functors of the derived category.** This is
  the step that moves `H^i` past the restriction `π_{V,*}`, and it is exactly what the
  exactness hypotheses of Stacks 075N's carrier supply.
* `AlgebraicGeometry.Space.restrictedHigherDirectImageChartIso`: the identity of Stacks 0GQH in
  derived form, from the base change isomorphism `bc` of the chart square. The lemma itself, for
  `ℱ` in `LQCoh^{fbc}(𝒪_𝒳)` and the fppf higher direct image of `Mod(𝒪_𝒳)`, is
  `AlgebraicGeometry.Stack.restrictedFppfModulesHigherDirectImage`, which carries the tag.

## Implementation notes

**What is proved, and what is assumed.** The conclusion is assembled, in four steps, from

1. `hDg`, that the derived inverse image along the chart `𝒱 ⥤ 𝒴` is computed degreewise — the
   inverse image of sheaves of modules is exact, so its derived functor commutes with `H^i`;
2. `bc`, **the base change isomorphism of the 2-cartesian square**, in its derived form
   `Rf_* ∘ Dg⁻¹ ≅ Dg'⁻¹ ∘ Rf'_*`. This is Stacks 075H for the square of the chart. The library
   carries 075H for **abelian** sheaves only
   (`AlgebraicGeometry.Stack.abelianHigherDirectImageBaseChangeIso`); at module coefficients
   `AlgebraicGeometry.Stack.nonempty_moduleHigherDirectImageBaseChangeIso` is itself
   conditional on a linearity hypothesis which is 075H's own assertion at those coefficients,
   so the module-coefficient base change is assumed here. Assuming the conclusion of 075H to
   prove 0GQH is assuming one tag to prove another; `bc` mentions no restriction to a small
   étale site and no small-site direct image, which is where all of 0GQH's content lies.
3. `derivedPushforwardOfExactCompHomologyFunctorIso`, proved here, which moves `H^i` past
   `π_{V,*}`;
4. `AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`, Stacks 075N at module
   coefficients, which is unconditional. Four hypotheses that declaration used to ask for are
   no longer hypotheses of either statement: Stacks 073N, the 2-isomorphism of the two legs of
   the square, which is now
   `AlgebraicGeometry.Space.restrictionRingedSquareInducedAlgebraicSpaces`, proved from
   invertibility of the comparison map of equation 075M; exactness of the two module-level
   restrictions, which is now
   `AlgebraicGeometry.Space.exactFunctor_pushforwardModules_projectionRingedToposHom`;
   Stacks 093Y for degreewise `f_*`, which the invertible unit of the exact restriction
   `π_{V,*}` makes unnecessary; and the condition the composition criterion consumes at the leg
   `f_small ∘ π_U`, which is now
   `AlgebraicGeometry.Space.pushforwardComputesDerived_smallEtaleRingedToposHom`, proved from
   the unconditional Stacks 0D6E for a morphism of ringed topoi.

Steps 1 and 2 are the source's "by Sheaves on Stacks, Lemma 96.21.3 we can reduce to the case
where `𝒳` is represented by `U` and `𝒴` is represented by `V`"; steps 3 and 4 are its "the
result follows from Sheaves on Stacks, Lemma 96.22.2".

**How the source's geometric hypotheses enter.** They are not carried as unused binders; each
is consumed where the source uses it, in the shape this development has for it.

* *Representability of `f` by algebraic spaces* is `hF` together with `eF`: the 2-fibre product
  `𝒰 = 𝒱 ×_𝒴 𝒳` is presented by an algebraic space `F = U`. That presentation, and the
  presentation `eG` of `𝒱` by `G = V`, are precisely what make the small étale sites of `U` and
  `V` and the induced morphism `U ⟶ V` of algebraic spaces exist, hence what make the
  right-hand side of 0GQH meaningful. `U` is an algebraic space and not a scheme, as the source
  notes, and nothing below assumes that it is one.
* *Quasi-compactness and quasi-separatedness of `f`* used to enter through Stacks 093Y for
  degreewise `f_*`, the hypothesis this development's form of Stacks 0D6E carries for the
  first morphism of a composite. On the leg `π_V ∘ f` the second morphism `π_V` has exact
  degreewise direct image, so its derived functor's unit is invertible and that hypothesis is
  not needed; see `AlgebraicGeometry.RingedToposHom.pushforwardComputesDerived_of_isIso`.
  They are not needed anywhere else in the chain and so are not restated.
* *`ℱ ∈ LQCoh^{fbc}(𝒪_𝒳)`* is what licenses, by Stacks 0771 part (4)(a), computing `R^i f_*`
  in the **étale** topology rather than the fppf one. Every site below is already the étale
  one — the `SiteKind.etale` argument of `AlgebraicGeometry.FibredSite.associatedRingedTopos`
  and of `AlgebraicGeometry.FibredSite.ringedToposMorphism` — so that choice is built into the
  statement, and the conclusion is an isomorphism of functors of an arbitrary complex of
  `𝒪_𝒳`-modules, which contains the `LQCoh^{fbc}` case. Stacks 0771 part (3)
  (`AlgebraicGeometry.Stack.isLocallyQuasicoherentWithFlatBaseChange_stackModulePresheafPullback`),
  which says the inverse image of such a module is again such a module, is therefore not
  needed as an input: the statement is not restricted to that subcategory on either side.

**The shape of the two sides.** `R^i` is `H^i` of the total right derived direct image, which
is what the source means by `R^i f_*` and what composes with Stacks 075N; the total derived
functors `Rf`, `RfSpace`, `RfStack` and their units `αf`, `αfSpace`, `αfStack` are parameters
with `CategoryTheory.Functor.IsRightDerivedFunctor` instance hypotheses, exactly as in
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`. The two derived inverse images are
parameters `Dg`, `Dg'` as well; only `Dg` is pinned to the degreewise inverse image, by `hDg`,
because only `Dg` has to be pushed past `H^i`.

## References

* [Stacks Project, Tag 0GQH](https://stacks.math.columbia.edu/tag/0GQH)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposHom

universe w w' v u v' u' dX dY

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

section Homology

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]

/-- The functor on unbounded derived categories induced by an **exact** degreewise direct image
of sheaves of modules is `CategoryTheory.Functor.mapDerivedCategory` of that direct image.

This holds by definition — it is how
`AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact` is built — but that definition is
marked `irreducible`, so the equation is unavailable to unification and has to be recorded.
The finite-limit half of exactness is an instance argument here rather than supplied by
`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesFiniteLimits`; `PreservesFiniteLimits`
is a `Prop`, so the two agree. -/
theorem derivedPushforwardOfExact_eq (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)]
    [PreservesFiniteLimits (pushforwardModules f)] :
    derivedPushforwardOfExact f = (pushforwardModules f).mapDerivedCategory := by
  with_unfolding_all rfl

/-- **An exact degreewise direct image of sheaves of modules commutes with the cohomology
functors of the derived category.** For `f` whose degreewise direct image `f_*` is exact,

```text
H^n ∘ (the functor D(𝒪_X) ⥤ D(𝒪_Y) induced by f_*) ≅ f_* ∘ H^n.
```

This is the step that lets `H^i` be taken inside an underived restriction functor, which is how
the identity of Stacks 0GQH is read off the derived identity of Stacks 075N. The comparison is
`StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`, transported along
`AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExact_eq`. -/
noncomputable def derivedPushforwardOfExactCompHomologyFunctorIso (f : RingedToposHom X Y)
    [PreservesFiniteColimits (pushforwardModules f)] (n : ℤ) :
    derivedPushforwardOfExact f ⋙ DerivedCategory.homologyFunctor Y.Modules n ≅
      DerivedCategory.homologyFunctor X.Modules n ⋙ pushforwardModules f :=
  have := pushforwardModules_preservesFiniteLimits f
  Functor.isoWhiskerRight (eqToIso (derivedPushforwardOfExact_eq f))
      (DerivedCategory.homologyFunctor Y.Modules n) ≪≫
    StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (pushforwardModules f) n

end Homology

end AlgebraicGeometry.RingedToposHom

/-! ### Stacks 0GQH -/

namespace AlgebraicGeometry.Space

universe u v w v' w' vX wX vY wY dU dV dF dG dX dY

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type vX} [Category.{wX} 𝒳] {𝒴 : Type vY} [Category.{wY} 𝒴]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (fStack : 𝒳 ⥤ 𝒴) (hfStack : p𝒳.IsFibredOneMorphism p𝒴 fStack)
  (fChart : 𝒰 ⥤ 𝒱) (hfChart : p.IsFibredOneMorphism q fChart)
  (y : 𝒱 ⥤ 𝒴) (hy : q.IsFibredOneMorphism p𝒴 y)
  (y' : 𝒰 ⥤ 𝒳) (hy' : p.IsFibredOneMorphism p𝒳 y')
  [∀ P : 𝒰ᵒᵖ ⥤ Type u, fChart.op.HasPointwiseRightKanExtension P]
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, fStack.op.HasPointwiseRightKanExtension P]
  [∀ P : 𝒱ᵒᵖ ⥤ Type u, y.op.HasPointwiseRightKanExtension P]
  [∀ P : 𝒰ᵒᵖ ⥤ Type u, y'.op.HasPointwiseRightKanExtension P]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).J.HasSheafCompose
    (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS q hq .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).J AddCommGrpCat.{u}]
  [HasSheafify (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedTopos B S hS ⟨G, hG⟩).J AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS q hq .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).J.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(smallEtaleRingedTopos B S hS ⟨G, hG⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{dU} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [HasDerivedCategory.{dV} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [HasDerivedCategory.{dX} (FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).Modules]
  [HasDerivedCategory.{dY} (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).Modules]
  [HasDerivedCategory.{dF} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  [HasDerivedCategory.{dG} (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules]
  [IsGrothendieckAbelian.{u} (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules]
  [IsGrothendieckAbelian.{u} (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules]
  (Rf : DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules ⥤
    DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules)
  (RfSpace : DerivedCategory (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules ⥤
    DerivedCategory (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules)
  (RfStack : DerivedCategory (FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).Modules ⥤
    DerivedCategory (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).Modules)
  (αf : RingedToposHom.pushforwardToDerivedCategory
      (FibredSite.ringedToposMorphism B S hS p q hp hq fChart hfChart .etale) ⟶
    DerivedCategory.Qh ⋙ Rf)
  (αfSpace : RingedToposHom.pushforwardToDerivedCategory
      (smallEtaleRingedToposHom B S hS
        (inducedAlgebraicSpacesHom B S hS F G p q hF hG eF eG fChart hfChart)) ⟶
    DerivedCategory.Qh ⋙ RfSpace)
  (αfStack : RingedToposHom.pushforwardToDerivedCategory
      (FibredSite.ringedToposMorphism B S hS p𝒳 p𝒴 h𝒳 h𝒴 fStack hfStack .etale) ⟶
    DerivedCategory.Qh ⋙ RfStack)
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
    (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules (ComplexShape.up ℤ))]
  [RfSpace.IsRightDerivedFunctor αfSpace (HomotopyCategory.quasiIso
    (smallEtaleRingedTopos B S hS ⟨F, hF⟩).Modules (ComplexShape.up ℤ))]

include αfStack in
/-- **The identity of Stacks 0GQH, in derived form.** For an object `y : V ⟶ 𝒴` of `𝒴`, with
`𝒱` the category fibred in groupoids of that object, `𝒰 = 𝒱 ×_𝒴 𝒳` the 2-fibre product —
presented by the *algebraic space* `F = U`, because `f` is representable by algebraic
spaces — and `f' : 𝒰 ⥤ 𝒱` the base change of `f`, inducing a morphism `U ⟶ V` on presenting
algebraic spaces
(`AlgebraicGeometry.Space.inducedAlgebraicSpacesHom`):

```text
(R^i f_* ℱ)|_{V_étale} ≅ R^i f'_{small,*}(ℱ|_{U_étale}),
```

naturally in the complex `ℱ` of `𝒪_𝒳`-modules. On the left, `R^i f_* ℱ` is `H^i` of the total
right derived direct image `RfStack`, and `(-)|_{V_étale}` is inverse image along `𝒱 ⥤ 𝒴`
followed by the restriction `π_{V,*}` of Stacks 073M. On the right, `(-)|_{U_étale}` is derived
inverse image along `𝒰 ⥤ 𝒳` followed by `π_{U,*}`, and `R^i f'_{small,*}` is `H^i` of the total
right derived direct image `RfSpace` of the small étale sites of the algebraic spaces `U`
and `V`.

The chain is the source's: `hDg` and `bc` are its reduction to the representable case, and
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso` together with
`AlgebraicGeometry.RingedToposHom.derivedPushforwardOfExactCompHomologyFunctorIso` are its
appeal to Stacks 075N. See the implementation notes of this file for what each hypothesis is
and where the source's hypotheses on `f` and on `ℱ` are consumed.

This declaration takes the base change isomorphism `bc` as an argument. Stacks 0GQH itself,
with exactly the source's hypotheses, is
`AlgebraicGeometry.Stack.restrictedFppfModulesHigherDirectImage`, which goes through
`AlgebraicGeometry.Stack.restrictedStackModuleHigherDirectImageIsoOfScheme` instead. -/
noncomputable def restrictedHigherDirectImageChartIso
    (Dy : DerivedCategory
        (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).Modules ⥤
      DerivedCategory (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules)
    (Dy' : DerivedCategory
        (FibredSite.associatedRingedTopos B S hS p𝒳 h𝒳 .etale).Modules ⥤
      DerivedCategory (FibredSite.associatedRingedTopos B S hS p hp .etale).Modules)
    (i : ℤ)
    (hDy : Dy ⋙ DerivedCategory.homologyFunctor
          (FibredSite.associatedRingedTopos B S hS q hq .etale).Modules i ≅
        DerivedCategory.homologyFunctor
            (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).Modules i ⋙
          Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (FibredSite.ringedToposMorphism B S hS q p𝒴 hq h𝒴 y hy .etale).toModulesHom)
    (bc : RfStack ⋙ Dy ≅ Dy' ⋙ Rf) :
    RfStack ⋙ DerivedCategory.homologyFunctor
          (FibredSite.associatedRingedTopos B S hS p𝒴 h𝒴 .etale).Modules i ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (FibredSite.ringedToposMorphism B S hS q p𝒴 hq h𝒴 y hy .etale).toModulesHom ⋙
          RingedToposHom.pushforwardModules
            (projectionRingedToposHom B S hS G q hq hG eG) ≅
      Dy' ⋙ RingedToposHom.derivedPushforwardOfExact
            (projectionRingedToposHom B S hS F p hp hF eF) ⋙
        RfSpace ⋙ DerivedCategory.homologyFunctor
          (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules i :=
  Functor.isoWhiskerLeft RfStack
      (Functor.isoWhiskerRight hDy.symm
        (RingedToposHom.pushforwardModules
          (projectionRingedToposHom B S hS G q hq hG eG))) ≪≫
    Functor.isoWhiskerLeft RfStack
      (Functor.isoWhiskerLeft Dy
        (RingedToposHom.derivedPushforwardOfExactCompHomologyFunctorIso
          (projectionRingedToposHom B S hS G q hq hG eG) i).symm) ≪≫
    Functor.isoWhiskerRight bc
      (RingedToposHom.derivedPushforwardOfExact
          (projectionRingedToposHom B S hS G q hq hG eG) ⋙
        DerivedCategory.homologyFunctor
          (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules i) ≪≫
    Functor.isoWhiskerLeft Dy'
      (Functor.isoWhiskerRight
        (restrictedDerivedDirectImageIso B S hS F G p q hp hq hF hG eF eG fChart hfChart
          Rf RfSpace αf αfSpace)
        (DerivedCategory.homologyFunctor
          (smallEtaleRingedTopos B S hS ⟨G, hG⟩).Modules i))

end AlgebraicGeometry.Space

end
