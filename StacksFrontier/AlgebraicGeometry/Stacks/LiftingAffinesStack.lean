module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesFibredInGroupoids
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.MorSheafFromIsom

/-!
# The category of smooth lifts of étale opens is a stack in groupoids (Stacks 0CJU)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` over `S` and
a smooth 1-morphism `x : W ⟶ 𝒳`, and consider the category
`AlgebraicGeometry.Stack.EtaleSmoothLift` of smooth lifts of étale opens of `W` along `ι`
together with its projection `AlgebraicGeometry.Stack.EtaleSmoothLift.proj` to the spaces-étale
site of `W` (**Stacks 0CJP**). Stacks 0CJU says that projection is a stack in groupoids.

The source's proof is in three parts, one for each condition of **Stacks 02ZI**. Condition (1),
that the projection is fibred in groupoids, is **Stacks 0CJT**. Condition (2), that the `Isom`
presheaves are sheaves — descent of morphisms — the source leaves to the reader. Condition (3),
descent of objects, the source proves: refine the covering so that each `U_k` is a scheme, read
off from the restriction morphisms of the descent datum the two étale legs
`s_{kk'} : U'_{kk'} ⟶ U'_k` and `t_{kk'} : U'_{kk'} ⟶ U'_{k'}` (**Stacks 0CJS**), show that
`j = (∐ s_{kk'}, ∐ t_{kk'})` is an étale equivalence relation — a monomorphism by
**Stacks 0BPG** part (6), symmetric by **Stacks 026C**, transitive by the cocycle condition —
take the quotient algebraic space `U'` (**Stacks 02WW**), and descend the maps `x'_k` along the
étale covering `{U'_k ⟶ U'}` because `𝒳'` is a stack.

What is proved here is condition (1), from Stacks 0CJT, and the part of condition (3) that lives
inside the category of smooth lifts: that the inclusion `i : U ⟶ U'` of an object is a
thickening, the two legs of the relation, their étaleness, and the reflexivity, symmetry and
transitivity of the relation they carry, the last four read on the ambient algebraic spaces
through `AlgebraicGeometry.Stack.EtaleSmoothLift.ambientSpaceFunctor`. Condition (2) is carried
as a hypothesis of the assembled statement. Condition (3) is *reduced*, not carried: the
assembled statement asks only for the source's own first move, a covering refinement along which
descent is effective, and derives condition (3) for an arbitrary index type from it. See the
implementation notes for what blocks the refinement, and in particular for the one step that is
not merely unlanded but absent for cardinality reasons.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.ambientSpaceFunctor`: the second component of a smooth
  lift and of a morphism of smooth lifts, as a functor to the algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.relationFst` and
  `AlgebraicGeometry.Stack.EtaleSmoothLift.relationSnd`: the morphisms `s_{kk'}` and `t_{kk'}`
  attached to a descent datum for the projection.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isThickening_inclusion`: **Stacks 0CJP**, the
  inclusion `i : U ⟶ U'` of an object is a thickening, which Remark 0CJP asserts in prose and
  Stacks 0CJU re-uses.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_relation`: **Stacks 0CJU**, the two legs of
  the relation are étale, which is Stacks 0CJS applied to the restriction morphisms of the
  descent datum.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.relation_refl`,
  `AlgebraicGeometry.Stack.EtaleSmoothLift.relation_symm` and
  `AlgebraicGeometry.Stack.EtaleSmoothLift.relation_trans`: **Stacks 0CJU**, the three
  equivalence-relation identities carried by the relation on the ambient spaces, from the two
  identities of Stacks 026C and from the cocycle condition.
* The three conditions of Stacks 02ZI assembled, **Stacks 0CJU**, with no hypothesis, are
  `AlgebraicGeometry.Stack.EtaleSmoothLift.isStackInGroupoids_proj`, in
  `StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesIsStack`.

## Implementation notes

**What is delivered and what is carried.** Of the three conditions of Stacks 02ZI, condition (1)
is discharged outright here from `AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids`
(**Stacks 0CJT**), which carries the two hypotheses `hiso` and `hfib` of that lemma; those two
are passed on unchanged and are documented there. Condition (2) is carried as the hypothesis
`hisom`, written out as the `isom_isSheaf` field of
`CategoryTheory.Functor.IsStackInGroupoids`. Condition (3) is *not* carried: it is derived from
the hypothesis `href`, that every covering sieve of the spaces-étale site admits a covering
refinement, presented as a family, along which every sieve-indexed descent datum is effective.

**How condition (3) is derived from `href`.** This is the source's "in order to prove effectivity
we may first refine the covering", as
`CategoryTheory.Functor.hasEffectiveDescent_of_familyRefinements` and
`CategoryTheory.Functor.DescentDatum.isEffective_of_hasEffectiveDescent`. The first of those asks
for condition (2) of Stacks 026F, the sheaf condition for the morphism presheaves, which comes
from `hisom` through `CategoryTheory.Functor.isMorSheaf_of_isomIsSheaf` — the bridge that does
*not* consume effective descent, so the derivation is not circular;
`CategoryTheory.Functor.isMorSheaf_of_isStackInGroupoids` would be, since it consumes the whole
`IsStackInGroupoids`. The index type of `href`'s family is free, so a refinement may be taken in
whatever class the construction of the descended object needs, while the conclusion holds for
the arbitrary index type that clause (3) of Stacks 02ZI quantifies over. This forces the
`isom_isSheaf` universe: `isMorSheaf_of_isomIsSheaf` reads `hisom` at `max u₁ v₁`, which for the
spaces-étale site is `u + 1`, so such an assembly is stated at
`CategoryTheory.Functor.IsStackInGroupoids.{u + 1}`.

**Why condition (2) is carried.** It is the descent of morphisms, which the source explicitly
leaves to the reader. Gluing an isomorphism of smooth lifts over a covering `{U_k ⟶ U}` means
gluing its three components; the ambient component has to be glued over the family
`{U'_k ⟶ U'}`, and that this family is an étale covering of `U'` is the topological invariance
of the small étale site along the thickening `U ⟶ U'`, **Stacks 07VW**. That tag is proved, as
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence`, but it carries a hypothesis `hEquiv`
— that base change on the spaces-étale sites is an equivalence — and the library proves that
only for a *first-order* thickening, by
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isFirstOrderThickening`, whereas the
thickening attached to an object of Stacks 0CJP is an arbitrary one. This is the same missing
input as the hypothesis `hfib` of Stacks 0CJT.

**Why `href` is carried, step by step.** Of the source's steps on the refinement, most are
available and two are not.

Available: that `i : U ⟶ U'` is a thickening is `isThickening_inclusion` below; the two legs and
their étaleness and the three relation identities are the results below; that a thickening of a
scheme is a scheme is **Stacks 05ZR**,
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom`, granted the three hypotheses of
Stacks 07VT that it carries; the quotient algebraic space and the étale surjective chart
`∐ U'_l ⟶ U'` are **Stacks 02WW**,
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional` with
`AlgebraicGeometry.Space.quotientMap_etale_unconditional` and
`AlgebraicGeometry.Space.quotientMap_surjective_unconditional`; and the final step "since `𝒳'`
is a stack this descent datum is effective" is
`AlgebraicGeometry.Stack.isStackInGroupoids_of_isAlgebraicStack`. Stacks 02WW's
`Stacks.Groupoids.PreRelation` is formed in `CategoryTheory.Over S` through
`Over.post B.inclusion`, so no bridge between `CategoryTheory.Over S` and the big fppf site is
owed.

Not available:

* **The refinement itself.** Stacks 02WW takes a relation between two objects of
  `BigFppfOver B S hS`, so `∐_{l ∈ L} U'_l` has to be an object of that site, whose objects are
  schemes bounded by the site's cutoff. The only coproduct instance is
  `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_discrete`, which asks for `[Small.{u} L]` and
  `[Countable L]`; no cardinality-bounded instance exists, so even a refinement of size below the
  cutoff does not suffice. A refinement indexed by a *singleton* would need no coproduct at all,
  and an object of the spaces-étale site is indeed covered by a single étale scheme chart, but
  the declaration proving that — `exists_scheme_chart_cover` in
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison` — covers the object itself rather
  than producing a member of a *given* covering sieve, which is
  what `href` asks for. Charting each member of a given covering family instead returns a family
  indexed by that covering's own index type, which is where the countability fails.
* **The monomorphism step** is **Stacks 0BPG** part (6),
  `Stacks.Thickenings.CartesianFiniteTypeMorphism.mono_iff`, a statement about *schemes*. It
  becomes applicable only after the refinement above has made every `U'_k` a scheme; the
  algebraic-space analogue that would avoid the refinement is clause (6) of **Stacks 0BPJ**, and
  that is not proved —
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified` and its sibling
  `…ThickeningMorphism.EtaleLocalProperties` prove clauses (5), `locally_quasi_finite` and
  `vanishing_differentials` of 0BPJ and no monomorphism clause.
* **The 2-fibre product condition `U = 𝒳 ×_{𝒳'} U'`** for the glued object, which the
  `AlgebraicGeometry.Stack.EtaleSmoothLift.isTwoFibreProduct` field of the descended object
  demands, and the assembly of the remaining data of
  `CategoryTheory.Functor.SieveDescentDatum.IsEffective`.

One further gap sits between `isThickening_inclusion` and the use of Stacks 05ZR: 05ZR asks for
`AlgebraicGeometry.Space.IsThickeningHom B S hS i`, a condition on the morphism of algebraic
spaces, while `isThickening_inclusion` concludes `AlgebraicGeometry.Stack.IsThickening` for the
1-morphism of algebraic stacks attached to `i`. Nothing in the tree converts between them —
`algebraicSpaceStackFunctor` has no consumer outside the Stacks 0CJP, 0CJS, 0CJT and 0CJU files —
and `AlgebraicGeometry.Space.ThickeningMorphisms` carries no base-change lemma that would produce
`IsThickeningHom` directly from the 2-fibre product condition.

**The hypothesis `hCJC`.** The étaleness statement consumes **Stacks 0CJS**,
`AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_ambient`, which carries the étale clause, item
(9), of **Stacks 0CJC** as a hypothesis `hCJC`, because only the flatness, smoothness and
syntomicity clauses of 0CJC are proved, in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationProperties`. That hypothesis is
passed on unchanged and is documented at 0CJS.

**Inherited caveat.** Thickenings of algebraic stacks are
`AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)), which omits the
homeomorphism-of-underlying-spaces clause of the source for want of a library site for the point
topology of Stacks 04XL. That omission is inherited here, through
`AlgebraicGeometry.Stack.EtaleSmoothLift`.

## References

* [Stacks Project, Tag 026C](https://stacks.math.columbia.edu/tag/026C)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VW](https://stacks.math.columbia.edu/tag/07VW)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJS](https://stacks.math.columbia.edu/tag/0CJS)
* [Stacks Project, Tag 0CJT](https://stacks.math.columbia.edu/tag/0CJT)
* [Stacks Project, Tag 0CJU](https://stacks.math.columbia.edu/tag/0CJU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w t

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The second component of a smooth lift, as a functor.** A smooth lift
`(U, U', a, i, x', α)` is sent to its ambient algebraic space `U'` and a morphism
`(f, f', γ)` to its ambient component `f'`. Functoriality holds by definition of the identity
and the composition of `AlgebraicGeometry.Stack.EtaleSmoothLift.instCategory`. -/
def ambientSpaceFunctor : EtaleSmoothLift B S hS ι hι W x hx ⥤ AlgebraicSpaces B S hS where
  obj ξ := ξ.ambient
  map m := Hom.ambient m
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 0CJP, the inclusion of an object is a thickening.** For a smooth lift
`(U, U', a, i, x', α)` the 2-fibre product condition `U = 𝒳 ×_{𝒳'} U'` exhibits `i : U ⟶ U'` as
the base change of the thickening `ι : 𝒳 ⟶ 𝒳'` along `x' : U' ⟶ 𝒳'`, so `i` is a thickening by
**Stacks 0BPR**, `AlgebraicGeometry.Stack.isThickening_baseChange`.

This is the source's "In particular `U ⊂ U'` is a thickening", which Remark 0CJP asserts and
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory` records only in prose; Stacks 0CJU
re-uses it as "above we have already shown that there is a thickening `i : U ⟶ U'`". The
conclusion is read in the 2-category of algebraic stacks, that is for the 1-morphism which
`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor` attaches to `i`; see the implementation
notes for why it cannot yet be read as `AlgebraicGeometry.Space.IsThickeningHom` on `i`
itself. -/
@[stacks 0CJP "the inclusion of an object is a thickening"]
theorem isThickening_inclusion (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    IsThickening ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion) :=
  isThickening_baseChange B S hS ι ξ.ambientMap _ ξ.isTwoFibreProduct hι

section Descent

variable {Z : Space.SpacesEtale B S hS W} {K : Type t}
  {V : K → Space.SpacesEtale B S hS W} {f : ∀ k, V k ⟶ Z}
  {Vij : K → K → Space.SpacesEtale B S hS W}
  {pr₁ : ∀ k k', Vij k k' ⟶ V k} {pr₂ : ∀ k k', Vij k k' ⟶ V k'}
  {hVij : ∀ k k', IsPullback (pr₁ k k') (pr₂ k k') (f k) (f k')}
  {Vijk : K → K → K → Space.SpacesEtale B S hS W}
  {s₁₂ : ∀ k k' k'', Vijk k k' k'' ⟶ Vij k k'}
  {s₂₃ : ∀ k k' k'', Vijk k k' k'' ⟶ Vij k' k''}
  {hVijk : ∀ k k' k'', IsPullback (s₁₂ k k' k'') (s₂₃ k k' k'') (pr₂ k k') (pr₁ k' k'')}
  {q₁ : ∀ k k' k'', Vijk k k' k'' ⟶ V k} {q₂ : ∀ k k' k'', Vijk k k' k'' ⟶ V k'}
  {q₃ : ∀ k k' k'', Vijk k k' k'' ⟶ V k''}
  {hq₁ : ∀ k k' k'', q₁ k k' k'' = s₁₂ k k' k'' ≫ pr₁ k k'}
  {hq₂ : ∀ k k' k'', q₂ k k' k'' = s₁₂ k k' k'' ≫ pr₂ k k'}
  {hq₃ : ∀ k k' k'', q₃ k k' k'' = s₂₃ k k' k'' ≫ pr₂ k' k''}
  (D : Functor.DescentDatum (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) V f Vij pr₁ pr₂
    hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- **The leg `s_{kk'}` of the relation attached to a descent datum.** It is the ambient
component of the restriction morphism `ξ_k|_{U_k ×_U U_{k'}} ⟶ ξ_k` of the descent datum, which
is the second component of that morphism of the category of smooth lifts. -/
def relationFst (k k' : K) : (D.xrij k k').pt.ambient ⟶ (D.x k).ambient :=
  ambientSpaceFunctor.map (D.xrij k k').hom

/-- **The leg `t_{kk'}` of the relation attached to a descent datum.** It is the ambient
component of the composite
`ξ_k|_{U_k ×_U U_{k'}} ⟶ ξ_{k'}|_{U_k ×_U U_{k'}} ⟶ ξ_{k'}` of the gluing isomorphism of the
descent datum with the restriction morphism of `ξ_{k'}`. -/
def relationSnd (k k' : K) : (D.xrij k k').pt.ambient ⟶ (D.x k').ambient :=
  ambientSpaceFunctor.map (D.φ k k' ≫ (D.xrji k k').hom)

/-- **Stacks 0CJU, the two legs of the relation are étale.** Both `s_{kk'}` and `t_{kk'}` are
ambient components of morphisms of the category of smooth lifts, so **Stacks 0CJS** applies to
each of them.

The hypothesis `hCJC` is the one carried by
`AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_ambient`: the étale clause, item (9), of
**Stacks 0CJC** for the thickening `ι`, which is not available in this library. -/
@[stacks 0CJU "the two legs of the relation are étale"]
theorem isEtale_relation
    (hCJC : ∀ (U U' V' V'' : AlgebraicSpaces B S hS) (i : U ⟶ U') (j : V' ⟶ V'')
      (u : (algebraicSpaceStackFunctor B S hS).obj U ⟶ 𝒳)
      (v : (algebraicSpaceStackFunctor B S hS).obj V' ⟶ 𝒳)
      (y : (algebraicSpaceStackFunctor B S hS).obj U' ⟶ 𝒳')
      (y' : (algebraicSpaceStackFunctor B S hS).obj V'' ⟶ 𝒳')
      (α : u ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ y)
      (β : v ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map j ≫ y'),
      IsTwoFibreProduct
          (⟨(algebraicSpaceStackFunctor B S hS).obj U, u,
            (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι y) →
        IsTwoFibreProduct
            (⟨(algebraicSpaceStackFunctor B S hS).obj V', v,
              (algebraicSpaceStackFunctor B S hS).map j, β⟩ : TwoCommSq ι y') →
          AlgebraicStacks.IsFlat B S hS y →
            AlgebraicStacks.IsLocallyOfFinitePresentation B S hS y →
              AlgebraicStacks.IsLocallyOfFiniteType B S hS y' →
                ∀ (g : U ⟶ V') (g' : U' ⟶ V'')
                  (hL : u ≫ ι = (algebraicSpaceStackFunctor B S hS).map g ≫ (v ≫ ι)),
                  i ≫ g' = g ≫ j →
                    ∀ (γ : y ⟶ (algebraicSpaceStackFunctor B S hS).map g' ≫ y')
                      (hR : (algebraicSpaceStackFunctor B S hS).map g ≫
                          ((algebraicSpaceStackFunctor B S hS).map j ≫ y') =
                        (algebraicSpaceStackFunctor B S hS).map i ≫
                          ((algebraicSpaceStackFunctor B S hS).map g' ≫ y')),
                      α.hom ≫ ((algebraicSpaceStackFunctor B S hS).map i ◁ γ) =
                          eqToHom hL ≫
                            ((algebraicSpaceStackFunctor B S hS).map g ◁ β.hom) ≫ eqToHom hR →
                        Space.IsEtale B S hS g.hom → Space.IsEtale B S hS g'.hom)
    (k k' : K) :
    Space.IsEtale B S hS (relationFst D k k').hom ∧
      Space.IsEtale B S hS (relationSnd D k k').hom :=
  ⟨isEtale_ambient hCJC _ _ (D.xrij k k').hom,
    isEtale_ambient hCJC _ _ (D.φ k k' ≫ (D.xrji k k').hom)⟩

/-- **Stacks 0CJU, reflexivity of the relation.** A fibre automorphism `e` of `ξ_k` which is the
pullback along the diagonal `Δ : U_k ⟶ U_k ×_U U_k ×_U U_k` of each of the three gluing
isomorphisms of the triple `(k, k, k)` has identity ambient component. This is the first
identity of **Stacks 026C** read on the ambient spaces.

The hypotheses `hiso` and `hfib` are the two carried by
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids` (**Stacks 0CJT**), which is where
the fibred-in-groupoids hypothesis of Stacks 026C comes from. -/
@[stacks 0CJU "reflexivity of the relation"]
theorem relation_refl
    (hiso : ∀ (ζ ζ' : EtaleSmoothLift B S hS ι hι W x hx) (n : ζ ⟶ ζ'),
      IsIso (Hom.base n) → IsIso (Hom.ambient n))
    (hfib : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibredCategory)
    (k : K) {d : V k ⟶ Vijk k k k}
    {hd₁ : 𝟙 (V k) = d ≫ q₁ k k k} {hd₂ : 𝟙 (V k) = d ≫ q₂ k k k}
    {hd₃ : 𝟙 (V k) = d ≫ q₃ k k k}
    {e : D.x k ⟶ D.x k}
    (he : Functor.FibreHom (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (D.x k) (D.x k) (D.hx k) (D.hx k) e)
    (heij : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d hd₁ hd₂
      (D.wi k k k) (D.wj k k k)
      (Functor.Restriction.id _ (D.x k) (D.hx k)) (Functor.Restriction.id _ (D.x k) (D.hx k))
      (D.αij k k k) e)
    (hejk : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d hd₂ hd₃
      (D.wj k k k) (D.wk k k k)
      (Functor.Restriction.id _ (D.x k) (D.hx k)) (Functor.Restriction.id _ (D.x k) (D.hx k))
      (D.αjk k k k) e)
    (heik : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d hd₁ hd₃
      (D.wi k k k) (D.wk k k k)
      (Functor.Restriction.id _ (D.x k) (D.hx k)) (Functor.Restriction.id _ (D.x k) (D.hx k))
      (D.αik k k k) e) :
    ambientSpaceFunctor.map e = 𝟙 (D.x k).ambient := by
  rw [D.diagonalPullback_eq_id (isFiberedInGroupoids hiso hfib) k he heij hejk heik]
  exact CategoryTheory.Functor.map_id _ _

/-- **Stacks 0CJU, symmetry of the relation.** Over the overlap `U_k ×_U U_{k'}` the gluing
isomorphism `φ_{kk'}` and the pullback `σ^*φ_{k'k}` of `φ_{k'k}` along the switching morphism
have mutually inverse ambient components: this is the second identity of **Stacks 026C** read on
the ambient spaces, and it is the source's observation that `φ_{kk'}⁻¹` is the flip of
`φ_{k'k}`. -/
@[stacks 0CJU "symmetry of the relation"]
theorem relation_symm (k k' : K) {d₁₃ : Vij k k' ⟶ Vijk k k' k}
    {hd₁ : pr₁ k k' = d₁₃ ≫ q₁ k k' k} {hd₂ : pr₂ k k' = d₁₃ ≫ q₂ k k' k}
    {hd₃ : pr₁ k k' = d₁₃ ≫ q₃ k k' k}
    {σφ : (D.xrji k k').pt ⟶ (D.xrij k k').pt}
    (hσφ : Functor.FibreHom (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (D.xrji k k').pt (D.xrij k k').pt (D.xrji k k').hpt (D.xrij k k').hpt σφ)
    (hij : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d₁₃ hd₁ hd₂
      (D.wi k k' k) (D.wj k k' k) (D.xrij k k') (D.xrji k k') (D.αij k k' k) (D.φ k k'))
    (hji : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d₁₃ hd₂ hd₃
      (D.wj k k' k) (D.wk k k' k) (D.xrji k k') (D.xrij k k') (D.αjk k k' k) σφ)
    (hik : Functor.IsRestrictionOf (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) d₁₃ hd₁ hd₃
      (D.wi k k' k) (D.wk k k' k) (D.xrij k k') (D.xrij k k') (D.αik k k' k)
      (𝟙 (D.xrij k k').pt)) :
    ambientSpaceFunctor.map (D.φ k k') ≫ ambientSpaceFunctor.map σφ =
      𝟙 (D.xrij k k').pt.ambient := by
  rw [← CategoryTheory.Functor.map_comp,
    D.gluing_comp_switchPullback_eq_id k k' hσφ hij hji hik]
  exact CategoryTheory.Functor.map_id _ _

/-- **Stacks 0CJU, transitivity of the relation.** Over the triple overlap the cocycle condition
of the descent datum says that the gluing isomorphism from `ξ_k` to `ξ_{k''}` is the composite
of the ones from `ξ_k` to `ξ_{k'}` and from `ξ_{k'}` to `ξ_{k''}`; the same therefore holds of
their ambient components. This is the source's transitivity of the relation. -/
@[stacks 0CJU "transitivity of the relation"]
theorem relation_trans (k k' k'' : K) :
    ambientSpaceFunctor.map (D.αik k k' k'') =
      ambientSpaceFunctor.map (D.αij k k' k'') ≫ ambientSpaceFunctor.map (D.αjk k k' k'') := by
  rw [← CategoryTheory.Functor.map_comp, D.cocycle k k' k'']

end Descent

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
