module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor

/-! # A stackification is determined up to 2-isomorphism (the "moreover" of Stacks 02ZN/02ZP)

Let `(𝒞, J)` be a site and let `p : 𝒜 ⥤ 𝒞` be a fibred category. Stacks 02ZN produces a stack
`p' : ℬ ⥤ 𝒞` and a 1-morphism `G : 𝒜 ⥤ ℬ` over `𝒞` satisfying

1. for every `U` and all `a`, `b` in the fibre `𝒜_U` the induced map `Mor(a, b) ⟶ Mor(G a, G b)`
   of presheaves on `𝒞/U` identifies the target with the sheafification of the source, and
2. every object of a fibre of `ℬ` is, locally on the base, in the essential image of `G` on
   fibres,

and then asserts, as its last sentence — repeated verbatim by Stacks 02ZP for the fibred-in-
groupoids case — that *`ℬ` is determined up to unique 2-isomorphism by these conditions*. The
existence half is the construction; **this file is the determinacy half**, which is what makes the
two clauses a *criterion*: a 1-morphism `F : 𝒜 ⥤ 𝒳` into a stack `q` satisfying (1) and (2) does
not merely have a stack for its target, it exhibits that target as *the* stackification, so the
target is equivalent to `ℬ` over `𝒞`.

That is the direction consumers need. Stacks 05YQ, for instance, builds a functor
`Spec : FA_d ⟶ ℋ_d`, checks (1) and (2) for it, and concludes from "Stacks, Lemma 02ZP" that
`ℋ_d` is equivalent to the stackification of `FA_d`, which is the quotient stack `[X/G]`. The two
results already in the tree under that tag,
`CategoryTheory.Functor.Stackification.isFiberedInGroupoids_of_isStackification` and
`.isStackInGroupoids_of_isStackification`, say only that a *given* stackification has a stack in
groupoids for its target; they take clauses (1) and (2) as hypotheses and carry them unchanged to
the conclusion, so they cannot produce an equivalence.

## Main results

* `CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_of_locally_fullyFaithful`: a
  1-morphism `H : ℬ ⥤ 𝒳` from a stackification into a stack is an equivalence over `𝒞` as soon as
  the composite `G ⋙ H` satisfies clauses (1) and (2);
* `CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_of_natIso`: the same with the
  hypotheses read on a 1-morphism `F` only 2-isomorphic to `G ⋙ H`, which is the shape in which
  the universal property (Stacks 0435/0436) delivers a comparison;
* `CategoryTheory.Functor.Stackification.nonempty_isEquivalenceOver_extend`: the determinacy
  clause itself — if `F : 𝒜 ⥤ 𝒳` into a stack `q` satisfies clauses (1) and (2), then the
  extension of `F` along `G` given by Stacks 0435 is an equivalence of `p'` with `q` over `𝒞`,
  compatibly with `G` and `F` by `CategoryTheory.Functor.Stackification.unit`.

## The argument

All three are the universal property plus the two characterisation lemmas, with no new
mathematics:

* `H` is fully faithful by Stacks 04WQ in the form the tree already has it for an extension along
  a stackification, `CategoryTheory.Functor.Stackification.full_of_extension` and
  `.faithful_of_extension`. These take an *arbitrary* `H` out of the stackification — the clauses
  on the composite are exactly their hypotheses — so nothing has to be known about how `H` arose.
* `H` is locally essentially surjective on fibres because `G ⋙ H` is: a local preimage under
  `G ⋙ H` of an object of a fibre of `q` is, in particular, a local preimage under `H`, namely of
  its image under `G`.
* A fully faithful 1-morphism of stacks that is locally essentially surjective on fibres is an
  equivalence over `𝒞`, which is Stacks 046N,
  `CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`.

For the third result the clauses have to be moved from `F` across the 2-isomorphism
`CategoryTheory.Functor.Stackification.unit : G ⋙ H ≅ F`: clause (1) by
`CategoryTheory.Functor.Stackification.isLocallyBijective_morPresheafMap_of_natIso`, which exists
for exactly this purpose, and clause (2) by
`CategoryTheory.Functor.IsFibredOneMorphism.natIsoFiber`, the isomorphism of induced functors on
a fibre that a vertical 2-isomorphism gives.

## Implementation notes

What is *not* here is the uniqueness of the 2-isomorphism, the other half of the source's
"determined up to **unique** 2-isomorphism". That is already in the tree as Stacks 04W9,
`CategoryTheory.Functor.Stackification.restrict_isEquivalence`: restriction along a stackification
is an equivalence of the morphism categories, so a 1-morphism out of `ℬ` and a 2-isomorphism
between two such are determined by their restrictions along `G`. The results below consume the
full-faithfulness half of that same statement through `full_of_extension`.

"Equivalence" is read as equivalence in the 2-category of fibred categories over `𝒞`,
`CategoryTheory.Functor.IsEquivalenceOver`: a quasi-inverse that is again strictly over `𝒞`, with
vertical unit and counit. It is data, hence the `Nonempty`; the source's "equivalent" is this
notion, not an equivalence of underlying categories.

The three fibred categories share one morphism universe. That is forced by
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, whose source and target are
presheaves of types in the morphism universes of the two categories it relates, and it is the
configuration `CategoryTheory.Functor.Stackification.full_of_extension` is stated at. The base's
morphism universe is independent. No `UnivLE` hypothesis occurs.

## References

* [Stacks 02ZN](https://stacks.math.columbia.edu/tag/02ZN).
* [Stacks 02ZP](https://stacks.math.columbia.edu/tag/02ZP).
* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435).
* [Stacks 046N](https://stacks.math.columbia.edu/tag/046N).
* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9).
* [Stacks 04WQ](https://stacks.math.columbia.edu/tag/04WQ).
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

namespace Stackification

universe vb v u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {ℬ : Type u₃} [Category.{v} ℬ] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒜 ⥤ 𝒞} {p' : ℬ ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} [p.IsFibered] [p'.IsFibered] [q.IsFibered]
  {G : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒳}
  (hG : p.IsFibredOneMorphism p' G) (hH : p'.IsFibredOneMorphism q H)
  (J : GrothendieckTopology 𝒞)

/-! ### A 1-morphism out of a stackification whose composite satisfies the two clauses -/

section Composite

variable
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
  (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) ((hG.comp hH).morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) ((hG.comp hH).morPresheafMap a b))
  (hFobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (hG.comp hH).comp_eq V).essImage (pullbackFiber q x f))
  (hp' : p'.IsStack J) (hq : q.IsStack J)

include hGmor hGobj hFmor hFobj hp' hq

/-- **The determinacy clause of Stacks 02ZN and 02ZP, in the form a consumer uses.** Let
`G : 𝒜 ⥤ ℬ` exhibit the stack `p'` as the stackification of the fibred category `p` — that is, let
it satisfy the two clauses `hGmor` and `hGobj` — and let `H : ℬ ⥤ 𝒳` be a 1-morphism of fibred
categories into a stack `q`. If the composite `G ⋙ H` satisfies the same two clauses, then `H` is
an equivalence of `p'` with `q` over `𝒞`.

So two stackifications of one fibred category have equivalent targets, and the comparison realising
the equivalence is any 1-morphism between them compatible with the two presentations. The two
clauses, which for a given stackification are hypotheses carried to the conclusion by
`CategoryTheory.Functor.Stackification.isStackInGroupoids_of_isStackification`, thereby become a
*criterion* on `G ⋙ H`.

`H` is fully faithful by `CategoryTheory.Functor.Stackification.full_of_extension` and
`.faithful_of_extension`, Stacks 04WQ for a 1-morphism out of a stackification, whose hypotheses
are precisely the clauses on `G` and on the composite. It is locally essentially surjective on
fibres because `G ⋙ H` is, a local preimage under the composite being one under `H`. Stacks 046N,
`CategoryTheory.Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers`, then concludes. -/
@[stacks 02ZP "the determinacy half of the statement — `𝒮'` is determined up to 2-isomorphism by \
clauses (1) and (2) — read as: a 1-morphism from a stackification into a stack whose composite \
with the stackification again satisfies the two clauses is an equivalence over the site. The \
existence half is the construction of Stacks 02ZN, not assembled in the tree; the uniqueness of \
the 2-isomorphism is Stacks 04W9, \
`CategoryTheory.Functor.Stackification.restrict_isEquivalence`; and the groupoid half of 02ZP is \
`CategoryTheory.Functor.Stackification.isStackInGroupoids_of_isStackification`"]
theorem nonempty_isEquivalenceOver_of_locally_fullyFaithful :
    Nonempty (IsEquivalenceOver p' q H) := by
  have : H.Full := full_of_extension hG hH J hGmor hGobj hFmor hp'.isMorSheaf hq.isMorSheaf
  have : H.Faithful := faithful_of_extension hG hH J hGmor hGobj hFmor hp'.isMorSheaf hq.isMorSheaf
  rw [isEquivalenceOver_iff_locallyEssSurjOnFibers hp' hq hH]
  intro U x
  obtain ⟨R, hR, hRess⟩ := hFobj U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨a, ⟨ι⟩⟩ := hRess hf
  exact ⟨(fiberFunctorOfCompEq hG.comp_eq V).obj a, ⟨ι⟩⟩

end Composite

/-! ### The two clauses read on a 1-morphism 2-isomorphic to the composite -/

section NatIso

variable {F : 𝒜 ⥤ 𝒳} (hF : p.IsFibredOneMorphism q F) (α : G ⋙ H ≅ F)
  (hα : ∀ a : 𝒜, q.IsHomLift (𝟙 (p.obj a)) (α.hom.app a))
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
  (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b))
  (hFobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q x f))

include hα hFobj

omit [p.IsFibered] [p'.IsFibered] in
/-- **Clause (2) transports across a vertical 2-isomorphism.** If every object of a fibre of `q` is
locally in the essential image of `F` on fibres and `α : G ⋙ H ≅ F` is vertical, the same holds
for `G ⋙ H`: the induced functors on a fibre are isomorphic by
`CategoryTheory.Functor.IsFibredOneMorphism.natIsoFiber`. -/
theorem locally_essImage_comp_of_natIso (U : 𝒞) (x : q.Fiber U) : ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq (hG.comp hH).comp_eq V).essImage (pullbackFiber q x f) := by
  obtain ⟨R, hR, hRess⟩ := hFobj U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨a, ⟨ι⟩⟩ := hRess hf
  exact ⟨a, ⟨(IsFibredOneMorphism.natIsoFiber (hG.comp hH) hF α hα a).trans ι⟩⟩

include hH hGmor hGobj hFmor

/-- **The determinacy clause of Stacks 02ZN and 02ZP with the clauses read on a 1-morphism
`F : 𝒜 ⥤ 𝒳` only vertically 2-isomorphic to `G ⋙ H`.** This is the shape in which the universal
property of stackification, Stacks 0435 and 0436, delivers a comparison: it produces `H` together
with a 2-isomorphism `G ⋙ H ≅ F`, not an equality. Both clauses transport,
clause (1) by `CategoryTheory.Functor.Stackification.isLocallyBijective_morPresheafMap_of_natIso`
and clause (2) by
`CategoryTheory.Functor.Stackification.locally_essImage_comp_of_natIso`. -/
theorem nonempty_isEquivalenceOver_of_natIso (hp' : p'.IsStack J) (hq : q.IsStack J) :
    Nonempty (IsEquivalenceOver p' q H) :=
  nonempty_isEquivalenceOver_of_locally_fullyFaithful hG hH J hGmor hGobj
    (isLocallyBijective_morPresheafMap_of_natIso hG hH J hF α hα hFmor)
    (locally_essImage_comp_of_natIso hG hH J hF α hα hFobj) hp' hq

end NatIso

/-! ### The determinacy clause for the canonical extension -/

section Extend

variable {F : 𝒜 ⥤ 𝒳} (hF : p.IsFibredOneMorphism q F)
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
  (hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hF.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hF.morPresheafMap a b))
  (hFobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF.comp_eq V).essImage (pullbackFiber q x f))
  (hp' : p'.IsStack J) (hq : q.IsStack J)

include hGmor hGobj hFmor hFobj hp' hq

/-- **A stackification is determined up to 2-isomorphism: the "moreover" of Stacks 02ZN, repeated
by Stacks 02ZP.** Let `G : 𝒜 ⥤ ℬ` exhibit the stack `p'` as the stackification of the fibred
category `p`, and let `F : 𝒜 ⥤ 𝒳` be a 1-morphism into a stack `q` satisfying the same two
clauses — `hFmor`, that the induced maps of morphism presheaves are locally bijective, and
`hFobj`, that every object of a fibre of `q` is locally in the essential image of `F` on fibres.
Then the extension of `F` along `G` supplied by the universal property, Stacks 0435, is an
equivalence of `p'` with `q` over `𝒞`.

So a 1-morphism satisfying the two clauses does not merely land in *a* stack: it exhibits its
target as *the* stackification. The extension is compatible with the two presentations by
`CategoryTheory.Functor.Stackification.unit`, which is the 2-isomorphism `G ⋙ H ≅ F`, so the
equivalence identifies the two presentations and not just the two targets. -/
@[stacks 02ZP "the determinacy half of the statement — `𝒮'` is determined up to 2-isomorphism by \
clauses (1) and (2) — for the canonical extension: a 1-morphism into a stack satisfying the two \
clauses exhibits that stack as the stackification, so the extension of Stacks 0435 is an \
equivalence over the site. The existence half is the construction of Stacks 02ZN, not assembled \
in the tree; the uniqueness of the 2-isomorphism is Stacks 04W9, \
`CategoryTheory.Functor.Stackification.restrict_isEquivalence`; and the groupoid half of 02ZP is \
`CategoryTheory.Functor.Stackification.isStackInGroupoids_of_isStackification`"]
theorem nonempty_isEquivalenceOver_extend :
    Nonempty (IsEquivalenceOver p' q
      (extend hG hF hGmor hq.isMorSheaf hGobj hq.hasEffectiveDescent)) :=
  nonempty_isEquivalenceOver_of_natIso hG
    (extend_isFibredOneMorphism hG hF hGmor hq.isMorSheaf hGobj hq.hasEffectiveDescent) J hF
    (unit hG hF hGmor hq.isMorSheaf hGobj hq.hasEffectiveDescent)
    (isHomLift_unit_app hG hF hGmor hq.isMorSheaf hGobj hq.hasEffectiveDescent)
    hGmor hGobj hFmor hFobj hp' hq

end Extend

end Stackification

end Functor

end CategoryTheory

end
