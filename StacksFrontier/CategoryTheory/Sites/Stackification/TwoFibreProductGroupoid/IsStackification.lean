module

public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.MorphismSections
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocalEssentialImage

/-!
# The stackification of a 2-fibre product is the 2-fibre product of the stackifications

This file is the last part of the proof of Stacks 04Y2, assembled in
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid`. It proves clause (2)
for the 2-fibre product from its local form in
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocalEssentialImage`
(`objClause`) and local injectivity of the map of morphism presheaves induced by `H`, and combines
them with the local surjectivity of
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProductGroupoid.LocallySurjective` into
Stacks 04Y2.


Let `(𝒞, J)` be a site and let `f : 𝒳 ⥤ 𝒴` and `g : 𝒵 ⥤ 𝒴` be 1-morphisms of categories fibred in
groupoids over `𝒞`. A *stackification* of a category `p : 𝒳 ⥤ 𝒞` fibred in groupoids (Stacks 02ZP,
Stacks 02ZN) is a 1-morphism `i : 𝒳 ⥤ 𝒳'` over `𝒞` whose target is a stack in groupoids over
`(𝒞, J)` and which is such that (1) for every `U` and all `x`, `y` in the fibre `𝒳_U` the induced
map `Mor(x, y) ⟶ Mor(i x, i y)` of presheaves on `𝒞/U` exhibits the target as the sheafification of
the source, and (2) every object of `𝒳'` is, locally on the base, in the essential image of `i`.

Let `i : 𝒳 ⥤ 𝒳'`, `j : 𝒴 ⥤ 𝒴'` and `k : 𝒵 ⥤ 𝒵'` be stackifications and let
`f' : 𝒳' ⥤ 𝒴'`, `g' : 𝒵' ⥤ 𝒴'` be 1-morphisms over `𝒞` 2-commuting with `f` and `g` along them,
that is with vertical 2-isomorphisms `α : i ⋙ f' ≅ f ⋙ j` and `β : k ⋙ g' ≅ g ⋙ j` (such `f'`,
`g'` exist by the universal property of the stackification, Stacks 0436). Stacks 04Y2 says that the
stackification of the 2-fibre product is the 2-fibre product of the stackifications: the 2-fibre
product `𝒳' ×_{𝒴'} 𝒵'` is a stack in groupoids and the canonical 1-morphism
`𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'` — the one induced by `i`, `j`, `k` through the universal property of the
target — is a stackification of `𝒳 ×_𝒴 𝒵` in exactly the above sense.

## Main results

* `CategoryTheory.TwoFibreProductOver.isStackification_of_isStackification`: Stacks 04Y2.

## Implementation notes

The 2-fibre product is the one taken in the 2-category of categories over `𝒞`,
`CategoryTheory.TwoFibreProductOver` (Stacks 0040): its objects are the quadruples `(U, x, y, φ)`
with `x` over `U`, `y` over `U` and `φ : f x ≅ g y` *vertical* over `U`. Mathlib's
`CategoryTheory.Limits.CategoricalPullback` is the 2-fibre product of plain categories
(Stacks 003R), built from arbitrary isomorphisms `f x ≅ g y`, and Stacks 0H2D exhibits a cospan for
which the two constructions are inequivalent, so it is not the object of this statement.

"Stack in groupoids" (Stacks 02ZI) is spelled as `IsFiberedInGroupoids` together with `IsStack J`,
these being equivalent by Stacks 02ZJ
(`CategoryTheory.Functor.stackInGroupoids_tfae`). Of the two, only `IsStack J` appears in the
conclusion: that the structure functor of a 2-fibre product of categories fibred in groupoids is
again fibred in groupoids is Stacks 0041
(`CategoryTheory.TwoFibreProductOver.isFiberedInGroupoids`), which is invoked inside the statement,
for both 2-fibre products, to supply the fibredness instances the presheaves `Mor(·, ·)` are built
from.

The 1-morphisms of the 2-category of categories fibred in groupoids over `𝒞` (Stacks 02XS) are the
functors *strictly* over `𝒞`, and that is the hypothesis carried by `f`, `g`, `f'`, `g'`, `i`, `j`
and `k`: for categories fibred in groupoids such a functor automatically preserves strongly
cartesian morphisms
(`CategoryTheory.Functor.IsFiberedInGroupoids.isFibredOneMorphism`), which is how the
1-morphisms of fibred categories that the presheaf maps below need are obtained. The 2-morphisms of
that 2-category are the natural transformations with vertical components, which is the hypothesis
carried by `α`, `β` and by the two comparison 2-isomorphisms `γ`, `δ` below.

"`i` is a stackification" is spelled out from the two conditions of Stacks 02ZP rather than
referred to a predicate, there being none in the tree yet — Stacks 02ZN is not formalized — and the
two conditions are then repeated verbatim for the canonical 1-morphism in the conclusion, so that
hypothesis and conclusion assert one and the same notion. The spelling is the one fixed by the
statement of Stacks 06NS (`CategoryTheory.RelativeInertia.isStackification_functoriality`), which
states the same notion for the inertia:

* Condition (1) is read through the canonical map of Stacks 042V,
  `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, between the presheaves `Mor(x, y)`
  of Stacks 02ZB on the slice `𝒞/U`. "Identifies the target with the sheafification of the source"
  is stated as: the map is locally injective and locally surjective for the induced topology
  `J.over U`, the target being a sheaf. That is the standard characterisation of a sheafification
  map (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`), and it is used in place of an
  isomorphism from a sheafification functor because `Mor(x, y)` is valued in the hom-universe of
  the fibred category, which Mathlib's sheafification of type-valued presheaves does not
  accommodate. That the target is a sheaf is not repeated as a clause: on the hypothesis side it is
  `hs𝒳'.isMorSheaf` and on the conclusion side it is the `IsStack` conjunct.
* Condition (2) is read in sieve language and without chosen pullbacks: for every object `x'` there
  is a covering sieve `R` of `p𝒳'.obj x'` such that for each `u : V ⟶ p𝒳'.obj x'` in `R` there are
  an object `x` of `𝒳` and a morphism `i x ⟶ x'` strongly cartesian over `u`. Giving such a
  morphism is the same as giving an isomorphism `u^* x' ≅ i x` in the fibre over `V`, cartesian
  lifts being unique up to unique vertical isomorphism, so this is "`x'|_V` is in the essential
  image of `𝒳_V ⥤ 𝒳'_V`"; and quantifying over all objects `x'` is quantifying over all `U` and all
  objects of the fibre `𝒳'_U`.

Clause (2) is stated in the same form as in the statement of Stacks 06NS. The statement of Stacks
02ZN, which asserts the existence of the stackification, states it in the equivalent form
"`u^* x'` lies in the essential image of the functor on fibres"
(`CategoryTheory.Functor.essImage` of `CategoryTheory.Functor.fiberFunctorOfCompEq` at
`CategoryTheory.Functor.pullbackFiber`); the two agree because a morphism `i x ⟶ x'` strongly
cartesian over `u` is the same datum as an isomorphism `u^* x' ≅ i x` of the fibre over `V`, the
chosen cartesian lift of `u` at `x'` being unique up to unique vertical isomorphism. The form used
here does not mention the chosen pullbacks.

The canonical 1-morphism is pinned by the property the source names it by — "by construction of
2-fibre products there is a canonical 1-morphism `𝒳 ×_𝒴 𝒵 → 𝒳' ×_{𝒴'} 𝒵'`" — rather than by a
choice of construction: the statement quantifies over every `H` that is a morphism of the two
2-commutative squares, namely one carrying vertical 2-isomorphisms
`γ : H ⋙ π₁' ≅ π₁ ⋙ i` and `δ : H ⋙ π₂' ≅ π₂ ⋙ k` whose compatibility square with the two
filling 2-cells `ψ`, `ψ'` and with `α`, `β` commutes. Componentwise at `P = (U, x, z, φ)` that
compatibility reads
`(H P).φ ≫ g'(δ_P) = f'(γ_P) ≫ α_x ≫ j(φ) ≫ β⁻¹_z`, which determines `H` on objects and on
morphisms up to the given 2-isomorphisms; by the universal property of the 2-fibre product
(Stacks 0040, `CategoryTheory.TwoFibreProductOver.liftIso`) any two such `H` are 2-isomorphic over
`𝒞`, and `CategoryTheory.TwoFibreProductOver.lift` provides one, with `γ` and `δ` the identity, so
the hypothesis is satisfiable and the universally quantified statement is the assertion about the
canonical 1-morphism. Being a stackification is invariant under 2-isomorphism over `𝒞`, so nothing
is gained or lost by taking `H` general rather than constructed.

The source states the conclusion as an equivalence: it names `𝒲` the stackification of
`𝒳 ×_𝒴 𝒵`, obtains from the canonical 1-morphism `𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'` an induced
`h : 𝒲 ⥤ 𝒳' ×_{𝒴'} 𝒵'` by the universal property of the stackification (Stacks 0435), and shows
`h` to be an equivalence by checking that it is bijective on `Mor`-sheaves and that every object of
the target is locally in its essential image (Stacks 04WQ, Stacks 046N). Here the conclusion is
instead that the canonical 1-morphism is itself a stackification. The two assert the same thing:
`𝒳 ×_𝒴 𝒵 ⥤ 𝒲` satisfies the two conditions of Stacks 02ZP, so for the composite
`𝒳 ×_𝒴 𝒵 ⥤ 𝒲 ⥤ 𝒳' ×_{𝒴'} 𝒵'` those two conditions hold if and only if they hold for `h`, and for
a 1-morphism of stacks in groupoids they hold if and only if it is an equivalence over `𝒞`
(Stacks 04WQ, Stacks 046N again). Phrasing it without `𝒲` keeps the existence of the stackification
of `𝒳 ×_𝒴 𝒵` (Stacks 02ZN) out of a statement that does not otherwise use it.

The hom-universes of the six categories of the two squares are one and the same `v`, while the
site's is the independent `vb` and the universes of objects are all independent: a map
`Mor(x, y) ⟶ Mor(i x, i y)` is a map of presheaves valued in the hom-universes of the source and
of the target respectively, so the map of Stacks 042V exists without a universe lift only when
those agree, and the 2-fibre product has the hom-universe assembled from those of `𝒞` and of the
two factors. Nothing, on the other hand, forces the site's hom-universe to join them, and the
026G this proof consumes,
`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`, is already stated with the two
separate. Keeping `vb` free is what lets the result apply over a big fppf site to categories whose
morphisms live one universe above the site's, which is the case of a quotient stack.

The source's route uses clause (1) of the stackification hypothesis on `j` — that
`Mor(f x, g z) ⟶ Mor(j f x, j g z)` is locally surjective, which is what makes the comparison
isomorphism of an object of `𝒳' ×_{𝒴'} 𝒵'` locally come from a morphism of `𝒴` — but not clause
(2); the clause is nevertheless part of the hypothesis, because it is what makes `𝒴'` *the*
stackification of `𝒴` rather than merely a stack in groupoids receiving a map that sheafifies the
morphism presheaves, and Stacks 04Y2 is a statement about the stackifications.

Faithfulness. (1) No hypothesis is dead: `h𝒳`, `h𝒴`, `h𝒵`, `hf`, `hg` are what make `𝒳 ×_𝒴 𝒵` a
category fibred in groupoids over `𝒞` and provide the chosen pullbacks the presheaves `Mor(·, ·)`
of the conclusion are built from, `h𝒳'`, `h𝒴'`, `h𝒵'`, `hf'`, `hg'` do the same for `𝒳' ×_{𝒴'} 𝒵'`,
`hs𝒳'`, `hs𝒴'`, `hs𝒵'` are the hypothesis of the `IsStack` conjunct, the triples
`(hi, hmor𝒳, hobj𝒳)`, `(hj, hmor𝒴, hobj𝒴)` and `(hk, hmor𝒵, hobj𝒵)` are exactly the data of "`i`,
`j`, `k` are stackifications" (see the paragraph above on clause (2) for `j`), `α`, `β` with their
verticality are the 2-commutativity of the two functoriality squares without which `𝒳' ×_{𝒴'} 𝒵'`
is not the 2-fibre product of the stackified cospan, and `γ`, `δ`, `hγ`, `hδ`, `hψ` are what pin
`H`; drop any one of the three conjuncts of the conclusion and it no longer says that
`𝒳' ×_{𝒴'} 𝒵'` is the stackification of `𝒳 ×_𝒴 𝒵`. (2) The base and the topology are the source's:
one site `(𝒞, J)` throughout, all six structure functors and the two structure functors of the
2-fibre products are functors to that same `𝒞`, all seven 1-morphisms are strictly over `𝒞`, and
the presheaves `Mor(·, ·)` are presheaves on the slice `𝒞/U` for the induced topology `J.over U`,
not on `𝒞`. (3) The canonical maps the source names are pinned, not merely asserted to exist: the
2-fibre products are the explicit ones of Stacks 0040 with their projections and filling 2-cells,
the maps on morphism presheaves are those of Stacks 042V, and the canonical 1-morphism of 2-fibre
products is characterised by `γ`, `δ` and `hψ` as described above. (4) The hypotheses are
satisfiable non-vacuously: any stack in groupoids is its own stackification, with `𝒳' = 𝒳`,
`i = 𝟭 𝒳`, `hmor𝒳` holding because the map of presheaves is then an isomorphism and `hobj𝒳` with
the maximal sieve, and with `f' = f`, `g' = g`, `α`, `β` the identity and `H` the identity functor
the statement specialises to Stacks 026G for `𝒳 ×_𝒴 𝒵`; the instantiation is not degenerate,
because for `𝒳`, `𝒴`, `𝒵` not already stacks the two conditions on `H` are conditions on a
1-morphism that is not an equivalence.

## References

* [StacksProject 04Y2](https://stacks.math.columbia.edu/tag/04Y2)
-/

@[expose] public section

-- The endpoints of the chosen cartesian lifts compared below are spelled through
-- `Functor.pullbackFiber`, `Functor.Fiber.fiberInclusion` and `Functor.fiberFunctorOfCompEq`, so
-- the instance arguments of `IsHomLift` and `IsCartesian` are only found after unfolding those.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe vb v u₀ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.TwoFibreProductOver

variable {𝒞 : Type u₀} [Category.{vb} 𝒞] {𝒳 : Type u₁} [Category.{v} 𝒳] {𝒴 : Type u₂}
  [Category.{v} 𝒴] {𝒵 : Type u₃} [Category.{v} 𝒵] {𝒳' : Type u₄} [Category.{v} 𝒳'] {𝒴' : Type u₅}
  [Category.{v} 𝒴'] {𝒵' : Type u₆} [Category.{v} 𝒵']

/-- If `a : i x ⟶ x'` lies over `u ≫ eqToHom _` and `i` is strictly over the base, then `a` lies
over `u` and `x` lies over the source of `u`. -/
private lemma isHomLift_and_obj_eq {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] {pA : 𝒜 ⥤ 𝒞}
    {pB : ℬ ⥤ 𝒞} {i : 𝒜 ⥤ ℬ} (hi : i ⋙ pB = pA) {x : 𝒜} {x' : ℬ} {b V : 𝒞} (hb : pB.obj x' = b)
    (u : V ⟶ b) (a : i.obj x ⟶ x') (ha : pB.IsHomLift (u ≫ eqToHom hb.symm) a) :
    pB.IsHomLift u a ∧ pA.obj x = V := by
  have h := (IsHomLift.lift_comp_eqToHom_iff pB u a hb.symm).mp ha
  exact ⟨h, (Functor.congr_obj hi x).symm.trans (IsHomLift.domain_eq pB u a)⟩

section

variable {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} {i : 𝒳 ⥤ 𝒳'} {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'}
  {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'} [p𝒳.IsFibered]
  [p𝒴.IsFibered] [p𝒵.IsFibered] [p𝒳'.IsFibered] [p𝒴'.IsFibered] [p𝒵'.IsFibered]
  [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered]
  (hf₁ : Functor.IsFibredOneMorphism p𝒳 p𝒴 f) (hg₁ : Functor.IsFibredOneMorphism p𝒵 p𝒴 g)

variable (hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f')
  (hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')

section

variable (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i) (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
  (hHmor :
    Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
  (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
  (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P))
  (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
  (hδ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒵'.IsHomLift (𝟙 P.base) (δ.hom.app P))

include hf₁ hg₁ hi₁ hk₁ hHmor γ hγ δ hδ in
open Opposite _root_.CategoryTheory.Functor in
omit [p𝒳'.IsFibered] [p𝒵'.IsFibered] [(structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered] hHmor in
omit [(structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered] in
/-- **Clause (2) for the 2-fibre product.** Every object of `𝒳' ×_{𝒴'} 𝒵'` is, locally on the base,
the image under `H` of an object of `𝒳 ×_𝒴 𝒵`: intersect the coverings on which the two components
come from `𝒳` and from `𝒵`, and refine each member by the covering on which the comparison
isomorphism comes from `𝒴`. -/
private lemma objClause (J : GrothendieckTopology 𝒞) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (hq' : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFiberedInGroupoids)
    (hf'₁ : Functor.IsFibredOneMorphism p𝒳' p𝒴' f') (hg'₁ : Functor.IsFibredOneMorphism p𝒵' p𝒴' g')
    (hj₁ : Functor.IsFibredOneMorphism p𝒴 p𝒴' j) (α : i ⋙ f' ≅ f ⋙ j)
    (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x)) (β : k ⋙ g' ≅ g ⋙ j)
    (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z))
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫ Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv)
    (hobj𝒳 :
      ∀ x' : 𝒳',
        ∃ R ∈ J (p𝒳'.obj x'),
          ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒳'.obj x'),
            R u → ∃ (x : 𝒳) (φ : i.obj x ⟶ x'), p𝒳'.IsStronglyCartesian u φ)
    (hobj𝒵 :
      ∀ z' : 𝒵',
        ∃ R ∈ J (p𝒵'.obj z'),
          ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒵'.obj z'),
            R u → ∃ (z : 𝒵) (φ : k.obj z ⟶ z'), p𝒵'.IsStronglyCartesian u φ)
    (hmor𝒴 :
      ∀ (V : 𝒞) (y w : p𝒴.Fiber V),
        Presheaf.IsLocallySurjective (J.over V) (hj₁.morPresheafMap y w))
    (P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g') :
    ∃ R ∈ J P'.base,
      ∀ ⦃V : 𝒞⦄ (u : V ⟶ P'.base),
        R u →
          ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : H.obj P ⟶ P'),
            (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian u φ := by
  obtain ⟨R₁, hR₁, hR₁'⟩ := hobj𝒳 P'.x
  obtain ⟨R₂, hR₂, hR₂'⟩ := hobj𝒵 P'.y
  set S₀ : Sieve P'.base :=
    R₁.pullback (eqToHom P'.hx.symm) ⊓ R₂.pullback (eqToHom P'.hy.symm) with hS₀def
  have hS₀ : S₀ ∈ J P'.base :=
    J.intersection_covering (J.pullback_stable _ hR₁) (J.pullback_stable _ hR₂)
  have key :
    ∀ ⦃V : 𝒞⦄ (u : V ⟶ P'.base),
      S₀ u →
        ∃ R ∈ J V,
          ∀ ⦃W : 𝒞⦄ (t : W ⟶ V),
            R t →
              ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : H.obj P ⟶ P'),
                (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian (t ≫ u) φ := by
    intro V u hu
    obtain ⟨x, a, ha⟩ := hR₁' (u ≫ eqToHom P'.hx.symm) hu.1
    obtain ⟨z, b, hb⟩ := hR₂' (u ≫ eqToHom P'.hy.symm) hu.2
    obtain ⟨ha1, hxV⟩ := isHomLift_and_obj_eq hi₁.comp_eq P'.hx u a ha.toIsHomLift
    obtain ⟨hb1, hzV⟩ := isHomLift_and_obj_eq hk₁.comp_eq P'.hy u b hb.toIsHomLift
    have := ha1
    have := hb1
    exact
      objStep hf₁ hg₁ hi₁ hk₁ γ hγ δ hδ J h𝒴 h𝒴' hq' hf'₁ hg'₁ hj₁ α hα β hβ hψ hmor𝒴 P' u a
        ha1 hxV b hb1 hzV
  refine
    ⟨Sieve.bind S₀.1 (fun V u hu => (key u hu).choose),
      J.transitive hS₀ _
        (fun V u hu =>
          J.superset_covering (Sieve.le_pullback_bind _ _ _ hu) (key u hu).choose_spec.1),
      ?_⟩
  rintro W h ⟨V, t, u, hu, ht, rfl⟩
  exact (key u hu).choose_spec.2 t ht

end

omit [p𝒴'.IsFibered] in
include hf₁ hg₁ in
open Opposite _root_.CategoryTheory.Functor in
omit [p𝒴.IsFibered] in
/-- Local injectivity of the map of morphism presheaves induced by `H`: two sections with the same
image have `𝒳`- and `𝒵`-components with the same images under `i` and `k`, hence agree locally in
each component by the hypothesis on `i` and on `k`, hence agree locally. -/
private lemma isLocallyInjective_morPresheafMap (J : GrothendieckTopology 𝒞)
    (hi₁ : Functor.IsFibredOneMorphism p𝒳 p𝒳' i) (hk₁ : Functor.IsFibredOneMorphism p𝒵 p𝒵' k)
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    (hHmor :
      Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
        (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H)
    (hmor𝒳 :
      ∀ (U : 𝒞) (x y : p𝒳.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) (hi₁.morPresheafMap x y))
    (hmor𝒵 :
      ∀ (U : 𝒞) (z w : p𝒵.Fiber U),
        Presheaf.IsLocallyInjective (J.over U) (hk₁.morPresheafMap z w))
    {U : 𝒞} (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U) :
    Presheaf.IsLocallyInjective (J.over U) (hHmor.morPresheafMap P Q) := by
  refine ⟨fun {X} s t h => ?_⟩
  have hst : H.map (Fiber.fiberInclusion.map s) = H.map (Fiber.fiberInclusion.map t) :=
    (morPresheafMap_app_inj_iff hHmor P Q X s t).mp h
  obtain ⟨ha, hb⟩ := (H_map_eq_iff γ δ _ _).mp hst
  have := hmor𝒳 U (fibFst P) (fibFst Q)
  have := hmor𝒵 U (fibSnd P) (fibSnd Q)
  have hA :=
    Presheaf.equalizerSieve_mem (J.over U) (hi₁.morPresheafMap (fibFst P) (fibFst Q))
      (morFstSection hf₁ hg₁ P Q X s) (morFstSection hf₁ hg₁ P Q X t)
      ((morPresheafMap_morFstSection_inj_iff hf₁ hg₁ hi₁ P Q X s t).mpr ha)
  have hB :=
    Presheaf.equalizerSieve_mem (J.over U) (hk₁.morPresheafMap (fibSnd P) (fibSnd Q))
      (morSndSection hf₁ hg₁ P Q X s) (morSndSection hf₁ hg₁ P Q X t)
      ((morPresheafMap_morSndSection_inj_iff hf₁ hg₁ hk₁ P Q X s t).mpr hb)
  refine (J.over U).superset_covering ?_ ((J.over U).intersection_covering hA hB)
  rintro W hw ⟨h1, h2⟩
  simp only [Presheaf.equalizerSieve_apply] at h1 h2 ⊢
  refine section_ext hf₁ hg₁ P Q (op W) _ _ ?_ ?_
  · rwa [morFstSection_naturality, morFstSection_naturality]
  · rwa [morSndSection_naturality, morSndSection_naturality]

end

/-- **Stacks 04Y2.** Let `(𝒞, J)` be a site, let `f : 𝒳 ⥤ 𝒴` and `g : 𝒵 ⥤ 𝒴` be 1-morphisms of
categories fibred in groupoids over `𝒞`, let `i : 𝒳 ⥤ 𝒳'`, `j : 𝒴 ⥤ 𝒴'`, `k : 𝒵 ⥤ 𝒵'` be
stackifications (Stacks 02ZP: the targets are stacks in groupoids, the induced maps
`Mor(x, y) ⟶ Mor(i x, i y)` of presheaves on `𝒞/U` are locally bijective, and every object of the
target is locally in the essential image), and let `f' : 𝒳' ⥤ 𝒴'`, `g' : 𝒵' ⥤ 𝒴'` be 1-morphisms
over `𝒞` 2-commuting with `f` and `g` along `i`, `j`, `k` via vertical 2-isomorphisms `α`, `β`.
Then the stackification of the 2-fibre product is the 2-fibre product of the stackifications: the
2-fibre product `𝒳' ×_{𝒴'} 𝒵'` is a stack over `(𝒞, J)` — a stack in groupoids, being fibred in
groupoids by Stacks 0041 — and every canonical 1-morphism `H : 𝒳 ×_𝒴 𝒵 ⥤ 𝒳' ×_{𝒴'} 𝒵'`, that is
every morphism of the two 2-commutative squares, is a 1-morphism of fibred categories over `𝒞`
which is a stackification of `𝒳 ×_𝒴 𝒵`, in the same two clauses. -/
@[stacks 04Y2]
public theorem isStackification_of_isStackification {J : GrothendieckTopology 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞}
    {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞} {p𝒵' : 𝒵' ⥤ 𝒞}
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) (h𝒵 : p𝒵.IsFiberedInGroupoids)
    (h𝒳' : p𝒳'.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒵' : p𝒵'.IsFiberedInGroupoids) (hs𝒳' : p𝒳'.IsStack J) (hs𝒴' : p𝒴'.IsStack J)
    (hs𝒵' : p𝒵'.IsStack J) {f : 𝒳 ⥤ 𝒴} {g : 𝒵 ⥤ 𝒴} (hf : f ⋙ p𝒴 = p𝒳) (hg : g ⋙ p𝒴 = p𝒵)
    {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒵' ⥤ 𝒴'} (hf' : f' ⋙ p𝒴' = p𝒳') (hg' : g' ⋙ p𝒴' = p𝒵') {i : 𝒳 ⥤ 𝒳'}
    {j : 𝒴 ⥤ 𝒴'} {k : 𝒵 ⥤ 𝒵'} (hi : i ⋙ p𝒳' = p𝒳) (hj : j ⋙ p𝒴' = p𝒴) (hk : k ⋙ p𝒵' = p𝒵)
    (hmor𝒳 :
      haveI : p𝒳.IsFibered := h𝒳.isFibered
      haveI : p𝒳'.IsFibered := h𝒳'.isFibered
      ∀ (U : 𝒞) (x₁ x₂ : p𝒳.Fiber U),
        Presheaf.IsLocallyInjective (J.over U)
            ((h𝒳'.isFibredOneMorphism hi).morPresheafMap x₁ x₂) ∧
          Presheaf.IsLocallySurjective (J.over U)
            ((h𝒳'.isFibredOneMorphism hi).morPresheafMap x₁ x₂))
    (hobj𝒳 :
      ∀ x' : 𝒳',
        ∃ R ∈ J (p𝒳'.obj x'),
          ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒳'.obj x'),
            R u → ∃ (x : 𝒳) (φ : i.obj x ⟶ x'), p𝒳'.IsStronglyCartesian u φ)
    (hmor𝒴 :
      haveI : p𝒴.IsFibered := h𝒴.isFibered
      haveI : p𝒴'.IsFibered := h𝒴'.isFibered
      ∀ (U : 𝒞) (y₁ y₂ : p𝒴.Fiber U),
        Presheaf.IsLocallyInjective (J.over U)
            ((h𝒴'.isFibredOneMorphism hj).morPresheafMap y₁ y₂) ∧
          Presheaf.IsLocallySurjective (J.over U)
            ((h𝒴'.isFibredOneMorphism hj).morPresheafMap y₁ y₂))
    (_hobj𝒴 :
      ∀ y' : 𝒴',
        ∃ R ∈ J (p𝒴'.obj y'),
          ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒴'.obj y'),
            R u → ∃ (y : 𝒴) (φ : j.obj y ⟶ y'), p𝒴'.IsStronglyCartesian u φ)
    (hmor𝒵 :
      haveI : p𝒵.IsFibered := h𝒵.isFibered
      haveI : p𝒵'.IsFibered := h𝒵'.isFibered
      ∀ (U : 𝒞) (z₁ z₂ : p𝒵.Fiber U),
        Presheaf.IsLocallyInjective (J.over U)
            ((h𝒵'.isFibredOneMorphism hk).morPresheafMap z₁ z₂) ∧
          Presheaf.IsLocallySurjective (J.over U)
            ((h𝒵'.isFibredOneMorphism hk).morPresheafMap z₁ z₂))
    (hobj𝒵 :
      ∀ z' : 𝒵',
        ∃ R ∈ J (p𝒵'.obj z'),
          ∀ ⦃V : 𝒞⦄ (u : V ⟶ p𝒵'.obj z'),
            R u → ∃ (z : 𝒵) (φ : k.obj z ⟶ z'), p𝒵'.IsStronglyCartesian u φ)
    (α : i ⋙ f' ≅ f ⋙ j) (hα : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (α.hom.app x))
    (β : k ⋙ g' ≅ g ⋙ j) (hβ : ∀ z : 𝒵, p𝒴'.IsHomLift (𝟙 (p𝒵.obj z)) (β.hom.app z))
    {H : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g ⥤ TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g'}
    (γ : H ⋙ fst p𝒳' p𝒵' p𝒴' f' g' ≅ fst p𝒳 p𝒵 p𝒴 f g ⋙ i)
    (hγ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒳'.IsHomLift (𝟙 P.base) (γ.hom.app P))
    (δ : H ⋙ snd p𝒳' p𝒵' p𝒴' f' g' ≅ snd p𝒳 p𝒵 p𝒴 f g ⋙ k)
    (hδ : ∀ P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g, p𝒵'.IsHomLift (𝟙 P.base) (δ.hom.app P))
    (hψ :
      Functor.whiskerLeft H (psi p𝒳' p𝒵' p𝒴' f' g') ≫ Functor.whiskerRight δ.hom g' =
        Functor.whiskerRight γ.hom f' ≫
          Functor.whiskerLeft (fst p𝒳 p𝒵 p𝒴 f g) α.hom ≫
          Functor.whiskerRight (psi p𝒳 p𝒵 p𝒴 f g) j ≫
          Functor.whiskerLeft (snd p𝒳 p𝒵 p𝒴 f g) β.inv) :
    haveI : (structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered :=
      (isFiberedInGroupoids p𝒳 p𝒵 p𝒴 f g h𝒳 h𝒵 h𝒴 hf hg).isFibered
    haveI : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered :=
      (isFiberedInGroupoids p𝒳' p𝒵' p𝒴' f' g' h𝒳' h𝒵' h𝒴' hf' hg').isFibered
    (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStack J ∧
      ∃ hH :
        Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
          (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H,
        (∀ (U : 𝒞) (P Q : (structureFunctor p𝒳 p𝒵 p𝒴 f g).Fiber U),
            Presheaf.IsLocallyInjective (J.over U) (hH.morPresheafMap P Q) ∧
              Presheaf.IsLocallySurjective (J.over U) (hH.morPresheafMap P Q)) ∧
          ∀ P' : TwoFibreProductOver p𝒳' p𝒵' p𝒴' f' g',
            ∃ R ∈ J P'.base,
              ∀ ⦃V : 𝒞⦄ (u : V ⟶ P'.base),
                R u →
                  ∃ (P : TwoFibreProductOver p𝒳 p𝒵 p𝒴 f g) (φ : H.obj P ⟶ P'),
                    (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsStronglyCartesian u φ := by
  have := h𝒳.isFibered
  have := h𝒴.isFibered
  have := h𝒵.isFibered
  have := h𝒳'.isFibered
  have := h𝒴'.isFibered
  have := h𝒵'.isFibered
  have hfib : (structureFunctor p𝒳 p𝒵 p𝒴 f g).IsFibered :=
    (isFiberedInGroupoids p𝒳 p𝒵 p𝒴 f g h𝒳 h𝒵 h𝒴 hf hg).isFibered
  have hfib' : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFibered :=
    (isFiberedInGroupoids p𝒳' p𝒵' p𝒴' f' g' h𝒳' h𝒵' h𝒴' hf' hg').isFibered
  have hq' : (structureFunctor p𝒳' p𝒵' p𝒴' f' g').IsFiberedInGroupoids :=
    isFiberedInGroupoids p𝒳' p𝒵' p𝒴' f' g' h𝒳' h𝒵' h𝒴' hf' hg'
  have hcomp : H ⋙ structureFunctor p𝒳' p𝒵' p𝒴' f' g' = structureFunctor p𝒳 p𝒵 p𝒴 f g :=
    comp_eq_of_gamma hi γ hγ
  have hHmor :
    Functor.IsFibredOneMorphism (structureFunctor p𝒳 p𝒵 p𝒴 f g)
      (structureFunctor p𝒳' p𝒵' p𝒴' f' g') H :=
    Functor.IsFiberedInGroupoids.isFibredOneMorphism hq' hcomp
  refine
    ⟨isStack_structureFunctor p𝒳' p𝒵' p𝒴' f' g' J hs𝒳' hs𝒵' hs𝒴' (h𝒴'.isFibredOneMorphism hf')
        (h𝒴'.isFibredOneMorphism hg'),
      hHmor, ?_, ?_⟩
  · refine fun U P Q =>
      ⟨isLocallyInjective_morPresheafMap (h𝒴.isFibredOneMorphism hf) (h𝒴.isFibredOneMorphism hg) J
          (h𝒳'.isFibredOneMorphism hi) (h𝒵'.isFibredOneMorphism hk) γ δ hHmor
          (fun U x y => (hmor𝒳 U x y).1) (fun U z w => (hmor𝒵 U z w).1) P Q,
        ?_⟩
    exact
      isLocallySurjective_morPresheafMap (h𝒴.isFibredOneMorphism hf) (h𝒴.isFibredOneMorphism hg)
        (h𝒴'.isFibredOneMorphism hf') (h𝒴'.isFibredOneMorphism hg') (h𝒳'.isFibredOneMorphism hi)
        (h𝒵'.isFibredOneMorphism hk) hHmor γ hγ δ hδ J α β (h𝒴'.isFibredOneMorphism hj) hψ
        (fun V x y => (hmor𝒳 V x y).2) (fun V z w => (hmor𝒵 V z w).2)
        (fun V y w => (hmor𝒴 V y w).1) P Q
  · exact
      objClause (h𝒴.isFibredOneMorphism hf) (h𝒴.isFibredOneMorphism hg)
        (h𝒳'.isFibredOneMorphism hi) (h𝒵'.isFibredOneMorphism hk) γ hγ δ hδ J h𝒴 h𝒴' hq'
        (h𝒴'.isFibredOneMorphism hf') (h𝒴'.isFibredOneMorphism hg') (h𝒴'.isFibredOneMorphism hj) α
        hα β hβ hψ hobj𝒳 hobj𝒵 (fun V y w => (hmor𝒴 V y w).2)

end CategoryTheory.TwoFibreProductOver

end
