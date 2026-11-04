module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistCocycle
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn

/-!
# The cocycle for Tag 01NO's twist comparison, transposed across the adjunction

The third assertion of Stacks Tag 01MZ says that the comparison maps on the twists compose,
`θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`. For the restriction maps of a quasi-coherent graded algebra the
comparison in question is
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, and the equation is the one
hypothesis of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_comp_of` — the single input the
nested cocycle of Tag 01NR, and hence the twist `𝒪(1)` of Tag 01VM, was conditional on. It is
discharged in `StacksFrontier/AlgebraicGeometry/ProjTwistCocycle/Pointwise.lean`; see "What is not
done here" below for what this file contributes and what that one adds.

That equation is between morphisms **out of an inverse image**, and the inverse image of sheaves
of modules is a left adjoint produced by a choice principle: reading the equation
on sections factor by factor exceeds the kernel's deterministic budget, as recorded in
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistSectionOn.lean` and in
`StacksFrontier/AlgebraicGeometry/ProjInclusionTwist/Basic.lean`. This file takes the route those
files identify as the affordable one: transpose the equation across the
pullback--pushforward adjunction, where no inverse image occurs at all.

## Main definitions

* `…ProjTwistCocycle.legTranspose`: **the transpose of a two-leg composite** — a congruence, the
  pseudofunctoriality isomorphism of a composite, the inverse image of one morphism and a second
  morphism — as a morphism into a pushforward. Every composite appearing below has this shape.
* `…ProjTwistCocycle.twistTranspose`: the transpose of a six-factor comparison of Tag 01NO's
  shape, which is `legTranspose` with the trivialisation of the open domain as its second leg.
* `…ProjTwistCocycle.legComposite`: **the composite of two morphisms into pushforwards** along a
  factorisation — the first, the pushforward of the second, and the congruence of pushforwards.
  This is the shape of the transposed cocycle.
* `…ProjTwistCocycle.twistTrivialisation`: **the trivialisation of the open domain, read from the
  restriction** — a morphism from the restriction of the twist to the open domain to its
  pushforward along the section. Source and target are both concrete.

## Main results

* `…ProjTwistCocycle.hom_ext_of_transpose`: two morphisms out of an inverse image are equal as
  soon as their transposes are, `CategoryTheory.Adjunction.homEquiv` being a bijection.
* `…ProjTwistCocycle.transpose_legComp`: **the transpose of a two-leg composite is
  `legTranspose`**, at the level of variables.
* `…ProjTwistCocycle.transpose_projInclusionTwistIso`: **the transpose of Tag 01NO's twist
  isomorphism.** The instance of the previous item at
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, which is where the six
  factors disappear.
* `…ProjTwistCocycle.legTranspose_eq_legComposite`: `legTranspose` written as `legComposite` of
  the two legs' own transposes, which is the form in which the two legs of the cocycle are
  recognised as transposes of twist isomorphisms.
* `…ProjTwistCocycle.transpose_cocycle_lhs`: **the left-hand side of Tag 01MZ's third assertion
  transposes to the composite of the two transposes.**
* `…ProjTwistCocycle.transpose_twistTail`: **the transpose of the trivialisation of the open
  domain** — factors four, five and six of Tag 01NO's comparison — is the congruence isomorphism
  of pushforwards and nothing else.
* `…ProjTwistCocycle.twistTrivialisation_app_preimage`: **the trivialisation on sections**, at an
  open of the form `ι ⁻¹ᵁ W`: it is the congruence isomorphism of pushforwards, hence a presheaf
  restriction map.
* `…ProjTwistCocycle.preimage_eq_image`: a section of an open immersion inverts it on opens —
  `p ⁻¹ᵁ T = ι ''ᵁ T` — which is the identification of opens the trivialisation transports along.
* `…ProjTwistCocycle.transpose_congrTail` and `transpose_twistTail'`: **the transpose of the
  trivialisation of the open domain is the congruence isomorphism of pushforwards**, with no
  isomorphism cancelled anywhere.
* `…ProjTwistCocycle.restrictUnit_comp_map_twistTrivialisation` and its primed form: **the
  trivialisation is inverse to the unit of the restriction adjunction**, which is a presheaf
  restriction map. This is the statement that pins the trivialisation down without mentioning an
  inverse image; the primed form has the congruence on the other side, so that both factors on
  the left are restriction maps.
* `…ProjTwistCocycle.twistTranspose_eq`: **the transpose of Tag 01NO's comparison is
  `legComposite` of Tag 01MY's adjoint comparison `twistPushforwardMap` with the
  trivialisation** — both of them concrete, and neither mentioning an inverse image.
* `…ProjTwistCocycle.isCocycle_of_transpose`: **Tag 01MZ's third assertion follows from the
  transposed equation** `θ̃_{W'U} ≫ ψ_*θ̃_{WW'} = θ̃_{WU}`, in which no inverse image occurs. This
  is the equation `…ChartTransRelativeProj.pushNested_comp_of` asks for, reduced to a statement
  about morphisms into pushforwards only.

## The route, and why it is this one

Write `g` for the transition morphism of `W ⊆ U`, and `φ`, `ψ` for those of `W ⊆ W'` and
`W' ⊆ U`, so that `φ ≫ ψ = g` is Tag 01NP's transitivity. Transposing a morphism
`g^*𝒪_U(n) ⟶ 𝒪_W(n)` means composing the unit of the adjunction of `g` with the pushforward of
it, and the four factors of the cocycle's left-hand side then transpose one at a time by the four
morphism-level statements of
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistSectionOn.lean`: the leading congruence by
`…PullbackUnit.unit_comp_map_pullbackCongr_inv`, the pseudofunctoriality isomorphism by
`…PullbackUnit.unit_comp_map_pullbackComp_inv` together with
`CategoryTheory.Adjunction.comp_unit_app`, the inverse image of a morphism by naturality of the
unit, and the last factor by nothing at all. The result is `legTranspose`.

Applied to the six factors of `projInclusionTwistIso` — whose fourth, fifth and sixth factors are
the trivialisation of the open domain, and so form the second leg — the same statement computes
the transpose of Tag 01NO's comparison. Applied to the cocycle's left-hand side, whose legs are
the two twist isomorphisms themselves, it computes that side as the composite of the two
transposes. So the cocycle becomes an equation between morphisms into pushforwards of the twists,
and that is `isCocycle_of_transpose`.

## Implementation notes

Three elaboration facts shape the file, each the difference between seconds and a kernel timeout.

* **The transposed equation is written with `legTranspose`, a named definition, and has to be.**
  Spelling its right-hand side out at the instance makes the kernel convert
  `(p ≫ q)_* N` against `q_*(p_* N)` with `p` and `q` the concrete transition morphisms of the
  relative `Proj`; the two are definitionally equal, and at the level of variables the conversion
  is free, but at the instance it exceeds the kernel's deterministic timeout.
  With the right-hand side named, the instance checks in about fifteen seconds; written out, it
  does not check at all. The same conversion is what makes
  `CategoryTheory.Adjunction.comp_unit_app` usable only inside the general lemma.
* **No step is a `calc` step.** The two sides of the intermediate equations live in hom-types that
  are definitionally equal and not syntactically equal — `(p ≫ q)_*` against `q_* ∘ p_*` again —
  and `calc` requires a `Trans` instance, whose synthesis compares those types as they stand and
  fails. `Eq.trans`, which unifies at default transparency, accepts them. So every chain below is
  a `refine Eq.trans … ?_`.
* **The conversion between `(p ≫ ι)_*` and `ι_*p_*` is crossed in a statement and never inside a
  proof.** It is `…PushforwardCocycle.pushforward_comp_map`, and at the level of variables it is
  `rfl` in seconds; but *every* way of crossing it inside a proof — cancelling the congruence
  isomorphism, reassociating across it, or rewriting with `Category.comp_id` at a composite whose
  two halves are spelled on opposite sides of it — reaches the elaborator's `isDefEq` or `whnf`
  timeout, even with every argument supplied explicitly. That is why
  `transpose_twistTail'` is proved from `transpose_cocycle` at `γ := p ≫ ι` with `hγ := rfl`,
  where the congruence of pushforwards is the identity and nothing needs cancelling, rather than
  from `transpose_twistTail` by cancelling it.
* **`CategoryTheory.Functor.map_comp` is applied with its arguments explicit** at the one step
  where the functor has to be read as `q_* ∘ p_*` rather than as `(p ≫ q)_*`: with the arguments
  left to unification the elaborator cannot see the second spelling inside the first, and reports
  a mismatch rather than unfolding.

Congruence for a composite is `CategoryTheory.whisker_eq` and
`CategoryTheory.eq_whisker`, never `rw`: the untouched factor is read off the goal rather than
inferred from the equation.

## What is not done here

**The transposed equation itself is a hypothesis of this file.** `isCocycle_of_transpose` reduces
Tag 01MZ's third assertion to it and does not prove it; no project tag is attached below. It is
proved in `StacksFrontier/AlgebraicGeometry/ProjTwistCocycle/Pointwise.lean`, as
`…ProjTwistCocycle.transposed_cocycle`, and the chain it closes —
`…ChartTransRelativeProj.IsNestedCocycle A n` in every integer degree — is carried to the end
there.

Of the three identifications of opens that stood between the transposed equation and the
pointwise cocycle, two are discharged here. The comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is absorbed into
`twistTrivialisation` by `twistTranspose_eq`, and the trivialisation of the open domain is pinned
by `restrictUnit_comp_map_twistTrivialisation`, whose other factor is a presheaf restriction map.
The third is the one lemma this file leaves open: for an arbitrary open `T` of the open domain,

`(twistTrivialisation p ι hpi N).app T = N.presheaf.map (eqToHom (preimage_eq_image …)).op`

— the trivialisation is the restriction along the equality of opens `p ⁻¹ᵁ T = ι ''ᵁ T` and
nothing else. `twistTrivialisation_app_preimage` is that statement at the opens of the form
`ι ⁻¹ᵁ W`, and every open is of that form, `T` being `ι ⁻¹ᵁ (ι ''ᵁ T)`, but only
propositionally. **That transport is now performed**, in
`StacksFrontier/AlgebraicGeometry/ProjTwistCocycle/Trivialisation.lean`, as
`…ProjTwistCocycle.twistTrivialisation_app`: not by rewriting — the motive is dependent and the
equation's right-hand side is the variable its left-hand side mentions — but by naturality of the
trivialisation at `eqToHom (ι.preimage_image_eq T)`, the restriction this introduces on the source
being inverse to the one the unit of the restriction adjunction already is, by `Subsingleton.elim`
on the hom-sets of `Opens`.

With it the transposed cocycle is a pointwise statement in which every factor of every
`twistTranspose` is a restriction map, hence acts on the underlying family of homogeneous
fractions by reindexing and on its values by `rfl`; the content is then
`Stacks.AlgebraicGeometry.TwistBaseChange.fibreMap_comp`, the fibre comparison of a composite of
graded maps being the composite of the fibre comparisons, with the three points matched by reading
`…ChartTransRelativeProj.projInclusionMap_comp'` on `AlgebraicGeometry.Scheme.Hom.base`. Tag
01MY's adjoint comparison is pointwise the fibre comparison by
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`, which is `rfl`, and the
congruence of pushforwards is a restriction by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app`, which is also `rfl`. That is
exactly the route `Pointwise.lean` takes.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.PushforwardCocycle
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ProjTwistCocycle

universe u

/-! ### Transposing a two-leg composite, at the level of variables -/

section General

variable {X Z Y : Scheme.{u}}

/-- **Two morphisms out of an inverse image are equal as soon as their transposes are.** The
transpose is `CategoryTheory.Adjunction.homEquiv`, which is a bijection; this is the statement in
the form in which the unit is visible, so that the four morphism-level identities of
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/TwistSectionOn.lean` apply to it. -/
public theorem hom_ext_of_transpose {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N : D} {a b : F.obj M ⟶ N}
    (hab : adj.unit.app M ≫ G.map a = adj.unit.app M ≫ G.map b) : a = b := by
  refine (adj.homEquiv M N).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact hab

variable (φ : X ⟶ Z) (ψ : Z ⟶ Y) (g : X ⟶ Y) (hg : φ ≫ ψ = g)
  (M : Y.Modules) (P : Z.Modules) (N : X.Modules)
  (a : (Scheme.Modules.pullback ψ).obj M ⟶ P)
  (b : (Scheme.Modules.pullback φ).obj P ⟶ N)

/-- **The composite of two morphisms into pushforwards**, along a factorisation `φ ≫ ψ = g`: the
first, the pushforward of the second, and the congruence identifying `ψ_*φ_*` with `g_*`.

Named, rather than written out at the point of use: the junction between `ψ_*(φ_*N)` and `g_*N` is
a conversion the kernel performs for free at the level of variables and cannot afford at the
transition morphisms of a relative `Proj`. See the implementation notes. -/
public def legComposite (s : M ⟶ (Scheme.Modules.pushforward ψ).obj P)
    (t : P ⟶ (Scheme.Modules.pushforward φ).obj N) :
    M ⟶ (Scheme.Modules.pushforward g).obj N :=
  (s ≫ (Scheme.Modules.pushforward ψ).map t) ≫
    (Scheme.Modules.pushforwardCongr hg).hom.app N

/-- **The transpose of a two-leg composite.** For a factorisation `φ ≫ ψ = g` and two morphisms
`a : ψ^*M ⟶ P` and `b : φ^*P ⟶ N`, this is `legComposite` of the two legs' own adjoint
transposes. By `transpose_legComp` it is the transpose across the adjunction of `g` of the
composite of the congruence for the factorisation, the pseudofunctoriality isomorphism of the
composite, the inverse image of `a` along `φ`, and `b`. -/
public def legTranspose : M ⟶ (Scheme.Modules.pushforward g).obj N :=
  legComposite φ ψ g hg M P N (transpose ψ M a) (transpose φ P b)

/-- `legTranspose` is `legComposite` of the two legs' own transposes, by definition. -/
public theorem legTranspose_eq_legComposite :
    legTranspose φ ψ g hg M P N a b =
      legComposite φ ψ g hg M P N (transpose ψ M a) (transpose φ P b) :=
  rfl

/-- **`legComposite` absorbs a factorisation of its first argument.** A first leg presented as a
morphism followed by the pushforward of a further morphism may have that further morphism moved
into the second leg. This is how the adjoint form of Tag 01MY's comparison is separated from the
identification of restriction with pullback that follows it. -/
public theorem legComposite_comp_map (R : Z.Modules)
    (s : M ⟶ (Scheme.Modules.pushforward ψ).obj R) (u : R ⟶ P)
    (t : P ⟶ (Scheme.Modules.pushforward φ).obj N) :
    legComposite φ ψ g hg M P N (s ≫ (Scheme.Modules.pushforward ψ).map u) t =
      legComposite φ ψ g hg M R N s (u ≫ t) := by
  rw [legComposite, legComposite, Functor.map_comp, Category.assoc]

/-- **`legComposite` on sections**: the first leg, then the second leg over the inverse image of
the open, then the congruence of pushforwards. Definitionally so, at the level of variables, which
is where the junction between `ψ_*φ_*` and `g_*` is affordable. -/
public theorem legComposite_app (s : M ⟶ (Scheme.Modules.pushforward ψ).obj P)
    (t : P ⟶ (Scheme.Modules.pushforward φ).obj N) (T : Y.Opens) :
    (legComposite φ ψ g hg M P N s t).app T =
      (s.app T ≫ t.app (ψ ⁻¹ᵁ T)) ≫
        ((Scheme.Modules.pushforwardCongr hg).hom.app N).app T :=
  rfl

/-- **The transpose of a two-leg composite is `legTranspose`.** This is
`…PushforwardCocycle.transpose_cocycle` with its cocycle hypothesis discharged by `rfl`, so that
the two-leg composite names itself; the only work is the one reassociation separating that
statement's right-hand side from `legComposite`. -/
public theorem transpose_legComp :
    transpose g M ((Scheme.Modules.pullbackCongr hg).inv.app M ≫
        (Scheme.Modules.pullbackComp φ ψ).inv.app M ≫
        (Scheme.Modules.pullback φ).map a ≫ b) =
      legTranspose φ ψ g hg M P N a b :=
  (transpose_cocycle φ ψ g hg M P N a b _ rfl).symm.trans (Category.assoc _ _ _).symm

/-- **The cocycle from the transposed cocycle**, at the level of variables: the converse of
`…PushforwardCocycle.transpose_cocycle`, which is the direction Tag 01MZ's third assertion needs.
Both are available because the transpose is a bijection. -/
public theorem cocycle_of_transpose_cocycle (c : (Scheme.Modules.pullback g).obj M ⟶ N)
    (htr : legTranspose φ ψ g hg M P N a b = transpose g M c) :
    (Scheme.Modules.pullbackCongr hg).inv.app M ≫
        (Scheme.Modules.pullbackComp φ ψ).inv.app M ≫
        (Scheme.Modules.pullback φ).map a ≫ b = c :=
  hom_ext_of_transpose (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((transpose_legComp φ ψ g hg M P N a b).trans htr)

end General

/-! ### The transpose of Tag 01NO's twist isomorphism -/

section Twist

variable {X D Y : Scheme.{u}} (p : X ⟶ D) (q : D ⟶ Y) (ι : D ⟶ X) (g : X ⟶ Y)
  (hg : p ≫ q = g) (hpi : p ≫ ι = 𝟙 X) (M : Y.Modules) (N : X.Modules)
  (θ : (Scheme.Modules.pullback q).obj M ⟶ (Scheme.Modules.pullback ι).obj N)

/-- **The transpose of a six-factor comparison of Tag 01NO's shape**: `legTranspose` whose second
leg is the trivialisation of the open domain, namely the pseudofunctoriality isomorphism of
`p ≫ ι`, the congruence for `p ≫ ι = 𝟙` and the inverse image along the identity. -/
public def twistTranspose : M ⟶ (Scheme.Modules.pushforward g).obj N :=
  legTranspose p q g hg M ((Scheme.Modules.pullback ι).obj N) N θ
    ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
      (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
      (Scheme.Modules.pullbackId X).hom.app N)

/-- **The transpose of a six-factor comparison is `twistTranspose`.** -/
public theorem transpose_sixFold :
    transpose g M
        ((Scheme.Modules.pullbackCongr hg).inv.app M ≫
          (Scheme.Modules.pullbackComp p q).inv.app M ≫
          (Scheme.Modules.pullback p).map θ ≫
          (Scheme.Modules.pullbackComp p ι).hom.app N ≫
          (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
          (Scheme.Modules.pullbackId X).hom.app N) =
      twistTranspose p q ι g hg hpi M N θ :=
  transpose_legComp p q g hg M ((Scheme.Modules.pullback ι).obj N) N θ
    ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
      (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
      (Scheme.Modules.pullbackId X).hom.app N)

/-- Inverting the pseudofunctoriality isomorphism of `p ≫ ι` cancels against its forward map, past
the inverse image of an identity. -/
private theorem comp_inv_map_id_comp_hom_comp {Z : X.Modules}
    (r : (Scheme.Modules.pullback (p ≫ ι)).obj N ⟶ Z) :
    (Scheme.Modules.pullbackComp p ι).inv.app N ≫
        (Scheme.Modules.pullback p).map (𝟙 ((Scheme.Modules.pullback ι).obj N)) ≫
        (Scheme.Modules.pullbackComp p ι).hom.app N ≫ r = r := by
  refine Eq.trans (whisker_eq _ ((eq_whisker (CategoryTheory.Functor.map_id _ _) _).trans
    (Category.id_comp _))) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((eq_whisker (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp p ι) N) _).trans
      (Category.id_comp _))

/-- **The transpose of the trivialisation of the open domain is the identity**, once the
congruence of pushforwards along `p ≫ ι = 𝟙` has been applied.

The trivialisation — the fourth, fifth and sixth factors of Tag 01NO's comparison — is the second
leg of `twistTranspose`, and this is the statement that computes it: its transpose along `ι` is
the congruence isomorphism of pushforwards and nothing else. It is `transpose_cocycle` at
`α := p`, `β := ι`, `γ := 𝟙`, where the pseudofunctoriality isomorphism of `p ≫ ι` cancels
against the fourth factor, the congruence against the fifth, and the pullback along the identity
is `…PullbackUnit.unit_comp_map_pullbackId_hom`. -/
public theorem transpose_twistTail :
    transpose ι N (𝟙 ((Scheme.Modules.pullback ι).obj N)) ≫
        (Scheme.Modules.pushforward ι).map
          (transpose p ((Scheme.Modules.pullback ι).obj N)
            ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
              (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
              (Scheme.Modules.pullbackId X).hom.app N)) ≫
        (Scheme.Modules.pushforwardCongr hpi).hom.app N = 𝟙 N := by
  have hcongr : (Scheme.Modules.pullbackCongr hpi).inv.app N ≫
        ((Scheme.Modules.pullbackCongr hpi).hom.app N ≫
          (Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app N :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (Iso.inv_hom_id_app (Scheme.Modules.pullbackCongr hpi) N) _).trans
        (Category.id_comp _))
  refine Eq.trans (transpose_cocycle p ι (𝟙 X) hpi N ((Scheme.Modules.pullback ι).obj N) N
    (𝟙 ((Scheme.Modules.pullback ι).obj N))
    ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
      (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
      (Scheme.Modules.pullbackId X).hom.app N)
    ((Scheme.Modules.pullbackId X).hom.app N)
    ((whisker_eq _ (comp_inv_map_id_comp_hom_comp p ι N _)).trans hcongr)) ?_
  exact unit_comp_map_pullbackId_hom X N

/-- **The transpose of the congruence and the pullback along the identity.** Factors five and six
of Tag 01NO's comparison, transposed along `p ≫ ι`, are the congruence isomorphism of pushforwards
along `p ≫ ι = 𝟙`.

Every term in the chain is spelled through `(p ≫ ι)_*`, and that is what makes it affordable: the
conversion between `(p ≫ ι)_*` and `ι_*p_*` is paid once, in the statement of
`transpose_twistTail'`, and never inside a proof. See the implementation notes. -/
public theorem transpose_congrTail :
    transpose (p ≫ ι) N
        ((Scheme.Modules.pullbackCongr hpi).hom.app N ≫
          (Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pushforwardCongr hpi).inv.app N := by
  have hid : (Adjunction.id (C := X.Modules)).unit.app N =
      𝟙 ((Scheme.Modules.pushforward (𝟙 X)).obj N) := rfl
  rw [transpose]
  refine Eq.trans (whisker_eq _ (Functor.map_comp _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (unit_comp_map_pullbackCongr_hom hpi N) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (((Scheme.Modules.pushforwardCongr hpi).inv.naturality _).symm)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (unit_comp_map_pullbackId_hom X N) _) ?_
  refine Eq.trans (eq_whisker hid _) ?_
  exact Category.id_comp ((Scheme.Modules.pushforwardCongr hpi).inv.app N)

/-- **The transpose of the trivialisation of the open domain is the congruence isomorphism of
pushforwards.** The clean form of `transpose_twistTail`: no isomorphism has to be cancelled,
because `transpose_cocycle` is applied at `γ := p ≫ ι` with `hγ := rfl`, where the congruence of
pushforwards is the identity by `…PushforwardCocycle.pushforwardCongr_refl_hom_app`. -/
public theorem transpose_twistTail' :
    transpose ι N (𝟙 ((Scheme.Modules.pullback ι).obj N)) ≫
        (Scheme.Modules.pushforward ι).map
          (transpose p ((Scheme.Modules.pullback ι).obj N)
            ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
              (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
              (Scheme.Modules.pullbackId X).hom.app N)) =
      (Scheme.Modules.pushforwardCongr hpi).inv.app N := by
  have hrefl : (Scheme.Modules.pullbackCongr (rfl : p ≫ ι = p ≫ ι)).inv.app N =
      𝟙 ((Scheme.Modules.pullback (p ≫ ι)).obj N) := rfl
  have hcoc : (Scheme.Modules.pullbackCongr (rfl : p ≫ ι = p ≫ ι)).inv.app N ≫
        (Scheme.Modules.pullbackComp p ι).inv.app N ≫
        (Scheme.Modules.pullback p).map (𝟙 ((Scheme.Modules.pullback ι).obj N)) ≫
        ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
          (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
          (Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
        (Scheme.Modules.pullbackId X).hom.app N :=
    (eq_whisker hrefl _).trans ((Category.id_comp _).trans
      (comp_inv_map_id_comp_hom_comp p ι N _))
  have hstep := transpose_cocycle p ι (p ≫ ι) rfl N ((Scheme.Modules.pullback ι).obj N) N
    (𝟙 ((Scheme.Modules.pullback ι).obj N))
    ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
      (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
      (Scheme.Modules.pullbackId X).hom.app N)
    ((Scheme.Modules.pullbackCongr hpi).hom.app N ≫
      (Scheme.Modules.pullbackId X).hom.app N) hcoc
  rw [pushforwardCongr_refl_hom_app] at hstep
  have hci : (Scheme.Modules.pushforward ι).map
        (transpose p ((Scheme.Modules.pullback ι).obj N)
          ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
            (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
            (Scheme.Modules.pullbackId X).hom.app N)) ≫
      𝟙 ((Scheme.Modules.pushforward (p ≫ ι)).obj N) =
      (Scheme.Modules.pushforward ι).map
        (transpose p ((Scheme.Modules.pullback ι).obj N)
          ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
            (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
            (Scheme.Modules.pullbackId X).hom.app N)) :=
    Category.comp_id _
  exact ((whisker_eq
    (transpose ι N (𝟙 ((Scheme.Modules.pullback ι).obj N))) hci).symm.trans hstep).trans
    (transpose_congrTail p ι hpi N)

/-! ### The trivialisation of the open domain, as a morphism of restrictions -/

section Trivialisation

variable [IsOpenImmersion ι]

include hpi in
/-- **A section of an open immersion inverts it on opens.** If `p ≫ ι = 𝟙` with `ι` an open
immersion, then the inverse image along `p` of an open of the domain is its image under `ι`.

This is the identification of opens that `twistTrivialisation` transports along: its source has,
over an open `T`, the sections of `N` over `ι ''ᵁ T`, and its target those over `p ⁻¹ᵁ T`. -/
public theorem preimage_eq_image (T : D.Opens) : p ⁻¹ᵁ T = ι ''ᵁ T := by
  have h1 : p ⁻¹ᵁ T = (p ≫ ι) ⁻¹ᵁ (ι ''ᵁ T) := by
    rw [Scheme.Hom.comp_preimage, ι.preimage_image_eq]
  rw [h1, hpi]
  simp

include hg hpi in
/-- **The inverse image along the composite is the image of the inverse image.** `p ⁻¹ᵁ` being
`ι ''ᵁ` by `preimage_eq_image`, the open over which `twistTranspose` delivers its sections is the
image under `ι` of the inverse image along `q`. -/
public theorem preimage_eq_image_comp (T : Y.Opens) : g ⁻¹ᵁ T = ι ''ᵁ (q ⁻¹ᵁ T) := by
  rw [← hg, Scheme.Hom.comp_preimage]
  exact preimage_eq_image p ι hpi _

/-- **The trivialisation of the open domain, read from the restriction.** The identification of
restriction with pullback followed by the transpose of the trivialisation: a morphism from the
restriction of `N` to `D` to the pushforward of `N` along the section `p`.

Both source and target are concrete — the restriction of `N` has, over an open of `D`, exactly the
sections of `N` over its image, and the pushforward along `p` those over its inverse image — so
this is the form in which the last three factors of Tag 01NO's comparison can be read on
sections. -/
public def twistTrivialisation :
    (Scheme.Modules.restrictFunctor ι).obj N ⟶ (Scheme.Modules.pushforward p).obj N :=
  (Scheme.Modules.restrictFunctorIsoPullback ι).hom.app N ≫
    transpose p ((Scheme.Modules.pullback ι).obj N)
      ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
        (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
        (Scheme.Modules.pullbackId X).hom.app N)

/-- The trivialisation composed with the unit of the restriction adjunction is the congruence
isomorphism of pushforwards. -/
private theorem restrictUnit_comp_map_twistTrivialisation_eq :
    (Scheme.Modules.restrictAdjunction ι).unit.app N ≫
        (Scheme.Modules.pushforward ι).map (twistTrivialisation p ι hpi N) =
      (Scheme.Modules.pushforwardCongr hpi).inv.app N := by
  have htid : transpose ι N (𝟙 ((Scheme.Modules.pullback ι).obj N)) =
      (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N := by
    rw [transpose, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  refine Eq.trans (whisker_eq _ (Functor.map_comp (Scheme.Modules.pushforward ι)
    ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app N)
    (transpose p ((Scheme.Modules.pullback ι).obj N)
      ((Scheme.Modules.pullbackComp p ι).hom.app N ≫
        (Scheme.Modules.pullbackCongr hpi).hom.app N ≫
        (Scheme.Modules.pullbackId X).hom.app N)))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback ι N) _) ?_
  refine Eq.trans (eq_whisker htid.symm _) ?_
  exact transpose_twistTail' p ι hpi N

/-- **The trivialisation is inverse to the unit of the restriction adjunction**, up to the
congruence of pushforwards along `p ≫ ι = 𝟙`.

This is the statement that pins `twistTrivialisation` down, and it mentions no inverse image: the
unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is a presheaf restriction map by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`. It is `transpose_twistTail`
with the identification of restriction with pullback traded for that unit by
`Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`. -/
public theorem restrictUnit_comp_map_twistTrivialisation :
    (Scheme.Modules.restrictAdjunction ι).unit.app N ≫
        (Scheme.Modules.pushforward ι).map (twistTrivialisation p ι hpi N) ≫
        (Scheme.Modules.pushforwardCongr hpi).hom.app N = 𝟙 N :=
  (Category.assoc _ _ _).symm.trans
    ((eq_whisker (restrictUnit_comp_map_twistTrivialisation_eq p ι hpi N) _).trans
      (Iso.inv_hom_id_app _ _))

/-- **The trivialisation composed with the unit of the restriction adjunction is the congruence
isomorphism of pushforwards.** The form of `restrictUnit_comp_map_twistTrivialisation` with the
congruence on the other side, which is the one that can be read on sections: both factors on the
left are then presheaf restriction maps. -/
public theorem restrictUnit_comp_map_twistTrivialisation' :
    (Scheme.Modules.restrictAdjunction ι).unit.app N ≫
        (Scheme.Modules.pushforward ι).map (twistTrivialisation p ι hpi N) =
      (Scheme.Modules.pushforwardCongr hpi).inv.app N :=
  restrictUnit_comp_map_twistTrivialisation_eq p ι hpi N

/-- **The trivialisation on sections, at an open of the form `ι ⁻¹ᵁ W`.** Precomposed with the
restriction that the unit of the restriction adjunction is, the trivialisation is the congruence
isomorphism of pushforwards read on sections — and that, by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr_inv_app_app`, is a presheaf restriction map.

So the trivialisation involves no inverse image and no transpose: it is a restriction along an
equality of opens. Every open of the open domain is of the form `ι ⁻¹ᵁ W`, namely
`T = ι ⁻¹ᵁ (ι ''ᵁ T)`; see "What is not done" for the transport that remains. -/
public theorem twistTrivialisation_app_preimage (W : X.Opens) :
    N.presheaf.map (homOfLE (ι.image_preimage_le W)).op ≫
        (twistTrivialisation p ι hpi N).app (ι ⁻¹ᵁ W) =
      ((Scheme.Modules.pushforwardCongr hpi).inv.app N).app W := by
  have h := congrArg
    (fun φ : N ⟶ (Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pushforward p).obj N) =>
      Scheme.Modules.Hom.app φ W)
    (restrictUnit_comp_map_twistTrivialisation' p ι hpi N)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforward_map_app] at h
  exact h

end Trivialisation

end Twist

/-! ### The transpose of Tag 01NO's comparison, through Tag 01MY's adjoint form -/

section TwistAdjoint

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂] [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The transpose of a six-factor comparison built from Tag 01MY's twist map, through the
adjoint form of that twist map.**

For a homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings whose open domain admits a
section `p` of its inclusion, the transpose of Tag 01NO's comparison is `legComposite` of
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap` — the adjoint form of `θ`, which
is given pointwise by the fibre comparison — with the trivialisation `twistTrivialisation`. Both
factors are concrete, and no inverse image of a sheaf of modules occurs in either.

The identification of restriction with pullback, which stands between the two in
`Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap`, is absorbed into the
trivialisation by `legComposite_comp_map`. -/
public theorem twistTranspose_eq (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (p : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ ψ).toScheme)
    (g : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜)
    (hg : p ≫ mapHom 𝒜 ℬ ψ = g)
    (hpi : p ≫ (mapDomain 𝒜 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ)) :
    twistTranspose p (mapHom 𝒜 ℬ ψ) (mapDomain 𝒜 ℬ ψ).ι g hg hpi
        (twistingSheaf 𝒜 n) (twistingSheaf ℬ n) (twistMap 𝒜 ℬ ψ n) =
      legComposite p (mapHom 𝒜 ℬ ψ) g hg (twistingSheaf 𝒜 n)
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))
        (twistingSheaf ℬ n) (twistPushforwardMap 𝒜 ℬ ψ n)
        (twistTrivialisation p (mapDomain 𝒜 ℬ ψ).ι hpi (twistingSheaf ℬ n)) := by
  refine Eq.trans (congrArg (fun z => legComposite p (mapHom 𝒜 ℬ ψ) g hg (twistingSheaf 𝒜 n)
      ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) (twistingSheaf ℬ n)
      z (transpose p ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))
        ((Scheme.Modules.pullbackComp p (mapDomain 𝒜 ℬ ψ).ι).hom.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackCongr hpi).hom.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app (twistingSheaf ℬ n))))
      (unit_comp_map_twistMap 𝒜 ℬ ψ n)) ?_
  exact legComposite_comp_map p (mapHom 𝒜 ℬ ψ) g hg (twistingSheaf 𝒜 n)
    ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) (twistingSheaf ℬ n)
    ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))
    (twistPushforwardMap 𝒜 ℬ ψ n)
    ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app (twistingSheaf ℬ n))
    (transpose p ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))
      ((Scheme.Modules.pullbackComp p (mapDomain 𝒜 ℬ ψ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hpi).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app (twistingSheaf ℬ n)))

end TwistAdjoint

/-! ### The instance: the transition morphisms of a relative projective spectrum -/

section Instance

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (hUV : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ)

/-- **The transpose of Tag 01NO's twist isomorphism.** For an inclusion `U ⊆ V` of affine opens of
the base, the transpose across the pullback--pushforward adjunction of the canonical isomorphism
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso` is `twistTranspose` at Tag
01MY's twist map; in particular it mentions no inverse image of a morphism of sheaves of modules.

This is where the six factors of the comparison disappear: they are matched against
`transpose_sixFold` through
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq`. -/
public theorem transpose_projInclusionTwistIso :
    transpose (projInclusionMap A U V hUV hU hV) (twistingSheaf (A.grading V) n)
        (ProjInclusionTwist.projInclusionTwistIso A U V hUV hU hV n).hom =
      twistTranspose (projInclusionTopSection A U V hUV hU hV)
        (projMapData (A.grading V) (A.grading U) (A.res hUV)).hom
        (mapDomain (A.grading V) (A.grading U) (A.res hUV)).ι
        (projInclusionMap A U V hUV hU hV) (projInclusionMap_eq_comp A U V hUV hU hV)
        (projInclusionTopSection_ι A U V hUV hU hV)
        (twistingSheaf (A.grading V) n) (twistingSheaf (A.grading U) n)
        ((projMapData (A.grading V) (A.grading U) (A.res hUV)).twistMap n) :=
  Eq.trans
    (congrArg (fun w => transpose (projInclusionMap A U V hUV hU hV)
        (twistingSheaf (A.grading V) n) w)
      ((ProjInclusionTwist.projInclusionTwistIso_hom A U V hUV hU hV n).trans
        (ProjInclusionTwist.projInclusionTwistMap_eq A U V hUV hU hV n)))
    (transpose_sixFold (projInclusionTopSection A U V hUV hU hV)
      (projMapData (A.grading V) (A.grading U) (A.res hUV)).hom
      (mapDomain (A.grading V) (A.grading U) (A.res hUV)).ι
      (projInclusionMap A U V hUV hU hV) (projInclusionMap_eq_comp A U V hUV hU hV)
      (projInclusionTopSection_ι A U V hUV hU hV)
      (twistingSheaf (A.grading V) n) (twistingSheaf (A.grading U) n)
      ((projMapData (A.grading V) (A.grading U) (A.res hUV)).twistMap n))

end Instance

/-! ### The cocycle from the transposed cocycle -/

section Cocycle

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (n : ℤ) (W W' U : S.Opens)
  (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W')
  (hU : IsAffineOpen U)

/-- The transpose of the left-hand side of Tag 01MZ's third assertion: the composite of the two
twist isomorphisms transposes to the composite of their transposes. -/
public theorem transpose_cocycle_lhs :
    transpose (projInclusionMap A W U hWU hW hU) (twistingSheaf (A.grading U) n)
          ((Scheme.Modules.pullbackCongr
              (ChartTransRelativeProj.projInclusionMap_comp'
                A W W' U hWW' hW'U hWU hW hW' hU)).inv.app
            (twistingSheaf (A.grading U) n) ≫
            (Scheme.Modules.pullbackComp (projInclusionMap A W W' hWW' hW hW')
                (projInclusionMap A W' U hW'U hW' hU)).inv.app
              (twistingSheaf (A.grading U) n) ≫
            (Scheme.Modules.pullback (projInclusionMap A W W' hWW' hW hW')).map
              (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom ≫
            (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom) =
      legComposite (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (ChartTransRelativeProj.projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
        (twistingSheaf (A.grading W) n)
        (twistTranspose (projInclusionTopSection A W' U hW'U hW' hU)
          (projMapData (A.grading U) (A.grading W') (A.res hW'U)).hom
          (mapDomain (A.grading U) (A.grading W') (A.res hW'U)).ι
          (projInclusionMap A W' U hW'U hW' hU)
          (projInclusionMap_eq_comp A W' U hW'U hW' hU)
          (projInclusionTopSection_ι A W' U hW'U hW' hU)
          (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
          ((projMapData (A.grading U) (A.grading W') (A.res hW'U)).twistMap n))
        (twistTranspose (projInclusionTopSection A W W' hWW' hW hW')
          (projMapData (A.grading W') (A.grading W) (A.res hWW')).hom
          (mapDomain (A.grading W') (A.grading W) (A.res hWW')).ι
          (projInclusionMap A W W' hWW' hW hW')
          (projInclusionMap_eq_comp A W W' hWW' hW hW')
          (projInclusionTopSection_ι A W W' hWW' hW hW')
          (twistingSheaf (A.grading W') n) (twistingSheaf (A.grading W) n)
          ((projMapData (A.grading W') (A.grading W) (A.res hWW')).twistMap n)) := by
  refine Eq.trans (transpose_legComp (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (ChartTransRelativeProj.projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)
    (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
    (twistingSheaf (A.grading W) n)
    (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom
    (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom) ?_
  refine Eq.trans (legTranspose_eq_legComposite _ _ _ _ _ _ _ _ _) ?_
  rw [transpose_projInclusionTwistIso A W' U hW'U hW' hU n,
    transpose_projInclusionTwistIso A W W' hWW' hW hW' n]

/-- **Stacks Tag 01MZ's third assertion for the restriction maps of a quasi-coherent graded
algebra, reduced to the transposed equation.** Given that the transposes of Tag 01NO's twist
isomorphisms compose — an equation between morphisms into pushforwards of the twists, in which no
inverse image of a sheaf of modules occurs — the twist isomorphisms themselves compose.

The conclusion is verbatim the hypothesis of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_comp_of`. -/
public theorem isCocycle_of_transpose
    (htr : legComposite (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (ChartTransRelativeProj.projInclusionMap_comp' A W W' U hWW' hW'U hWU hW hW' hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
        (twistingSheaf (A.grading W) n)
        (twistTranspose (projInclusionTopSection A W' U hW'U hW' hU)
          (projMapData (A.grading U) (A.grading W') (A.res hW'U)).hom
          (mapDomain (A.grading U) (A.grading W') (A.res hW'U)).ι
          (projInclusionMap A W' U hW'U hW' hU)
          (projInclusionMap_eq_comp A W' U hW'U hW' hU)
          (projInclusionTopSection_ι A W' U hW'U hW' hU)
          (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W') n)
          ((projMapData (A.grading U) (A.grading W') (A.res hW'U)).twistMap n))
        (twistTranspose (projInclusionTopSection A W W' hWW' hW hW')
          (projMapData (A.grading W') (A.grading W) (A.res hWW')).hom
          (mapDomain (A.grading W') (A.grading W) (A.res hWW')).ι
          (projInclusionMap A W W' hWW' hW hW')
          (projInclusionMap_eq_comp A W W' hWW' hW hW')
          (projInclusionTopSection_ι A W W' hWW' hW hW')
          (twistingSheaf (A.grading W') n) (twistingSheaf (A.grading W) n)
          ((projMapData (A.grading W') (A.grading W) (A.res hWW')).twistMap n)) =
      twistTranspose (projInclusionTopSection A W U hWU hW hU)
        (projMapData (A.grading U) (A.grading W) (A.res hWU)).hom
        (mapDomain (A.grading U) (A.grading W) (A.res hWU)).ι
        (projInclusionMap A W U hWU hW hU) (projInclusionMap_eq_comp A W U hWU hW hU)
        (projInclusionTopSection_ι A W U hWU hW hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading W) n)
        ((projMapData (A.grading U) (A.grading W) (A.res hWU)).twistMap n)) :
    (Scheme.Modules.pullbackCongr
            (ChartTransRelativeProj.projInclusionMap_comp'
              A W W' U hWW' hW'U hWU hW hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullbackComp (projInclusionMap A W W' hWW' hW hW')
            (projInclusionMap A W' U hW'U hW' hU)).inv.app
          (twistingSheaf (A.grading U) n) ≫
        (Scheme.Modules.pullback (projInclusionMap A W W' hWW' hW hW')).map
          (ProjInclusionTwist.projInclusionTwistIso A W' U hW'U hW' hU n).hom ≫
        (ProjInclusionTwist.projInclusionTwistIso A W W' hWW' hW hW' n).hom =
      (ProjInclusionTwist.projInclusionTwistIso A W U hWU hW hU n).hom :=
  hom_ext_of_transpose
    (Scheme.Modules.pullbackPushforwardAdjunction (projInclusionMap A W U hWU hW hU))
    ((transpose_cocycle_lhs A n W W' U hWW' hW'U hWU hW hW' hU).trans
      (htr.trans (transpose_projInclusionTwistIso A W U hWU hW hU n).symm))

end Cocycle

end Stacks.AlgebraicGeometry.ProjTwistCocycle

end
