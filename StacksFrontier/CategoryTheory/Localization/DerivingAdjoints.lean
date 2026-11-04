module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Monoidal.Mon
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Deriving adjoints

Let `F : 𝒟 ⥤ 𝒟'` be right adjoint to `G : 𝒟' ⥤ 𝒟`, let `S`, resp. `S'`, be a class of morphisms
of `𝒟`, resp. `𝒟'`, and let `Q : 𝒟 ⥤ S⁻¹𝒟`, `Q' : 𝒟' ⥤ (S')⁻¹𝒟'` be localization functors.
Write `RF` for the partially defined right derived functor of `Q' ∘ F` with respect to `S`, and
`LG` for the partially defined left derived functor of `Q ∘ G` with respect to `S'`. Thus `RF` is
defined at an object `K` of `𝒟` when the ind-object
$$ (s : K \to I) \longmapsto Q'(F(I)), \qquad s \in S, $$
of `(S')⁻¹𝒟'` is essentially constant, its value being `RF(K)`, and dually `LG` is defined at an
object `M` of `𝒟'` when the pro-object `(t : P ⟶ M) ↦ Q(G(P))`, `t ∈ S'`, of `S⁻¹𝒟` is
essentially constant with value `LG(M)`.

This file proves that the derived functors of an adjoint pair are adjoint, in three forms.

*Pointwise.* If `RF` is defined at `K` and `LG` is defined at `M`, then the adjunction between
`F` and `G` descends to a bijection
$$ \operatorname{Hom}_{(S')^{-1}\mathcal{D}'}(M, RF(K)) =
   \operatorname{Hom}_{S^{-1}\mathcal{D}}(LG(M), K), $$
and this bijection is the unique one compatible with the fractions computing the two sides: a
morphism `M ⟶ RF(K)` of `(S')⁻¹𝒟'` is `Q'(t)⁻¹ ≫ Q'(f) ≫ (coprojection at s)` for an index
`s : K ⟶ I` of the ind-object, an index `t : P ⟶ M` of the pro-object and a morphism
`f : P ⟶ F(I)` of `𝒟'`, and it corresponds to `(projection at t) ≫ Q(f^♯) ≫ Q(s)⁻¹`, where
`f^♯ : G(P) ⟶ I` is the morphism adjoint to `f`.

*Pointwise, between derived categories of abelian categories.* For `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒜`
functors of abelian categories with `F` right adjoint to `G`, the induced functors
`K(F) : K(𝒜) ⥤ K(ℬ)` and `K(G) : K(ℬ) ⥤ K(𝒜)` of the unbounded homotopy categories have
partially defined derived functors `RF` and `LG` with respect to the quasi-isomorphisms, and the
same bijection
$$ \operatorname{Hom}_{D(\mathcal{B})}(M, RF(K)) =
   \operatorname{Hom}_{D(\mathcal{A})}(LG(M), K) $$
holds. Here the numerator `f : P ⟶ F(I)` of a fraction is a chain map and the morphism
corresponding to it on the other side is its degreewise transpose `g : G(P) ⟶ I`, that is
`f.f n = adj.homEquiv _ _ (g.f n)` for every `n`.

*Globally.* If `RF` and `LG` are defined at *every* object, so that they are functors
`RF : S⁻¹𝒟 ⥤ (S')⁻¹𝒟'` and `LG : (S')⁻¹𝒟' ⥤ S⁻¹𝒟` equipped with the canonical maps
`β : Q'(F(K)) ⟶ RF(Q(K))` and `α : LG(Q'(M)) ⟶ Q(G(M))`, then `RF` is right adjoint to `LG`, by
the adjunction which is compatible with `β`, `α` and the given adjunction between `F` and `G`.

## Main results

* `CategoryTheory.Adjunction.existsUnique_homEquiv_of_isRightDerivedValueAt`: the pointwise
  bijection, together with its characterisation by the fractions, [Stacks 0FND].
* `CategoryTheory.Adjunction.existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt`: the
  same bijection between derived categories of abelian categories, with the two numerators
  degreewise adjoint chain maps, [Stacks 0DVC].
* `CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`:
  the derived adjunction `LG ⊣ RF`, [Stacks 09T5].

## Implementation notes

*Plain categories rather than triangulated ones.* The source states the pointwise result in the
situation of [Stacks, Tag 0FNC]: `F` and `G` exact functors of triangulated categories and `S`,
`S'` multiplicative systems compatible with the triangulated structures. Neither the statement nor
the source's proof uses the triangulated structure or exactness: the proof is the calculus of
fractions (which describes the two sides as colimits over the index categories), the interchange
of two filtered colimits, essential constancy (Tags 05PY and 05PZ, which is what makes `Hom`
commute with the colimit computing the value) and adjointness. So the statement is made for
arbitrary categories `𝒟`, `𝒟'` and morphism properties `S`, `S'`; specializing to the source's
situation — where `S` and `S'` are multiplicative systems by Tag 05R4 — recovers the source's
lemma. Of the two halves of the calculus of fractions, `S` is used through its *left* fractions
(`Hom_{S⁻¹𝒟}(G(P), K) = colim_{s : K → I} Hom_𝒟(G(P), I)`) and `S'` through its *right* fractions
(`Hom_{(S')⁻¹𝒟'}(M, F(I)) = colim_{t : P → M} Hom_{𝒟'}(P, F(I))`), so only those two hypotheses
are imposed; the localizations `Q`, `Q'` are arbitrary localization functors, not the canonical
construction. The same generality is used for the global statement, which the source states for
the total derived functors `RF : D(𝒜) ⥤ D(ℬ)`, `LG : D(ℬ) ⥤ D(𝒜)` of functors of abelian
categories: specializing to `𝒟 = K(𝒜)`, `𝒟' = K(ℬ)` with `S`, `S'` the quasi-isomorphisms
recovers it.

*Definedness is the source's essential constancy, not the existence of a Kan extension.* Being
defined at `K` is `CategoryTheory.Functor.IsRightDerivedValueAt` of [Stacks, Tag 05S9], the
source's notion, with the cocone carrying the value as a parameter rather than existentially
quantified, so that the value `RF(K) = c.pt` can be named in the conclusion, together with the
coprojections `c.ι.app s : F(I) ⟶ RF(K)` and the projections `d.π.app t : LG(M) ⟶ G(P)` that the
characterisation uses. Mathlib's `Functor.HasPointwiseRightDerivedFunctorAt` — the mere existence
of the colimit computing the value — is strictly weaker, and it is not enough here: what the proof
uses is that `Hom` out of the value commutes with that colimit, which holds because an essentially
constant ind-object exhibits its value as a retract of one of the terms, and fails for a colimit
that is not absolute. In the two pointwise statements neither derived functor is assumed to be
defined everywhere, so no functor `RF` or `LG` on the localized categories is available, and none
is assumed: only the two values are.

*The left derived value by duality.* Tag 05S9 records the left derived value in the pro-object
form, as a cone. The pointwise statement over arbitrary categories takes it in the equivalent
dual form `(G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d`, whose index category
`S'.op.Under ⊤ (op M)` is the source's category of morphisms `t : P ⟶ M` in `S'`, whose diagram
is `t ↦ op (Q(G(P)))`, and whose value is `LG(M) = d.pt.unop`; the projections of the source's
pro-object are the `(d.ι.app t).unop : LG(M) ⟶ Q(G(P))`. The two other statements use the
pro-object form directly. The two index categories are exchanged by the mutually inverse
assignments `t ↦ op t` on objects and morphisms (`opUnderOfOver` and `overOfOpUnder`, inverse to
each other by definition), and a cone is carried to a cocone by taking opposites
(`opCoconeOfCone`); essential constancy is preserved because its two clauses are exchanged by the
same assignments.

*The refinement condition of the pointwise proof.* No filtered colimit is formed. The equality of
the fibres of the two representation relations is proved by refining two triples `(s, t, f)` to a
common pair of indices, which is possible because `S` admits left fractions and `S'` right
fractions, and then observing that for a fixed pair of indices `(s, t)` and morphisms
`g, g' : P ⟶ F(I)` both conditions are equivalent to the single condition
$$ p ≫ g ≫ F(w) = p ≫ g' ≫ F(w) $$
for some `w : I ⟶ I₁` under `K` with `s ≫ w ∈ S` and some `p : P₁ ⟶ P` over `M` with
`p ≫ t ∈ S'`. On the ind-object side, essential constancy is what produces such a `w` — this is
the one place where the value being a retract of a term of the diagram is used — and the calculus
of right fractions produces the `p`; on the pro-object side the roles are exchanged. The two
conditions are literally the same equation once `f ↦ f^♯` is applied, and that is where
adjointness enters. This refinement condition is not given a name: it occurs as the conclusion of
`exists_refinement_of_ind` and `exists_refinement_of_pro` and as the hypothesis of
`ind_of_refinement` and `pro_of_refinement`, and naming it would amount to naming a type of
refinement data whose only role is to be existentially quantified in those four statements.

*The derived-category situation.* The source's `D(𝒜)` and `D(ℬ)` are `DerivedCategory 𝒜` and
`DerivedCategory ℬ`, localizations of the unbounded homotopy categories at the quasi-isomorphisms
through `DerivedCategory.Qh`, and `RF`, resp. `LG`, is the partially defined derived functor of
`K(F) ⋙ Qh`, resp. `K(G) ⋙ Qh`, with respect to `HomotopyCategory.quasiIso` — the situation of
Tags 05S8 and 0FNC. The objects `K` and `M` are taken in the homotopy categories rather than in
the categories of cochain complexes: objects of `K(𝒜)` *are* complexes of `𝒜`, and a cochain
complex `K` is used as `(HomotopyCategory.quotient 𝒜 _).obj K`.

*The induced adjunctions.* An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` whose unit and counit are the given ones
in each degree, and hence, by passing to the quotients by homotopy, an adjunction
`G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c`. Neither is in Mathlib; both are proved here
(`mapHomologicalComplexAdjunction` and `mapHomotopyCategoryAdjunction`), together with the two
facts about them that the specialization uses: the transpose of a chain map is its degreewise
transpose, and the transpose of the class of a chain map is the class of its transpose.

*Adjointness of the fractions' numerators, degreewise.* The morphism `f` of the fraction on the
`D(ℬ)` side is a homotopy class, and its transpose `g` across the induced adjunction
`K(G) ⊣ K(F)` is what the `D(𝒜)` side needs. So the two are quantified over as *chain maps*
`f : P ⟶ F(I)` and `g : G(P) ⟶ I` between the complexes underlying the indices, related by `adj`
in each degree: `f.f n = adj.homEquiv _ _ (g.f n)`. This loses nothing: every homotopy class is
represented by a chain map, and a chain map `f` has a unique degreewise transpose `g` (the
differentials commute with it by naturality of `adj`), so every morphism `ψ : M ⟶ RF(K)` of `D(ℬ)`
is covered by the characterisation — which is what makes it determine the bijection uniquely,
hence the `∃!`.

*Additivity of `F` and `G`.* Neither is an extra hypothesis in the derived-category statement:
both follow from the adjunction alone. Being a left adjoint between abelian categories, `G`
preserves the initial object and binary coproducts, hence is additive
(`CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_object` and
`CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`), and then `F` is additive by
`CategoryTheory.Adjunction.right_adjoint_additive`. They are nevertheless taken as instance
arguments, because the induced functors `K(F)` and `K(G)` on the homotopy categories cannot be
written down without them.

*A bijection, as in the source.* The source writes an equality of `Hom`-sets, and what is
asserted here is a bijection; no additivity of the bijection is claimed, although both `Hom`s are
abelian groups.

*Functoriality.* The source's assertion that the isomorphism is functorial in both variables on
the subcategories where `RF` and `LG` are defined is the compatibility of these bijections with
the ind- and pro-structures, and that compatibility, for every index `s`, every index `t` and
every (adjoint pair of) morphism(s) between them, is exactly what is asserted here; it is also
what determines the bijection uniquely, which is why the pointwise conclusions are `∃!`. Stating
functoriality as the naturality of a natural transformation would require the morphisms `RF(s)`,
`LG(t)` between values of Tag 05SA, which are not available while the derived functors are only
partially defined; the source omits the proof of functoriality.

*Existence of `RF` is everywhere-definedness together with the functor it produces.* For the
global statement, the source's "`RF : D(𝒜) ⥤ D(ℬ)` exists" is: `RF` is defined at every object in
the sense of Tag 05S9 (Tag 05SV), whence a functor on the localization together with the canonical
transformation `F ⋙ Q' ⟶ Q ⋙ RF` (Tag 05SW, via Proposition 05SE). Since the passage from
everywhere-definedness to that functor is a separate result, the functor and its structure map are
taken here as data — `RF` with `β : F ⋙ Q' ⟶ Q ⋙ RF`, and `LG` with `α : Q' ⋙ LG ⟶ G ⋙ Q`, the
transformations Mathlib uses for derived functors — and the hypotheses say that they compute the
derived values: for every `K` the ind-object is essentially constant with value `RF(Q(K))`, the
coprojection at `s : K ⟶ I` being `β_I` followed by the inverse of `RF(Q(s))`, which is the
equation `c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right` written without inverses;
dually for `LG`. Essential constancy is transported along the isomorphism `e`, so the hypotheses
say exactly that these two prescribed cocone and cone are values in the sense of Tag 05S9.

*Why Mathlib's `Adjunction.derived` does not cover the global statement.* Mathlib derives an
adjunction `LG ⊣ RF` from `LG` and `RF` being derived functors in the sense of Kan extensions,
under the additional hypothesis that they are *absolute*, i.e. that `LG ⋙ RF` and `RF ⋙ LG`
remain derived functors of the composites. The source assumes no such thing: a derived value in
Deligne's sense is a retract of a term of the diagram, hence an absolute colimit, and that is what
makes the `Hom` computation of the pointwise statement work. Accordingly the hypotheses here are
the source's, and no Kan extension property is assumed; that a value in Deligne's sense is a
*pointwise* Kan extension — the value is a retract of a term of the ind-object, resp. pro-object,
so the (co)limit computing the Kan extension is achieved by that retract, the calculus of
fractions being what reduces an arbitrary index of the (co)structured-arrow category to an index
of the ind-, resp. pro-object — is proved here, and the same argument applied to the diagrams
composed with a functor supplies absoluteness.

*The two pointwise Kan extension statements are proved separately* rather than one being deduced
from the other by passing to opposite categories: the pro-object form of a left derived value
(Tag 05S9(2)) is a cone on a diagram indexed by `S'.Over ⊤ M`, and relating it to a cocone indexed
by `S'.op.Under ⊤ (op M)` costs more than the mirrored argument. An index `t : P ⟶ M` of the
pro-object is turned into an index of the limit computing the right Kan extension, that is an
object of `StructuredArrow (Q'(M)) Q'`, by inverting `Q'(t)`; this is `structuredArrowOfOver`, and
`structuredArrowHomMk` is the resulting comparison of indices. The calculus of right fractions
enters exactly once, to produce for an arbitrary index of `StructuredArrow (Q'(M)) Q'` an index of
the pro-object mapping to it. Dually for the colimit, with `costructuredArrowOfUnder` and
`costructuredArrowHomMk`.

*The derived adjunction is pinned by its unit and counit.* The two compatibilities in the
conclusion of the global statement are Mathlib's `Adjunction.derived'` conditions: the unit of the
derived adjunction restricted along `Q'` is `Q'(unit)` followed by `β`, and the counit restricted
along `Q` is `α` followed by `Q(counit)`. Together with the derived-functor property they
determine the adjunction; only their existence is asserted, since the uniqueness argument is the
universal property that the source proves separately.

## References

* [Stacks, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks, Tag 0DVC](https://stacks.math.columbia.edu/tag/0DVC)
* [Stacks, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

/-! ### The derived adjunction at an object -/

section PointwiseGeneral

open Limits Opposite MorphismProperty

section

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {SD : Type u₃} [Category.{v₃} SD] {SD' : Type u₄} [Category.{v₄} SD']
  {F : D ⥤ D'} {G : D' ⥤ D}
  {S : MorphismProperty D} {S' : MorphismProperty D'}
  {Q : D ⥤ SD} {Q' : D' ⥤ SD'}
  {K : D} {M : D'}

/-- A cocone on the ind-object at `K` computing the right derived functor of `Q' ∘ F`. -/
private abbrev IndCocone (F : D ⥤ D') (Q' : D' ⥤ SD') (S : MorphismProperty D) (K : D) :=
  Cocone (MorphismProperty.Under.forget S ⊤ K ⋙ CategoryTheory.Under.forget K ⋙ F ⋙ Q')

/-- A cocone on the opposite of the pro-object at `M` computing the left derived functor
of `Q ∘ G`. -/
private abbrev ProCocone (G : D' ⥤ D) (Q : D ⥤ SD) (S' : MorphismProperty D') (M : D') :=
  Cocone (MorphismProperty.Under.forget S'.op ⊤ (Opposite.op M) ⋙
    CategoryTheory.Under.forget (Opposite.op M) ⋙ (G ⋙ Q).op)

/-- The coprojection of the ind-object at the index `s`, with its source written
as `Q'(F(s.right))`. -/
private abbrev coprj (c : IndCocone F Q' S K) (s : S.Under ⊤ K) :
    Q'.obj (F.obj s.right) ⟶ c.pt := c.ι.app s

/-- The projection of the pro-object at the index `t`, with its target written
as `Q(G(t.right.unop))`. -/
private abbrev proj (d : ProCocone G Q S' M) (t : S'.op.Under ⊤ (Opposite.op M)) :
    d.pt.unop ⟶ Q.obj (G.obj t.right.unop) := (d.ι.app t).unop

/-- A morphism of indices of the pro-object, written in `𝒟` rather than in `𝒟ᵒᵖ`. -/
private lemma unop_right_comp_hom {t t' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t') :
    p.right.unop ≫ t.hom.unop = t'.hom.unop :=
  congrArg Quiver.Hom.unop (MorphismProperty.Under.w p)

section Loc

variable [Q.IsLocalization S] [Q'.IsLocalization S']

/-- A morphism of indices of the ind-object at `K` becomes invertible in the localization. -/
private lemma isIso_map_right_of_under {s s' : S.Under ⊤ K} (w : s ⟶ s') :
    IsIso (Q.map w.right) := by
  have : IsIso (Q.map s'.hom) := Localization.inverts Q S _ s'.prop
  have : IsIso (Q.map s.hom) := Localization.inverts Q S _ s.prop
  exact IsIso.of_isIso_fac_left (f := Q.map s.hom) (h := Q.map s'.hom)
    (by rw [← Q.map_comp, MorphismProperty.Under.w w])

/-- A morphism of indices of the pro-object at `M` becomes invertible in the localization. -/
private lemma isIso_map_unop_right_of_under {t t' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t') :
    IsIso (Q'.map p.right.unop) := by
  have : IsIso (Q'.map t'.hom.unop) := Localization.inverts Q' S' _ t'.prop
  have : IsIso (Q'.map t.hom.unop) := Localization.inverts Q' S' _ t.prop
  exact IsIso.of_isIso_fac_right (f := Q'.map t.hom.unop) (h := Q'.map t'.hom.unop)
    (by rw [← Q'.map_comp, unop_right_comp_hom p])

end Loc

/-- Compatibility of the projections of the pro-object with its transition morphisms, written in
`𝒟` rather than in `𝒟ᵒᵖ`. -/
private lemma proj_comp_map (d : ProCocone G Q S' M)
    {t t' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t') :
    proj d t' ≫ Q.map (G.map p.right.unop) = proj d t :=
  congrArg Quiver.Hom.unop (d.w p)

/-- `proj_comp_map`, reassociated. -/
private lemma proj_comp_map_assoc (d : ProCocone G Q S' M) {t t' : S'.op.Under ⊤ (Opposite.op M)}
    (p : t ⟶ t') {X : SD} (z : Q.obj (G.obj t.right.unop) ⟶ X) :
    proj d t' ≫ Q.map (G.map p.right.unop) ≫ z = proj d t ≫ z := by
  rw [← Category.assoc, proj_comp_map d p]

section Fractions

variable [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]

/-- Any two indices of the ind-object at `K` admit a common target: `K/S` is filtered. -/
private lemma nonempty_under_common (s s' : S.Under ⊤ K) :
    ∃ s'' : S.Under ⊤ K, Nonempty (s ⟶ s'') ∧ Nonempty (s' ⟶ s'') := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk s.hom s.prop s'.hom).exists_leftFraction
  exact ⟨MorphismProperty.Under.mk ⊤ (s'.hom ≫ ψ.s) (S.comp_mem _ _ s'.prop ψ.hs),
    ⟨MorphismProperty.Under.homMk ψ.f hψ.symm⟩, ⟨MorphismProperty.Under.homMk ψ.s rfl⟩⟩

/-- Any two indices of the pro-object at `M` admit a common target: `S'/M` is cofiltered. -/
private lemma nonempty_op_under_common (t t' : S'.op.Under ⊤ (Opposite.op M)) :
    ∃ t'' : S'.op.Under ⊤ (Opposite.op M), Nonempty (t ⟶ t'') ∧ Nonempty (t' ⟶ t'') := by
  obtain ⟨φ, hφ⟩ :=
    (MorphismProperty.LeftFraction.mk t.hom.unop t'.hom.unop t'.prop).exists_rightFraction
  exact ⟨MorphismProperty.Under.mk ⊤ (φ.s ≫ t.hom.unop).op (S'.comp_mem _ _ φ.hs t.prop),
    ⟨MorphismProperty.Under.homMk φ.s.op rfl⟩,
    ⟨MorphismProperty.Under.homMk φ.f.op (Quiver.Hom.unop_inj hφ.symm)⟩⟩

end Fractions

/-- Refining the pair of indices does not change the morphism `ψ` represented. -/
private lemma ind_refine (c : IndCocone F Q' S K)
    {s s'' : S.Under ⊤ K} (w : s ⟶ s'') {t t'' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t'')
    {f : t.right.unop ⟶ F.obj s.right} {ψ : Q'.obj M ⟶ c.pt}
    (h : Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ coprj c s) :
    Q'.map t''.hom.unop ≫ ψ
      = Q'.map (p.right.unop ≫ f ≫ F.map w.right) ≫ coprj c s'' := by
  have hcw : Q'.map (F.map w.right) ≫ coprj c s'' = coprj c s := c.w w
  rw [← unop_right_comp_hom p]
  simp only [Q'.map_comp, Category.assoc, hcw, h]

/-- The transpose of a composite `p ≫ f ≫ F.map w`. -/
private lemma homEquiv_symm_comp_comp_map (adj : G ⊣ F) {P P' : D'} {I I' : D} (p : P' ⟶ P)
    (f : P ⟶ F.obj I) (w : I ⟶ I') :
    (adj.homEquiv _ _).symm (p ≫ f ≫ F.map w) = G.map p ≫ (adj.homEquiv _ _).symm f ≫ w := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]

/-- Refining the pair of indices does not change the morphism `χ` represented. -/
private lemma pro_refine (adj : G ⊣ F) (d : ProCocone G Q S' M)
    {s s'' : S.Under ⊤ K} (w : s ⟶ s'') {t t'' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t'')
    {f : t.right.unop ⟶ F.obj s.right} {χ : d.pt.unop ⟶ Q.obj K}
    (h : χ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f)) :
    χ ≫ Q.map s''.hom = proj d t'' ≫
      Q.map ((adj.homEquiv _ _).symm (p.right.unop ≫ f ≫ F.map w.right)) := by
  rw [homEquiv_symm_comp_comp_map, ← MorphismProperty.Under.w w]
  simp only [Q.map_comp]
  rw [proj_comp_map_assoc, ← Category.assoc, h, Category.assoc]

/-- From an equality on the ind-object side, a refinement of the indices equalizing the two
morphisms already in `𝒟'`. This is the one step that uses essential constancy of the
ind-object. -/
private lemma exists_refinement_of_ind [Q'.IsLocalization S']
    [S'.HasRightCalculusOfFractions] (c : IndCocone F Q' S K)
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (g g' : t.right.unop ⟶ F.obj s.right)
    (h : Q'.map g ≫ coprj c s = Q'.map g' ≫ coprj c s) :
    ∃ (s'' : S.Under ⊤ K) (w : s ⟶ s'') (t'' : S'.op.Under ⊤ (Opposite.op M)) (p : t ⟶ t''),
      p.right.unop ≫ g ≫ F.map w.right = p.right.unop ≫ g' ≫ F.map w.right := by
  obtain ⟨s₀, r, -, hb⟩ := hc
  obtain ⟨s'', u, v, huv⟩ := hb s
  have h1 : Q'.map (F.map u.right) = coprj c s ≫ r ≫ Q'.map (F.map v.right) := huv
  have hQ : Q'.map (g ≫ F.map u.right) = Q'.map (g' ≫ F.map u.right) := by
    simp only [Q'.map_comp, h1, ← Category.assoc, h]
  obtain ⟨X, p, hp, hpe⟩ := (MorphismProperty.map_eq_iff_precomp Q' S' _ _).1 hQ
  exact ⟨s'', u, MorphismProperty.Under.mk ⊤ (p ≫ t.hom.unop).op (S'.comp_mem _ _ hp t.prop),
    MorphismProperty.Under.homMk p.op rfl, hpe⟩

/-- Conversely, a refinement of the indices equalizing the two morphisms in `𝒟'` gives an
equality on the ind-object side. -/
private lemma ind_of_refinement [Q'.IsLocalization S'] (c : IndCocone F Q' S K)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (g g' : t.right.unop ⟶ F.obj s.right)
    {s'' : S.Under ⊤ K} (w : s ⟶ s'') {t'' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t'')
    (h : p.right.unop ≫ g ≫ F.map w.right = p.right.unop ≫ g' ≫ F.map w.right) :
    Q'.map g ≫ coprj c s = Q'.map g' ≫ coprj c s := by
  have : IsIso (Q'.map p.right.unop) := isIso_map_unop_right_of_under p
  have h2 : Q'.map g ≫ Q'.map (F.map w.right) = Q'.map g' ≫ Q'.map (F.map w.right) := by
    have h3 := congrArg Q'.map h
    simp only [Q'.map_comp] at h3
    exact (cancel_epi (Q'.map p.right.unop)).1 h3
  have hcw : Q'.map (F.map w.right) ≫ coprj c s'' = coprj c s := c.w w
  rw [← hcw, ← Category.assoc, h2, Category.assoc]

/-- From an equality on the pro-object side, a refinement of the indices equalizing the two
morphisms already in `𝒟'`. This is the one step that uses essential constancy of the
pro-object. -/
private lemma exists_refinement_of_pro [Q.IsLocalization S] [S.HasLeftCalculusOfFractions]
    (adj : G ⊣ F) (d : ProCocone G Q S' M)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (Opposite.op M) d)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (g g' : t.right.unop ⟶ F.obj s.right)
    (h : proj d t ≫ Q.map ((adj.homEquiv _ _).symm g)
      = proj d t ≫ Q.map ((adj.homEquiv _ _).symm g')) :
    ∃ (s'' : S.Under ⊤ K) (w : s ⟶ s'') (t'' : S'.op.Under ⊤ (Opposite.op M)) (p : t ⟶ t''),
      p.right.unop ≫ g ≫ F.map w.right = p.right.unop ≫ g' ≫ F.map w.right := by
  obtain ⟨t₀, r, -, hb⟩ := hd
  obtain ⟨t'', u, v, huv⟩ := hb t
  have huv' : Q.map (G.map u.right.unop)
      = (Q.map (G.map v.right.unop) ≫ r.unop) ≫ proj d t :=
    congrArg Quiver.Hom.unop huv
  have hQ : Q.map (G.map u.right.unop ≫ (adj.homEquiv _ _).symm g)
      = Q.map (G.map u.right.unop ≫ (adj.homEquiv _ _).symm g') := by
    simp only [Q.map_comp, huv', Category.assoc, h]
  obtain ⟨Z, w, hw, hwe⟩ := (MorphismProperty.map_eq_iff_postcomp Q S _ _).1 hQ
  refine ⟨MorphismProperty.Under.mk ⊤ (s.hom ≫ w) (S.comp_mem _ _ s.prop hw),
    MorphismProperty.Under.homMk w rfl, t'', u, ?_⟩
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_comp_comp_map, homEquiv_symm_comp_comp_map]
  simp only [← Category.assoc]
  exact hwe

/-- Conversely, a refinement of the indices equalizing the two morphisms in `𝒟'` gives an
equality on the pro-object side. -/
private lemma pro_of_refinement [Q.IsLocalization S] (adj : G ⊣ F) (d : ProCocone G Q S' M)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (g g' : t.right.unop ⟶ F.obj s.right)
    {s'' : S.Under ⊤ K} (w : s ⟶ s'') {t'' : S'.op.Under ⊤ (Opposite.op M)} (p : t ⟶ t'')
    (h : p.right.unop ≫ g ≫ F.map w.right = p.right.unop ≫ g' ≫ F.map w.right) :
    proj d t ≫ Q.map ((adj.homEquiv _ _).symm g)
      = proj d t ≫ Q.map ((adj.homEquiv _ _).symm g') := by
  have : IsIso (Q.map w.right) := isIso_map_right_of_under w
  have h1 : G.map p.right.unop ≫ (adj.homEquiv _ _).symm g ≫ w.right
      = G.map p.right.unop ≫ (adj.homEquiv _ _).symm g' ≫ w.right := by
    have h0 := congrArg (adj.homEquiv _ _).symm h
    rwa [homEquiv_symm_comp_comp_map, homEquiv_symm_comp_comp_map] at h0
  have h2 : Q.map (G.map p.right.unop) ≫ Q.map ((adj.homEquiv _ _).symm g)
      = Q.map (G.map p.right.unop) ≫ Q.map ((adj.homEquiv _ _).symm g') := by
    have h3 := congrArg Q.map h1
    simp only [Q.map_comp] at h3
    rw [← cancel_mono (Q.map w.right)]
    simpa only [Category.assoc] using h3
  rw [← proj_comp_map d p]
  simp only [Category.assoc, h2]

section Main

variable [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
  [Q.IsLocalization S] [Q'.IsLocalization S']

/-- Two triples represent the same `ψ` if and only if they represent the same `χ`. -/
private lemma eq_iff_of_rep (adj : G ⊣ F)
    (c : IndCocone F Q' S K) (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (d : ProCocone G Q S' M) (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (Opposite.op M) d)
    {s s₁ : S.Under ⊤ K} {t t₁ : S'.op.Under ⊤ (Opposite.op M)}
    {f : t.right.unop ⟶ F.obj s.right} {f₁ : t₁.right.unop ⟶ F.obj s₁.right}
    {ψ ψ₁ : Q'.obj M ⟶ c.pt} {χ χ₁ : d.pt.unop ⟶ Q.obj K}
    (h : Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ coprj c s)
    (h₁ : Q'.map t₁.hom.unop ≫ ψ₁ = Q'.map f₁ ≫ coprj c s₁)
    (k : χ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f))
    (k₁ : χ₁ ≫ Q.map s₁.hom = proj d t₁ ≫ Q.map ((adj.homEquiv _ _).symm f₁)) :
    ψ = ψ₁ ↔ χ = χ₁ := by
  obtain ⟨s₂, ⟨w⟩, ⟨w₁⟩⟩ := nonempty_under_common s s₁
  obtain ⟨t₂, ⟨p⟩, ⟨p₁⟩⟩ := nonempty_op_under_common t t₁
  have hg := ind_refine c w p h
  have hg₁ := ind_refine c w₁ p₁ h₁
  have kg := pro_refine adj d w p k
  have kg₁ := pro_refine adj d w₁ p₁ k₁
  have : IsIso (Q'.map t₂.hom.unop) := Localization.inverts Q' S' _ t₂.prop
  have : IsIso (Q.map s₂.hom) := Localization.inverts Q S _ s₂.prop
  have e1 : ψ = ψ₁ ↔ Q'.map (p.right.unop ≫ f ≫ F.map w.right) ≫ coprj c s₂
      = Q'.map (p₁.right.unop ≫ f₁ ≫ F.map w₁.right) ≫ coprj c s₂ := by
    rw [← hg, ← hg₁]; exact (cancel_epi (Q'.map t₂.hom.unop)).symm
  have e2 : χ = χ₁ ↔ proj d t₂ ≫
      Q.map ((adj.homEquiv _ _).symm (p.right.unop ≫ f ≫ F.map w.right))
      = proj d t₂ ≫
        Q.map ((adj.homEquiv _ _).symm (p₁.right.unop ≫ f₁ ≫ F.map w₁.right)) := by
    rw [← kg, ← kg₁]; exact (cancel_mono (Q.map s₂.hom)).symm
  rw [e1, e2]
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨s₃, w₃, t₃, p₃, hh₃⟩ := exists_refinement_of_ind c hc s₂ t₂ _ _ hh
    exact pro_of_refinement adj d s₂ t₂ _ _ w₃ p₃ hh₃
  · obtain ⟨s₃, w₃, t₃, p₃, hh₃⟩ := exists_refinement_of_pro adj d hd s₂ t₂ _ _ hh
    exact ind_of_refinement c s₂ t₂ _ _ w₃ p₃ hh₃

omit [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions] in
/-- Every triple represents a (necessarily unique) morphism `ψ : M ⟶ RF(K)`. -/
private lemma exists_ind (c : IndCocone F Q' S K)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right) :
    ∃ ψ : Q'.obj M ⟶ c.pt, Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ coprj c s := by
  have : IsIso (Q'.map t.hom.unop) := Localization.inverts Q' S' _ t.prop
  exact ⟨inv (Q'.map t.hom.unop) ≫ Q'.map f ≫ coprj c s, by simp⟩

omit [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions] in
/-- Every triple represents a (necessarily unique) morphism `χ : LG(M) ⟶ K`. -/
private lemma exists_pro (adj : G ⊣ F) (d : ProCocone G Q S' M)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right) :
    ∃ χ : d.pt.unop ⟶ Q.obj K,
      χ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f) := by
  have : IsIso (Q.map s.hom) := Localization.inverts Q S _ s.prop
  exact ⟨proj d t ≫ Q.map ((adj.homEquiv _ _).symm f) ≫ inv (Q.map s.hom), by simp⟩

omit [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions] in
/-- A triple represents at most one `ψ`. -/
private lemma ind_inj (c : IndCocone F Q' S K)
    {s : S.Under ⊤ K} {t : S'.op.Under ⊤ (Opposite.op M)} {f : t.right.unop ⟶ F.obj s.right}
    {ψ₁ ψ₂ : Q'.obj M ⟶ c.pt}
    (h₁ : Q'.map t.hom.unop ≫ ψ₁ = Q'.map f ≫ coprj c s)
    (h₂ : Q'.map t.hom.unop ≫ ψ₂ = Q'.map f ≫ coprj c s) : ψ₁ = ψ₂ := by
  have : IsIso (Q'.map t.hom.unop) := Localization.inverts Q' S' _ t.prop
  exact (cancel_epi (Q'.map t.hom.unop)).1 (h₁.trans h₂.symm)

omit [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions] in
/-- A triple represents at most one `χ`. -/
private lemma pro_inj (adj : G ⊣ F) (d : ProCocone G Q S' M)
    {s : S.Under ⊤ K} {t : S'.op.Under ⊤ (Opposite.op M)} {f : t.right.unop ⟶ F.obj s.right}
    {χ₁ χ₂ : d.pt.unop ⟶ Q.obj K}
    (h₁ : χ₁ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f))
    (h₂ : χ₂ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f)) :
    χ₁ = χ₂ := by
  have : IsIso (Q.map s.hom) := Localization.inverts Q S _ s.prop
  exact (cancel_mono (Q.map s.hom)).1 (h₁.trans h₂.symm)

omit [S.HasLeftCalculusOfFractions] in
/-- Every `ψ : M ⟶ RF(K)` is represented by some triple: the calculus of right fractions
describes it as a fraction, and essential constancy of the ind-object supplies the index `s`. -/
private lemma exists_ind_rep (c : IndCocone F Q' S K)
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c) (ψ : Q'.obj M ⟶ c.pt) :
    ∃ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right),
      Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ coprj c s := by
  obtain ⟨s₀, r, hr, -⟩ := hc
  obtain ⟨φ, hφ⟩ :=
    Localization.exists_rightFraction Q' S' (Y := F.obj s₀.right) (ψ ≫ r)
  have h1 : Q'.map φ.s ≫ ψ ≫ r = Q'.map φ.f := by
    rw [hφ]; exact φ.map_s_comp_map Q' _
  refine ⟨s₀, MorphismProperty.Under.mk ⊤ φ.s.op φ.hs, φ.f, ?_⟩
  calc Q'.map φ.s ≫ ψ
      = Q'.map φ.s ≫ ψ ≫ r ≫ coprj c s₀ := by rw [hr, Category.comp_id]
    _ = (Q'.map φ.s ≫ ψ ≫ r) ≫ coprj c s₀ := by simp only [Category.assoc]
    _ = Q'.map φ.f ≫ coprj c s₀ := by rw [h1]

omit [S'.HasRightCalculusOfFractions] in
/-- Every `χ : LG(M) ⟶ K` is represented by some triple: the calculus of left fractions
describes it as a fraction, and essential constancy of the pro-object supplies the index `t`. -/
private lemma exists_pro_rep (adj : G ⊣ F) (d : ProCocone G Q S' M)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (Opposite.op M) d) (χ : d.pt.unop ⟶ Q.obj K) :
    ∃ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right),
      χ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f) := by
  obtain ⟨t₀, r, hr, -⟩ := hd
  have hr' : proj d t₀ ≫ r.unop = 𝟙 d.pt.unop := congrArg Quiver.Hom.unop hr
  obtain ⟨φ, hφ⟩ :=
    Localization.exists_leftFraction Q S (X := G.obj t₀.right.unop) (r.unop ≫ χ)
  have h1 : (r.unop ≫ χ) ≫ Q.map φ.s = Q.map φ.f := by
    rw [hφ]; exact φ.map_comp_map_s Q _
  have key : χ ≫ Q.map φ.s = proj d t₀ ≫ Q.map φ.f := by
    rw [← h1]
    simp only [← Category.assoc, hr', Category.id_comp]
  have key' : χ ≫ Q.map φ.s
      = proj d t₀ ≫ Q.map ((adj.homEquiv _ _).symm ((adj.homEquiv _ _) φ.f)) := by
    rwa [Equiv.symm_apply_apply]
  exact ⟨MorphismProperty.Under.mk ⊤ φ.s φ.hs, t₀, (adj.homEquiv _ _) φ.f, key'⟩

/-- The two representation relations are matched: if one triple represents both `ψ` and `χ`,
then a triple represents `ψ` exactly when it represents `χ`. -/
private lemma forall_iff_of_rep (adj : G ⊣ F)
    (c : IndCocone F Q' S K) (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (d : ProCocone G Q S' M) (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (Opposite.op M) d)
    {ψ : Q'.obj M ⟶ c.pt} {χ : d.pt.unop ⟶ Q.obj K}
    {s₁ : S.Under ⊤ K} {t₁ : S'.op.Under ⊤ (Opposite.op M)} {f₁ : t₁.right.unop ⟶ F.obj s₁.right}
    (h : Q'.map t₁.hom.unop ≫ ψ = Q'.map f₁ ≫ coprj c s₁)
    (k : χ ≫ Q.map s₁.hom = proj d t₁ ≫ Q.map ((adj.homEquiv _ _).symm f₁)) :
    ∀ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right),
      Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ coprj c s ↔
        χ ≫ Q.map s.hom = proj d t ≫ Q.map ((adj.homEquiv _ _).symm f) := by
  intro s t f
  obtain ⟨χ₂, hχ₂⟩ := exists_pro adj d s t f
  obtain ⟨ψ₂, hψ₂⟩ := exists_ind c s t f
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · have e : χ₂ = χ := (eq_iff_of_rep adj c hc d hd hh h hχ₂ k).1 rfl
    rw [← e]; exact hχ₂
  · have e : ψ₂ = ψ := (eq_iff_of_rep adj c hc d hd hψ₂ h hh k).2 rfl
    rw [← e]; exact hψ₂

end Main

end

/-- **Stacks 0FND**: deriving adjoints. Let `F : 𝒟 ⥤ 𝒟'` be right adjoint to `G : 𝒟' ⥤ 𝒟`, let
`S`, `S'` be classes of morphisms of `𝒟`, `𝒟'` admitting left, resp. right fractions, and let
`Q : 𝒟 ⥤ S⁻¹𝒟` and `Q' : 𝒟' ⥤ (S')⁻¹𝒟'` be localization functors. Let `K` be an object of `𝒟`
at which the right derived functor `RF` of `Q' ∘ F` is defined, with value `RF(K) = c.pt`, and
let `M` be an object of `𝒟'` at which the left derived functor `LG` of `Q ∘ G` is defined, with
value `LG(M) = d.pt.unop` (the left derived value is the right derived value of the opposite
functors, as in Stacks 05S9). Then there is a unique bijection
`Hom_{(S')⁻¹𝒟'}(M, RF(K)) ≃ Hom_{S⁻¹𝒟}(LG(M), K)` compatible with the fractions computing the
two sides: for every index `s : K ⟶ I` of the ind-object defining `RF(K)`, every index
`t : P ⟶ M` of the pro-object defining `LG(M)` and every `f : P ⟶ F(I)`, a morphism
`ψ : M ⟶ RF(K)` satisfies `Q'(t) ≫ ψ = Q'(f) ≫ (coprojection at s)` if and only if its image
satisfies `φ(ψ) ≫ Q(s) = (projection at t) ≫ Q(f^♯)`, where `f^♯ : G(P) ⟶ I` is adjoint
to `f`. -/
@[stacks 0FND, sga "4 XVII 2.3.7" "outer Hom bijection"]
theorem existsUnique_homEquiv_of_isRightDerivedValueAt
    {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
    {SD : Type u₃} [Category.{v₃} SD] {SD' : Type u₄} [Category.{v₄} SD']
    {F : D ⥤ D'} {G : D' ⥤ D} (adj : G ⊣ F)
    (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    (Q : D ⥤ SD) [Q.IsLocalization S] (Q' : D' ⥤ SD') [Q'.IsLocalization S']
    (K : D) (M : D')
    (c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙ Under.forget K ⋙ F ⋙ Q'))
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (d : Cocone (MorphismProperty.Under.forget S'.op ⊤ (Opposite.op M) ⋙
      Under.forget (Opposite.op M) ⋙ (G ⋙ Q).op))
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (Opposite.op M) d) :
    ∃! φ : (Q'.obj M ⟶ c.pt) ≃ (d.pt.unop ⟶ Q.obj K),
      ∀ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M))
        (f : t.right.unop ⟶ F.obj s.right) (ψ : Q'.obj M ⟶ c.pt),
        Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ c.ι.app s ↔
          φ ψ ≫ Q.map s.hom = (d.ι.app t).unop ≫ Q.map ((adj.homEquiv _ _).symm f) := by
  have h1 : ∀ ψ : Q'.obj M ⟶ c.pt, ∃ χ : d.pt.unop ⟶ Q.obj K,
      ∀ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right),
        Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ c.ι.app s ↔
          χ ≫ Q.map s.hom = (d.ι.app t).unop ≫ Q.map ((adj.homEquiv _ _).symm f) := by
    intro ψ
    obtain ⟨s₁, t₁, f₁, h⟩ := exists_ind_rep (S' := S') c hc ψ
    obtain ⟨χ, k⟩ := exists_pro adj d s₁ t₁ f₁
    exact ⟨χ, forall_iff_of_rep adj c hc d hd h k⟩
  have h2 : ∀ χ : d.pt.unop ⟶ Q.obj K, ∃ ψ : Q'.obj M ⟶ c.pt,
      ∀ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (Opposite.op M)) (f : t.right.unop ⟶ F.obj s.right),
        Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ c.ι.app s ↔
          χ ≫ Q.map s.hom = (d.ι.app t).unop ≫ Q.map ((adj.homEquiv _ _).symm f) := by
    intro χ
    obtain ⟨s₁, t₁, f₁, k⟩ := exists_pro_rep (S := S) adj d hd χ
    obtain ⟨ψ, h⟩ := exists_ind c s₁ t₁ f₁
    exact ⟨ψ, forall_iff_of_rep adj c hc d hd h k⟩
  choose fwd hfwd using h1
  choose bwd hbwd using h2
  refine ⟨⟨fwd, bwd, fun ψ => ?_, fun χ => ?_⟩, fun s t f ψ => hfwd ψ s t f, fun φ hφ => ?_⟩
  · obtain ⟨s₁, t₁, f₁, h⟩ := exists_ind_rep (S' := S') c hc ψ
    exact ind_inj c ((hbwd (fwd ψ) s₁ t₁ f₁).2 ((hfwd ψ s₁ t₁ f₁).1 h)) h
  · obtain ⟨s₁, t₁, f₁, k⟩ := exists_pro_rep (S := S) adj d hd χ
    exact pro_inj adj d ((hfwd (bwd χ) s₁ t₁ f₁).1 ((hbwd χ s₁ t₁ f₁).2 k)) k
  · ext ψ
    obtain ⟨s₁, t₁, f₁, h⟩ := exists_ind_rep (S' := S') c hc ψ
    exact pro_inj adj d ((hφ s₁ t₁ f₁ ψ).1 h) ((hfwd ψ s₁ t₁ f₁).1 h)

end PointwiseGeneral

/-! ### Deriving adjoints between derived categories of abelian categories -/

section PointwiseDerivedCategory

open Limits Opposite

section Adjunctions

variable {ι : Type*} {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction between the functors on
categories of homological complexes, with unit and counit given in each degree by those of the
original adjunction. -/
public def mapHomologicalComplexAdjunction (adj : G ⊣ F) (c : ComplexShape ι) :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun X =>
        { f := fun n => adj.unit.app (X.X n)
          comm' := fun i j _ => by simp }
      naturality := fun X Y f => by ext n; simp }
  counit :=
    { app := fun Y =>
        { f := fun n => adj.counit.app (Y.X n)
          comm' := fun i j _ => by simp }
      naturality := fun X Y f => by ext n; simp }
  left_triangle_components := by intro X; ext n; simp
  right_triangle_components := by intro Y; ext n; simp

/-- The transpose of a morphism of complexes is its degreewise transpose. -/
private lemma mapHomologicalComplexAdjunction_homEquiv_symm_f (adj : G ⊣ F) (c : ComplexShape ι)
    {X : HomologicalComplex B c} {Y : HomologicalComplex A c}
    (f : X ⟶ (F.mapHomologicalComplex c).obj Y) (n : ι) :
    (((mapHomologicalComplexAdjunction adj c).homEquiv X Y).symm f).f n =
      (adj.homEquiv _ _).symm (f.f n) := rfl

/-- A morphism of complexes has a unique degreewise transpose, namely its transpose. -/
private lemma mapHomologicalComplexAdjunction_homEquiv_symm_eq (adj : G ⊣ F) (c : ComplexShape ι)
    {X : HomologicalComplex B c} {Y : HomologicalComplex A c}
    (f : X ⟶ (F.mapHomologicalComplex c).obj Y)
    (g : (G.mapHomologicalComplex c).obj X ⟶ Y) (h : ∀ n, f.f n = adj.homEquiv _ _ (g.f n)) :
    ((mapHomologicalComplexAdjunction adj c).homEquiv X Y).symm f = g := by
  ext n
  rw [mapHomologicalComplexAdjunction_homEquiv_symm_f, h n, Equiv.symm_apply_apply]

/-- **The unit of the induced adjunction on complexes is degreewise the unit.** True by
definition; it is a declaration of its own so that a consumer never unfolds
`mapHomologicalComplexAdjunction` inside a larger computation. -/
public lemma mapHomologicalComplexAdjunction_unit_app_f (adj : G ⊣ F) (c : ComplexShape ι)
    (X : HomologicalComplex B c) (n : ι) :
    ((mapHomologicalComplexAdjunction adj c).unit.app X).f n = adj.unit.app (X.X n) := rfl

/-- **The unit of the induced adjunction on complexes, at a complex concentrated in one degree,
is the unit of the original adjunction.** Conjugating the unit at
`CategoryTheory.HomologicalComplex.single B c j` by the two identifications
`CategoryTheory.HomologicalComplex.singleMapHomologicalComplex` of `single` with `G` and with `F`
returns `single` of the unit at the object.

Both sides are maps of complexes, so this is a degreewise check: away from `j` the source is the
zero object, and in degree `j` the two identifications are the canonical isomorphisms of
`CategoryTheory.HomologicalComplex.singleObjXSelf`, against which the naturality of the unit is
exactly the claim. -/
public lemma mapHomologicalComplexAdjunction_unit_app_single [Limits.HasZeroObject A]
    [Limits.HasZeroObject B] (adj : G ⊣ F) (c : ComplexShape ι) [DecidableEq ι] (j : ι) (M : B) :
    (mapHomologicalComplexAdjunction adj c).unit.app ((HomologicalComplex.single B c j).obj M) ≫
        (F.mapHomologicalComplex c).map
          ((HomologicalComplex.singleMapHomologicalComplex G c j).hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex F c j).hom.app (G.obj M) =
      (HomologicalComplex.single B c j).map (adj.unit.app M) := by
  ext n
  by_cases hn : n = j
  · subst hn
    simp [mapHomologicalComplexAdjunction_unit_app_f,
      HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X c j M n hn).eq_of_src _ _

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction between the functors on
homotopy categories, with unit and counit the classes of those of the induced adjunction on
complexes. -/
public noncomputable def mapHomotopyCategoryAdjunction (adj : G ⊣ F) (c : ComplexShape ι) :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c where
  unit := Quotient.natTransLift _
    (Functor.whiskerRight (mapHomologicalComplexAdjunction adj c).unit
      (HomotopyCategory.quotient B c))
  counit := Quotient.natTransLift _
    (Functor.whiskerRight (mapHomologicalComplexAdjunction adj c).counit
      (HomotopyCategory.quotient A c))
  left_triangle_components := by
    rintro ⟨X⟩
    exact ((HomotopyCategory.quotient A c).map_comp _ _).symm.trans
      ((congrArg _ ((mapHomologicalComplexAdjunction adj c).left_triangle_components X)).trans
        ((HomotopyCategory.quotient A c).map_id _))
  right_triangle_components := by
    rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient B c).map_comp _ _).symm.trans
      ((congrArg _ ((mapHomologicalComplexAdjunction adj c).right_triangle_components Y)).trans
        ((HomotopyCategory.quotient B c).map_id _))

/-- The transpose of the class of a morphism of complexes is the class of its transpose. -/
private lemma mapHomotopyCategoryAdjunction_homEquiv_symm_quotient_map (adj : G ⊣ F)
    (c : ComplexShape ι) {X : HomotopyCategory B c} {Y : HomotopyCategory A c}
    (f : X.as ⟶ (F.mapHomologicalComplex c).obj Y.as) :
    ((mapHomotopyCategoryAdjunction adj c).homEquiv X Y).symm
        ((HomotopyCategory.quotient B c).map f) =
      (HomotopyCategory.quotient A c).map
        (((mapHomologicalComplexAdjunction adj c).homEquiv X.as Y.as).symm f) := rfl

end Adjunctions

section OppositeIndices

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {W : MorphismProperty D} {X : D}

/-- The index of the pro-object at `X` given by an index of the ind-object at `op X` of the
opposite functors. -/
private def overOfOpUnder (W : MorphismProperty D) (X : D) (t : W.op.Under ⊤ (Opposite.op X)) :
    W.Over ⊤ X :=
  MorphismProperty.Over.mk ⊤ t.hom.unop t.prop

/-- The index of the ind-object at `op X` of the opposite functors given by an index of the
pro-object at `X`. -/
private def opUnderOfOver (W : MorphismProperty D) (X : D) (t : W.Over ⊤ X) :
    W.op.Under ⊤ (Opposite.op X) :=
  MorphismProperty.Under.mk ⊤ t.hom.op t.prop

private lemma overOfOpUnder_opUnderOfOver (t : W.Over ⊤ X) :
    overOfOpUnder W X (opUnderOfOver W X t) = t := rfl

private lemma opUnderOfOver_overOfOpUnder (t : W.op.Under ⊤ (Opposite.op X)) :
    opUnderOfOver W X (overOfOpUnder W X t) = t := rfl

/-- A morphism of indices of the pro-object gives a morphism of indices of the opposite
ind-object, in the other direction. -/
private def opUnderHomOfOverHom {t s : W.Over ⊤ X} (u : t ⟶ s) :
    opUnderOfOver W X s ⟶ opUnderOfOver W X t :=
  MorphismProperty.Under.homMk u.left.op
    (show s.hom.op ≫ u.left.op = t.hom.op by rw [← op_comp, MorphismProperty.Over.w u])

/-- A morphism of indices of the opposite ind-object gives a morphism of indices of the
pro-object, in the other direction. -/
private def overHomOfOpUnderHom {t s : W.op.Under ⊤ (Opposite.op X)} (u : t ⟶ s) :
    overOfOpUnder W X s ⟶ overOfOpUnder W X t :=
  MorphismProperty.Over.homMk u.right.unop
    (show u.right.unop ≫ t.hom.unop = s.hom.unop by
      rw [← unop_comp, MorphismProperty.Under.w u])

/-- The opposite of a cone on the pro-object at `X` computing a left derived value is a cocone
on the ind-object at `op X` of the opposite functors. -/
private def opCoconeOfCone (H : D ⥤ D') (W : MorphismProperty D) (X : D)
    (d : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ H)) :
    Cocone (MorphismProperty.Under.forget W.op ⊤ (Opposite.op X) ⋙
      CategoryTheory.Under.forget (Opposite.op X) ⋙ H.op) where
  pt := Opposite.op d.pt
  ι :=
    { app := fun t => (d.π.app (overOfOpUnder W X t)).op
      naturality := fun _ _ u =>
        Quiver.Hom.unop_inj ((d.w (overHomOfOpUnderHom u)).trans (Category.id_comp _).symm) }

/-- A value of the left derived functor of `H` at `X`, in the pro-object form of Stacks 05S9, is a
value of the right derived functor of `H.op` at `op X`, in the ind-object form used by
Stacks 0FND. -/
private lemma isRightDerivedValueAt_op_of_isLeftDerivedValueAt (H : D ⥤ D')
    (W : MorphismProperty D) (X : D)
    (d : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ H))
    (hd : H.IsLeftDerivedValueAt W X d) :
    H.op.IsRightDerivedValueAt W.op (Opposite.op X) (opCoconeOfCone H W X d) := by
  obtain ⟨s₀, r, hr, hfac⟩ := hd
  refine ⟨opUnderOfOver W X s₀, r.op, ?_, fun s => ?_⟩
  · exact Quiver.Hom.unop_inj hr
  · obtain ⟨t, u, v, h⟩ := hfac (overOfOpUnder W X s)
    refine ⟨opUnderOfOver W X t, opUnderHomOfOverHom u, opUnderHomOfOverHom v, ?_⟩
    exact Quiver.Hom.unop_inj (h.trans (Category.assoc _ _ _).symm)

end OppositeIndices

/-- **Stacks 0DVC**: deriving adjoints between derived categories. Let `F : 𝒜 ⥤ ℬ` be right
adjoint to `G : ℬ ⥤ 𝒜`, functors of abelian categories, let `K` be a complex of `𝒜` and `M` a
complex of `ℬ`, and let `RF`, resp. `LG`, be the right, resp. left, derived functor of
`K(𝒜) ⥤ K(ℬ) ⥤ D(ℬ)`, resp. `K(ℬ) ⥤ K(𝒜) ⥤ D(𝒜)`, with respect to the quasi-isomorphisms.
Assume `RF` is defined at `K`, with value `RF(K) = c.pt`, and `LG` is defined at `M`, with value
`LG(M) = d.pt` (Stacks 05S9). Then there is a unique bijection
`Hom_{D(ℬ)}(M, RF(K)) ≃ Hom_{D(𝒜)}(LG(M), K)` compatible with the fractions computing the two
sides: for every index `s : K ⟶ I` of the ind-object defining `RF(K)`, every index `t : P ⟶ M`
of the pro-object defining `LG(M)` and every pair of chain maps `f : P ⟶ F(I)`, `g : G(P) ⟶ I`
that are adjoint to one another in each degree, a morphism `ψ : M ⟶ RF(K)` satisfies
`Qh(t) ≫ ψ = Qh(f) ≫ (coprojection at s)` if and only if its image satisfies
`φ(ψ) ≫ Qh(s) = (projection at t) ≫ Qh(g)`. -/
@[stacks 0DVC]
theorem existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : G ⊣ F)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) (M : HomotopyCategory B (ComplexShape.up ℤ))
    (c : Cocone (MorphismProperty.Under.forget
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K ⋙
      Under.forget K ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (d : Cone (MorphismProperty.Over.forget
        (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ⊤ M ⋙
      Over.forget M ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d) :
    ∃! φ : (DerivedCategory.Qh.obj M ⟶ c.pt) ≃ (d.pt ⟶ DerivedCategory.Qh.obj K),
      ∀ (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K)
        (t : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).Over ⊤ M)
        (f : t.left.as ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj s.right.as)
        (g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj t.left.as ⟶ s.right.as),
        (∀ n, f.f n = adj.homEquiv _ _ (g.f n)) →
        ∀ ψ : DerivedCategory.Qh.obj M ⟶ c.pt,
          DerivedCategory.Qh.map t.hom ≫ ψ =
              DerivedCategory.Qh.map
                ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f) ≫ c.ι.app s ↔
            φ ψ ≫ DerivedCategory.Qh.map s.hom =
              d.π.app t ≫ DerivedCategory.Qh.map
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) := by
  obtain ⟨φ, hφ, huniq⟩ :=
    existsUnique_homEquiv_of_isRightDerivedValueAt
      (mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh K M c hc
      (opCoconeOfCone _ _ _ d) (isRightDerivedValueAt_op_of_isLeftDerivedValueAt _ _ _ d hd)
  refine ⟨φ, fun s t f g hfg ψ => ?_, fun φ' hφ' => huniq φ' (fun s t f ψ => ?_)⟩
  · have hg : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g =
        ((mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).homEquiv t.left s.right).symm
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f) := by
      rw [mapHomotopyCategoryAdjunction_homEquiv_symm_quotient_map,
        mapHomologicalComplexAdjunction_homEquiv_symm_eq adj _ f g hfg]
    exact (hφ s (opUnderOfOver _ _ t) _ ψ).trans (iff_of_eq (congrArg
      (fun z => φ ψ ≫ DerivedCategory.Qh.map s.hom =
        d.π.app t ≫ DerivedCategory.Qh.map z) hg.symm))
  · have e₁ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f.out = f :=
      HomotopyCategory.quotient_map_out f
    have e₂ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (((mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).homEquiv
            (overOfOpUnder _ M t).left.as s.right.as).symm f.out) =
        ((mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).homEquiv
          (overOfOpUnder _ M t).left s.right).symm f := by
      conv_rhs => rw [← e₁]
      exact (mapHomotopyCategoryAdjunction_homEquiv_symm_quotient_map adj _ f.out).symm
    have hfg : ∀ n, f.out.f n = adj.homEquiv _ _
        ((((mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).homEquiv
          (overOfOpUnder _ M t).left.as s.right.as).symm f.out).f n) := fun n =>
      ((congrArg (fun x => adj.homEquiv _ _ x)
          (mapHomologicalComplexAdjunction_homEquiv_symm_f adj _ f.out n)).trans
        ((adj.homEquiv _ _).apply_symm_apply _)).symm
    have key := hφ' s (overOfOpUnder _ _ t) f.out
      (((mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).homEquiv
        (overOfOpUnder _ M t).left.as s.right.as).symm f.out) hfg ψ
    exact (iff_of_eq (congrArg (fun z => DerivedCategory.Qh.map t.hom.unop ≫ ψ =
        DerivedCategory.Qh.map z ≫ c.ι.app s) e₁.symm)).trans
      (key.trans (iff_of_eq (congrArg (fun z => φ' ψ ≫ DerivedCategory.Qh.map s.hom =
        d.π.app (overOfOpUnder _ M t) ≫ DerivedCategory.Qh.map z) e₂)))

end PointwiseDerivedCategory

/-! ### The derived functors of an adjoint pair are adjoint -/

section Global

open Category Limits _root_.CategoryTheory.Functor

section Preserve

variable {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

/-- A functor preserves a retraction. -/
private lemma map_comp_map_eq_id {X Y : E} {i : X ⟶ Y} {p : Y ⟶ X} (h : i ≫ p = 𝟙 X)
    (H : E ⥤ E') : H.map i ≫ H.map p = 𝟙 (H.obj X) := by
  rw [← H.map_comp, h, H.map_id]

/-- A functor preserves a factorisation through two intermediate objects. -/
private lemma map_eq_map_comp_map_comp_map {X Y Z W : E} {a : X ⟶ W} {b : X ⟶ Y} {c : Y ⟶ Z}
    {g : Z ⟶ W} (h : a = b ≫ c ≫ g) (H : E ⥤ E') :
    H.map a = H.map b ≫ H.map c ≫ H.map g := by
  rw [h, H.map_comp, H.map_comp]

/-- A morphism into a retract is determined by its composite with the section. -/
private lemma eq_comp_comp_of_comp_comp_eq {X Y Z W : E} {m : X ⟶ Y} {a : Y ⟶ Z} {b : Z ⟶ W}
    {p : W ⟶ Z} {q : Z ⟶ Y} {n : X ⟶ W} (hn : m ≫ a ≫ b = n) (hbp : b ≫ p = 𝟙 Z)
    (haq : a ≫ q = 𝟙 Y) : m = n ≫ p ≫ q := by
  rw [← hn]
  simp only [assoc]
  rw [← assoc b p, hbp, id_comp, haq, comp_id]

/-- A morphism out of a retract is determined by its composite with the retraction. -/
private lemma eq_comp_comp_of_comp_comp_eq' {X Y Z W : E} {m : Y ⟶ X} {a : Z ⟶ Y} {b : W ⟶ Z}
    {p : Z ⟶ W} {q : Y ⟶ Z} {n : W ⟶ X} (hn : (b ≫ a) ≫ m = n) (hpb : p ≫ b = 𝟙 Z)
    (hqa : q ≫ a = 𝟙 Y) : m = q ≫ p ≫ n := by
  rw [← hn]
  simp only [assoc]
  rw [← assoc p b, hpb, id_comp, ← assoc q a, hqa, id_comp]

/-- Reassociation of a composite along a factorisation of one of its factors: if `a ≫ b = A`,
if `c` factors as `b ≫ z`, and if `a ≫ c = n`, then `A ≫ z = n`. -/
private lemma comp_eq_of_eq_comp {X₁ X₂ X₃ X₄ : E} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {A : X₁ ⟶ X₃}
    {z : X₃ ⟶ X₄} {c : X₂ ⟶ X₄} {n : X₁ ⟶ X₄} (hA : a ≫ b = A) (hc : c = b ≫ z)
    (hn : a ≫ c = n) : A ≫ z = n := by
  rw [← hA, ← hn, hc, assoc]

/-- Reassociation of a composite along a factorisation of one of its factors, dual form: if
`b ≫ a = A`, if `c` factors as `z ≫ y ≫ b`, and if `c ≫ a = n`, then `z ≫ y ≫ A = n`. -/
private lemma comp_eq_of_eq_comp' {X₁ X₂ X₃ X₄ X₅ : E} {b : X₃ ⟶ X₄} {a : X₄ ⟶ X₅}
    {A : X₃ ⟶ X₅} {z : X₁ ⟶ X₂} {y : X₂ ⟶ X₃} {c : X₁ ⟶ X₄} {n : X₁ ⟶ X₅} (hA : b ≫ a = A)
    (hc : c = z ≫ y ≫ b) (hn : c ≫ a = n) : z ≫ y ≫ A = n := by
  rw [← hA, ← hn, hc]
  simp only [assoc]

/-- Cancelling a retraction in the middle of a composite: if `a ≫ q = B` with `a = h ≫ p`, if
`g ≫ h` is the identity, and if `m ≫ r ≫ p = w` with `w ≫ q = n`, then
`(m ≫ r ≫ g) ≫ B = n`. -/
private lemma comp_comp_eq_of_comp_eq_id {Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : E} {m : Y₁ ⟶ Y₂} {r : Y₂ ⟶ Y₃}
    {g : Y₃ ⟶ Y₄} {h : Y₄ ⟶ Y₃} {p : Y₃ ⟶ Y₅} {a : Y₄ ⟶ Y₅} {q : Y₅ ⟶ Y₆} {B : Y₄ ⟶ Y₆}
    {w : Y₁ ⟶ Y₅} {n : Y₁ ⟶ Y₆} (hB : a ≫ q = B) (ha : a = h ≫ p) (hg : g ≫ h = 𝟙 Y₃)
    (hw : m ≫ r ≫ p = w) (hn : w ≫ q = n) : (m ≫ r ≫ g) ≫ B = n := by
  rw [← hB, ha, ← hn, ← hw]
  simp only [assoc]
  rw [← assoc g h, hg, id_comp]

/-- Cancelling a retraction in the middle of a composite, dual form: if `q ≫ a = B` with
`a = p ≫ h`, if `h ≫ g` is the identity, and if `p ≫ r ≫ m = w` with `q ≫ w = n`, then
`B ≫ g ≫ r ≫ m = n`. -/
private lemma comp_comp_eq_of_comp_eq_id' {Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : E} {q : Y₆ ⟶ Y₅} {a : Y₅ ⟶ Y₄}
    {B : Y₆ ⟶ Y₄} {p : Y₅ ⟶ Y₃} {h : Y₃ ⟶ Y₄} {g : Y₄ ⟶ Y₃} {r : Y₃ ⟶ Y₂} {m : Y₂ ⟶ Y₁}
    {w : Y₅ ⟶ Y₁} {n : Y₆ ⟶ Y₁} (hB : q ≫ a = B) (ha : a = p ≫ h) (hg : h ≫ g = 𝟙 Y₃)
    (hw : p ≫ r ≫ m = w) (hn : q ≫ w = n) : B ≫ g ≫ r ≫ m = n := by
  rw [← hB, ha, ← hn, ← hw]
  simp only [assoc]
  rw [← assoc h g, hg, id_comp]

end Preserve

section Left

variable {D' : Type u₁} [Category.{v₁} D'] {SD' : Type u₂} [Category.{v₂} SD']
  {E : Type u₃} [Category.{v₃} E]

/-- A value of the left derived functor of `Φ` at `M` in Deligne's sense (Stacks 05S9(2))
remains one after post-composing with an arbitrary functor `H`: the value is a retract of a
term of the pro-object, and a retract is preserved by every functor. -/
private lemma isLeftDerivedValueAt_mapCone {Φ : D' ⥤ E} (S' : MorphismProperty D') (M : D')
    {d : Cone (MorphismProperty.Over.forget S' ⊤ M ⋙ CategoryTheory.Over.forget M ⋙ Φ)}
    (hd : Φ.IsLeftDerivedValueAt S' M d) {E' : Type u₄} [Category.{v₄} E'] (H : E ⥤ E') :
    (Φ ⋙ H).IsLeftDerivedValueAt S' M (H.mapCone d) := by
  obtain ⟨t₀, r, hr, hb⟩ := hd
  refine ⟨t₀, H.map r, map_comp_map_eq_id hr H, fun t => ?_⟩
  obtain ⟨t', u, v, hfac⟩ := hb t
  exact ⟨t', u, v, map_eq_map_comp_map_comp_map hfac H⟩

section

variable (S' : MorphismProperty D') (Q' : D' ⥤ SD') [Q'.IsLocalization S']

/-- An index `t : P ⟶ M` of the pro-object computing a left derived value at `M`, viewed as an
index of the limit computing a right Kan extension at `Q'(M)`: the object of
`StructuredArrow (Q'(M)) Q'` given by the inverse of the isomorphism `Q'(t)`. -/
private noncomputable abbrev structuredArrowOfOver (M : D') (t : S'.Over ⊤ M) :
    StructuredArrow (Q'.obj M) Q' :=
  StructuredArrow.mk (Localization.isoOfHom Q' S' t.hom t.prop).inv

/-- Comparison of indices: a morphism `f` of `𝒟'` out of the source of the index `t` whose image
in the localization is `Q'(t)` followed by the structure map of `j` induces a morphism of
structured arrows from the index `t` to `j`. -/
private noncomputable def structuredArrowHomMk (M : D') {t : S'.Over ⊤ M}
    {j : StructuredArrow (Q'.obj M) Q'} (f : t.left ⟶ j.right)
    (hf : Q'.map f = Q'.map t.hom ≫ j.hom) :
    structuredArrowOfOver S' Q' M t ⟶ j :=
  StructuredArrow.homMk f
    (((Localization.isoOfHom Q' S' t.hom t.prop).inv_comp_eq (f := Q'.map f) (g := j.hom)).mpr hf)

/-- The projections of a cone on the diagram of a right Kan extension at `Q'(M)` are compatible
with the comparison of indices. -/
private lemma cone_π_app_comp (Φ : D' ⥤ E) (M : D')
    (s : Cone (StructuredArrow.proj (Q'.obj M) Q' ⋙ Φ)) {t : S'.Over ⊤ M}
    {j : StructuredArrow (Q'.obj M) Q'} (f : t.left ⟶ j.right)
    (hf : Q'.map f = Q'.map t.hom ≫ j.hom) :
    s.π.app (structuredArrowOfOver S' Q' M t) ≫ Φ.map f = s.π.app j :=
  s.w (structuredArrowHomMk S' Q' M f hf)

variable [S'.HasRightCalculusOfFractions] {Φ : D' ⥤ E} {LΦ : SD' ⥤ E}

/-- A value of the left derived functor of `Φ` at `M` in Deligne's sense (Stacks 05S9(2)),
identified with `LΦ(Q'(M))` compatibly with the projections of the pro-object, exhibits `LΦ`
as a pointwise right Kan extension of `Φ` along `Q'` at `Q'(M)`. -/
private noncomputable def isPointwiseRightKanExtensionAt_of_isLeftDerivedValueAt
    (α : Q' ⋙ LΦ ⟶ Φ) (M : D')
    (d : Cone (MorphismProperty.Over.forget S' ⊤ M ⋙ CategoryTheory.Over.forget M ⋙ Φ))
    (t₀ : S'.Over ⊤ M) (r : Φ.obj t₀.left ⟶ d.pt) (hr : d.π.app t₀ ≫ r = 𝟙 d.pt)
    (hb : ∀ t : S'.Over ⊤ M, ∃ (t' : S'.Over ⊤ M) (u : t' ⟶ t) (v : t' ⟶ t₀),
      Φ.map u.left = Φ.map v.left ≫ r ≫ d.π.app t)
    (e : LΦ.obj (Q'.obj M) ≅ d.pt)
    (he : ∀ t : S'.Over ⊤ M, LΦ.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left) :
    (RightExtension.mk LΦ α).IsPointwiseRightKanExtensionAt (Q'.obj M) := by
  -- the projections of the pro-object are the projections of the limit cone
  have hπ : ∀ t : S'.Over ⊤ M,
      ((RightExtension.mk LΦ α).coneAt (Q'.obj M)).π.app (structuredArrowOfOver S' Q' M t) =
        e.hom ≫ d.π.app t := fun t =>
    ((LΦ.mapIso (Localization.isoOfHom Q' S' t.hom t.prop)).inv_comp_eq
      (f := α.app t.left) (g := e.hom ≫ d.π.app t)).mpr (he t).symm
  -- a transition morphism of the pro-object is a comparison of indices
  have hmap : ∀ {t t' : S'.Over ⊤ M} (u : t ⟶ t'),
      Q'.map u.left = Q'.map t.hom ≫ (structuredArrowOfOver S' Q' M t').hom := fun {t t'} u =>
    ((Localization.isoOfHom Q' S' t'.hom t'.prop).eq_comp_inv
      (f := Q'.map t.hom) (g := Q'.map u.left)).mpr (by
        rw [Localization.isoOfHom_hom, ← Q'.map_comp, MorphismProperty.Over.w u])
  refine
    { lift := fun s => s.π.app (structuredArrowOfOver S' Q' M t₀) ≫ r ≫ e.inv
      fac := ?_
      uniq := ?_ }
  · intro s j
    -- the retraction computes every projection of `s`
    have hkey : ∀ t : S'.Over ⊤ M,
        s.π.app (structuredArrowOfOver S' Q' M t₀) ≫ r ≫ d.π.app t =
          s.π.app (structuredArrowOfOver S' Q' M t) := by
      intro t
      obtain ⟨t', u, v, hfac⟩ := hb t
      exact comp_eq_of_eq_comp
        (cone_π_app_comp S' Q' Φ M s (t := t') (j := structuredArrowOfOver S' Q' M t₀)
          v.left (hmap v)) hfac
        (cone_π_app_comp S' Q' Φ M s (t := t') (j := structuredArrowOfOver S' Q' M t)
          u.left (hmap u))
    -- an arbitrary index is refined by an index of the pro-object, by right fractions
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q' S' j.hom
    have hf : Q'.map φ.f =
        Q'.map (MorphismProperty.Over.mk ⊤ φ.s φ.hs).hom ≫ j.hom := by
      rw [hφ]
      exact (MorphismProperty.RightFraction.map_s_comp_map φ Q'
        (Localization.inverts Q' S')).symm
    exact comp_comp_eq_of_comp_eq_id
      (cone_π_app_comp S' Q' Φ M ((RightExtension.mk LΦ α).coneAt (Q'.obj M))
        (t := MorphismProperty.Over.mk ⊤ φ.s φ.hs) (j := j) φ.f hf)
      (hπ (MorphismProperty.Over.mk ⊤ φ.s φ.hs)) e.inv_hom_id
      (hkey (MorphismProperty.Over.mk ⊤ φ.s φ.hs))
      (cone_π_app_comp S' Q' Φ M s (t := MorphismProperty.Over.mk ⊤ φ.s φ.hs) (j := j) φ.f hf)
  · intro s m hm
    have h₀ := hm (structuredArrowOfOver S' Q' M t₀)
    rw [hπ t₀] at h₀
    exact eq_comp_comp_of_comp_comp_eq h₀ hr e.hom_inv_id

/-- **A left derived functor in Deligne's sense is one in Mathlib's sense.** If for every object
`M` the pro-object `(t : P ⟶ M) ↦ Φ(P)`, `t ∈ S'`, is essentially constant with value
`LΦ(Q'(M))` and projections induced by `α` (Stacks 05S9(2)), then `α` makes `LΦ` a left derived
functor of `Φ`, i.e. a right Kan extension along the localization functor `Q'`. -/
private lemma isLeftDerivedFunctor_of_forall_isLeftDerivedValueAt (α : Q' ⋙ LΦ ⟶ Φ)
    (h : ∀ M : D', ∃ (d : Cone (MorphismProperty.Over.forget S' ⊤ M ⋙
          CategoryTheory.Over.forget M ⋙ Φ))
        (_ : Φ.IsLeftDerivedValueAt S' M d) (e : LΦ.obj (Q'.obj M) ≅ d.pt),
        ∀ t : S'.Over ⊤ M, LΦ.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left) :
    LΦ.IsLeftDerivedFunctor α S' := by
  have := Localization.essSurj Q' S'
  have hp : ∀ Y : SD', Nonempty ((RightExtension.mk LΦ α).IsPointwiseRightKanExtensionAt Y) := by
    intro Y
    obtain ⟨d, hd, e, he⟩ := h (Q'.objPreimage Y)
    obtain ⟨t₀, r, hr, hb⟩ := hd
    exact ⟨(RightExtension.mk LΦ α).isPointwiseRightKanExtensionAtEquivOfIso'
      (Q'.objObjPreimageIso Y)
      (isPointwiseRightKanExtensionAt_of_isLeftDerivedValueAt S' Q' α _ d t₀ r hr hb e he)⟩
  exact ⟨Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (fun Y => (hp Y).some)⟩

end

end Left

section Right

variable {D : Type u₁} [Category.{v₁} D] {SD : Type u₂} [Category.{v₂} SD]
  {E : Type u₃} [Category.{v₃} E]

/-- A value of the right derived functor of `Φ` at `K` in Deligne's sense (Stacks 05S9(1))
remains one after post-composing with an arbitrary functor `H`: the value is a retract of a
term of the ind-object, and a retract is preserved by every functor. -/
private lemma isRightDerivedValueAt_mapCocone {Φ : D ⥤ E} (S : MorphismProperty D) (K : D)
    {c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙ CategoryTheory.Under.forget K ⋙ Φ)}
    (hc : Φ.IsRightDerivedValueAt S K c) {E' : Type u₄} [Category.{v₄} E'] (H : E ⥤ E') :
    (Φ ⋙ H).IsRightDerivedValueAt S K (H.mapCocone c) := by
  obtain ⟨s₀, r, hr, hb⟩ := hc
  refine ⟨s₀, H.map r, map_comp_map_eq_id hr H, fun s => ?_⟩
  obtain ⟨s', u, v, hfac⟩ := hb s
  exact ⟨s', u, v, map_eq_map_comp_map_comp_map hfac H⟩

section

variable (S : MorphismProperty D) (Q : D ⥤ SD) [Q.IsLocalization S]

/-- An index `s : K ⟶ I` of the ind-object computing a right derived value at `K`, viewed as an
index of the colimit computing a left Kan extension at `Q(K)`: the object of
`CostructuredArrow Q (Q(K))` given by the inverse of the isomorphism `Q(s)`. -/
private noncomputable abbrev costructuredArrowOfUnder (K : D) (s : S.Under ⊤ K) :
    CostructuredArrow Q (Q.obj K) :=
  CostructuredArrow.mk (Localization.isoOfHom Q S s.hom s.prop).inv

/-- Comparison of indices: a morphism `f` of `𝒟` into the target of the index `s` whose image in
the localization is the structure map of `j` followed by `Q(s)` induces a morphism of
costructured arrows from `j` to the index `s`. -/
private noncomputable def costructuredArrowHomMk (K : D) {s : S.Under ⊤ K}
    {j : CostructuredArrow Q (Q.obj K)} (f : j.left ⟶ s.right)
    (hf : Q.map f = j.hom ≫ Q.map s.hom) :
    j ⟶ costructuredArrowOfUnder S Q K s :=
  CostructuredArrow.homMk f
    (((Localization.isoOfHom Q S s.hom s.prop).comp_inv_eq (f := Q.map f) (g := j.hom)).mpr hf)

/-- The coprojections of a cocone on the diagram of a left Kan extension at `Q(K)` are compatible
with the comparison of indices. -/
private lemma cocone_ι_app_comp (Φ : D ⥤ E) (K : D)
    (σ : Cocone (CostructuredArrow.proj Q (Q.obj K) ⋙ Φ)) {s : S.Under ⊤ K}
    {j : CostructuredArrow Q (Q.obj K)} (f : j.left ⟶ s.right)
    (hf : Q.map f = j.hom ≫ Q.map s.hom) :
    Φ.map f ≫ σ.ι.app (costructuredArrowOfUnder S Q K s) = σ.ι.app j :=
  σ.w (costructuredArrowHomMk S Q K f hf)

variable [S.HasLeftCalculusOfFractions] {Φ : D ⥤ E} {RΦ : SD ⥤ E}

/-- A value of the right derived functor of `Φ` at `K` in Deligne's sense (Stacks 05S9(1)),
identified with `RΦ(Q(K))` compatibly with the coprojections of the ind-object, exhibits `RΦ`
as a pointwise left Kan extension of `Φ` along `Q` at `Q(K)`. -/
private noncomputable def isPointwiseLeftKanExtensionAt_of_isRightDerivedValueAt
    (β : Φ ⟶ Q ⋙ RΦ) (K : D)
    (c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙ CategoryTheory.Under.forget K ⋙ Φ))
    (s₀ : S.Under ⊤ K) (r : c.pt ⟶ Φ.obj s₀.right) (hr : r ≫ c.ι.app s₀ = 𝟙 c.pt)
    (hb : ∀ s : S.Under ⊤ K, ∃ (s' : S.Under ⊤ K) (u : s ⟶ s') (v : s₀ ⟶ s'),
      Φ.map u.right = c.ι.app s ≫ r ≫ Φ.map v.right)
    (e : c.pt ≅ RΦ.obj (Q.obj K))
    (he : ∀ s : S.Under ⊤ K, c.ι.app s ≫ e.hom ≫ RΦ.map (Q.map s.hom) = β.app s.right) :
    (LeftExtension.mk RΦ β).IsPointwiseLeftKanExtensionAt (Q.obj K) := by
  have hι : ∀ s : S.Under ⊤ K,
      ((LeftExtension.mk RΦ β).coconeAt (Q.obj K)).ι.app (costructuredArrowOfUnder S Q K s) =
        c.ι.app s ≫ e.hom := fun s =>
    ((RΦ.mapIso (Localization.isoOfHom Q S s.hom s.prop)).comp_inv_eq
      (f := β.app s.right) (g := c.ι.app s ≫ e.hom)).mpr ((he s).symm.trans (assoc _ _ _).symm)
  have hmap : ∀ {s s' : S.Under ⊤ K} (u : s ⟶ s'),
      Q.map u.right = (costructuredArrowOfUnder S Q K s).hom ≫ Q.map s'.hom := fun {s s'} u =>
    ((Localization.isoOfHom Q S s.hom s.prop).eq_inv_comp
      (f := Q.map s'.hom) (g := Q.map u.right)).mpr (by
        rw [Localization.isoOfHom_hom, ← Q.map_comp, MorphismProperty.Under.w u])
  refine
    { desc := fun σ => e.inv ≫ r ≫ σ.ι.app (costructuredArrowOfUnder S Q K s₀)
      fac := ?_
      uniq := ?_ }
  · intro σ j
    have hkey : ∀ s : S.Under ⊤ K,
        c.ι.app s ≫ r ≫ σ.ι.app (costructuredArrowOfUnder S Q K s₀) =
          σ.ι.app (costructuredArrowOfUnder S Q K s) := by
      intro s
      obtain ⟨s', u, v, hfac⟩ := hb s
      exact comp_eq_of_eq_comp'
        (cocone_ι_app_comp S Q Φ K σ (s := s') (j := costructuredArrowOfUnder S Q K s₀)
          v.right (hmap v)) hfac
        (cocone_ι_app_comp S Q Φ K σ (s := s') (j := costructuredArrowOfUnder S Q K s)
          u.right (hmap u))
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q S j.hom
    have hf : Q.map φ.f =
        j.hom ≫ Q.map (MorphismProperty.Under.mk ⊤ φ.s φ.hs).hom := by
      rw [hφ]
      exact (MorphismProperty.LeftFraction.map_comp_map_s φ Q
        (Localization.inverts Q S)).symm
    exact comp_comp_eq_of_comp_eq_id'
      (cocone_ι_app_comp S Q Φ K ((LeftExtension.mk RΦ β).coconeAt (Q.obj K))
        (s := MorphismProperty.Under.mk ⊤ φ.s φ.hs) (j := j) φ.f hf)
      (hι (MorphismProperty.Under.mk ⊤ φ.s φ.hs)) e.hom_inv_id
      (hkey (MorphismProperty.Under.mk ⊤ φ.s φ.hs))
      (cocone_ι_app_comp S Q Φ K σ (s := MorphismProperty.Under.mk ⊤ φ.s φ.hs) (j := j) φ.f hf)
  · intro σ m hm
    have h₀ := hm (costructuredArrowOfUnder S Q K s₀)
    rw [hι s₀] at h₀
    exact eq_comp_comp_of_comp_comp_eq' h₀ hr e.inv_hom_id

/-- **A right derived functor in Deligne's sense is one in Mathlib's sense.** If for every object
`K` the ind-object `(s : K ⟶ I) ↦ Φ(I)`, `s ∈ S`, is essentially constant with value `RΦ(Q(K))`
and coprojections induced by `β` (Stacks 05S9(1)), then `β` makes `RΦ` a right derived functor
of `Φ`, i.e. a left Kan extension along the localization functor `Q`. -/
private lemma isRightDerivedFunctor_of_forall_isRightDerivedValueAt (β : Φ ⟶ Q ⋙ RΦ)
    (h : ∀ K : D, ∃ (c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙
          CategoryTheory.Under.forget K ⋙ Φ))
        (_ : Φ.IsRightDerivedValueAt S K c) (e : c.pt ≅ RΦ.obj (Q.obj K)),
        ∀ s : S.Under ⊤ K, c.ι.app s ≫ e.hom ≫ RΦ.map (Q.map s.hom) = β.app s.right) :
    RΦ.IsRightDerivedFunctor β S := by
  have := Localization.essSurj Q S
  have hp : ∀ Y : SD, Nonempty ((LeftExtension.mk RΦ β).IsPointwiseLeftKanExtensionAt Y) := by
    intro Y
    obtain ⟨c, hc, e, he⟩ := h (Q.objPreimage Y)
    obtain ⟨s₀, r, hr, hb⟩ := hc
    exact ⟨(LeftExtension.mk RΦ β).isPointwiseLeftKanExtensionAtEquivOfIso'
      (Q.objObjPreimageIso Y)
      (isPointwiseLeftKanExtensionAt_of_isRightDerivedValueAt S Q β _ c s₀ r hr hb e he)⟩
  exact ⟨Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
    (fun Y => (hp Y).some)⟩

end

end Right

/-- **Stacks 09T5**: the derived functors of an adjoint pair are adjoint. Let `F : 𝒟 ⥤ 𝒟'` be
right adjoint to `G : 𝒟' ⥤ 𝒟`, let `S`, `S'` be classes of morphisms of `𝒟`, `𝒟'` admitting
left, resp. right fractions, and let `Q : 𝒟 ⥤ S⁻¹𝒟`, `Q' : 𝒟' ⥤ (S')⁻¹𝒟'` be localization
functors. Let `RF : S⁻¹𝒟 ⥤ (S')⁻¹𝒟'` with `β : F ⋙ Q' ⟶ Q ⋙ RF` be the right derived functor
of `Q' ∘ F`, in the sense that for every object `K` of `𝒟` the ind-object
`(s : K ⟶ I) ↦ Q'(F(I))` is essentially constant with value `RF(Q(K))` and coprojections
induced by `β` (Stacks 05S9), and let `LG : (S')⁻¹𝒟' ⥤ S⁻¹𝒟` with `α : Q' ⋙ LG ⟶ G ⋙ Q` be
the left derived functor of `Q ∘ G`, in the dual sense. Then `LG` is left adjoint to `RF`, by an
adjunction whose unit and counit are compatible with `α`, `β` and the adjunction between `F`
and `G`. -/
@[stacks 09T5]
theorem exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
    {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
    {SD : Type u₃} [Category.{v₃} SD] {SD' : Type u₄} [Category.{v₄} SD']
    {F : D ⥤ D'} {G : D' ⥤ D} (adj : G ⊣ F)
    (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    (Q : D ⥤ SD) [Q.IsLocalization S] (Q' : D' ⥤ SD') [Q'.IsLocalization S']
    (RF : SD ⥤ SD') (β : F ⋙ Q' ⟶ Q ⋙ RF)
    (LG : SD' ⥤ SD) (α : Q' ⋙ LG ⟶ G ⋙ Q)
    (hRF : ∀ K : D, ∃ (c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙
          Under.forget K ⋙ F ⋙ Q'))
        (_ : (F ⋙ Q').IsRightDerivedValueAt S K c) (e : c.pt ≅ RF.obj (Q.obj K)),
        ∀ s : S.Under ⊤ K, c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right)
    (hLG : ∀ M : D', ∃ (d : Cone (MorphismProperty.Over.forget S' ⊤ M ⋙
          Over.forget M ⋙ G ⋙ Q))
        (_ : (G ⋙ Q).IsLeftDerivedValueAt S' M d) (e : LG.obj (Q'.obj M) ≅ d.pt),
        ∀ t : S'.Over ⊤ M, LG.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left) :
    ∃ adj' : LG ⊣ RF,
      (∀ M : D', adj'.unit.app (Q'.obj M) ≫ RF.map (α.app M) =
          Q'.map (adj.unit.app M) ≫ β.app (G.obj M)) ∧
        (∀ K : D, LG.map (β.app K) ≫ adj'.counit.app (Q.obj K) =
          α.app (F.obj K) ≫ Q.map (adj.counit.app K)) := by
  have h₁ : LG.IsLeftDerivedFunctor α S' :=
    isLeftDerivedFunctor_of_forall_isLeftDerivedValueAt S' Q' α hLG
  have h₂ : RF.IsRightDerivedFunctor β S :=
    isRightDerivedFunctor_of_forall_isRightDerivedValueAt S Q β hRF
  have h₃ : (LG ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator Q' LG RF).inv ≫ whiskerRight α RF) S' := by
    refine isLeftDerivedFunctor_of_forall_isLeftDerivedValueAt S' Q' _ fun M => ?_
    obtain ⟨d, hd, e, he⟩ := hLG M
    refine ⟨RF.mapCone d, isLeftDerivedValueAt_mapCone S' M hd RF, RF.mapIso e, fun t => ?_⟩
    have h : RF.map (LG.map (Q'.map t.hom)) ≫ RF.map e.hom ≫ RF.map (d.π.app t) =
        RF.map (α.app t.left) := (map_eq_map_comp_map_comp_map (he t).symm RF).symm
    simp only [Functor.comp_map, Functor.mapIso_hom, Functor.mapCone_π_app, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_inv_app, id_comp]
    exact h
  have h₄ : (RF ⋙ LG).IsRightDerivedFunctor
      (whiskerRight β LG ≫ (Functor.associator Q RF LG).hom) S := by
    refine isRightDerivedFunctor_of_forall_isRightDerivedValueAt S Q _ fun K => ?_
    obtain ⟨c, hc, e, he⟩ := hRF K
    refine ⟨LG.mapCocone c, isRightDerivedValueAt_mapCocone S K hc LG, LG.mapIso e, fun s => ?_⟩
    have h : LG.map (c.ι.app s) ≫ LG.map e.hom ≫ LG.map (RF.map (Q.map s.hom)) =
        LG.map (β.app s.right) := (map_eq_map_comp_map_comp_map (he s).symm LG).symm
    simp only [Functor.comp_map, Functor.mapIso_hom, Functor.mapCocone_ι_app, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, comp_id]
    exact h
  refine ⟨adj.derived S' S α β, fun M => ?_, fun K => ?_⟩
  · exact adj.derivedη_fac_app S' α β M
  · exact adj.derivedε_fac_app S α β K

end Global

end CategoryTheory.Adjunction

end
