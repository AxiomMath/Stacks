module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointSpaceSober
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecializationTranscendenceDegree
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober

/-!
# From the topological conditions back to dimension zero, over a field

Stacks 0ACA compares five conditions on an algebraic space `X` locally of finite type over a
field `k`: that `|X|` is finite, that `|X|` is discrete, that `dim(|X|) = 0`, that `dim(X) = 0`,
and that `X ⟶ Spec(k)` is locally quasi-finite.
`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverField.lean` proves the implications which
run *out of* the dimension condition. This file proves the implications which run back *into* it,
with no decency hypothesis: the source's transcendence-degree argument.

The argument is the one the source gives. Fix an étale scheme chart `a : U ⟶ X` and a nontrivial
specialization `u ⤳ u'` in `U`. The two points have the same image in `|X|`, because `|U| → |X|`
is continuous and the specialization relation on `|X|` is trivial, and therefore the same
transcendence degree over `k`, because the transcendence degree at a point of `X` is well defined
(Tag 04NM) and is read off any one chart. But along a nontrivial specialization in a scheme
locally of finite type over a field the transcendence degree drops strictly (Tag 0A21). So `U` has
no nontrivial specializations, is sober, and hence has Krull dimension at most zero; so has each
of its points, so has `X` at each of its points, and Tag 04NV turns that into local
quasi-finiteness.

## Main definitions

No new definitions are introduced.

## Main results

* `topologicalKrullDim_le_zero_of_specializes_imp_eq`: a sober topological space whose
  specialization relation is trivial has Krull dimension at most zero.
* `AlgebraicGeometry.eq_of_specializes_of_trdeg_eq`: two points of a scheme locally of finite
  type over a field which lie in a specialization relation and have the same residue-field
  transcendence degree are equal.
* `AlgebraicGeometry.Space.dimension_le_zero_of_specializes_imp_eq` and
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_specializes_imp_eq`: an algebraic space
  locally of finite type over a field whose point space has trivial specialization relation has
  dimension at most zero, and is locally quasi-finite over the field.
* `AlgebraicGeometry.Space.dimension_le_zero_of_discreteTopology_points` is Stacks 0ACA,
  condition (2) implies condition (4).
* `AlgebraicGeometry.Space.tfae_discreteTopology_dimension_le_zero_isLocallyQuasiFinite` is the
  part of Stacks 0ACA which holds in general: conditions (2), (4) and (5) are equivalent with no
  separation hypothesis on `|X|`, no decency and no nonemptiness.
* `AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero` is Stacks
  0ACA, condition (3) implies condition (2), **for a `T₀` point space**; see the implementation
  notes for why that hypothesis cannot be dropped.

## Implementation notes

**The base must be the spectrum of a field here.** The implications of
`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverField.lean` use nothing about the base
beyond its underlying scheme having at most one point, and are stated under that weaker
hypothesis. The implications proved here are not like that: transcendence degree over the base is
what makes the argument run, and the input used,
`AlgebraicGeometry.lt_trdeg_of_specialization_of_ne`, is a statement about a scheme over the
spectrum of a field. So the base object of the site is taken to be presented by a field, as the
source presents it: `hk : k = AlgebraicGeometry.BigFppfOver.mk B S hS hκ σ` for a field `κ`
contained in the site with a structure morphism `σ` to `S`. A field-valued point `p` of a
presheaf presents its base this way with `hk := rfl`, since
`AlgebraicGeometry.Space.FieldValuedPoint.siteObject` is that object, which is how the
consumers in Tag 0ACK supply it.

**The source's condition (3) is not enough, and the counterexample is `𝔸¹/ℤ`.** The source
asserts that conditions (2), (3), (4) and (5) are equivalent for every algebraic space locally of
finite type over a field, and derives (3) ⟹ (4) from the observation that the images `x`, `x'` of
a nontrivial specialization `u ⤳ u'` in a chart are *distinct* points of `|X|`. Distinctness is
not enough: `dim(|X|) = 0` forbids a chain `closure {x'} ⊊ closure {x}` of irreducible closed
subsets, and two distinct points with `x ⤳ x'` give such a chain only when `|X|` is `T₀`. The
point space of an algebraic space need not be `T₀`. Take `X = 𝔸¹_k/ℤ` for a field `k` of
characteristic zero, the quotient of the affine line by the translation action of `ℤ`, which is
Stacks 02Z7: the action is free in the sense of Stacks 02Z3, so `X` is an algebraic space, and it
is locally of finite type over `k`. A `ℤ`-invariant open subscheme of `𝔸¹_k` is empty or
everything, because the complement of a nonempty one is a finite invariant set of closed points
while every orbit of a closed point is infinite.
So `|X|` carries the indiscrete topology on its infinitely many points: every nonempty closed
subset is the whole of `|X|`, so `dim(|X|) = 0`, while `|X|` is not discrete, `dim(X) = 1` and
`X ⟶ Spec(k)` is not locally quasi-finite. Condition (3) therefore implies the others only under
a hypothesis the source does not state, and the `T₀` hypothesis is carried explicitly here. No
such hypothesis is needed for condition (2): a discrete space is `T₁`, so its specialization
relation is trivial outright.

The hypothesis the argument really uses is that the specialization relation on `|X|` is trivial,
and the two results that carry it, `dimension_le_zero_of_specializes_imp_eq` and
`isLocallyQuasiFinite_of_specializes_imp_eq`, are stated with it. Both conditions (2) and
(3) + `T₀` are routed through them.

Sobriety of the chart is Mathlib's `QuasiSober` instance for schemes, and it is what turns
"no nontrivial specializations" into "Krull dimension at most zero": a `T₁` space need not have
dimension zero, as the cofinite topology on an infinite set shows.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 02Z3](https://stacks.math.columbia.edu/tag/02Z3)
* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-! ### Krull dimension zero and the specialization relation -/

/-- **A sober space with no nontrivial specializations has dimension at most zero.** Every
irreducible closed subset is the closure of a generic point, and an inclusion of two such
exhibits a specialization between the generic points, hence an equality.

Sobriety is needed: the cofinite topology on an infinite set is `T₁`, so has trivial
specialization relation, and its irreducible closed subsets are the singletons together with
the whole space, so it has dimension one. -/
theorem topologicalKrullDim_le_zero_of_specializes_imp_eq {T : Type*} [TopologicalSpace T]
    [QuasiSober T] (h : ∀ a b : T, a ⤳ b → a = b) : topologicalKrullDim T ≤ 0 := by
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
  intro Z Y hZY
  have hz : IsGenericPoint Z.2.genericPoint Z.1 := Z.2.isGenericPoint_genericPoint Z.3
  have hy : IsGenericPoint Y.2.genericPoint Y.1 := Y.2.isGenericPoint_genericPoint Y.3
  have hcar : Y.carrier = Z.carrier := by
    rw [← hy.def, ← hz.def, h _ _ (hy.specializes (hZY hz.mem))]
  exact (IrreducibleCloseds.ext hcar).le

namespace AlgebraicGeometry

/-! ### The strict drop of the transcendence degree, as an equality criterion -/

/-- **Two points of a scheme over a field in a specialization relation with the same
transcendence degree coincide.** On a scheme locally of finite type over a field the
residue-field transcendence degree drops strictly along a nontrivial specialization
(`AlgebraicGeometry.lt_trdeg_of_specialization_of_ne`, Tag 0A21), so equality of the two
degrees forces the specialization to be trivial. -/
theorem eq_of_specializes_of_trdeg_eq {κ : Type u} [Field κ] {W : Scheme.{u}}
    (q : W ⟶ Spec (CommRingCat.of κ)) (hq : LocallyOfFiniteType q) {u u' : W} (huu : u ⤳ u')
    (hdeg :
      letI := (q.residueFieldMap u).hom.toAlgebra
      letI := (q.residueFieldMap u').hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg ((Spec (CommRingCat.of κ)).residueField (q u))
          (W.residueField u)) =
        Cardinal.toENat (Algebra.trdeg ((Spec (CommRingCat.of κ)).residueField (q u'))
          (W.residueField u'))) :
    u = u' := by
  by_contra hne
  have := hq
  exact absurd hdeg (ne_of_gt (lt_trdeg_of_specialization_of_ne q huu hne _ _
    (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom q u)
    (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom q u')))

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : BigFppfOver B S hS} {κ : Type u} [Field κ]

/-! ### No nontrivial specializations on a chart -/

/-- **A chart of an algebraic space with trivial specialization relation has trivial
specialization relation.** Two points of an étale scheme chart which lie in a specialization
relation have the same image in the point space of Tag 03BU, because that map is continuous
(Tag 03BX clause (2)); hence the same transcendence degree over the base field, because the
transcendence degree at a point of Tag 04NM is read off any one chart; hence are equal, by the
strict drop of Tag 0A21. -/
private theorem eq_of_specializes_chart
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (g : X ⟶ yoneda.obj (BigFppfOver.mk B S hS hκ σ)) (hg : IsLocallyOfFiniteType B S hS g)
    (hsp : ∀ x y : points B S hS X, x ⤳ y → x = y) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {u u' : (BigFppfOver.toScheme B S hS).obj U} (huu : u ⤳ u') : u = u' := by
  have := isMultiplicative_presheaf_etale B S hS
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (𝟙 (yoneda.obj (BigFppfOver.mk B S hS hκ σ))) :=
    MorphismProperty.id_mem _ _
  have hcomm : yoneda.map (yoneda.preimage (a ≫ g)) ≫
      𝟙 (yoneda.obj (BigFppfOver.mk B S hS hκ σ)) = a ≫ g := by
    rw [Category.comp_id, yoneda.map_preimage]
  have hlft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g))) :=
    hg U (BigFppfOver.mk B S hS hκ σ) a (𝟙 _) (yoneda.preimage (a ≫ g)) ha hb hcomm
  have key : ∀ (w : (BigFppfOver.toScheme B S hS).obj U) (r : ℕ∞),
      HasTranscendenceDegreeAt B S hS g
          (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm w)) r ↔
        let _ := (((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (a ≫ g))).residueFieldMap w).hom.toAlgebra
        Cardinal.toENat (Algebra.trdeg
            (((BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hκ σ)).residueField
              ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g)) w))
            (((BigFppfOver.toScheme B S hS).obj U).residueField w)) = r :=
    fun w r => hasTranscendenceDegreeAt_pointsMap_iff B S hS r g U
      (BigFppfOver.mk B S hS hκ σ) a (𝟙 _) (yoneda.preimage (a ≫ g)) ha hb hcomm w
  have hcont : Continuous (fun w : (BigFppfOver.toScheme B S hS).obj U =>
      pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm w)) :=
    (continuous_pointsMap B S hS a).comp (schemePointsHomeomorph B S hS U).symm.continuous
  have himg := hsp _ _ (huu.map hcont)
  exact eq_of_specializes_of_trdeg_eq
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ g))) hlft huu
    ((key u _).mp (himg ▸ (key u' _).mpr rfl))

/-! ### The dimension of a space with trivial specialization relation -/

/-- **An algebraic space over a field whose point space has trivial specialization relation has
dimension at most zero.** The dimension of Tag 04N5 at a point is the local dimension of an
étale scheme chart above it, that chart has no nontrivial specializations by
`AlgebraicGeometry.Space.eq_of_specializes_chart`, and a sober space with no nontrivial
specializations has Krull dimension at most zero.

The source states condition (4) as `dim(X) = 0`; the dimension of Tag 04N6 is a supremum in
`WithBot ℕ∞`, so the empty space has dimension `⊥`, and the unconditional form is the
inequality. -/
theorem dimension_le_zero_of_specializes_imp_eq (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g)
    (hsp : ∀ x y : points B S hS X, x ⤳ y → x = y) :
    dimension B S hS X hX ≤ 0 := by
  subst hk
  refine iSup_le fun x => ?_
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp]
  refine le_trans ((topologicalKrullDimAt_isLeast _ _).2
    ⟨Set.univ, Set.mem_univ _, isOpen_univ, rfl⟩) (le_trans
      (topologicalKrullDim_subspace_le _ Set.univ) ?_)
  exact topologicalKrullDim_le_zero_of_specializes_imp_eq
    fun _ _ huu => eq_of_specializes_chart B S hS hκ σ g hg hsp U a ha huu

/-- **An algebraic space over a field whose point space has trivial specialization relation is
locally quasi-finite over the field.** Combine
`AlgebraicGeometry.Space.dimension_le_zero_of_specializes_imp_eq` with Stacks 0ACA, conditions
(4) and (5) equivalent, which is available over any base whose scheme has at most one point. -/
theorem isLocallyQuasiFinite_of_specializes_imp_eq (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g)
    (hsp : ∀ x y : points B S hS X, x ⤳ y → x = y) :
    IsLocallyQuasiFinite B S hS g := by
  have hdim := dimension_le_zero_of_specializes_imp_eq B S hS hX hκ σ hk g hg hsp
  subst hk
  exact (isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX
    (inferInstanceAs (Subsingleton (Spec (CommRingCat.of κ)))) g hg).mpr hdim

/-! ### Conditions (2) and (3) imply condition (4) -/

/-- **Stacks 0ACA, condition (2) implies condition (4).** An algebraic space locally of finite
type over a field whose point space of Tag 03BU is discrete has dimension at most zero.

A discrete space is `T₁`, so its specialization relation is trivial, which is the hypothesis of
`AlgebraicGeometry.Space.dimension_le_zero_of_specializes_imp_eq`. The source states condition
(4) as `dim(X) = 0`; the empty space is discrete and has dimension `⊥`, so the unconditional
form is the inequality. -/
@[stacks 0ACA "unconditional part (2) <=> (4) <=> (5): the arrow (2) => (4), dim <= 0 form"]
theorem dimension_le_zero_of_discreteTopology_points (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g)
    (hdisc : DiscreteTopology (points B S hS X)) :
    dimension B S hS X hX ≤ 0 :=
  have := hdisc
  dimension_le_zero_of_specializes_imp_eq B S hS hX hκ σ hk g hg
    fun _ _ huu => huu.eq

/-- **Stacks 0ACA, condition (2) implies condition (5).** An algebraic space locally of finite
type over a field whose point space of Tag 03BU is discrete is locally quasi-finite over the
field. -/
@[stacks 0ACA "unconditional part (2) <=> (4) <=> (5): the arrow (2) => (5)"]
theorem isLocallyQuasiFinite_of_discreteTopology_points (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g)
    (hdisc : DiscreteTopology (points B S hS X)) :
    IsLocallyQuasiFinite B S hS g :=
  have := hdisc
  isLocallyQuasiFinite_of_specializes_imp_eq B S hS hX hκ σ hk g hg
    fun _ _ huu => huu.eq

/-! ### The unconditional equivalence of conditions (2), (4) and (5) -/

/-- **Stacks 0ACA, conditions (2), (4) and (5) are equivalent.** For an algebraic space locally
of finite type over a field, with *no* further hypothesis: the point space of Tag 03BU is
discrete exactly when the space has dimension at most zero, exactly when the structure morphism
is locally quasi-finite.

This is the part of the tag that holds in general. It carries no separation hypothesis on `|X|`,
no decency and no nonemptiness: the three arrows it is assembled from — `(2) ⟹ (4)` here,
`(4) ⟹ (5)` by `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero` and
`(5) ⟹ (2)` by
`AlgebraicGeometry.Space.discreteTopology_points_of_isLocallyQuasiFinite` — carry none either.
Condition (3) is deliberately absent: the arrow out of it is false in this generality, and is
`AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero` below.

The source writes conditions (3) and (4) with `= 0`. The dimension of Tag 04N6 is a supremum in
`WithBot ℕ∞`, so the empty space has dimension `⊥` while being discrete and locally quasi-finite
over any base; the faithful *unconditional* form of condition (4) is therefore the inequality.
The `= 0` form, which needs `|X|` to have a point, is
`FiniteTypeOverField.tfae_discretePoints_zeroDimension_locallyQuasiFinite`. -/
@[stacks 0ACA "unconditional part: (2) <=> (4) <=> (5), no T0Space, no decency, no nonemptiness",
  ega "IV 4.1.2" "(ii), case Y = Spec(κ)"]
theorem tfae_discreteTopology_dimension_le_zero_isLocallyQuasiFinite
    (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g) :
    [DiscreteTopology (points B S hS X), dimension B S hS X hX ≤ 0,
      IsLocallyQuasiFinite B S hS g].TFAE := by
  subst hk
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.mk B S hS hκ σ)) := by
    rw [BigFppfOver.toScheme_obj_mk]
    infer_instance
  tfae_have 1 → 2 := dimension_le_zero_of_discreteTopology_points B S hS hX hκ σ rfl g hg
  tfae_have 2 → 3 := (isLocallyQuasiFinite_iff_dimension_le_zero B S hS hX hsub g hg).mpr
  tfae_have 3 → 1 := discreteTopology_points_of_isLocallyQuasiFinite B S hS hX hsub g
  tfae_finish

/-! ### Condition (3) implies condition (2), for a `T₀` point space -/

/-- **Condition (3) of Stacks 0ACA implies condition (2), for a `T₀` point space.** An algebraic
space locally of finite type over a field whose point space of Tag 03BU is `T₀` and has Krull
dimension zero has discrete point space.

In a `T₀` space a nontrivial specialization `x ⤳ x'` gives the chain
`closure {x'} ⊊ closure {x}` of irreducible closed subsets, so dimension zero makes the
specialization relation trivial; then
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_specializes_imp_eq` and Stacks 0ACA, condition
(5) implies condition (2), close the loop.

**The `T₀` hypothesis is not in the source and cannot be dropped**, so the source's
unrestricted claim is false: the point space of `𝔸¹_k/ℤ` is the indiscrete topology on an
infinite set, so it has Krull dimension zero without being discrete. See the implementation
notes of this file. This is the strongest true form of the implication; with `T₀` discharged
for a decent space it is
`discreteTopology_points_of_topologicalKrullDim_eq_zero_of_isDecentSpace`. -/
@[stacks 0ACA "corrected part (3) => (2), the sharp form: |X| Kolmogorov"]
theorem discreteTopology_points_of_topologicalKrullDim_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g) (ht0 : T0Space (points B S hS X))
    (hdim : topologicalKrullDim (points B S hS X) = (0 : WithBot ℕ∞)) :
    DiscreteTopology (points B S hS X) := by
  have := ht0
  have hsp : ∀ x y : points B S hS X, x ⤳ y → x = y := fun _ _ hxy =>
    Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero
      hdim.le hxy
  subst hk
  exact discreteTopology_points_of_isLocallyQuasiFinite B S hS hX
    (inferInstanceAs (Subsingleton (Spec (CommRingCat.of κ)))) g
    (isLocallyQuasiFinite_of_specializes_imp_eq B S hS hX hκ σ rfl g hg hsp)

/-- **Stacks 0ACA, condition (3) implies condition (2) for a decent space.** A decent algebraic
space locally of finite type over a field whose point space of Tag 03BU has Krull dimension
zero has discrete point space.

The point space of a decent algebraic space is Kolmogorov by Stacks 03K3, which discharges the
`T₀` hypothesis of
`AlgebraicGeometry.Space.discreteTopology_points_of_topologicalKrullDim_eq_zero`. -/
@[stacks 0ACA "corrected part (3) => (2): decency gives the Kolmogorov hypothesis, by 03K3"]
theorem discreteTopology_points_of_topologicalKrullDim_eq_zero_of_isDecentSpace
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hκ : B.Contains (Spec (CommRingCat.of κ))) (σ : Spec (CommRingCat.of κ) ⟶ S)
    (hk : k = BigFppfOver.mk B S hS hκ σ) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g)
    (hdim : topologicalKrullDim (points B S hS X) = (0 : WithBot ℕ∞)) :
    DiscreteTopology (points B S hS X) :=
  discreteTopology_points_of_topologicalKrullDim_eq_zero B S hS hX hκ σ hk g hg
    (t0Space_points_of_isDecentSpace B S hS hX hdec) hdim

end Space

end AlgebraicGeometry

end
