module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.QuotientSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartQuotient

/-!
# Smashing a morphism down to a modification away from a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`,
let `T ⊆ |X|` be a closed subset and let `f : X' ⟶ X` be a morphism of algebraic spaces over
`S` which is locally of finite type. Write `U ⊆ X` for the open subspace with `|U| = |X| ∖ T`
and `U' = f⁻¹U ⊆ X'`.

**Stacks 0AR9** says that if `X` is locally Noetherian and `f` is étale outside of `T`, then
`f` factors as `X' ⟶ X'' ⟶ X` with

1. `X'' ⟶ X` locally of finite type,
2. `X'' ⟶ X` an isomorphism over `U`, and
3. `X'_{/T} ⟶ X''_{/T}` an isomorphism on the formal completions along the inverse images
   of `T`.

The source builds `X''` as the quotient `X'/R` of an étale equivalence relation `R` on `X'`
over `X`, obtained by glueing `X'` and `U' ×_U U'` along the open subspace `U'`. This file
carries out the second half of that proof: it takes the relation `R` as a hypothesis and derives
the three conclusions from it. The relation itself is constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.GluedDiagonalRelation`, and Stacks 0AR9 is assembled from
both in `StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleOutsideFactorization`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_quotientSheafToBase`: conclusion (1).
  The structure morphism `X'/R ⟶ X` of the quotient sheaf of **Stacks 044J** is locally of
  finite type as soon as `X' ⟶ X` is. This needs nothing about the relation at all: the
  quotient map `X' ⟶ X'/R` is a surjection of fppf sheaves for every pre-relation, and local
  finite type descends along such a morphism by **Stacks 06NR**.
* `AlgebraicGeometry.FormalSpace.isIso_pullback_snd_of_isKernelPair_baseChange`: conclusion
  (2), granted that the base change of the relation to an open subspace `W₀ ⊆ X` is the kernel
  pair of the projection `X' ×_X W₀ ⟶ W₀` and that this projection is a surjection of fppf
  sheaves.
* `AlgebraicGeometry.FormalSpace.isIso_completionSheafMap_toQuotientSheaf`: conclusion (3),
  granted that every arrow of the relation lying over `T` is degenerate.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_of_isEtaleEquivalenceRelation`:
  the three conclusions together, packaged as a finite-type modification of `X` outside `U` in
  the sense of **Stacks 0AS2** together with a morphism from `X'` over `X` whose completion map
  is an isomorphism. This is the shape **Stacks 0AR5** consumes.

## Implementation notes

### What is assumed about the relation, and why

The relation is carried as a pre-relation `j : R ⟶ X' ×_X X'` of **Stacks 043C** in the slice
of presheaves over `X`, with `X'` the object presheaf; `X''` is its quotient sheaf `X'/R` of
Stacks 044J and `X'' ⟶ X` is the canonical morphism to the base. Algebraicity of `X''` is
**Stacks 02WW** in the form this library carries it,
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isAlgebraicSpace`, whose hypotheses
— that `j` be an equivalence relation and that its source and target maps be representable and
étale — are the hypotheses carried here. Representability by schemes is more than the source
asks of a relation between algebraic spaces; it is what the library's Stacks 02WW requires.

Three further properties of `R` are hypotheses, one group for each conclusion that needs them:

* nothing, for conclusion (1);
* that the base change of `j` to `U` is the kernel pair of `U' ⟶ U`, and that `U' ⟶ U` is a
  surjection of fppf sheaves, for conclusion (2);
* that every section of `R` whose point-set image lies over `T` has equal source and target,
  for conclusion (3).

All three hold for the relation the source constructs: over `U` it is `U' ×_U U'`, the full
kernel pair of the surjective étale `U' ⟶ U` — surjective because the source first replaces
`X'` by `X' ⨿ U` — and over `T` only the copy of `X'` survives, which is the source's "by our
choice of `R` the completion of `R` along the preimage of `T` agrees with that of `X'`". None
of the three is a restatement of a conclusion: they are statements about `R`, and the
conclusions are statements about `X''`.

The construction of `R` is not carried out here but in
`StacksFrontier.AlgebraicGeometry.Spaces.GluedDiagonalRelation`, as the fppf sheafification inside
`X' ×_X X'` of the union of the diagonal and of the part over `U`; it is an algebraic space by
the open-covering criterion **Stacks 02WR**, and its two projections are étale but not
representable by schemes, so the algebraicity of its quotient is condition (1) of **Stacks
04S6** rather than the library's Stacks 02WW. The unconditional statement of Stacks 0AR9 is
`AlgebraicGeometry.FormalSpace.exists_factorization_of_isEtale_openComplementRestriction`.

### How each conclusion is obtained

Conclusion (1) is `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp_of_locallySurjective`,
the local-finite-type clause of Stacks 06NR, applied to `X' ⟶ X'/R ⟶ X`; the quotient map is a
surjection of fppf sheaves by
`AlgebraicGeometry.Space.isLocallySurjective_toQuotientSheaf`.

Conclusion (2) runs **Stacks 0DTF**,
`AlgebraicGeometry.Space.quotientSheaf_isPullback_baseChange`, which exhibits
`(X' ×_X W₀)/(R ×_X W₀) ⟶ W₀` as the base change of `X'/R ⟶ X` along `W₀ ⟶ X`. Its three
comparison morphisms come as an existential, so they are pinned down by the uniqueness of
descent out of a quotient sheaf: the comparison to `X` is the canonical morphism to the base,
and the comparison to `W₀` is the descent of `U' ⟶ U`, which is an isomorphism by the
recognition criterion **Stacks 044M** in the form
`AlgebraicGeometry.Space.isIso_quotientSheafDesc_of_isPullback`. Transporting that along the
cartesian square gives the base change of `X'' ⟶ X` to `W₀`, which is how
`AlgebraicGeometry.Space.IsModification` records "an isomorphism over `W₀`".

Conclusion (3) is the local-bijectivity criterion
`AlgebraicGeometry.FormalSpace.isIso_completionSheafMap_of_isLocallyBijective` for the
completion of **Stacks 0AMC**, applied to the quotient map. Local surjectivity of the induced
map of completion subfunctors is local surjectivity of the quotient map together with the fact
that a local lift of a section with point-set image in `T` automatically has point-set image in
the inverse image of `T`. Local injectivity is **Stacks 046O**,
`AlgebraicGeometry.Space.toQuotientSheaf_eq_iff_locally_related`: two sections of `X'` with the
same image in `X''` are, on an fppf covering, the source and the target of a section of `R`,
and that section lies over `T` because the sections do, so the degeneracy hypothesis makes them
equal there.

### Universes

`AlgebraicGeometry.Space.completionSheaf` lands one universe above the value universe of its
argument, so conclusion (3) is an isomorphism of sheaves of `Type (u + 1)`; nothing else in the
file leaves `Type u`.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044M](https://stacks.math.columbia.edu/tag/044M)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0AR6](https://stacks.math.columbia.edu/tag/0AR6)
* [Stacks Project, Tag 0AR8](https://stacks.math.columbia.edu/tag/0AR8)
* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 0DTF](https://stacks.math.columbia.edu/tag/0DTF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over X}

/-! ### Conclusion (1): the quotient is locally of finite type over the base -/

/-- **Conclusion (1) of Stacks 0AR9.** The structure morphism `X'/R ⟶ X` of the quotient sheaf
of a pre-relation on `X'` over `X` is locally of finite type as soon as `X' ⟶ X` is.

The quotient map `X' ⟶ X'/R` is a surjection of fppf sheaves for an arbitrary pre-relation, so
this is the local-finite-type clause of Stacks 06NR applied to `X' ⟶ X'/R ⟶ X`. No hypothesis
on the relation is needed. -/
theorem isLocallyOfFiniteType_quotientSheafToBase
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U.left)
    (j : Space.PreRelation R U)
    (hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf j).obj)
    (hUft : Space.IsLocallyOfFiniteType B S hS U.hom) :
    Space.IsLocallyOfFiniteType B S hS (Space.quotientSheafToBase hX.isSheaf j).hom := by
  refine Space.isLocallyOfFiniteType_of_comp_of_locallySurjective B S hS hU hQ hX
    (Space.toQuotientSheaf j) _ ?_ (Space.isLocallySurjective_toQuotientSheaf j)
  rwa [Space.toQuotientSheaf_quotientSheafToBase]

/-! ### Conclusion (2): the quotient is an isomorphism over the open subspace -/

/-- If one cartesian square over a cospan has an isomorphism for its second leg, then so does
the chosen fibre product of that cospan. -/
private theorem isIso_pullback_snd_of_isPullback {C : Type*} [Category C]
    {P F G Y : C} {fst : P ⟶ F} {snd : P ⟶ G} {f : F ⟶ Y} {g : G ⟶ Y}
    (h : IsPullback fst snd f g) [HasPullback f g] [IsIso snd] :
    IsIso (pullback.snd f g) := by
  have : IsIso (h.isoPullback.hom ≫ pullback.snd f g) := by
    rw [h.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left h.isoPullback.hom (pullback.snd f g)

/-- A morphism out of a quotient sheaf whose restriction to the object presheaf is a surjection
of fppf sheaves with kernel pair the given relation is an isomorphism.

This is the recognition criterion Stacks 044M in the form
`AlgebraicGeometry.Space.isIso_quotientSheafDesc_of_isPullback`, transported along the
uniqueness of descent out of a quotient sheaf. -/
private theorem isIso_of_isPullback_of_isLocallySurjective
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R' U' : Over Z}
    (j' : Space.PreRelation R' U')
    (A : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (d : Space.quotientSheaf j' ⟶ A) (k : U'.left ⟶ A.obj)
    (hd : Space.toQuotientSheaf j' ≫ d.hom = k)
    (hker : IsPullback j'.target.left j'.source.left k k)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) k) :
    IsIso d := by
  rw [Space.quotientSheafDesc_unique j' A k hker.w d hd]
  exact Space.isIso_quotientSheafDesc_of_isPullback j' A k hker hsurj

/-- **Conclusion (2) of Stacks 0AR9.** Let `j` be a pre-relation on `X'` over `X`, let
`W₀ ⊆ X` be a subfunctor which is an fppf sheaf, and let `g : X'/R ⟶ X` be a morphism out of
the quotient sheaf restricting to the structure morphism of `X'`. If the base change of `j`
along `W₀ ⟶ X` is the kernel pair of the projection `X' ×_X W₀ ⟶ W₀`, and that projection is a
surjection of fppf sheaves, then the base change of `g` to `W₀` is an isomorphism.

Stacks 0DTF identifies the quotient of the base-changed relation with the base change of the
quotient; the comparison morphism to `W₀` is the descent of `X' ×_X W₀ ⟶ W₀`, an isomorphism by
Stacks 044M, and the comparison morphism to `X` is `g`, both by uniqueness of descent. -/
theorem isIso_pullback_snd_of_isKernelPair_baseChange
    (hX : IsAlgebraicSpace B S hS X) (j : Space.PreRelation R U)
    (W₀ : Subfunctor X)
    (hW₀ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W₀.toFunctor)
    (g : Space.quotientSheaf j ⟶ Space.baseSheaf hX.isSheaf)
    (hg : Space.toQuotientSheaf j ≫ g.hom = U.hom)
    (hker : IsPullback
      (Space.baseChangedPreRelation j U.hom W₀.ι
        (Space.target_toBase_eq_source j)).val.target.left
      (Space.baseChangedPreRelation j U.hom W₀.ι
        (Space.target_toBase_eq_source j)).val.source.left
      (pullback.fst W₀.ι U.hom) (pullback.fst W₀.ι U.hom))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (pullback.fst W₀.ι U.hom)) :
    IsIso (pullback.snd g.hom W₀.ι) := by
  obtain ⟨qToX, q'ToX', q'ToQ, h1, h2, h3, hpb⟩ :=
    Space.quotientSheaf_isPullback_baseChange j hX.isSheaf hW₀ U.hom W₀.ι
      (Space.target_toBase_eq_source j)
  have hq : qToX = g :=
    (Space.quotientSheafDesc_unique j (Space.baseSheaf hX.isSheaf) U.hom
        (Space.target_toBase_eq_source j) qToX h1).trans
      (Space.quotientSheafDesc_unique j (Space.baseSheaf hX.isSheaf) U.hom
        (Space.target_toBase_eq_source j) g hg).symm
  have : IsIso q'ToX' :=
    isIso_of_isPullback_of_isLocallySurjective B S hS _ _ q'ToX' _ h2 hker hsurj
  have : IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map q'ToX') :=
    inferInstance
  rw [← hq]
  exact isIso_pullback_snd_of_isPullback
    (hpb.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)))

/-! ### Conclusion (3): the completions along the closed subset agree -/

/-- The morphism of completion subfunctors induced by the quotient map of a pre-relation is a
surjection of fppf sheaves.

The quotient map itself is one, and a local lift of a section with point-set image in the given
set of points has point-set image in its inverse image, these being the same condition. -/
theorem isLocallySurjective_completionMap_toQuotientSheaf
    (j : Space.PreRelation R U)
    (T' : Set (Space.points B S hS (Space.quotientSheaf j).obj)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS (Space.toQuotientSheaf j) T') where
  imageSieve_mem {V} y := by
    have := Space.isLocallySurjective_toQuotientSheaf j
    obtain ⟨⟨y⟩, hy⟩ := y
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) (Space.toQuotientSheaf j) y)
    rintro W g ⟨x, hx⟩
    refine ⟨⟨ULift.up x, ?_⟩, Subtype.ext (ULift.ext _ _ hx)⟩
    refine (hasImageIn_preimage_pointsMap_iff B S hS (Space.toQuotientSheaf j) T' W x).2 ?_
    rw [hx]
    exact (Space.completionSubfunctor B S hS (Space.quotientSheaf j).obj T').map g.op hy

/-- The morphism of completion subfunctors induced by the quotient map of a pre-equivalence
relation all of whose arrows lying over `T` are degenerate is locally injective for the fppf
topology.

Two sections of `X'` with the same image in `X'/R` are, on an fppf covering, the source and the
target of a section of `R` by Stacks 046O. That section lies over `T`, because the two sections
of `X'` have point-set image over `T` and the structure morphism of `R` factors through the
source map; so the degeneracy hypothesis identifies the two sections on that covering. -/
theorem isLocallyInjective_completionMap_toQuotientSheaf
    (j : Space.PreRelation R U) (hj : Space.IsPreEquivalenceRelation j)
    (T : Set (Space.points B S hS X)) (gh : (Space.quotientSheaf j).obj ⟶ X)
    (hgh : Space.toQuotientSheaf j ≫ gh = U.hom)
    (hdiag : ∀ (W : BigFppfOver B S hS) (r : R.left.obj (op W)),
      Space.HasImageIn B S hS X T W (R.hom.app (op W) r) →
        j.source.left.app (op W) r = j.target.left.app (op W) r) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS (Space.toQuotientSheaf j)
        (Space.pointsMap B S hS (Space.quotientSheaf j).obj gh ⁻¹' T)) where
  equalizerSieve_mem {V} x₁ x₂ hx := by
    obtain ⟨⟨a⟩, ha⟩ := x₁
    obtain ⟨⟨b⟩, hb⟩ := x₂
    have hab : (Space.toQuotientSheaf j).app V a = (Space.toQuotientSheaf j).app V b :=
      congrArg (fun z => z.1.down) hx
    obtain ⟨E, hE, hrel⟩ :=
      (Space.toQuotientSheaf_eq_iff_locally_related j hj V.unop a b).1 hab
    have h1 : Space.HasImageIn B S hS X T V.unop (U.hom.app V a) := by
      have h2 := (hasImageIn_preimage_pointsMap_iff B S hS (Space.toQuotientSheaf j)
        (Space.pointsMap B S hS (Space.quotientSheaf j).obj gh ⁻¹' T) V.unop a).1 ha
      have h3 := (hasImageIn_preimage_pointsMap_iff B S hS gh T V.unop
        ((Space.toQuotientSheaf j).app V a)).1 h2
      have he : gh.app V ((Space.toQuotientSheaf j).app V a) = U.hom.app V a := by
        simpa [ConcreteCategory.comp_apply] using congrArg (fun f => f.app V a) hgh
      rwa [he] at h3
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Space.fppf_hypercover_sieve_mem hS V.unop E hE)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨r, hra, hrb⟩ := hrel i
    have h4 : Space.HasImageIn B S hS X T (E.X i) (X.map (E.f i).op (U.hom.app V a)) :=
      (Space.completionSubfunctor B S hS X T).map (E.f i).op h1
    have hR : R.hom.app (op (E.X i)) r = X.map (E.f i).op (U.hom.app V a) := by
      have hw : U.hom.app (op (E.X i)) (j.source.left.app (op (E.X i)) r) =
          R.hom.app (op (E.X i)) r := by
        simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
          congrArg (fun f => f.app (op (E.X i)) r) (Over.w j.source)
      rw [← hw, ← hra, NatTrans.naturality_apply]
    exact Subtype.ext (ULift.ext _ _ (hra.trans ((hdiag (E.X i) r (hR ▸ h4)).trans hrb.symm)))

/-- **Conclusion (3) of Stacks 0AR9.** Let `j` be a pre-equivalence relation on `X'` over `X`
and let `g : X'/R ⟶ X` restrict to the structure morphism of `X'`. If every section of `R`
whose point-set image lies over `T` has equal source and target, then the completion of the
quotient map along the inverse image of `T` is an isomorphism, that is
`X'_{/T} ⟶ (X'/R)_{/T}` is an isomorphism.

The quotient map is a surjection of fppf sheaves and, by the degeneracy hypothesis read through
Stacks 046O, locally injective on the completion subfunctors; a locally bijective morphism of
completion subfunctors sheafifies to an isomorphism of completions. -/
theorem isIso_completionSheafMap_toQuotientSheaf
    (j : Space.PreRelation R U) (hj : Space.IsPreEquivalenceRelation j)
    (T : Set (Space.points B S hS X)) (gh : (Space.quotientSheaf j).obj ⟶ X)
    (hgh : Space.toQuotientSheaf j ≫ gh = U.hom)
    (hdiag : ∀ (W : BigFppfOver B S hS) (r : R.left.obj (op W)),
      Space.HasImageIn B S hS X T W (R.hom.app (op W) r) →
        j.source.left.app (op W) r = j.target.left.app (op W) r) :
    IsIso (Space.completionSheafMap B S hS (Space.toQuotientSheaf j)
      (Space.pointsMap B S hS (Space.quotientSheaf j).obj gh ⁻¹' T)) := by
  have := isLocallySurjective_completionMap_toQuotientSheaf B S hS j
    (Space.pointsMap B S hS (Space.quotientSheaf j).obj gh ⁻¹' T)
  have := isLocallyInjective_completionMap_toQuotientSheaf B S hS j hj T gh hgh hdiag
  exact isIso_completionSheafMap_of_isLocallyBijective B S hS (Space.toQuotientSheaf j) _

/-! ### The three conclusions together -/

/-- **Stacks 0AR9, granted the relation.** Let `S` be a scheme contained in a big fppf site
`B`, let `X` be an algebraic space over `S`, let `T ⊆ |X|` be closed, and let `f : X' ⟶ X` be
a morphism of algebraic spaces over `S` which is locally of finite type. Let
`j : R ⟶ X' ×_X X'` be an equivalence relation on `X'` over `X` whose source and target maps
are representable and étale, and assume

* `hker`: the base change of `j` to the open subspace `U` with `|U| = |X| ∖ T` is the kernel
  pair of the projection `U' = X' ×_X U ⟶ U`,
* `hsurj`: that projection is a surjection of fppf sheaves,
* `hdiag`: every section of `R` whose point-set image lies over `T` has equal source and
  target.

Then `f` factors as `X' ⟶ X'' ⟶ X` with `X'' = X'/R` a finite-type modification of `X` outside
`U` in the sense of Stacks 0AS2 — so `X'' ⟶ X` is locally of finite type and an isomorphism
over `U` — and with `X'_{/T} ⟶ X''_{/T}` an isomorphism of completions.

The three hypotheses hold for the relation Stacks 0AR9 constructs by glueing `X'` and
`U' ×_U U'` along `U'`; that relation's projections are étale but not representable by schemes,
so the unconditional Stacks 0AR9,
`AlgebraicGeometry.FormalSpace.exists_factorization_of_isEtale_openComplementRestriction`, uses
conclusions (1) and (3) of this file directly, with conclusion (2) proved there for that relation,
rather than this packaging. -/
theorem exists_finiteTypeModification_of_isEtaleEquivalenceRelation
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U.left)
    (j : Space.PreRelation R U) [IsEquivalenceRelation j.target j.source]
    (ht : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.target.left)
    (hs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.source.left)
    (hUft : Space.IsLocallyOfFiniteType B S hS U.hom)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hker : IsPullback
      (Space.baseChangedPreRelation j U.hom
        (Space.openSubspaceOfPoints B S hS X Tᶜ).ι
        (Space.target_toBase_eq_source j)).val.target.left
      (Space.baseChangedPreRelation j U.hom
        (Space.openSubspaceOfPoints B S hS X Tᶜ).ι
        (Space.target_toBase_eq_source j)).val.source.left
      (pullback.fst (Space.openSubspaceOfPoints B S hS X Tᶜ).ι U.hom)
      (pullback.fst (Space.openSubspaceOfPoints B S hS X Tᶜ).ι U.hom))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (pullback.fst (Space.openSubspaceOfPoints B S hS X Tᶜ).ι U.hom))
    (hdiag : ∀ (W : BigFppfOver B S hS) (r : R.left.obj (op W)),
      Space.HasImageIn B S hS X T W (R.hom.app (op W) r) →
        j.source.left.app (op W) r = j.target.left.app (op W) r) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS X Tᶜ),
      ∃ φ : U.left ⟶ M.obj.left, φ ≫ M.obj.hom = U.hom ∧
        IsIso (Space.completionSheafMap B S hS φ
          (Space.pointsMap B S hS M.obj.left M.obj.hom ⁻¹' T)) := by
  have hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf j).obj :=
    Space.isAlgebraicSpace_quotientSheaf_of_isAlgebraicSpace B S hS j hU ht hs
  have hW₀ : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor :=
    (Space.isOpenSubspace_openSubspaceOfPoints B S hS hX Tᶜ hT.isOpen_compl).1.isSheaf
  refine ⟨⟨Over.mk (Space.quotientSheafToBase hX.isSheaf j).hom, ⟨⟨hQ, ?_⟩, ?_⟩⟩,
    Space.toQuotientSheaf j, Space.toQuotientSheaf_quotientSheafToBase hX.isSheaf j, ?_⟩
  · exact isIso_pullback_snd_of_isKernelPair_baseChange B S hS hX j _ hW₀
      (Space.quotientSheafToBase hX.isSheaf j)
      (Space.toQuotientSheaf_quotientSheafToBase hX.isSheaf j) hker hsurj
  · exact isLocallyOfFiniteType_quotientSheafToBase B S hS hX hU j hQ hUft
  · exact isIso_completionSheafMap_toQuotientSheaf B S hS j
      ((Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1
        inferInstance).2 T (Space.quotientSheafToBase hX.isSheaf j).hom
      (Space.toQuotientSheaf_quotientSheafToBase hX.isSheaf j) hdiag

end AlgebraicGeometry.FormalSpace

end
