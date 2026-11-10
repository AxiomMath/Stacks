module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Representability of a quotient sheaf (Stacks 044L, 044M)

A pre-relation has a *representable quotient* when its quotient sheaf is representable by a
scheme, and a *quotient representable by an algebraic space* when the quotient sheaf is an
algebraic space; the same words apply to a groupoid in algebraic spaces through the pre-relation
`(t, s)`. Stacks 044M gives the criterion that recognizes a given object as the quotient: a map
out of `U` that equalizes the relation, is surjective as a map of sheaves, and whose kernel pair
is covered by `R`.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.QuotientIsAlgebraicSpace` and
  `AlgebraicGeometry.Space.PreRelation.HasRepresentableQuotient`: **Stacks 044L**, the two
  properties for a pre-relation.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.QuotientIsAlgebraicSpace` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.HasRepresentableQuotient`: **Stacks 044L**, the
  same two properties for a groupoid in algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_toSheafify_of_hasSheafify`: the unit of
  sheafification of a set-valued presheaf is locally surjective.
* `AlgebraicGeometry.Space.isIso_quotientSheafDesc_of_isLocallySurjective`: **Stacks 044M**, the
  recognition criterion.

## Implementation notes

The four clauses of Stacks 044L are recorded as abbreviations, so that a consumer can use the
existing API for algebraic spaces and for representable functors directly rather than through a
wrapper. The groupoid clauses are the pre-relation clauses applied to
`AlgebraicGeometry.Space.groupoidPreRelation`.

Stacks 044M is stated for an arbitrary target *sheaf* rather than only for an algebraic space:
nothing in the argument uses algebraicity, and the source's statement is the case
`⟨M.obj, M.property.isSheaf⟩`. Surjectivity of a map of sheaves is local surjectivity of the
underlying map of presheaves, and the condition on `R` says that the comparison map from `R` to
the kernel pair of `U ⟶ M`, which is the presheaf fibre product, is locally surjective.

The conclusion is that the canonical map supplied by the universal property of the quotient
sheaf is an isomorphism, which is stronger than bare representability: it also pins down the
compatibility of the identification with `U ⟶ M`.

Mathlib's `CategoryTheory.Presheaf.isLocallySurjective_toSheafify` is stated for presheaves of
type `Type (max u v)` on a site of type `Type u` with morphisms in `Type v`; the big fppf site
has objects in `Type (u + 1)`, morphisms in `Type u` and `Type u`-valued presheaves, so that
instance does not apply and `isLocallySurjective_toSheafify_of_hasSheafify` re-derives it from
the sheafification adjunction, for any site with set-valued sheafification.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044L](https://stacks.math.columbia.edu/tag/044L)
* [Stacks Project, Tag 044M](https://stacks.math.columbia.edu/tag/044M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w z

/-- The unit of sheafification of a set-valued presheaf is locally surjective, for any site on
which set-valued sheafification exists. -/
theorem isLocallySurjective_toSheafify_of_hasSheafify
    {C : Type z} [Category.{w} C] (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (P : Cᵒᵖ ⥤ Type v) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  set G := Subfunctor.sheafify J (Subfunctor.range (toSheafify J P))
  have hFsheaf : Presheaf.IsSheaf J (sheafify J P) :=
    ((presheafToSheaf J (Type v)).obj P).property
  have hGsheaf : Presheaf.IsSheaf J G.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range (toSheafify J P)).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp hFsheaf))
  have hfac : Subfunctor.toRangeSheafify J (toSheafify J P) ≫ G.ι = toSheafify J P := by
    ext X x
    rfl
  rw [Subfunctor.eq_top_iff_isIso]
  have hsplit : IsSplitEpi G.ι := by
    refine IsSplitEpi.mk
      ⟨⟨sheafifyLift J (Subfunctor.toRangeSheafify J (toSheafify J P)) hGsheaf, ?_⟩⟩
    refine sheafify_hom_ext J _ _ hFsheaf ?_
    rw [Category.comp_id, ← Category.assoc, toSheafify_sheafifyLift, hfac]
  exact isIso_of_mono_of_isSplitEpi G.ι

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Stacks 044L.** A pre-relation has *quotient representable by an algebraic space* when its
quotient sheaf is an algebraic space. -/
@[stacks 044L "pre-relation: quotient representable by an algebraic space"]
noncomputable abbrev PreRelation.QuotientIsAlgebraicSpace (j : PreRelation R U) : Prop :=
  IsAlgebraicSpace site S hS (quotientSheaf j).obj

/-- **Stacks 044L.** A pre-relation has a *representable quotient* when its quotient sheaf is
represented by a scheme of the site. -/
@[stacks 044L "pre-relation: representable quotient", sga "3 IV 3.3.2" "(ii)"]
noncomputable abbrev PreRelation.HasRepresentableQuotient (j : PreRelation R U) : Prop :=
  (quotientSheaf j).obj.IsRepresentable

private lemma coequalizer_π_app_surjective {C : Type z} [Category.{v} C]
    {R U : Cᵒᵖ ⥤ Type v} (f₁ f₂ : R ⟶ U) (X : Cᵒᵖ) :
    Function.Surjective ((coequalizer.π f₁ f₂).app X) :=
  (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 inferInstance X)

private lemma comp_app_eq_map_of_app_eq {C : Type z} [Category.{v} C] {R P U : Cᵒᵖ ⥤ Type v}
    (g : R ⟶ P) (pr : P ⟶ U) {T V : C} (φ : V ⟶ T) {r : R.obj (Opposite.op V)}
    {s : P.obj (Opposite.op T)}
    (hr : g.app (Opposite.op V) r = P.map φ.op s) :
    (g ≫ pr).app (Opposite.op V) r = U.map φ.op (pr.app (Opposite.op T) s) := by
  simp [hr]

/-- If `R` surjects locally onto the kernel pair of `k : U ⟶ A`, then the map from the presheaf
coequalizer of `R ⇉ U` to `A` induced by `k` is locally injective. -/
private theorem isLocallyInjective_coequalizerDesc_of_isLocallySurjective
    {C : Type z} [Category.{v} C] (J : GrothendieckTopology C)
    {R U A : Cᵒᵖ ⥤ Type v} (f₁ f₂ : R ⟶ U) (k : U ⟶ A) (heq : f₁ ≫ k = f₂ ≫ k)
    (hR : Presheaf.IsLocallySurjective J (pullback.lift f₁ f₂ heq)) :
    Presheaf.IsLocallyInjective J (coequalizer.desc k heq) := by
  refine ⟨?_⟩
  rintro ⟨T⟩ x y hxy
  obtain ⟨a, rfl⟩ := coequalizer_π_app_surjective f₁ f₂ (Opposite.op T) x
  obtain ⟨b, rfl⟩ := coequalizer_π_app_surjective f₁ f₂ (Opposite.op T) y
  have hpk (c) : (coequalizer.desc k heq).app (Opposite.op T)
      ((coequalizer.π f₁ f₂).app (Opposite.op T) c) = k.app (Opposite.op T) c := by
    rw [← NatTrans.comp_app_apply, coequalizer.π_desc]
  let qₐ : yoneda.obj T ⟶ U := yonedaEquiv.symm a
  let qᵦ : yoneda.obj T ⟶ U := yonedaEquiv.symm b
  have hq : qₐ ≫ k = qᵦ ≫ k := by
    apply yonedaEquiv.injective
    change (qₐ ≫ k).app (Opposite.op T) (𝟙 T) = (qᵦ ≫ k).app (Opposite.op T) (𝟙 T)
    simpa [qₐ, qᵦ] using (hpk a).symm.trans (hxy.trans (hpk b))
  let s := (pullback.lift qₐ qᵦ hq).app (Opposite.op T) (𝟙 T)
  have hz (pr : pullback k k ⟶ U) (c) (h : pullback.lift qₐ qᵦ hq ≫ pr = yonedaEquiv.symm c) :
      pr.app (Opposite.op T) s = c := by
    simpa [s] using congrArg (fun η => η.app (Opposite.op T) (𝟙 T)) h
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J (pullback.lift f₁ f₂ heq) s)
  rintro V φ ⟨r, hr⟩
  rw [Presheaf.equalizerSieve_apply]
  have ht := comp_app_eq_map_of_app_eq _ (pullback.fst k k) φ hr
  have hsrc := comp_app_eq_map_of_app_eq _ (pullback.snd k k) φ hr
  rw [pullback.lift_fst, hz _ a (pullback.lift_fst qₐ qᵦ hq)] at ht
  rw [pullback.lift_snd, hz _ b (pullback.lift_snd qₐ qᵦ hq)] at hsrc
  rw [← NatTrans.naturality_apply (coequalizer.π f₁ f₂) φ.op a,
    ← NatTrans.naturality_apply (coequalizer.π f₁ f₂) φ.op b, ← ht, ← hsrc]
  simp only [← NatTrans.comp_app_apply]
  rw [coequalizer.condition]

/-- **Stacks 044M.** If `U ⟶ A` is a surjection of sheaves equalizing the relation, and `R`
surjects onto the kernel pair of `U ⟶ A`, then the canonical map from the quotient sheaf to `A`
is an isomorphism, so `A` represents the quotient `U/R`. -/
@[stacks 044M]
theorem isIso_quotientSheafDesc_of_isLocallySurjective (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (k : U.left ⟶ A.obj)
    (heq : j.target.left ≫ k = j.source.left ≫ k)
    (hU : Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS) k)
    (hR : Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS)
      (pullback.lift j.target.left j.source.left heq)) :
    IsIso (quotientSheafDesc j A k heq) := by
  let J := BigFppfOver.topology site S hS
  let π := coequalizer.π j.target.left j.source.left
  let p := coequalizer.desc k heq
  have : Presheaf.IsLocallySurjective J π :=
    Presheaf.isLocallySurjective_of_surjective J π (coequalizer_π_app_surjective _ _)
  have hπp : π ≫ p = k := coequalizer.π_desc k heq
  have hpSurj : Presheaf.IsLocallySurjective J p := by
    rwa [← Presheaf.comp_isLocallySurjective_iff J π p, hπp]
  let d := quotientSheafDesc j A k heq
  let η := toSheafify J (coequalizer j.target.left j.source.left)
  have hfac : η ≫ d.hom = p := by
    dsimp [η, d, quotientSheafDesc, p]
    exact toSheafify_sheafifyLift J _ _
  have : Presheaf.IsLocallySurjective J η := isLocallySurjective_toSheafify_of_hasSheafify _ _
  have : Presheaf.IsLocallyInjective J (η ≫ d.hom) := by
    rw [hfac]
    exact isLocallyInjective_coequalizerDesc_of_isLocallySurjective J _ _ k heq hR
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J η d.hom,
      (Presheaf.comp_isLocallySurjective_iff J η d.hom).mp (by rwa [hfac])⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open CategoryTheory

universe u

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Stacks 044L.** A groupoid in algebraic spaces has *quotient representable by an algebraic
space* when the quotient sheaf of its pre-relation `(t, s)` is an algebraic space. -/
@[stacks 044L "groupoid: quotient representable by an algebraic space", sga "3 IV 3.3.2" "(ii)"]
noncomputable abbrev QuotientIsAlgebraicSpace (G : GroupoidInAlgebraicSpaces site S hS B) :
    Prop :=
  (Space.groupoidPreRelation G).QuotientIsAlgebraicSpace

/-- **Stacks 044L.** A groupoid in algebraic spaces has a *representable quotient* when the
quotient sheaf of its pre-relation `(t, s)` is represented by a scheme of the site. -/
@[stacks 044L "groupoid: representable quotient", sga "3 IV 3.3.2" "(ii)"]
noncomputable abbrev HasRepresentableQuotient (G : GroupoidInAlgebraicSpaces site S hS B) :
    Prop :=
  (Space.groupoidPreRelation G).HasRepresentableQuotient

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
