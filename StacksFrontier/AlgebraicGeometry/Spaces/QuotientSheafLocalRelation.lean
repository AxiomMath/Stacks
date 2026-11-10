module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientKernelPair0265
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafInjective

/-!
# Sections of the quotient sheaf of a pre-equivalence relation

The quotient sheaf `U/R` of a pre-relation is the sheafification of a pointwise coequalizer.
This file describes when two `T`-valued points of `U` have the same image in `(U/R)(T)`: exactly
when they become related by `R` after restriction along a covering of `T`. That is Groupoids,
Lemma **045Y**, at the sheaf level.

The source states the lemma as an equivalence of two conditions on `a, b ∈ U(T)`,

1. `a` and `b` map to the same element of `(U/R)(T)`;
2. there is a `τ`-covering `{f_i : T_i → T}` and morphisms `r_i : T_i → R` with
   `a ∘ f_i = s ∘ r_i` and `b ∘ f_i = t ∘ r_i`;

and then rephrases it as the surjectivity of the map of `τ`-sheaves
`h_R → h_U ×_{U/R} h_U`. Both forms are recorded below: condition (2) is the statement that
`Stacks.Groupoids.relSieveOfPoints` is a covering sieve, and
`Stacks.Groupoids.relSieve_mem_of_toQuotientSheaf_apply_eq` is the rephrasing — a section of
`h_U ×_{U/R} h_U` over `T` *is* a pair of points of `U` with the same image in `(U/R)(T)`, and
lifting it locally to `h_R` *is* the existence of the `r_i`.

## Main definitions

* `Stacks.Groupoids.relSieveOfPoints`: the sieve of morphisms `f : Y ⟶ T` along which two
  `F.obj T`-points of `U` become related by the pre-relation. The lemma names below shorten it
  to `relSieve`; `Stacks.Groupoids.relSieve` itself is the variant of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic` whose two points are arrows of the
  site into an object `X` with `U = F.obj X`.

## Main results

* `Stacks.Groupoids.relSieve_mem_of_toQuotientSheaf_apply_eq`: two points of `U` with the same
  image in the quotient sheaf of a pre-equivalence relation are locally related. This is the
  surjectivity of `h_R → h_U ×_{U/R} h_U`.
* `Stacks.Groupoids.toQuotientSheaf_apply_eq_of_relSieve_mem`: the converse, which needs no
  hypothesis on the pre-relation.
* `Stacks.Groupoids.toQuotientSheaf_apply_eq_iff_relSieve_mem` and
  `Stacks.Groupoids.toQuotientSheaf_apply_eq_iff_exists_cover`: **Groupoids, Lemma 045Y**, in the
  sieve form and in the source's own covering form.

The injectivity half of the kernel-pair property, that a point of `R` is determined by its
target and its source when the pre-relation is a monomorphism, is
`Stacks.Groupoids.PreRelation.eq_of_target_eq_of_source_eq`.

## Implementation notes

No local description of sheafification is needed, contrary to what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective` record. Both directions run
on general sheaf-theoretic facts applied to the pointwise computation of the quotient *presheaf*
already carried out in `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafInjective`:

* forwards, `CategoryTheory.Presheaf.isLocallyInjective_toSheafify` says that two sections of a
  presheaf with the same image in its sheafification agree on a covering sieve, and
  `Stacks.Groupoids.rel_of_toQuotientPresheaf_apply_eq` turns agreement in the quotient presheaf
  into the relation; the sieve on which they agree is therefore contained in
  `Stacks.Groupoids.relSieveOfPoints`;
* backwards, the quotient sheaf is a sheaf, so two of its sections agreeing on a covering sieve
  are equal, and `Stacks.Groupoids.toQuotientPresheaf_apply_eq_of_rel` supplies that agreement
  from the relation. This direction uses no hypothesis on the pre-relation at all.

Only the forward direction needs the pre-equivalence hypothesis, and it needs it exactly where
the source's hint puts it: the presheaf `T ↦ U(T)/j(R(T))` computes the quotient presheaf
because `j(R(T))` is already an equivalence relation, so no equivalence closure intervenes.

Presheaves of sets are taken in `Type u`, the universe of morphisms of `S`-schemes, and the site
is correspondingly constrained to `C : Type u` with `Category.{u} C`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective` and for the same reason:
Mathlib's local injectivity and local surjectivity of sheafification are stated for presheaves
valued in the canonical universe `Type (max u v)` of a site `C : Type u` with `Category.{v} C`.
The big and small Zariski, étale, fppf, smooth and syntomic sites of schemes in universe `u`
satisfy `C : Type u`, `Category.{u} C`.

The *kernel-pair* property of the quotient map — that `h_R` is isomorphic to
`h_U ×_{U/R} h_U`, rather than merely surjecting onto it — is strictly stronger than 045Y and is
not proved here. Over and above the lemma below it needs the pre-relation to be a monomorphism,
for which `Stacks.Groupoids.PreRelation.eq_of_target_eq_of_source_eq` is the relevant half; it
needs the functors of points of `R` and of `U` to be sheaves, which is descent for representable
presheaves and is a property of the presentation `F` rather than of the quotient-sheaf
construction; and it needs a locally bijective morphism of sheaves to be an isomorphism,
which is Mathlib's
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`.

No Stacks tag attribute is placed on anything in this file. Tag **045Y** belongs to Groupoids,
Chapter 39; the declarations are left unregistered here.

## References

* [Stacks Project, Tag 045Y](https://stacks.math.columbia.edu/tag/045Y)
* [Stacks Project, Tag 02VF](https://stacks.math.columbia.edu/tag/02VF)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type u} [Category.{u} C]
variable (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)

/-- The sieve of morphisms `f : Y ⟶ T` along which two `F.obj T`-points `a`, `b` of `U` become
related by the pre-relation: the arrows of the sieve are those `f` for which there is an
`F.obj Y`-point of `R` with target `a ∘ f` and source `b ∘ f`.

This is the source's condition (2) of Groupoids, Lemma **045Y**, read as a sieve rather than as
a covering: a covering `{f_i : T_i → T}` with the required morphisms `r_i` exists if and only if
this sieve is a covering sieve. -/
def relSieveOfPoints {T : C} (a b : F.obj T ⟶ U) : Sieve T where
  arrows _ f := j.Rel (F.map f ≫ a) (F.map f ≫ b)
  downward_closed := by
    rintro Y Z f ⟨r, hrt, hrs⟩ g
    exact ⟨F.map g ≫ r,
      by rw [Category.assoc, hrt, F.map_comp, Category.assoc],
      by rw [Category.assoc, hrs, F.map_comp, Category.assoc]⟩

/-- A morphism `f : Y ⟶ T` lies in `relSieveOfPoints F j a b` if and only if the restrictions
`F.map f ≫ a` and `F.map f ≫ b` are related by the pre-relation `j`. -/
@[simp]
theorem relSieveOfPoints_apply {T Y : C} (a b : F.obj T ⟶ U) (f : Y ⟶ T) :
    relSieveOfPoints F j a b f ↔ j.Rel (F.map f ≫ a) (F.map f ≫ b) := Iff.rfl

/-- **Groupoids, Lemma 045Y, (1) implies (2).** Two `F.obj T`-points of `U` with the same image
in the quotient sheaf of a pre-equivalence relation become related by the pre-relation after
restriction along a covering sieve of `T`.

This is the source's rephrasing of the lemma: the map of sheaves `h_R → h_U ×_{U/R} h_U` is
surjective. A section of `h_U ×_{U/R} h_U` over `T` is a pair of `F.obj T`-points of `U` with
the same image in `(U/R)(T)`, and lifting it locally to `h_R` is the conclusion below. -/
theorem relSieve_mem_of_toQuotientSheaf_apply_eq (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (hj : IsPreEquivalenceRelation j) {T : C}
    (a b : F.obj T ⟶ U)
    (h : (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b) :
    relSieveOfPoints F j a b ∈ J T := by
  have hx : (toSheafify J (quotientPresheaf F j)).app (op T)
      ((toQuotientPresheaf F j).app (op T) a) =
      (toSheafify J (quotientPresheaf F j)).app (op T)
        ((toQuotientPresheaf F j).app (op T) b) := by
    simpa only [toQuotientSheaf, NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
    (toSheafify J (quotientPresheaf F j)) _ _ hx)
  intro Y f hf
  have hf' : (toQuotientPresheaf F j).app (op Y) (F.map f ≫ a) =
      (toQuotientPresheaf F j).app (op Y) (F.map f ≫ b) := by
    rw [show F.map f ≫ a = (points F U).map f.op a from rfl,
      show F.map f ≫ b = (points F U).map f.op b from rfl,
      NatTrans.naturality_apply (toQuotientPresheaf F j) f.op a,
      NatTrans.naturality_apply (toQuotientPresheaf F j) f.op b]
    exact hf
  exact rel_of_toQuotientPresheaf_apply_eq F j hj Y hf'

/-- **Groupoids, Lemma 045Y, (2) implies (1).** Two `F.obj T`-points of `U` which become related
by the pre-relation after restriction along a covering sieve of `T` have the same image in the
quotient sheaf. The quotient sheaf is a sheaf, so its sections are determined locally; no
hypothesis on the pre-relation is needed. -/
theorem toQuotientSheaf_apply_eq_of_relSieve_mem (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] {T : C} (a b : F.obj T ⟶ U)
    (h : relSieveOfPoints F j a b ∈ J T) :
    (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b := by
  have hsheaf : Presieve.IsSheaf J (quotientSheaf J F j).obj :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1 (quotientSheaf J F j).property
  refine ((hsheaf _ h).isSeparatedFor).ext ?_
  intro Y f hf
  rw [← NatTrans.naturality_apply (toQuotientSheaf J F j) f.op a,
    ← NatTrans.naturality_apply (toQuotientSheaf J F j) f.op b]
  change (toQuotientPresheaf F j ≫ toSheafify J (quotientPresheaf F j)).app (op Y)
      ((points F U).map f.op a) = _
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact congrArg _ (toQuotientPresheaf_apply_eq_of_rel F j Y hf)

/-- **Groupoids, Lemma 045Y.** Let `j : R → U ×_S U` be a pre-equivalence relation over `S`
presented on a site `C` by `F`, and let `J` be a topology on `C`. Two `F.obj T`-points of `U`
have the same image in the quotient sheaf `U/R` over `T` if and only if they become related by
the pre-relation after restriction along a covering sieve of `T`. -/
theorem toQuotientSheaf_apply_eq_iff_relSieve_mem (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (hj : IsPreEquivalenceRelation j) {T : C}
    (a b : F.obj T ⟶ U) :
    (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b ↔
      relSieveOfPoints F j a b ∈ J T :=
  ⟨relSieve_mem_of_toQuotientSheaf_apply_eq F j J hj a b,
    toQuotientSheaf_apply_eq_of_relSieve_mem F j J a b⟩

/-- **Groupoids, Lemma 045Y**, in the source's own form: two `F.obj T`-points of `U` have the
same image in the quotient sheaf over `T` if and only if there is a covering of `T` on each
member of which a point of `R` relates their restrictions. -/
theorem toQuotientSheaf_apply_eq_iff_exists_cover (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (hj : IsPreEquivalenceRelation j) {T : C}
    (a b : F.obj T ⟶ U) :
    (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b ↔
      ∃ W : J.Cover T, ∀ ⦃Y : C⦄ (f : Y ⟶ T), (W : Sieve T) f →
        ∃ r : F.obj Y ⟶ R, r ≫ j.target = F.map f ≫ a ∧ r ≫ j.source = F.map f ≫ b := by
  rw [toQuotientSheaf_apply_eq_iff_relSieve_mem F j J hj]
  refine ⟨fun h => ⟨⟨relSieveOfPoints F j a b, h⟩, fun _ _ hf => hf⟩, fun ⟨W, hW⟩ => ?_⟩
  exact J.superset_covering (fun _ f hf => hW f hf) W.2

end Stacks.Groupoids

end
