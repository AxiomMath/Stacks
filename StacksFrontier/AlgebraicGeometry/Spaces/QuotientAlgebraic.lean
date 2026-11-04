module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives

/-!
# The quotient of an affine scheme by an étale equivalence relation

Let `U` be an affine scheme over `S` belonging to a big fppf site, and let
`j : R ⟶ U ×_S U` be an étale equivalence relation on `U` over `S`. Stacks 0265 asserts that
the quotient sheaf `U/R` is an algebraic space over `S` and that the canonical map `U ⟶ U/R`
is surjective and étale. This file develops the part of that statement which does not need
*effective* descent of schemes along fppf coverings: the sections of the quotient presheaf,
the identification of the canonical map, its local surjectivity, the kernel pair of the
canonical map, separatedness and quasi-finiteness of the relation, and the reduction of the
algebraic-space property to the remaining representability statements.

## Main definitions

* `Stacks.Groupoids.relQuotPresheaf` is the presheaf of equivalence classes of points of `U`
  under the relation induced by a pre-relation, and
  `Stacks.Groupoids.quotientPresheafToRelQuot` compares the quotient presheaf with it.
* `Stacks.Groupoids.yonedaToPoints` compares the presheaf represented by an object of the
  site with the restricted functor of points of its image, and is an isomorphism as soon as
  the presenting functor is fully faithful.
* `Stacks.Groupoids.quotientChart` is the canonical morphism from the presheaf represented by
  `U` to the quotient sheaf of a pre-relation on the image of `U`.
* `Stacks.Groupoids.relSieve` is the sieve of arrows along which two points of `U` become
  related.

## Main results

* `Stacks.Groupoids.mono_of_isEtaleEquivalenceRelation` and
  `Stacks.Groupoids.isPreEquivalenceRelation_of_isEtaleEquivalenceRelation`: an étale
  equivalence relation is monic and induces an equivalence relation on points.
* `Stacks.Groupoids.toQuotientPresheaf_app_eq_iff_rel`: two points of `U` have the same image
  in the quotient presheaf of a pre-equivalence relation exactly when they are related.
* `Stacks.Groupoids.yonedaEquiv_symm_app_toQuotientSheaf` identifies the Yoneda morphism
  determined by the image of the identity under the canonical quotient projection with
  `Stacks.Groupoids.quotientChart`.
* `Stacks.Groupoids.isLocallySurjective_quotientChart`: the chart of the quotient sheaf is
  locally surjective. This is the sheaf-theoretic half of the surjectivity of `U ⟶ U/R`;
  local surjectivity of the projection it factors through is
  `Stacks.Groupoids.isLocallySurjective_toQuotientSheaf`, from
  `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf`.
* `Stacks.Groupoids.quotientChart_app_eq_iff_relSieve_mem` and
  `Stacks.Groupoids.quotientChart_app_eq_iff_rel`: the kernel pair of the chart. Two points
  of `U` have the same image under the chart exactly when they are related locally for the
  topology, and — for a relation whose relation scheme has a sheaf of points — exactly when
  they are related. This is the identification of `U ×_{U/R} U` with `R`, read on points.
* `Stacks.Groupoids.isSeparated_isEtaleEquivalenceRelation`,
  `Stacks.Groupoids.locallyQuasiFinite_isEtaleEquivalenceRelation`,
  `Stacks.Groupoids.isSeparated_target_of_isAffine` and
  `Stacks.Groupoids.isSeparated_source_of_isAffine`: an étale equivalence relation on an
  affine `S`-scheme is separated and locally quasi-finite, and so are its two maps to `U`.
  These are the geometric hypotheses of the fppf descent the source appeals to.
* `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type` and
  `AlgebraicGeometry.BigFppfOver.hasSheafify_type`: sheafification of presheaves of `Type u`
  on the big fppf site of `S` exists and the sheafification equivalences are the local
  bijections. Both rest on `AlgebraicGeometry.BigFppfOver.essentiallySmall`, which is in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness`.
* `AlgebraicGeometry.isAlgebraicSpace_quotientSheaf_of_chart`: a quotient sheaf is an
  algebraic space over `S` as soon as its diagonal is representable and its chart is
  surjective and étale after every representable base change.

## Implementation notes

The three conclusions of Stacks 0265 are **not** proved here. Each of them contains the
assertion that the chart `U ⟶ U/R` is relatively representable, which in the source is
obtained as follows: a point of `U/R` over a scheme `T` lifts to `U` after an fppf covering
`{Tᵢ ⟶ T}`, the restriction of `T ×_{U/R} U` to `Tᵢ` is then the scheme `Tᵢ ×_U R`, and the
resulting descent datum relative to `{Tᵢ ⟶ T}` is effective because `R ⟶ U` is separated and
locally quasi-finite. Everything in that argument *except* the effectivity statement — Stacks
02W8, with the descent dictionary of Stacks 02W5 — is available here:
`isLocallySurjective_quotientChart` is the local lifting of points of Stacks 02WU and 02WV,
read as local surjectivity of the chart for the topology; `quotientChart_app_eq_iff_rel` is
the identification of `T ×_{U/R} U` with `T ×_U R`, read on points; and
`isSeparated_target_of_isAffine` together with `locallyQuasiFinite_isEtaleEquivalenceRelation`
is the geometric input the effectivity statement consumes. What remains is the production of
the descended *scheme*, which no result in this library supplies: Mathlib's
`CategoryTheory.MorphismProperty.DescendsAlong` descends a property of an existing morphism
rather than producing the object, and Mathlib's Stacks 01JJ
(`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`) descends representability
along a family of *open immersions* only. In the shape in which the proof of Stacks 03I2
consumes it, the missing statement is
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`
(`Spaces/EtaleDescent.lean`) for the étale morphisms, and for the monomorphisms in the case
of the diagonal. Finally `isAlgebraicSpace_quotientSheaf_of_chart` isolates the
representability statements as the only remaining content of the algebraic-space property.

The kernel pair is described in two stages. `quotientChart_app_eq_iff_relSieve_mem` needs
only that the sheafification unit is locally injective, and says that the chart identifies
exactly the points which are related *locally for the topology*.
`quotientChart_app_eq_iff_rel` removes the "locally" at the price of the sheaf condition for
the restricted functor of points of `R`: the local representatives of a locally related pair
are automatically compatible, because a *relation* — as opposed to a pre-relation — is
determined by its target and source maps, so they amalgamate. For an object of the site that
sheaf condition is `isSheaf_points_obj`; the relation scheme `R` of Stacks 0265 need not
belong to the site, and its sheaf condition is not proved here.

The quotient presheaf is a pointwise coequalizer, so its sections over `T` are the `T`-valued
points of `U` modulo the equivalence relation *generated* by the pre-relation. For a
pre-equivalence relation that generated relation is the pre-relation itself. This is proved
by comparing the quotient presheaf with the explicit quotient `Stacks.Groupoids.relQuotPresheaf`
rather than by computing the coequalizer in the functor category.

Local surjectivity of the sheafification unit does not come from Mathlib's instances: they
derive it from the plus construction, which for a site with objects in `Type (u + 1)` and
morphisms in `Type u` only produces sheaves of `Type (u + 1)`, whereas the sheaves of the big
fppf site of `S` take values in `Type u`. It is supplied instead by
`Stacks.Sheafification.isLocallySurjective_toSheafify_type`, which assumes only
`CategoryTheory.HasWeakSheafify`.
Local *injectivity* has no such construction-free proof, and is instead obtained
from `AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_type`: the cutoff category of a
big fppf site is essentially small at the universe of its schemes (Stacks 000J,
`AlgebraicGeometry.essentiallySmall_schemeBelow`), hence so is its slice over a contained
scheme, and both sheafification and the characterization of the sheafification equivalences
as the local bijections transport from a small model of the site. The same transport makes
the `CategoryTheory.HasSheafify` hypothesis of Stacks 0265 redundant; it is kept in the
statements of this library so that they are unchanged by the observation.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Groupoids

/-! ### Pointwise equivalence relations -/

variable {S : Scheme.{u}}

/-- An étale equivalence relation is a monomorphism, that is, a relation rather than merely a
pre-relation. -/
theorem mono_of_isEtaleEquivalenceRelation {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : Mono j :=
  ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).1

/-- An étale equivalence relation is a pre-equivalence relation: the relation it induces on
the `T`-valued points of `U` is an equivalence relation for every `S`-scheme `T`. -/
theorem isPreEquivalenceRelation_of_isEtaleEquivalenceRelation {R U : Over S}
    (j : PreRelation R U) [IsEtaleEquivalenceRelation j] : IsPreEquivalenceRelation j :=
  ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).2

/-- A relation, as opposed to a pre-relation, is determined by its target and source maps:
two points of `R` with the same target and the same source agree. -/
theorem PreRelation.ext_of_target_of_source {R U : Over S} (j : PreRelation R U) [Mono j]
    {T : Over S} {a b : T ⟶ R} (ht : a ≫ j.target = b ≫ j.target)
    (hs : a ≫ j.source = b ≫ j.source) : a = b := by
  refine (cancel_mono j).mp (prod.hom_ext ?_ ?_)
  · simpa only [Category.assoc] using ht
  · simpa only [Category.assoc] using hs

/-! ### Separatedness and quasi-finiteness of an étale equivalence relation

An étale equivalence relation `j : R ⟶ U ⨯ U` on an affine `S`-scheme is separated and
locally quasi-finite, and so are its two maps `R ⟶ U`. These are the geometric hypotheses
under which the fppf descent of Stacks 02W8 applies, and they are the first step of the
proof of Stacks 0265. -/

/-- The product of two `S`-schemes, read in the category of schemes, is their fibre product
over `S`. This is `CategoryTheory.Over.isPullback_of_binaryFan_isLimit` for the chosen
product. -/
private theorem isPullback_prod_left (U V : Over S) :
    IsPullback (prod.fst (X := U) (Y := V)).left (prod.snd (X := U) (Y := V)).left
      U.hom V.hom :=
  Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst (X := U) (Y := V)) prod.snd) (prodIsProd U V)

/-- An étale equivalence relation is separated, being a monomorphism. -/
theorem isSeparated_isEtaleEquivalenceRelation {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : AlgebraicGeometry.IsSeparated j.left :=
  have : Mono j := mono_of_isEtaleEquivalenceRelation j
  have : Mono j.left := inferInstance
  inferInstance

/-- An étale equivalence relation is locally of finite type: its target map is étale, hence
locally of finite type, and a morphism whose composite with another is locally of finite
type is itself locally of finite type. -/
theorem locallyOfFiniteType_isEtaleEquivalenceRelation {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : LocallyOfFiniteType j.left := by
  have : LocallyOfFiniteType (j.left ≫ (prod.fst (X := U) (Y := U)).left) := by
    show LocallyOfFiniteType (PreRelation.target j).left
    infer_instance
  exact locallyOfFiniteType_of_comp j.left (prod.fst (X := U) (Y := U)).left

/-- An étale equivalence relation is locally quasi-finite: it is a monomorphism, hence
universally injective, and it is locally of finite type. -/
theorem locallyQuasiFinite_isEtaleEquivalenceRelation {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : LocallyQuasiFinite j.left :=
  have : Mono j := mono_of_isEtaleEquivalenceRelation j
  have : Mono j.left := inferInstance
  have := locallyOfFiniteType_isEtaleEquivalenceRelation j
  inferInstance

/-- The first projection of the product of an affine `S`-scheme with itself is separated,
being the base change of the separated structure morphism. -/
theorem isSeparated_prod_fst_left (U : Over S) [IsAffine U.left] :
    AlgebraicGeometry.IsSeparated (prod.fst (X := U) (Y := U)).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left U U).flip inferInstance

/-- The second projection of the product of an affine `S`-scheme with itself is
separated. -/
theorem isSeparated_prod_snd_left (U : Over S) [IsAffine U.left] :
    AlgebraicGeometry.IsSeparated (prod.snd (X := U) (Y := U)).left :=
  MorphismProperty.of_isPullback (isPullback_prod_left U U) inferInstance

/-- The target map of an étale equivalence relation on an affine `S`-scheme is separated. -/
theorem isSeparated_target_of_isAffine {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] [IsAffine U.left] :
    AlgebraicGeometry.IsSeparated j.target.left := by
  have := isSeparated_isEtaleEquivalenceRelation j
  have := isSeparated_prod_fst_left U
  show AlgebraicGeometry.IsSeparated (j.left ≫ (prod.fst (X := U) (Y := U)).left)
  infer_instance

/-- The source map of an étale equivalence relation on an affine `S`-scheme is separated. -/
theorem isSeparated_source_of_isAffine {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] [IsAffine U.left] :
    AlgebraicGeometry.IsSeparated j.source.left := by
  have := isSeparated_isEtaleEquivalenceRelation j
  have := isSeparated_prod_snd_left U
  show AlgebraicGeometry.IsSeparated (j.left ≫ (prod.snd (X := U) (Y := U)).left)
  infer_instance

/-! ### The quotient presheaf of a pre-equivalence relation

The quotient presheaf of a pre-relation is a pointwise coequalizer, so its sections over `T`
are the `T`-valued points of `U` modulo the equivalence relation *generated* by the
pre-relation. For a pre-equivalence relation that generated relation is the pre-relation
itself, so two points of `U` have the same image in the quotient presheaf exactly when they
are related. This is proved by comparing the quotient presheaf with the explicit quotient. -/

variable {C : Type v} [Category.{u} C]

/-- Restriction of a point of an `S`-scheme along an arrow of the site is composition with
the image of that arrow under the functor presenting the site. -/
theorem points_map_op (F : C ⥤ Over S) (Z : Over S) {V W : C} (k : V ⟶ W)
    (r : ToType ((points F Z).obj (op W))) :
    (points F Z).map k.op r = F.map k ≫ r :=
  rfl

/-- The presheaf of equivalence classes of points of `U` under the relation induced by a
pre-relation: its sections over `T` are the `T`-valued points of `U` modulo that relation. -/
def relQuotPresheaf (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) : Cᵒᵖ ⥤ Type u where
  obj T := Quot (j.Rel (T := F.obj T.unop))
  map {_ _} g := ↾Quot.map (fun x ↦ F.map g.unop ≫ x) (fun _ _ ⟨r, hx, hy⟩ ↦
    ⟨F.map g.unop ≫ r, by rw [Category.assoc, hx], by rw [Category.assoc, hy]⟩)
  map_id _ := by
    ext x
    induction x using Quot.ind with | _ a => ?_
    simp [Quot.map]
  map_comp _ _ := by
    ext x
    induction x using Quot.ind with | _ a => ?_
    simp [Quot.map]

/-- The projection of the functor of points of `U` onto the presheaf of equivalence
classes. -/
def toRelQuotPresheaf (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) :
    points F U ⟶ relQuotPresheaf F j where
  app _ := ↾Quot.mk _
  naturality _ _ _ := rfl

/-- The projection onto the presheaf of equivalence classes identifies related points. -/
theorem sourceMap_toRelQuotPresheaf (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U) :
    sourceMap F j ≫ toRelQuotPresheaf F j = targetMap F j ≫ toRelQuotPresheaf F j := by
  ext T r
  exact (Quot.sound ⟨r, rfl, rfl⟩).symm

/-- The comparison morphism from the quotient presheaf of a pre-relation to the presheaf of
equivalence classes of its induced relation. -/
noncomputable def quotientPresheafToRelQuot (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) : quotientPresheaf F j ⟶ relQuotPresheaf F j :=
  coequalizer.desc (toRelQuotPresheaf F j) (sourceMap_toRelQuotPresheaf F j)

/-- The comparison morphism to the presheaf of equivalence classes is compatible with the two
projections from the functor of points of `U`. -/
theorem toQuotientPresheaf_quotientPresheafToRelQuot (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) :
    toQuotientPresheaf F j ≫ quotientPresheafToRelQuot F j = toRelQuotPresheaf F j :=
  coequalizer.π_desc _ _

/-- **Stacks 02VG, points of the quotient presheaf.** Two points of `U` over an object of the
site have the same image in the quotient presheaf of a pre-equivalence relation exactly when
they are related. -/
@[sga "3 IV 3.1.2" "partial"]
theorem toQuotientPresheaf_app_eq_iff_rel (F : C ⥤ Over S) {R U : Over S}
    (j : PreRelation R U) (hj : IsPreEquivalenceRelation j) {T : Cᵒᵖ}
    (x y : (points F U).obj T) :
    (toQuotientPresheaf F j).app T x = (toQuotientPresheaf F j).app T y ↔
      j.Rel (T := F.obj T.unop) x y := by
  constructor
  · intro h
    have e : ∀ z : ToType ((points F U).obj T),
        (quotientPresheafToRelQuot F j).app T ((toQuotientPresheaf F j).app T z) =
          Quot.mk (j.Rel (T := F.obj T.unop)) z := fun z ↦
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (toQuotientPresheaf_quotientPresheafToRelQuot F j) T) z
    have key : Quot.mk (j.Rel (T := F.obj T.unop)) x = Quot.mk _ y := by
      rw [← e x, ← e y, h]
    exact ((hj (F.obj T.unop)).eqvGen_iff).mp (Quot.eq.mp key)
  · rintro ⟨r, hx, hy⟩
    rw [← hx, ← hy]
    exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (coequalizer.condition (sourceMap F j) (targetMap F j)) T) r).symm

/-! ### The chart of a quotient sheaf -/

/-- The comparison morphism from the presheaf represented by an object `X` of a site of
`S`-schemes to the restricted functor of points of the `S`-scheme presented by `X`. -/
def yonedaToPoints (F : C ⥤ Over S) (X : C) : yoneda.obj X ⟶ points F (F.obj X) where
  app T := ↾fun (h : T.unop ⟶ X) ↦ F.map h
  naturality _ _ _ := by
    ext h
    exact F.map_comp _ h

/-- The comparison morphism of `Stacks.Groupoids.yonedaToPoints` sends an arrow of the site to
its image under the presenting functor. This is not a `simp` lemma: its left-hand side is not
in simp-normal form, because simplifying the hom-sets of the two presheaves changes the
coercion's implicit arguments. -/
theorem yonedaToPoints_app (F : C ⥤ Over S) (X : C) (T : Cᵒᵖ) (h : T.unop ⟶ X) :
    (yonedaToPoints F X).app T h = F.map h :=
  rfl

/-- The comparison morphism of `Stacks.Groupoids.yonedaToPoints` is an isomorphism when the
functor presenting the site is fully faithful. -/
instance isIso_yonedaToPoints (F : C ⥤ Over S) [F.Full] [F.Faithful] (X : C) :
    IsIso (yonedaToPoints F X) := by
  have (T : Cᵒᵖ) : IsIso ((yonedaToPoints F X).app T) := by
    rw [isIso_iff_bijective]
    exact ⟨fun _ _ h ↦ F.map_injective h, fun g ↦ ⟨F.preimage g, F.map_preimage g⟩⟩
  exact NatIso.isIso_of_isIso_app _

/-- The restricted functor of points of the `S`-scheme presented by an object of a
subcanonical site is a sheaf: it is isomorphic to the presheaf represented by that
object. -/
theorem isSheaf_points_obj (J : GrothendieckTopology C) [J.Subcanonical]
    (F : C ⥤ Over S) [F.Full] [F.Faithful] (X : C) :
    Presheaf.IsSheaf J (points F (F.obj X)) :=
  (Presheaf.isSheaf_of_iso_iff (asIso (yonedaToPoints F X))).mp
    ((isSheaf_iff_isSheaf_of_type J _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

/-- The canonical morphism from the presheaf represented by an object `X` of a site of
`S`-schemes to the quotient sheaf of a pre-relation on the `S`-scheme presented by `X`. -/
noncomputable def quotientChart (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X)) :
    yoneda.obj X ⟶ (quotientSheaf J F j).obj :=
  yonedaToPoints F X ≫ toQuotientSheaf J F j

/-- The chart of a quotient sheaf sends an arrow `h : T ⟶ X` of the site to the image under
the quotient projection of the point `F.map h`. -/
@[simp]
theorem quotientChart_app (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X)) (T : Cᵒᵖ)
    (h : T.unop ⟶ X) :
    (quotientChart J F X j).app T h = (toQuotientSheaf J F j).app T (F.map h) :=
  rfl

/-- The Yoneda morphism determined by the image of the identity under the canonical quotient
projection is the chart of the quotient sheaf. -/
theorem yonedaEquiv_symm_app_toQuotientSheaf (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (X : C) {R : Over S}
    (j : PreRelation R (F.obj X)) :
    yonedaEquiv.symm ((toQuotientSheaf J F j).app (op X) (𝟙 (F.obj X))) =
      quotientChart J F X j := by
  rw [Equiv.symm_apply_eq, quotientChart, yonedaEquiv_comp, yonedaEquiv_apply,
    yonedaToPoints_app, F.map_id]

/-- The chart of a quotient sheaf is locally surjective. This is the sheaf-theoretic form of
the surjectivity of the quotient map `U ⟶ U/R` of Stacks 0265. -/
theorem isLocallySurjective_quotientChart (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) [F.Full] [F.Faithful] (X : C) {R : Over S}
    (j : PreRelation R (F.obj X)) :
    Presheaf.IsLocallySurjective J (quotientChart J F X j) := by
  have := isLocallySurjective_toQuotientSheaf J F j
  exact Presheaf.isLocallySurjective_comp J _ _

/-- The chart of a quotient sheaf identifies two points of `X` which are related by the
pre-relation. -/
theorem quotientChart_app_eq_of_rel (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X)) {T : C}
    {x y : T ⟶ X} (h : j.Rel (T := F.obj T) (F.map x) (F.map y)) :
    (quotientChart J F X j).app (op T) x = (quotientChart J F X j).app (op T) y := by
  obtain ⟨r, hx, hy⟩ := h
  have ht : (targetMap F j).app (op T) r = F.map x := hx
  have hs : (sourceMap F j).app (op T) r = F.map y := hy
  rw [quotientChart_app, quotientChart_app, ← ht, ← hs]
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (sourceMap_toQuotientSheaf J F j) (op T)) r).symm

/-- The sieve on `T` consisting of the arrows along which two `T`-valued points of `X` become
related by a pre-relation. -/
def relSieve (F : C ⥤ Over S) {R : Over S} {X : C} (j : PreRelation R (F.obj X)) {T : C}
    (x y : T ⟶ X) : Sieve T where
  arrows T' g := j.Rel (T := F.obj T') (F.map (g ≫ x)) (F.map (g ≫ y))
  downward_closed := by
    rintro T' T'' g ⟨r, hx, hy⟩ h
    refine ⟨F.map h ≫ r, ?_, ?_⟩
    · rw [Category.assoc, hx, ← F.map_comp, Category.assoc]
    · rw [Category.assoc, hy, ← F.map_comp, Category.assoc]

/-- The chart of a quotient sheaf identifies two points of `X` which are related by the
pre-relation locally for the topology. The quotient sheaf is separated, and the two points
agree after restriction along every arrow of a covering sieve. -/
theorem quotientChart_app_eq_of_relSieve_mem (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (X : C) {R : Over S}
    (j : PreRelation R (F.obj X)) {T : C} {x y : T ⟶ X} (h : relSieve F j x y ∈ J T) :
    (quotientChart J F X j).app (op T) x = (quotientChart J F X j).app (op T) y := by
  have hsh : Presieve.IsSheaf J (quotientSheaf J F j).obj :=
    (isSheaf_iff_isSheaf_of_type J _).mp (quotientSheaf J F j).property
  refine (hsh.isSeparated _ h).ext fun {T'} {g} hg ↦ ?_
  have hnat : ∀ z : T ⟶ X, (quotientSheaf J F j).obj.map g.op
      ((quotientChart J F X j).app (op T) z) =
        (quotientChart J F X j).app (op T') (g ≫ z) := fun z ↦
    (ConcreteCategory.congr_hom ((quotientChart J F X j).naturality g.op) z).symm
  rw [hnat x, hnat y]
  exact quotientChart_app_eq_of_rel J F X j hg

/-- Two points of `X` identified by the chart of the quotient sheaf of a pre-equivalence
relation are related by the pre-relation locally for the topology.

This is the converse of `Stacks.Groupoids.quotientChart_app_eq_of_relSieve_mem`, and the
step of Stacks 0265 which identifies the kernel pair of `U ⟶ U/R` with `R`: the projection
onto the quotient presheaf identifies exactly the related points, and the sheafification
unit is locally injective. -/
theorem relSieve_mem_of_quotientChart_app_eq (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X))
    (hj : IsPreEquivalenceRelation j) {T : C} {x y : T ⟶ X}
    (h : (quotientChart J F X j).app (op T) x = (quotientChart J F X j).app (op T) y) :
    relSieve F j x y ∈ J T := by
  have hcomp : ∀ z : ToType ((points F (F.obj X)).obj (op T)),
      (toQuotientSheaf J F j).app (op T) z =
        (toSheafify J (quotientPresheaf F j)).app (op T)
          ((toQuotientPresheaf F j).app (op T) z) := fun _ ↦ rfl
  have h' : (toSheafify J (quotientPresheaf F j)).app (op T)
        ((toQuotientPresheaf F j).app (op T) (F.map x)) =
      (toSheafify J (quotientPresheaf F j)).app (op T)
        ((toQuotientPresheaf F j).app (op T) (F.map y)) := by
    rw [← hcomp, ← hcomp]
    simpa only [quotientChart_app] using h
  refine J.superset_covering ?_
    (Presheaf.equalizerSieve_mem J (toSheafify J (quotientPresheaf F j)) _ _ h')
  intro W g hg
  have hnat : ∀ z : ToType ((points F (F.obj X)).obj (op T)),
      (toQuotientPresheaf F j).app (op W) (F.map g ≫ z) =
        (quotientPresheaf F j).map g.op ((toQuotientPresheaf F j).app (op T) z) := fun z ↦
    NatTrans.naturality_apply (toQuotientPresheaf F j) g.op z
  have key : (toQuotientPresheaf F j).app (op W) (F.map g ≫ F.map x) =
      (toQuotientPresheaf F j).app (op W) (F.map g ≫ F.map y) := by
    rw [hnat, hnat]
    exact hg
  show j.Rel (F.map (g ≫ x)) (F.map (g ≫ y))
  rw [F.map_comp, F.map_comp]
  exact (toQuotientPresheaf_app_eq_iff_rel F j hj _ _).mp key

/-- **The kernel pair of the chart of a quotient sheaf.** Two points of `X` have the same
image under the chart of the quotient sheaf of a pre-equivalence relation exactly when they
are related by the pre-relation locally for the topology. -/
theorem quotientChart_app_eq_iff_relSieve_mem (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X))
    (hj : IsPreEquivalenceRelation j) {T : C} (x y : T ⟶ X) :
    (quotientChart J F X j).app (op T) x = (quotientChart J F X j).app (op T) y ↔
      relSieve F j x y ∈ J T :=
  ⟨relSieve_mem_of_quotientChart_app_eq J F X j hj,
    quotientChart_app_eq_of_relSieve_mem J F X j⟩

/-- Two points of `X` related by a *relation* locally for the topology are related, provided
the restricted functors of points of `R` and of the `S`-scheme presented by `X` are sheaves:
the local representatives are compatible because a relation is determined by its target and
source maps, so they amalgamate. -/
theorem rel_of_relSieve_mem (J : GrothendieckTopology C) (F : C ⥤ Over S)
    {R : Over S} {X : C} (j : PreRelation R (F.obj X)) [Mono j]
    (hR : Presheaf.IsSheaf J (points F R))
    (hX : Presheaf.IsSheaf J (points F (F.obj X)))
    {T : C} {x y : T ⟶ X} (h : relSieve F j x y ∈ J T) :
    j.Rel (F.map x) (F.map y) := by
  classical
  let fam : Presieve.FamilyOfElements (points F R) (relSieve F j x y).arrows :=
    fun _ _ hg ↦ hg.choose
  have hfam₁ : ∀ ⦃W : C⦄ (g : W ⟶ T) (hg : relSieve F j x y g),
      fam g hg ≫ j.target = F.map (g ≫ x) := fun _ _ hg ↦ hg.choose_spec.1
  have hfam₂ : ∀ ⦃W : C⦄ (g : W ⟶ T) (hg : relSieve F j x y g),
      fam g hg ≫ j.source = F.map (g ≫ y) := fun _ _ hg ↦ hg.choose_spec.2
  have hcompat : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W V g k hg
    refine PreRelation.ext_of_target_of_source j ?_ ?_ <;>
      simp [hfam₁, hfam₂]
  obtain ⟨r, hr, -⟩ := hR.isSheafFor _ h fam hcompat
  have hext : ∀ (a : T ⟶ X) (p : R ⟶ F.obj X),
      (∀ ⦃W : C⦄ (g : W ⟶ T) (hg : relSieve F j x y g), fam g hg ≫ p = F.map (g ≫ a)) →
        r ≫ p = F.map a := fun a p hfa ↦
    ((hX.isSheafFor _ h).isSeparatedFor).ext fun {W} g hg ↦ by
      rw [points_map_op, points_map_op, ← F.map_comp, ← hfa g hg, ← hr g hg, points_map_op,
        Category.assoc]
  exact ⟨r, hext x _ hfam₁, hext y _ hfam₂⟩

/-- **The kernel pair of the chart of a quotient sheaf is the relation.** For an equivalence
relation whose relation scheme has a sheaf of points, two points of `X` have the same image
under the chart of the quotient sheaf exactly when they are related.

This is the identification of `U ×_{U/R} U` with `R` of Stacks 0265, read on points. -/
theorem quotientChart_app_eq_iff_rel (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]
    (F : C ⥤ Over S) (X : C) {R : Over S} (j : PreRelation R (F.obj X)) [Mono j]
    (hj : IsPreEquivalenceRelation j)
    (hR : Presheaf.IsSheaf J (points F R))
    (hX : Presheaf.IsSheaf J (points F (F.obj X)))
    {T : C} (x y : T ⟶ X) :
    (quotientChart J F X j).app (op T) x = (quotientChart J F X j).app (op T) y ↔
      j.Rel (F.map x) (F.map y) :=
  ⟨fun h ↦ rel_of_relSieve_mem J F j hR hX
      (relSieve_mem_of_quotientChart_app_eq J F X j hj h),
    quotientChart_app_eq_of_rel J F X j⟩

end Stacks.Groupoids

namespace AlgebraicGeometry

/-! ### Smallness of a big fppf site

The cutoff category of a big fppf site is essentially small at the universe of its schemes
(Stacks 000J), so the sheaf theory of the site in the universe `Type u` of its morphisms is
transported from a small model: sheafification of presheaves of `Type u` exists, and the
sheafification equivalences are exactly the local bijections. In particular the
`CategoryTheory.HasSheafify` hypothesis of Stacks 0265 is redundant.

These declarations belong beside `AlgebraicGeometry.BigFppfOver.subcanonical_topology` in
`Topologies/Fppf/Subcanonical.lean` and should move there on the next pass through that
file. `AlgebraicGeometry.BigFppfOver.hasSheafify_type` is deliberately *not* an instance:
every statement about quotient sheaves in this library carries `HasSheafify` as a
hypothesis, and leaving it so keeps those statements unchanged. -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end BigFppfOver

/-- A quotient sheaf on the big fppf site of `S` is an algebraic space over `S` as soon as its
diagonal is representable and its chart is surjective and étale after every representable
base change.

This is the plumbing of Stacks 0265: the sheaf condition holds because the quotient sheaf is
a sheaf by construction, and the chart supplies the atlas. The two representability
hypotheses are the content of the source proof which is not formalized in this library. -/
theorem isAlgebraicSpace_quotientSheaf_of_chart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {R : Over S}
    (j : Stacks.Groupoids.PreRelation R ((Over.post B.inclusion).obj U))
    (hdiag : yoneda.relativelyRepresentable
      (diag (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj))
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) U j))
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) U j)) :
    IsAlgebraicSpace B S hS (Stacks.Groupoids.quotientSheaf
      (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj where
  isSheaf := (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) j).property
  diagonal_representable := hdiag
  exists_atlas := ⟨U, _, hsurj, hetale⟩

end AlgebraicGeometry

end
