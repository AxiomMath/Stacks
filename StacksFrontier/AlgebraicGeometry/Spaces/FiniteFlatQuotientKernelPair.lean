module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A monomorphic representation of a quotient sheaf has the relation for its kernel pair

Let `j : R ⟶ U ⨯ U` be a relation on a scheme `U` over `S` which is an equivalence relation on
the points of every test scheme, and let `f : U ⟶ M` be a morphism of `S`-schemes which
factors the canonical projection onto the fppf quotient sheaf `U/R` through a *pointwise
injective* map of presheaves. Then the square with sides the target and source maps of `j` and
`f` on both remaining sides is Cartesian: `R = U ×_M U`.

This is the converse, for the kernel-pair clause, of
`AlgebraicGeometry.quotientSheaf_isRepresented_of_isPullback`: that theorem derives the
representation of the quotient sheaf from the kernel-pair property, and this one derives the
kernel-pair property from the representation. **Nothing here is Stacks 07S6 and nothing here
carries that tag**: the existence of `f` is what 07S6 asserts and is a hypothesis throughout.

## Main results

* `Stacks.Groupoids.rel_of_comp_eq_comp`: two points of `U` over an object of the site which
  are identified by `f` are related by `j`. This is the whole of the sheaf-theoretic content.
* `Stacks.Groupoids.target_comp_eq_source_comp_of_quotientSheafFactor`: the square commutes,
  as soon as the relation scheme is itself presented by an object of the site.
* `Stacks.Groupoids.isPullback_of_quotientSheafFactor`: the square is Cartesian, for a site
  one of whose objects presents the fibre product `U ×_M U`.
* `AlgebraicGeometry.isPullback_of_quotientSheaf_isRepresented`: **the kernel-pair clause of
  the conclusion of Stacks 07S6, derived from the representation clause.** For a groupoid
  scheme over `S` whose pre-relation is an equivalence relation and a morphism `f : U ⟶ M` of
  `S`-schemes under which the quotient sheaf of the pre-relation is represented by `M` on one
  big fppf site containing `S`, `U` and `R`, the target and source maps form the kernel pair
  of `f`.

## Implementation notes

The kernel-pair property is proved by showing that the comparison morphism
`R ⟶ U ×_M U` is an isomorphism, and *not* by verifying the universal property of a Cartesian
square against an arbitrary test object of `CategoryTheory.Over S`: the sheaf-theoretic input
is available only over objects of the site, and the objects of a big fppf site are bounded in
size. Exhibiting a two-sided inverse needs a single test object, namely one presenting
`U ×_M U` itself; its existence is `AlgebraicGeometry.Scheme.size_pullback_lt`, the closure of
the size cutoff under fibre products, which needs no bound on `M`, the fibre product of two
copies of `U` over any base being bounded by `U`. The inverse is unique on each side for a
different reason on each: on the relation by
`Stacks.Groupoids.PreRelation.ext_of_target_of_source`, which is where monicity of `j` is
used, and on the fibre product by `CategoryTheory.Limits.pullback.hom_ext`.

The sheaf-theoretic step is `Stacks.Groupoids.quotientChart_app_eq_iff_rel`, whose forward
direction is the one used here: the chart of the quotient sheaf identifies two points of `U`
exactly when they are related. Local injectivity of the sheafification unit, which that
theorem consumes through `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, is the
reason the hypothesis on the factoring morphism is pointwise injectivity rather than
monicity: a monomorphism of presheaves of types is pointwise injective, but the hypothesis is
stated in the form in which an isomorphism supplies it, so that no criterion for monicity in a
category of sheaves is needed. The factorization is read on elements by
`CategoryTheory.ConcreteCategory.congr_hom` applied to the component of the factorization
equation, rather than by rewriting inside the presheaf category.

Commutativity of the square is not automatic from the factorization: the factorization is an
equation of presheaves on the site, so it sees the relation scheme only through its points over
objects of the site, and `R` need not be one of them. It becomes available as soon as some
object of the site presents `R`, which for the groupoid form is the hypothesis that the big
fppf site contains the arrow scheme — a hypothesis the `represents` field of
`Stacks.Groupoids.FiniteFlatQuotient` carries anyway.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace Stacks.Groupoids

variable {S : Scheme.{u}}

/-- Evaluating a factorization `toQuotientSheaf ≫ q = yoneda.map f` on a point `z`. -/
private theorem app_toQuotientSheaf_apply {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {U R M : Over S} (j : PreRelation R U)
    (f : U ⟶ M) (q : (quotientSheaf J F j).obj ⟶ points F M)
    (hfac : toQuotientSheaf J F j ≫ q = F.op.whiskerLeft (yoneda.map f))
    {T : C} (z : ToType ((points F U).obj (op T))) :
    q.app (op T) ((toQuotientSheaf J F j).app (op T) z) = z ≫ f :=
  ConcreteCategory.congr_hom (NatTrans.congr_app hfac (op T)) z

/-- Two points of `U` over an object of the site which become equal after composition with a
morphism `f : U ⟶ M` factoring the projection onto the quotient sheaf through a pointwise
injective map of presheaves are related by the pre-relation.

The factorization turns equality of the two composites into equality of their images in the
quotient sheaf, and `Stacks.Groupoids.quotientChart_app_eq_iff_rel` turns that into being
related. -/
theorem rel_of_comp_eq_comp {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]
    (F : C ⥤ Over S) [F.Full] {U R M : Over S} (X : C) (hXU : F.obj X = U)
    (j : PreRelation R U) [hmonoj : Mono j] (hj : IsPreEquivalenceRelation j)
    (hRsh : Presheaf.IsSheaf J (points F R))
    (hUsh : Presheaf.IsSheaf J (points F U))
    (f : U ⟶ M) (q : (quotientSheaf J F j).obj ⟶ points F M)
    (hinj : ∀ (T : Cᵒᵖ) (x y : ToType ((quotientSheaf J F j).obj.obj T)),
      q.app T x = q.app T y → x = y)
    (hfac : toQuotientSheaf J F j ≫ q = F.op.whiskerLeft (yoneda.map f))
    {T : C} {a b : F.obj T ⟶ U} (hab : a ≫ f = b ≫ f) : j.Rel a b := by
  subst hXU
  have h1 : (toQuotientSheaf J F j).app (op T) a = (toQuotientSheaf J F j).app (op T) b :=
    hinj (op T) _ _ (by rw [app_toQuotientSheaf_apply J F j f q hfac,
      app_toQuotientSheaf_apply J F j f q hfac, hab])
  obtain ⟨x, hx⟩ := F.map_surjective (X := T) (Y := X) a
  obtain ⟨y, hy⟩ := F.map_surjective (X := T) (Y := X) b
  subst hx hy
  refine (quotientChart_app_eq_iff_rel J F X j hj hRsh hUsh x y).mp ?_
  rw [quotientChart_app, quotientChart_app]
  exact h1

/-- A morphism factoring the projection onto the quotient sheaf identifies the target and the
source of the pre-relation, provided some object of the site presents the relation scheme.

Without such an object the factorization constrains `f` only on points over objects of the
site, and the equation asserted here is an equation of morphisms out of the relation
scheme. -/
theorem target_comp_eq_source_comp_of_quotientSheafFactor {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {U R M : Over S} (X : C) (hXU : F.obj X = U)
    (j : PreRelation R U)
    (f : U ⟶ M) (q : (quotientSheaf J F j).obj ⟶ points F M)
    (hfac : toQuotientSheaf J F j ≫ q = F.op.whiskerLeft (yoneda.map f))
    {Z : C} (e : F.obj Z ≅ R) : j.target ≫ f = j.source ≫ f := by
  subst hXU
  have hsq : (toQuotientSheaf J F j).app (op Z) (e.hom ≫ j.source) =
      (toQuotientSheaf J F j).app (op Z) (e.hom ≫ j.target) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (sourceMap_toQuotientSheaf J F j) (op Z))
      e.hom
  have h2 : (e.hom ≫ j.source) ≫ f = (e.hom ≫ j.target) ≫ f := by
    rw [← app_toQuotientSheaf_apply J F j f q hfac, ← app_toQuotientSheaf_apply J F j f q hfac,
      hsq]
  rw [Category.assoc, Category.assoc] at h2
  exact ((cancel_epi e.hom).mp h2).symm

/-- **The relation is the kernel pair of a monomorphic representation of its quotient sheaf.**
For a relation `j` on `U = F.obj X` which is an equivalence relation on the points of every
test scheme and a morphism `f : U ⟶ M` of `S`-schemes which factors the projection onto the
quotient sheaf through a pointwise injective map of presheaves, the square formed by the target
and source maps of `j` and two copies of `f` is Cartesian, provided some object of the site
presents the fibre product `U ×_M U`.

The comparison morphism `R ⟶ U ×_M U` is inverted by the arrow of the relation witnessing that
the two projections of the fibre product are related, which exists by
`Stacks.Groupoids.rel_of_comp_eq_comp`. -/
theorem isPullback_of_quotientSheafFactor {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]
    (F : C ⥤ Over S) [F.Full] {U R M : Over S} (X : C) (hXU : F.obj X = U)
    (j : PreRelation R U) [hmonoj : Mono j] (hj : IsPreEquivalenceRelation j)
    (hRsh : Presheaf.IsSheaf J (points F R))
    (hUsh : Presheaf.IsSheaf J (points F U))
    (f : U ⟶ M) (hw : j.target ≫ f = j.source ≫ f)
    (q : (quotientSheaf J F j).obj ⟶ points F M)
    (hinj : ∀ (T : Cᵒᵖ) (x y : ToType ((quotientSheaf J F j).obj.obj T)),
      q.app T x = q.app T y → x = y)
    (hfac : toQuotientSheaf J F j ≫ q = F.op.whiskerLeft (yoneda.map f))
    {Y : C} (e : F.obj Y ≅ pullback f f) :
    IsPullback j.target j.source f f := by
  obtain ⟨r, hr1, hr2⟩ := rel_of_comp_eq_comp J F X hXU j hj hRsh hUsh f q hinj hfac
    (T := Y) (a := e.hom ≫ pullback.fst f f) (b := e.hom ≫ pullback.snd f f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hg1 : (e.inv ≫ r) ≫ j.target = pullback.fst f f := by
    rw [Category.assoc, hr1, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hg2 : (e.inv ≫ r) ≫ j.source = pullback.snd f f := by
    rw [Category.assoc, hr2, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hk : IsIso (pullback.lift j.target j.source hw) := by
    refine ⟨e.inv ≫ r, ?_, ?_⟩
    · refine PreRelation.ext_of_target_of_source j ?_ ?_
      · rw [Category.assoc, hg1, pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, hg2, pullback.lift_snd, Category.id_comp]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, hg1, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, hg2, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift j.target j.source hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end Stacks.Groupoids

namespace AlgebraicGeometry

open Stacks.Groupoids

/-- **The kernel-pair clause of Stacks 07S6 from its representation clause.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S` whose pre-relation `(t, s)` is an equivalence
relation, and let `f : U ⟶ M` be a morphism of `S`-schemes under which `M` represents the fppf
quotient sheaf `U/R` on one big fppf site of `S` containing `S`, `U` and `R`, compatibly with
`f`. Then `(t, s)` is the kernel pair of `f`, that is `R = U ×_M U`.

No bound on `M` is needed: the fibre product `U ×_M U` belongs to the site because `U` does.
The representation is consumed only through pointwise injectivity of the representing
morphism, so this is a strictly weaker hypothesis than the `represents` field of
`Stacks.Groupoids.FiniteFlatQuotient`, which asks for it on every sufficiently large site.

Together with finite local freeness and surjectivity of `f` this is what
`AlgebraicGeometry.finiteFlatQuotientOfIsPullback` consumes; the existence of `f` is the
content of Stacks 07S6 and is a hypothesis here, so nothing in this file carries that tag. -/
@[sga "3 IV 4.6.5" "Converse direction"]
theorem isPullback_of_quotientSheaf_isRepresented {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] {M : Over S} (f : G.objects ⟶ M)
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hrep :
      let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
      let J := BigFppfOver.topology B S hS
      let j : PreRelation G.arrows G.objects := prod.lift G.target G.source
      ∃ hM : Presheaf.IsSheaf J (points F M),
        ∃ q : quotientSheaf J F j ⟶ (⟨points F M, hM⟩ : Sheaf J (Type u)),
          IsIso q ∧ toQuotientSheaf J F j ≫ q.hom = F.op.whiskerLeft (yoneda.map f)) :
    IsPullback G.target G.source f f := by
  obtain ⟨hM, q, hq, hfac⟩ := hrep
  have htgt : PreRelation.target (prod.lift G.target G.source) = G.target :=
    prod.lift_fst G.target G.source
  have hsrc : PreRelation.source (prod.lift G.target G.source) = G.source :=
    prod.lift_snd G.target G.source
  have hequiv : IsEquivalenceRelation
      (PreRelation.target (prod.lift G.target G.source : PreRelation G.arrows G.objects))
      (PreRelation.source (prod.lift G.target G.source : PreRelation G.arrows G.objects)) := by
    rw [htgt, hsrc]; infer_instance
  have hsplit := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (prod.lift G.target G.source : PreRelation G.arrows G.objects)).mp hequiv
  have hinj : ∀ (T : (BigFppfOver B S hS)ᵒᵖ)
      (x y : ToType ((quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (prod.lift G.target G.source : PreRelation G.arrows G.objects)).obj.obj T)),
      q.hom.app T x = q.hom.app T y → x = y := by
    intro T x y h
    have _ : IsIso q.hom := (sheafToPresheaf _ _).map_isIso q
    exact ((isIso_iff_bijective (q.hom.app T)).mp inferInstance).1 h
  have hPB : B.Contains (pullback f f).left :=
    lt_of_eq_of_lt
      (Scheme.size_congr (X := (pullback f f).left) (PreservesPullback.iso (Over.forget S) f f))
      (Scheme.size_pullback_lt f.left f.left hU hU)
  have hw := target_comp_eq_source_comp_of_quotientSheafFactor
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (Over.mk (X := B.obj hS) (Y := (⟨G.objects.left, hU⟩ : B.Schemes))
      (ObjectProperty.homMk G.objects.hom)) rfl
    (prod.lift G.target G.source) f q.hom hfac
    (Z := Over.mk (X := B.obj hS) (Y := (⟨G.arrows.left, hR⟩ : B.Schemes))
      (ObjectProperty.homMk G.arrows.hom)) (Iso.refl _)
  have hpb : IsPullback
      (PreRelation.target (prod.lift G.target G.source : PreRelation G.arrows G.objects))
      (PreRelation.source (prod.lift G.target G.source : PreRelation G.arrows G.objects))
      f f :=
    isPullback_of_quotientSheafFactor (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion)
      (Over.mk (X := B.obj hS) (Y := (⟨G.objects.left, hU⟩ : B.Schemes))
        (ObjectProperty.homMk G.objects.hom)) rfl
      (prod.lift G.target G.source) (hmonoj := hsplit.1) hsplit.2
      (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS G.arrows)
      (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS G.objects)
      f hw q.hom hinj hfac
      (Y := Over.mk (X := B.obj hS) (Y := (⟨(pullback f f).left, hPB⟩ : B.Schemes))
        (ObjectProperty.homMk (pullback f f).hom)) (Iso.refl _)
  rw [htgt, hsrc] at hpb
  exact hpb

end AlgebraicGeometry

end

end
