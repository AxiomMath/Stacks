module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleLiftDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOverAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleQuasiInverseRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# The stages of a dependent product along a representable thickening

Let `S` be a scheme contained in a big fppf site `B`, let `i : I ⟶ X` be a representable
thickening of fppf sheaves on the big fppf site of `S` and let `p : W ⟶ I` be representable by
algebraic spaces and étale. This file computes the base changes of the dependent product
`U_{W, p}` of Stacks 0DEG to the representable points of `X`, and the affine étale charts of a
sheaf representable étale over an object of the site. These are the two ingredients of the
proof that `U_{W, p}` is a formal algebraic space when `X` is an *affine* formal algebraic
space.

## Main definitions

* `AlgebraicGeometry.FormalSpace.liftAlongIsoOfIso`: the dependent product transported along an
  isomorphism of the morphism it is taken of.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_liftAlong_of_isThickening`: the
  dependent product, along a thickening `T₀ ⟶ T` of objects of the site, of an affine object of
  the site étale over `T₀` is represented by an affine object of the site étale over `T`. This
  is **Stacks 039R** and **Stacks 06AD** fed into
  `AlgebraicGeometry.FormalSpace.exists_iso_liftAlong_of_isThickening`.
* `AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_pullback_liftAlongBase`: the base
  change of `U_{W, p}` to a representable point of `X`, under the hypothesis that the base
  change of `p` to the stage of that point is affine. Its conclusion has the shape of its
  hypothesis, which is what lets it be applied twice in succession — first down to a stage of
  the thickening, then down to a stage of the base.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_affine_stages`: **Stacks
  0GVM** in the form the previous statement feeds: a sheaf representable over an affine formal
  algebraic space all of whose base changes to the stages of a presentation are affine is an
  affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.exists_affine_etale_charts_of_isRepresentableEtale`: **Stacks
  03FX** for a sheaf representable étale over an object `T` of the site, in the two forms its
  consumer needs — a family of affine objects of the site étale over `T` mapping to the sheaf,
  and, for every point of the sheaf given by an object of the site, an affine étale cover of
  that object, surjective on points, each member of which maps to one of the charts.

## Implementation notes

**Why the conclusions are existential.** The objects produced here are base changes along
relatively representable morphisms, so they are only defined up to isomorphism; carrying them
as existential witnesses keeps the statements free of a choice of representing object, and
every consumer destructures them immediately.

**Why `liftSheaf ∘ schemeSpace` rather than the sheafified Yoneda embedding.** The presheaf
underlying `liftSheaf (schemeSpace T)` is `uliftYoneda.obj T` on the nose, which is what
relative representability is tested against; the sheafified representable `h_T^#` is only
isomorphic to it. The two are identified by
`AlgebraicGeometry.FormalSpace.liftSheafYonedaSpaceIsoSheafifiedYoneda`, and the presentations
of affine formal algebraic spaces are written with the sheafified form, so the identification is
applied wherever a stage of a presentation meets a dependent product.

**The affine étale charts.** A sheaf representable étale over an object of the site is an
algebraic space, read off the base change along the identity point of the target, and after
descending to the value universe of the site Stacks 03FX gives it a surjective étale chart `U`
by a single object of the site. The charts are the affine opens of `U`: each is étale over `T`
because `U ⟶ T` is. The refinement of an arbitrary point by those charts is the affine open
cover of the base change of `U` along the point, decomposed by the affine opens of `U`; both
decompositions are open covers, so the composite is surjective on points, which is the form
`AlgebraicGeometry.FormalSpace.exists_affine_etale_cover_lift_of_isThickening` consumes.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of the dependent product along an isomorphism of its source -/

/-- **The dependent product only depends on the morphism `W ⟶ I` up to isomorphism of `W`.**
An isomorphism `W ≅ W'` over `I` induces an isomorphism `U_{W, p} ≅ U_{W', p'}` over `X`, by
functoriality of `AlgebraicGeometry.FormalSpace.liftAlongMap`. -/
def liftAlongIsoOfIso {X I W W' : FppfSheaf B S hS} (i : I ⟶ X) {p : W ⟶ I} {p' : W' ⟶ I}
    (e : W ≅ W') (he : e.hom ≫ p' = p) :
    liftAlong B S hS i p ≅ liftAlong B S hS i p' where
  hom := liftAlongMap B S hS i e.hom he
  inv := liftAlongMap B S hS i e.inv (by rw [← he, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [liftAlongMap_comp, liftAlongMap_congr B S hS i e.hom_inv_id _ (Category.id_comp p),
      liftAlongMap_id]
  inv_hom_id := by
    rw [liftAlongMap_comp, liftAlongMap_congr B S hS i e.inv_hom_id _ (Category.id_comp p'),
      liftAlongMap_id]

/-- The isomorphism `liftAlongIsoOfIso B S hS i e he` commutes with the structure morphisms
`liftAlongBase` of the two dependent products to `X`. -/
@[reassoc (attr := simp)]
theorem liftAlongIsoOfIso_hom_comp_liftAlongBase {X I W W' : FppfSheaf B S hS} (i : I ⟶ X)
    {p : W ⟶ I} {p' : W' ⟶ I} (e : W ≅ W') (he : e.hom ≫ p' = p) :
    (liftAlongIsoOfIso B S hS i e he).hom ≫ liftAlongBase B S hS i p'
      = liftAlongBase B S hS i p :=
  liftAlongMap_comp_base B S hS i e.hom he

/-! ### The dependent product of an affine chart along a thickening of the site -/

variable {B S hS}

/-- An affine object of the site which is étale over the thin end of a thickening of objects
of the site is, as a sheaf over that thin end, the base change of an affine object étale over
the thick end: the cartesian square of Stacks 039R, recorded inside the site. -/
theorem exists_isPullback_affine_etale_lift_of_isThickening {T₀ T : BigFppfOver B S hS}
    (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (A : BigFppfOver B S hS) (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (a : A ⟶ T₀) (ha : Etale ((BigFppfOver.toScheme B S hS).map a)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T) (b : A ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧ IsPullback b a q k := by
  obtain ⟨V, q, hq, hVaff, e, he⟩ :=
    exists_affine_etale_lift_of_isThickening B S hS k hk A hA
      ((BigFppfOver.toScheme B S hS).map a) ha
  obtain ⟨b, hb⟩ := Space.exists_isPullback_of_iso_pullback_toScheme B S hS q k a e he
  exact ⟨V, q, b, hVaff, hq, hb⟩

/-- **The dependent product, along a thickening `T₀ ⟶ T` of objects of the site, of an affine
object of the site étale over `T₀`, is represented by an affine object of the site étale over
`T`.**

The affine chart `A` over `T₀` lifts, by Stacks 039R and Stacks 06AD, to an affine object `V`
étale over `T` whose base change to `T₀` is `A`; and the dependent product along a thickening
of a base change of that thickening is the object one started from, which is
`AlgebraicGeometry.FormalSpace.exists_iso_liftAlong_of_isThickening`.

The hypothesis is stated for an arbitrary sheaf `W` over `T₀` identified with `A`, rather than
for `A` itself, so that the conclusion is again of the shape of the hypothesis and the
statement applies to its own output. -/
theorem exists_affine_etale_iso_liftAlong_of_isThickening {T₀ T : BigFppfOver B S hS}
    (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {W : FppfSheaf B S hS} {p : W ⟶ liftSheaf B S hS (schemeSpace T₀)}
    (A : BigFppfOver B S hS) (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (a : A ⟶ T₀) (ha : Etale ((BigFppfOver.toScheme B S hS).map a))
    (ε : liftSheaf B S hS (schemeSpace A) ≅ W)
    (hε : ε.hom ≫ p = liftSheafMap B S hS (schemeSpaceMap a)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        ∃ e : liftSheaf B S hS (schemeSpace V)
            ≅ liftAlong B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p,
          e.hom ≫ liftAlongBase B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p
            = liftSheafMap B S hS (schemeSpaceMap q) := by
  obtain ⟨V, q, b, hVaff, hq, hpb⟩ :=
    exists_isPullback_affine_etale_lift_of_isThickening k hk A hA a ha
  obtain ⟨e, he⟩ := exists_iso_liftAlong_of_isThickening (B := B) (S := S) (hS := hS) k hk
    (a := schemeSpaceMap q)
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS q).2 hq))
    (p := liftSheafMap B S hS (schemeSpaceMap a))
    (c₀ := liftSheafMap B S hS (schemeSpaceMap b)) (hpb.map (uliftYoneda.{u + 1}))
  refine ⟨V, q, hVaff, hq, e ≪≫ liftAlongIsoOfIso B S hS _ ε hε, ?_⟩
  rw [Iso.trans_hom, Category.assoc, liftAlongIsoOfIso_hom_comp_liftAlongBase, he]

/-! ### The sheaves represented by the objects of the site -/

/-- A morphism between the fppf sheaves represented by two objects of the site is induced by a
morphism of the site: the universe-lifted Yoneda embedding is full. -/
theorem exists_liftSheafMap_schemeSpaceMap_eq {A C : BigFppfOver B S hS}
    (f : liftSheaf B S hS (schemeSpace A) ⟶ liftSheaf B S hS (schemeSpace C)) :
    ∃ π : A ⟶ C, liftSheafMap B S hS (schemeSpaceMap π) = f :=
  ⟨(uliftYoneda.{u + 1}).preimage f.hom,
    Sheaf.hom_ext ((uliftYoneda.{u + 1}).map_preimage f.hom)⟩

/-- The fppf sheaf represented by an object of the site is functorial in that object. -/
@[simp]
theorem liftSheafMap_schemeSpaceMap_comp {A C D : BigFppfOver B S hS} (g : A ⟶ C) (k : C ⟶ D) :
    liftSheafMap B S hS (schemeSpaceMap (g ≫ k))
      = liftSheafMap B S hS (schemeSpaceMap g) ≫ liftSheafMap B S hS (schemeSpaceMap k) :=
  Sheaf.hom_ext ((uliftYoneda.{u + 1}).map_comp g k)

/-- **The fibre product of two objects of the site represents the fibre product of the fppf
sheaves they represent.** -/
theorem exists_iso_pullback_liftSheafMap {A C D : BigFppfOver B S hS} (a : A ⟶ C) (d : D ⟶ C) :
    ∃ ε : liftSheaf B S hS (schemeSpace (Limits.pullback a d))
        ≅ Limits.pullback (liftSheafMap B S hS (schemeSpaceMap a))
            (liftSheafMap B S hS (schemeSpaceMap d)),
      ε.hom ≫ pullback.snd (liftSheafMap B S hS (schemeSpaceMap a))
            (liftSheafMap B S hS (schemeSpaceMap d))
        = liftSheafMap B S hS (schemeSpaceMap (Limits.pullback.snd a d)) := by
  have hsq : IsPullback (liftSheafMap B S hS (schemeSpaceMap (Limits.pullback.fst a d)))
      (liftSheafMap B S hS (schemeSpaceMap (Limits.pullback.snd a d)))
      (liftSheafMap B S hS (schemeSpaceMap a)) (liftSheafMap B S hS (schemeSpaceMap d)) :=
    IsPullback.of_map_of_faithful
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      ((IsPullback.of_hasPullback a d).map (uliftYoneda.{u + 1}))
  exact ⟨hsq.isoIsPullback _ _ (IsPullback.of_hasPullback _ _),
    hsq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback _ _)⟩

/-! ### The dependent product, base changed to a representable point of the base -/

/-- **A representable thickening, base changed to a representable point of its target.** Let
`i : I ⟶ X` be a representable thickening and `x : T ⟶ X` a point of `X` given by an object `T`
of the site. Then `T ×_X I` is an object `T₀` of the site and the induced morphism `T₀ ⟶ T` is
a thickening. -/
theorem exists_isPullback_point_of_isRepresentableThickening {X I : FppfSheaf B S hS}
    {i : I ⟶ X} (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    {T : BigFppfOver B S hS} (x : liftSheaf B S hS (schemeSpace T) ⟶ X) :
    ∃ (T₀ : BigFppfOver B S hS) (k : T₀ ⟶ T) (g : liftSheaf B S hS (schemeSpace T₀) ⟶ I),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) ∧
      IsPullback (liftSheafMap B S hS (schemeSpaceMap k)) g x i :=
  ⟨hi.rep.pullback x.hom, hi.rep.snd x.hom, ⟨hi.rep.fst x.hom⟩, hi.property_snd x.hom,
    IsPullback.of_map_of_faithful
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      (hi.rep.isPullback x.hom).flip⟩

/-- **The base change of the dependent product `U_{W, p}` to a representable point of `X`.**
Let `x : T ⟶ X` be a point of `X` given by an object `T` of the site whose base change along
`i : I ⟶ X` is an object `T₀` of the site. Then

`U_{W, p} ×_X T = U_{W ×_I T₀, p₀}`,

the dependent product along `T₀ ⟶ T` of the base change of `p` to `T₀`.

This is `AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange` at a representable
point; the point of stating it separately is that the base of the resulting dependent product
is a thickening of *objects of the site*, which is the shape the affine charts of Stacks 039R
consume. -/
theorem exists_isPullback_liftAlong_point {X I W : FppfSheaf B S hS} {i : I ⟶ X} (p : W ⟶ I)
    {T T₀ : BigFppfOver B S hS} {k : T₀ ⟶ T}
    {x : liftSheaf B S hS (schemeSpace T) ⟶ X} {g : liftSheaf B S hS (schemeSpace T₀) ⟶ I}
    (hsq : IsPullback (liftSheafMap B S hS (schemeSpaceMap k)) g x i) :
    ∃ c : liftAlong B S hS (liftSheafMap B S hS (schemeSpaceMap k)) (pullback.snd p g)
        ⟶ liftAlong B S hS i p,
      IsPullback c (liftAlongBase B S hS (liftSheafMap B S hS (schemeSpaceMap k))
        (pullback.snd p g)) (liftAlongBase B S hS i p) x :=
  ⟨_, isPullback_liftAlongBaseChange (pullback.fst p g)
    (isSectionwisePullback_of_isPullback B S hS hsq)
    (isSectionwisePullback_of_isPullback B S hS (IsPullback.of_hasPullback p g).flip)
    hsq.w pullback.condition⟩

/-! ### The affine stages of a dependent product -/

/-- **If the base change of `p : W ⟶ I` to the stage `T₀` of a representable point `x : T ⟶ X`
is represented by an affine object of the site étale over `T₀`, then the base change of
`U_{W, p}` to that point is represented by an affine object of the site étale over `T`.**

The base change of `U_{W, p}` is the dependent product, along the thickening `T₀ ⟶ T` of
objects of the site, of the base change of `p`, by
`AlgebraicGeometry.FormalSpace.exists_isPullback_liftAlong_point`; and that dependent product
is represented by an affine object étale over `T` by
`AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_liftAlong_of_isThickening`.

The conclusion has the shape of the hypothesis, with `U_{W, p} ⟶ X` for `p` and `x` for `g`,
so the statement applies to its own output: that is how the affine stages of a dependent
product over an affine formal algebraic space are computed, in two steps -- first down to a
stage of the thickening, then down to a stage of the base. -/
theorem exists_affine_etale_iso_pullback_liftAlongBase {X I W : FppfSheaf B S hS} {i : I ⟶ X}
    {p : W ⟶ I} {T T₀ : BigFppfOver B S hS} {k : T₀ ⟶ T}
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {x : liftSheaf B S hS (schemeSpace T) ⟶ X} {g : liftSheaf B S hS (schemeSpace T₀) ⟶ I}
    (hsq : IsPullback (liftSheafMap B S hS (schemeSpaceMap k)) g x i)
    (A : BigFppfOver B S hS) (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (a : A ⟶ T₀) (ha : Etale ((BigFppfOver.toScheme B S hS).map a))
    (ε : liftSheaf B S hS (schemeSpace A) ≅ pullback p g)
    (hε : ε.hom ≫ pullback.snd p g = liftSheafMap B S hS (schemeSpaceMap a)) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        ∃ e : liftSheaf B S hS (schemeSpace V) ≅ pullback (liftAlongBase B S hS i p) x,
          e.hom ≫ pullback.snd (liftAlongBase B S hS i p) x
            = liftSheafMap B S hS (schemeSpaceMap q) := by
  obtain ⟨c, hc⟩ := exists_isPullback_liftAlong_point p hsq
  obtain ⟨V, q, hVaff, hq, e, he⟩ :=
    exists_affine_etale_iso_liftAlong_of_isThickening k hk A hA a ha ε hε
  refine ⟨V, q, hVaff, hq, e ≪≫ hc.isoIsPullback _ _ (IsPullback.of_hasPullback _ x), ?_⟩
  rw [Iso.trans_hom, Category.assoc, IsPullback.isoIsPullback_hom_snd, he]

/-! ### A sheaf over an affine formal algebraic space with affine stages -/

attribute [local instance] sheaf_hasColimits

/-- **A sheaf representable over an affine formal algebraic space whose base change to every
stage of a presentation is affine is itself an affine formal algebraic space.**

By `AlgebraicGeometry.FormalSpace.isoColimitPresentationBaseChange` the sheaf is the colimit of
its base changes to the stages, the transition morphisms of that colimit are base changes of
the transition morphisms of the presentation and hence representable thickenings, and the
set-theoretic condition of Stacks 0AIS descends from the base along the representable structure
morphism. Stacks 0GVM then applies. -/
theorem isAffineFormalAlgebraicSpace_of_affine_stages
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃ν μ : Λ⦄ (f : ν ⟶ μ), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {Y Z : FppfSheaf B S hS} (eY : Y ≅ colimit (presentationDiagram D))
    (hYset : SatisfiesSetTheoreticCondition B S hS Y) (u : Z ⟶ Y)
    (hu : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS u.hom)
    (hst : ∀ ν : Λ, ∃ V : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Nonempty (liftSheaf B S hS (schemeSpace V) ≅
        pullback (colimit.ι (presentationDiagram D) ν) (u ≫ eY.hom))) :
    IsAffineFormalAlgebraicSpace B S hS Z := by
  set v : Z ⟶ colimit (presentationDiagram D) := u ≫ eY.hom with hv
  set E : Λ ⥤ FppfSheaf B S hS :=
    _root_.CategoryTheory.Limits.baseChangeDiagram
      (colimit.cocone (presentationDiagram D)) v with hE
  -- every stage of the base-changed diagram is an affine formal algebraic space
  have hEaff : ∀ ν : Λ, IsAffineFormalAlgebraicSpace B S hS (E.obj ν) := by
    intro ν
    obtain ⟨V, hVaff, ⟨εV⟩⟩ := hst ν
    exact isAffineFormalAlgebraicSpace_of_iso B S hS εV
      (isAffineFormalAlgebraicSpace_of_iso B S hS
        (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).symm
        (isAffineFormalAlgebraicSpace_sheafifiedYoneda' B S hS V hVaff))
  -- the transition morphisms of the presentation are representable thickenings
  have hFthick : ∀ ⦃ν μ : Λ⦄ (f : ν ⟶ μ), MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ((presentationDiagram D).map f) := by
    intro ν μ f
    exact (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.map f)))).mpr
      (isRepresentableThickeningULift_sheafifiedYoneda_map B S hS _ (hD f))
  -- hence so are the transition morphisms of the base-changed diagram
  have hEthick : ∀ ⦃ν μ : Λ⦄ (f : ν ⟶ μ), MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (E.map f) := fun ν μ f ↦
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (equifibered_baseChangeπ (colimit.cocone (presentationDiagram D)) v f).flip (hFthick f)
  exact isAffineFormalAlgebraicSpace_colimit B S hS E hEaff hEthick Z
    (isoColimitPresentationBaseChange D v)
    (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS u hu hYset)

/-! ### The comparison `W ⟶ U_{W, p}` is natural in `W` -/

/-- **The comparison `W ⟶ U_{W, p}` is natural in `W`.** A morphism `q : W ⟶ W'` over `I`
commutes with the comparisons, because the quasi-inverse on morphisms postcomposes the second
component of a pair and the comparison of a section of `W` has that section, restricted, for
its second component. -/
theorem liftAlongSection_comp_liftAlongMap {X I W W' : FppfSheaf B S hS} {i : I ⟶ X}
    (hi : ∀ T : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op T)))
    {p : W ⟶ I} {p' : W' ⟶ I} (q : W ⟶ W') (hq : q ≫ p' = p) :
    liftAlongSection B S hS hi (p := p) ≫ liftAlongMap B S hS i q hq
      = q ≫ liftAlongSection B S hS hi (p := p') := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_))
  refine LiftAlong.ext _ _ ?_ fun T' t w h h' ↦ ?_
  · show i.hom.app T (p.hom.app T y)
      = i.hom.app T (p'.hom.app T (q.hom.app T y))
    rw [← comp_app_apply B S hS q p' T.unop y, hq]
  · exact app_map_op B S hS q t y

/-! ### Affine étale charts of a sheaf representable étale over an object of the site -/

/-- A morphism of fppf sheaves which is representable by algebraic spaces and étale and whose
target is represented by an object of the site has an algebraic space for its source and is
étale as a morphism of algebraic spaces: both are read off its base change along the identity
point of the target. -/
theorem isAlgebraicSpaceULift_isEtaleULift_of_isRepresentableEtale
    {Z : FppfSheaf B S hS} {T : BigFppfOver B S hS} {f : Z ⟶ liftSheaf B S hS (schemeSpace T)}
    (hf : IsRepresentableEtale B S hS f) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj
      ∧ Space.IsEtaleULift.{u + 1} B S hS f.hom := by
  have key : ∀ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
      (g : W ⟶ (uliftYoneda.{u + 1}).obj T),
      (∀ (V : BigFppfOver B S hS)
        (ξ : (uliftYoneda.{u + 1}).obj V ⟶ (uliftYoneda.{u + 1}).obj T),
        Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ g)) →
      (∀ (V : BigFppfOver B S hS)
        (ξ : (uliftYoneda.{u + 1}).obj V ⟶ (uliftYoneda.{u + 1}).obj T),
        Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ g)) →
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS W
        ∧ Space.IsEtaleULift.{u + 1} B S hS g := by
    intro W g h1 h2
    have hsq : IsPullback (pullback.fst (𝟙 ((uliftYoneda.{u + 1}).obj T)) g)
        (pullback.snd (𝟙 ((uliftYoneda.{u + 1}).obj T)) g)
        (𝟙 ((uliftYoneda.{u + 1}).obj T)) g := IsPullback.of_hasPullback _ _
    have hiso : IsIso (pullback.snd (𝟙 ((uliftYoneda.{u + 1}).obj T)) g) :=
      hsq.isIso_snd_of_isIso
    have hw : pullback.snd (𝟙 ((uliftYoneda.{u + 1}).obj T)) g ≫ g
        = pullback.fst (𝟙 ((uliftYoneda.{u + 1}).obj T)) g := by
      rw [← hsq.w, Category.comp_id]
    refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS
        (asIso (pullback.snd (𝟙 ((uliftYoneda.{u + 1}).obj T)) g))
        (h1 T (𝟙 ((uliftYoneda.{u + 1}).obj T))), ?_⟩
    refine (Space.isEtaleULift_isIso_comp_iff B S hS
      (pullback.snd (𝟙 ((uliftYoneda.{u + 1}).obj T)) g) g).mp ?_
    rw [hw]
    exact h2 T (𝟙 ((uliftYoneda.{u + 1}).obj T))
  exact key Z.obj f.hom (fun V ξ ↦ hf.1 V ξ) (fun V ξ ↦ hf.2 V ξ)

/-- **A sheaf representable étale over an object `T` of the site has a family of affine étale
charts, and every point of it refines by affines to that family.**

The charts are the affine opens of the chart of Stacks 03FX: the source `Z` is an algebraic
space, by
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_isEtaleULift_of_isRepresentableEtale`,
so after descending to the value universe of the site it has a surjective étale chart `U` by a
single object of the site, and the affine opens of `U` are étale over `T` because `U ⟶ T` is.

The second clause is what joint surjectivity of the resulting family of dependent products is
proved from: for a point `N ⟶ Z`, the base change `N ×_Z U` is an object of the site
surjective and étale over `N`, its decomposition by the affine opens of `U` is an open cover of
it, and refining that by affines gives an affine étale cover of `N`, surjective on points, each
member of which maps to one of the charts compatibly with the point. -/
theorem exists_affine_etale_charts_of_isRepresentableEtale
    {Z : FppfSheaf B S hS} {T : BigFppfOver B S hS} {f : Z ⟶ liftSheaf B S hS (schemeSpace T)}
    (hf : IsRepresentableEtale B S hS f) :
    ∃ (M : Type u) (A : M → BigFppfOver B S hS) (a : ∀ m, A m ⟶ T)
      (w : ∀ m, liftSheaf B S hS (schemeSpace (A m)) ⟶ Z),
      (∀ m, IsAffine ((BigFppfOver.toScheme B S hS).obj (A m))) ∧
      (∀ m, Etale ((BigFppfOver.toScheme B S hS).map (a m))) ∧
      (∀ m, w m ≫ f = liftSheafMap B S hS (schemeSpaceMap (a m))) ∧
      ∀ (N : BigFppfOver B S hS) (z : liftSheaf B S hS (schemeSpace N) ⟶ Z),
        ∃ (K : Type u) (E : K → BigFppfOver B S hS) (π : ∀ n, E n ⟶ N) (m : K → M)
          (t : ∀ n, E n ⟶ A (m n)),
          (∀ n, IsAffine ((BigFppfOver.toScheme B S hS).obj (E n))) ∧
          (∀ n, Etale ((BigFppfOver.toScheme B S hS).map (π n))) ∧
          (∀ x : (BigFppfOver.toScheme B S hS).obj N,
            ∃ n y, (BigFppfOver.toScheme B S hS).map (π n) y = x) ∧
          ∀ n, liftSheafMap B S hS (schemeSpaceMap (t n)) ≫ w (m n)
            = liftSheafMap B S hS (schemeSpaceMap (π n)) ≫ z := by
  classical
  obtain ⟨hZalg, hfet⟩ :=
    isAlgebraicSpaceULift_isEtaleULift_of_isRepresentableEtale hf
  obtain ⟨Z', hZ', ⟨ζ⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZalg
  obtain ⟨U, fU, -, -, -, -, hUsurj, hUet, -, -, -, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS Z' hZ'
  -- the chart of `Z` by a single object of the site, read as a morphism of fppf sheaves
  set wU : liftSheaf B S hS (schemeSpace U) ⟶ Z :=
    ⟨Functor.whiskerRight fU uliftFunctor.{u + 1} ≫ ζ.hom⟩ with hwU
  have hwUet : Space.IsEtaleULift.{u + 1} B S hS wU.hom := by
    show Space.IsEtaleULift.{u + 1} B S hS
      (Functor.whiskerRight fU uliftFunctor.{u + 1} ≫ ζ.hom)
    rw [Space.isEtaleULift_comp_isIso_iff]
    exact (Space.isEtaleULift_whiskerRight_iff B S hS fU).mpr
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS fU).mpr hUet)
  -- the composite `U ⟶ T`, inside the site, and its étaleness
  obtain ⟨u₀, hu₀⟩ := exists_liftSheafMap_schemeSpaceMap_eq (wU ≫ f)
  have hu₀et : Etale ((BigFppfOver.toScheme B S hS).map u₀) := by
    have h : Space.IsEtaleULift.{u + 1} B S hS ((wU ≫ f).hom) :=
      isEtaleULift_comp B S hS hwUet hfet
    rw [← hu₀] at h
    exact (Space.isEtaleULift_uliftYoneda_map_iff B S hS u₀).mp h
  -- the affine opens of the chart
  obtain ⟨M, A, ι, hAaff, hιopen, -, hιcov⟩ := BigFppfOver.exists_affine_open_cover' B S hS U
  have hopet : ∀ {A C : BigFppfOver B S hS} (g : A ⟶ C),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g) →
        Etale ((BigFppfOver.toScheme B S hS).map g) := fun g _ ↦ inferInstance
  refine ⟨M, A, fun m ↦ ι m ≫ u₀, fun m ↦ liftSheafMap B S hS (schemeSpaceMap (ι m)) ≫ wU,
    hAaff, fun m ↦ ?_, fun m ↦ ?_, ?_⟩
  · rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (hopet _ (hιopen m)) hu₀et
  · show liftSheafMap B S hS (schemeSpaceMap (ι m)) ≫ wU ≫ f
      = liftSheafMap B S hS (schemeSpaceMap (ι m ≫ u₀))
    rw [← hu₀, liftSheafMap_schemeSpaceMap_comp]
  intro N z
  -- the point of `Z`, descended to the value universe of the site
  obtain ⟨z', hz'⟩ : ∃ z' : yoneda.obj N ⟶ Z',
      Functor.whiskerRight z' uliftFunctor.{u + 1} ≫ ζ.hom = z.hom := by
    refine ⟨(liftFullyFaithful B S hS).preimage (z.hom ≫ ζ.inv), ?_⟩
    exact Eq.trans (congrArg (fun m ↦ m ≫ ζ.hom)
        ((liftFullyFaithful B S hS).map_preimage (z.hom ≫ ζ.inv)))
      ((Category.assoc z.hom ζ.inv ζ.hom).trans
        ((congrArg (fun m ↦ z.hom ≫ m) ζ.inv_hom_id).trans (Category.comp_id z.hom)))
  -- the base change of the chart to `N`, an object of the site surjective and étale over `N`
  set Q : BigFppfOver B S hS := hUsurj.rep.pullback z' with hQ
  set qN : Q ⟶ N := hUsurj.rep.snd z' with hqN
  have hqNsurj : Surjective ((BigFppfOver.toScheme B S hS).map qN) := hUsurj.property_snd z'
  have hqNet : Etale ((BigFppfOver.toScheme B S hS).map qN) :=
    hUet.property z' (hUsurj.rep.fst z') (hUsurj.rep.snd z') (hUsurj.rep.isPullback z')
  set ρ : Q ⟶ U := yoneda.preimage (hUsurj.rep.fst z') with hρ
  have hρw : liftSheafMap B S hS (schemeSpaceMap ρ) ≫ wU
      = liftSheafMap B S hS (schemeSpaceMap qN) ≫ z := by
    refine Sheaf.hom_ext ?_
    show Functor.whiskerRight (yoneda.map ρ) uliftFunctor.{u + 1} ≫
        (Functor.whiskerRight fU uliftFunctor.{u + 1} ≫ ζ.hom)
      = Functor.whiskerRight (yoneda.map qN) uliftFunctor.{u + 1} ≫ z.hom
    rw [← hz', ← Category.assoc, ← Category.assoc, ← Functor.whiskerRight_comp,
      ← Functor.whiskerRight_comp, yoneda.map_preimage, (hUsurj.rep.isPullback z').w]
  -- the pieces of `Q` over the affine opens of the chart are open in `Q` and cover it
  have hsq : ∀ m, IsPullback
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst ρ (ι m)))
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd ρ (ι m)))
      ((BigFppfOver.toScheme B S hS).map ρ) ((BigFppfOver.toScheme B S hS).map (ι m)) :=
    fun m ↦ (IsPullback.of_hasPullback ρ (ι m)).map (BigFppfOver.toScheme B S hS)
  have hpbet : ∀ m, Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst ρ (ι m))) :=
    fun m ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq m).flip
      (hopet _ (hιopen m))
  -- the affine open covers of those pieces
  choose Kp Ep πp hEpaff hEpopen hEpsieve hEpcov using
    fun m : M ↦ BigFppfOver.exists_affine_open_cover' B S hS (Limits.pullback ρ (ι m))
  refine ⟨Σ m : M, Kp m, fun n ↦ Ep n.1 n.2,
    fun n ↦ πp n.1 n.2 ≫ Limits.pullback.fst ρ (ι n.1) ≫ qN, fun n ↦ n.1,
    fun n ↦ πp n.1 n.2 ≫ Limits.pullback.snd ρ (ι n.1),
    fun n ↦ hEpaff n.1 n.2, fun n ↦ ?_, ?_, fun n ↦ ?_⟩
  · rw [Functor.map_comp, Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (hopet _ (hEpopen n.1 n.2))
      (MorphismProperty.comp_mem _ _ _ (hpbet n.1) hqNet)
  · intro x
    obtain ⟨q, hq⟩ := hqNsurj.surj x
    obtain ⟨m, y, hy⟩ := hιcov ((BigFppfOver.toScheme B S hS).map ρ q)
    obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback q y hy.symm
    obtain ⟨n, e, hn⟩ := hEpcov m ((hsq m).isoPullback.inv p)
    refine ⟨⟨m, n⟩, e, ?_⟩
    have hfst : (hsq m).isoPullback.inv ≫
        (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst ρ (ι m))
        = pullback.fst ((BigFppfOver.toScheme B S hS).map ρ)
            ((BigFppfOver.toScheme B S hS).map (ι m)) :=
      (Iso.inv_comp_eq _).mpr ((hsq m).isoPullback_hom_fst).symm
    rw [Functor.map_comp, Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map qN
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.fst ρ (ι m))
        ((BigFppfOver.toScheme B S hS).map (πp m n) e)) = x
    rw [hn]
    show (BigFppfOver.toScheme B S hS).map qN
      (((hsq m).isoPullback.inv ≫
        (BigFppfOver.toScheme B S hS).map (Limits.pullback.fst ρ (ι m))) p) = x
    rw [hfst, hp₁, hq]
  · simp only [liftSheafMap_schemeSpaceMap_comp, Category.assoc]
    rw [← hρw]
    congr 1
    rw [← Category.assoc, ← Category.assoc, ← liftSheafMap_schemeSpaceMap_comp,
      ← liftSheafMap_schemeSpaceMap_comp, ← Limits.pullback.condition]

end AlgebraicGeometry.FormalSpace

end
