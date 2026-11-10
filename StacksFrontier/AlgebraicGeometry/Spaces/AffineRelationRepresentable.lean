module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.FiniteFlatQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An algebraic space with an affine finite flat presentation is representable

Let `S` be a scheme, let `Z₁` and `R` be objects of the big fppf site of `S` with affine
underlying schemes, and let `s, t : R ⟶ Z₁` be two morphisms whose pre-relation on `Z₁ ×_S Z₁`
is an equivalence relation with finite locally free source and target maps. If an algebraic
space `V` over `S` is the coequalizer, in fppf sheaves, of `yoneda.map s` and `yoneda.map t`,
then `V` is *representable*: there is an object `V₀` of the site with affine underlying scheme
and an isomorphism `V ≅ h_{V₀}` carrying the atlas `h_{Z₁} ⟶ V` to a morphism of the site.

This is the step the finiteness clause of Stacks 082H is missing. There the open-and-closed
piece `V` of the decomposition is the quotient of the affine scheme `Z₁` of step 5 by the
étale equivalence relation `R = Z₁ ×_V Z₁`, whose two projections are finite — hence, being
also étale, finite locally free — and Tag 03BM identifies that quotient with the spectrum of
the ring of invariants. The identification of `V` with the quotient *sheaf* is Tag 0262 part
(3), which supplies the coequalizer hypothesis.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Groupoids.yonedaToPoints_naturality`: the comparison morphism between the presheaf
  represented by an object of a site of `S`-schemes and the restricted functor of points of
  its image is natural.
* `Stacks.Groupoids.map_comp_quotientChart`: the chart of a quotient sheaf coequalizes the two
  maps of the pre-relation, read on the presheaves represented by the objects of the site.
* `Stacks.Groupoids.exists_iso_quotientSheaf_of_descent`: **the double coequalizer.** A sheaf
  which is the coequalizer of `yoneda.map s` and `yoneda.map t` is isomorphic to the quotient
  sheaf of the corresponding pre-relation, compatibly with the two projections.
* `Stacks.Groupoids.exists_iso_yoneda_of_descent_of_represents`: the same with the quotient
  sheaf in turn represented by an object of the site, so that the conclusion is
  representability of the original sheaf.
* `Stacks.Groupoids.existsUnique_desc_of_isColimit`: the universal property of a cofork of
  sheaves, read as unique descent of morphisms of presheaves.
* `AlgebraicGeometry.exists_represents_quotientSheaf_of_extendsRelation`: **Tag 03BM for a
  pre-relation** rather than for a groupoid scheme. An equivalence relation on an affine
  `S`-scheme with affine relation scheme and finite locally free projections has its quotient
  sheaf represented by an affine `S`-scheme of no larger size, compatibly with the projection.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_affine_finiteFlat_relation`: the two combined.
  A sheaf which is the coequalizer of such a relation is isomorphic to the presheaf
  represented by an object of the site with affine underlying scheme.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_surjectiveEtale_atlas_of_affine_finiteFlat`:
  the same with the coequalizer hypothesis in the form Stacks 0262 part (3) supplies it, from
  a surjective étale atlas whose kernel pair is the relation.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_kernelPair_of_affine_finiteLocallyFree`: the
  same with the pre-relation and its groupoid scheme supplied, so that the only hypotheses
  left are the geometric ones: the atlas is surjective and étale, its kernel pair is given by
  two morphisms of the site, both objects are affine and both projections are finite locally
  free.
* `AlgebraicGeometry.isFiniteLocallyFree_of_etale_of_isFinite`: a finite étale morphism of
  schemes is finite locally free, which is how Stacks 082H obtains the last of those
  hypotheses.

## Implementation notes

The double coequalizer is the only place where the two universal properties meet, and it is
formal. The quotient sheaf of a pre-relation `j` on the image of `Z₁` is a coequalizer of the
two maps on *restricted functors of points*, whereas an algebraic space is a coequalizer of
the two maps on *represented presheaves*. The comparison between them is
`Stacks.Groupoids.yonedaToPoints`, an isomorphism because the functor presenting the site is
fully faithful, and it conjugates one pair of maps into the other by
`Stacks.Groupoids.yonedaToPoints_naturality`. Each of the two objects then receives a map from
the other by the other's universal property, and the two composites are identities by the
uniqueness halves — for the quotient sheaf
`Stacks.Groupoids.quotientSheafDesc_unique`, for the algebraic space the uniqueness in the
descent hypothesis.

The coequalizer hypothesis is stated as unique descent of morphisms of *presheaves* rather
than as a `CategoryTheory.Limits.IsColimit` for a cofork of sheaves, because that is the form
in which both universal properties are used; `Stacks.Groupoids.existsUnique_desc_of_isColimit`
converts the cofork form of Tag 0262 part (3) into it. Since the commutativity argument of a
cofork is a proposition, the cofork built from any proof of it is definitionally the one built
from any other, so no coherence hypothesis is needed there.

Tag 03BM is stated in the library for a groupoid scheme, whose object and arrow schemes are
*fields* of the groupoid; the relation of Stacks 082H is given instead by two morphisms of the
site. `AlgebraicGeometry.exists_represents_quotientSheaf_of_extendsRelation` restates it for a
pre-relation extended by a groupoid scheme in the sense of
`AlgebraicGeometry.ExtendsRelation`, which is the form
`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation` produces. The transport is not by
`eqToHom` gymnastics: the two identifications of `AlgebraicGeometry.ExtendsRelation` are
equalities of objects of `Over S`, so substituting them turns the `eqToHom` conjugations into
plain equalities of the source and target maps, and a pre-relation is determined by those by
`CategoryTheory.Limits.prod.hom_ext`.

Nothing here carries the tag 082H. What 082H asserts and this does not is the existence, after
an étale base change of the target, of the affine scheme `Z₁` which is étale onto the piece and
finite over the base, together with the affineness of its kernel pair and the finite local
freeness of the two projections; those are steps 1 to 5 of the source proof and the geometric
hypotheses here. None of the hypotheses is an existential, and none contains any part of the
conclusion: representability of `V` is concluded from affineness of `Z₁` and `R`, not assumed.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 02VG](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{u} C]

/-! ### The comparison between represented presheaves and restricted functors of points -/

/-- **The comparison morphism `Stacks.Groupoids.yonedaToPoints` is natural.** For a morphism
`g : X ⟶ Y` of a site of `S`-schemes, composing with `g` and then comparing is the same as
comparing and then composing with the image of `g`. -/
theorem yonedaToPoints_naturality (F : C ⥤ Over S) {X Y : C} (g : X ⟶ Y) :
    yonedaToPoints F X ≫ F.op.whiskerLeft (yoneda.map (F.map g)) =
      yoneda.map g ≫ yonedaToPoints F Y := by
  ext T h
  change F.map h ≫ F.map g = F.map (h ≫ g)
  rw [F.map_comp]

/-- The comparison morphism carries the source map of a pre-relation on the image of `X` to the
morphism of represented presheaves given by the source morphism of the site. -/
theorem yonedaToPoints_comp_sourceMap (F : C ⥤ Over S) {R X : C} (s : R ⟶ X)
    {j : PreRelation (F.obj R) (F.obj X)} (hjs : j.source = F.map s) :
    yonedaToPoints F R ≫ sourceMap F j = yoneda.map s ≫ yonedaToPoints F X := by
  rw [show sourceMap F j = F.op.whiskerLeft (yoneda.map (F.map s)) by rw [sourceMap, hjs]]
  exact yonedaToPoints_naturality F s

/-- The comparison morphism carries the target map of a pre-relation on the image of `X` to the
morphism of represented presheaves given by the target morphism of the site. -/
theorem yonedaToPoints_comp_targetMap (F : C ⥤ Over S) {R X : C} (t : R ⟶ X)
    {j : PreRelation (F.obj R) (F.obj X)} (hjt : j.target = F.map t) :
    yonedaToPoints F R ≫ targetMap F j = yoneda.map t ≫ yonedaToPoints F X := by
  rw [show targetMap F j = F.op.whiskerLeft (yoneda.map (F.map t)) by rw [targetMap, hjt]]
  exact yonedaToPoints_naturality F t

variable (J : GrothendieckTopology C) [HasSheafify J (Type u)]

/-- **The chart of a quotient sheaf coequalizes the relation.** If the source and target maps
of a pre-relation on the image of `X` are the images of two morphisms `s, t : R ⟶ X` of the
site, then the two induced morphisms of represented presheaves have the same composite with
the chart of the quotient sheaf. -/
theorem map_comp_quotientChart (F : C ⥤ Over S) {R X : C} (s t : R ⟶ X)
    {j : PreRelation (F.obj R) (F.obj X)} (hjs : j.source = F.map s)
    (hjt : j.target = F.map t) :
    yoneda.map s ≫ quotientChart J F X j = yoneda.map t ≫ quotientChart J F X j := by
  calc yoneda.map s ≫ quotientChart J F X j
      = yonedaToPoints F R ≫ sourceMap F j ≫ toQuotientSheaf J F j := by
        rw [quotientChart, ← Category.assoc, ← yonedaToPoints_comp_sourceMap F s hjs,
          Category.assoc]
    _ = yonedaToPoints F R ≫ targetMap F j ≫ toQuotientSheaf J F j := by
        rw [sourceMap_toQuotientSheaf]
    _ = yoneda.map t ≫ quotientChart J F X j := by
        rw [quotientChart, ← Category.assoc, yonedaToPoints_comp_targetMap F t hjt,
          Category.assoc]

/-! ### The double coequalizer -/

/-- **A sheaf which is the coequalizer of a relation of representables is the quotient
sheaf.** Let `s, t : R ⟶ X` be two morphisms of a site of `S`-schemes presented by a fully
faithful functor, let `j` be a pre-relation on the image of `X` whose source and target are
their images, and let `f : h_X ⟶ G` be a morphism into a sheaf through which every morphism
coequalizing `yoneda.map s` and `yoneda.map t` factors uniquely. Then `G` is isomorphic to the
quotient sheaf of `j`, by an isomorphism carrying `f` to the chart of the quotient sheaf.

Both objects are coequalizers of the same pair of maps: for `G` that is the hypothesis, and
for the quotient sheaf it is `Stacks.Groupoids.quotientSheafDesc` together with
`Stacks.Groupoids.quotientSheafDesc_unique`, transported along the isomorphism
`Stacks.Groupoids.yonedaToPoints`. -/
theorem exists_iso_quotientSheaf_of_descent (F : C ⥤ Over S) [F.Full] [F.Faithful]
    {R X : C} (s t : R ⟶ X) {j : PreRelation (F.obj R) (F.obj X)}
    (hjs : j.source = F.map s) (hjt : j.target = F.map t)
    {G : Cᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf J G) (f : yoneda.obj X ⟶ G)
    (hw : yoneda.map s ≫ f = yoneda.map t ≫ f)
    (hdesc : ∀ (A : Sheaf J (Type u)) (k : yoneda.obj X ⟶ A.obj),
      yoneda.map s ≫ k = yoneda.map t ≫ k → ∃! d : G ⟶ A.obj, f ≫ d = k) :
    ∃ e : G ≅ (quotientSheaf J F j).obj, f ≫ e.hom = quotientChart J F X j := by
  classical
  obtain ⟨q, hq, hquniq⟩ := hdesc (quotientSheaf J F j) (quotientChart J F X j)
    (map_comp_quotientChart J F s t hjs hjt)
  have hyi : yonedaToPoints F X ≫ inv (yonedaToPoints F X) = 𝟙 _ := IsIso.hom_inv_id _
  have hyi' : inv (yonedaToPoints F X) ≫ yonedaToPoints F X = 𝟙 _ := IsIso.inv_hom_id _
  have hcancel (g : yoneda.obj X ⟶ G) (m : points F (F.obj R) ⟶ points F (F.obj X)) (h : R ⟶ X)
      (hh : yonedaToPoints F R ≫ m = yoneda.map h ≫ yonedaToPoints F X) :
      yonedaToPoints F R ≫ m ≫ inv (yonedaToPoints F X) ≫ g = yoneda.map h ≫ g := by
    rw [← Category.assoc, hh, Category.assoc, ← Category.assoc (yonedaToPoints F X), hyi,
      Category.id_comp]
  have hk : sourceMap F j ≫ (inv (yonedaToPoints F X) ≫ f) =
      targetMap F j ≫ (inv (yonedaToPoints F X) ≫ f) := by
    rw [← cancel_epi (yonedaToPoints F R),
      hcancel f _ s (yonedaToPoints_comp_sourceMap F s hjs),
      hcancel f _ t (yonedaToPoints_comp_targetMap F t hjt)]
    exact hw
  set p : (quotientSheaf J F j).obj ⟶ G :=
    (quotientSheafDesc J F j ⟨G, hG⟩ (inv (yonedaToPoints F X) ≫ f) hk).hom with hp
  have htp : toQuotientSheaf J F j ≫ p = inv (yonedaToPoints F X) ≫ f :=
    toQuotientSheaf_quotientSheafDesc J F j ⟨G, hG⟩ (inv (yonedaToPoints F X) ≫ f) hk
  have hchart : quotientChart J F X j = yonedaToPoints F X ≫ toQuotientSheaf J F j := rfl
  have hqp : q ≫ p = 𝟙 G := by
    have h1 : f ≫ (q ≫ p) = f := by
      rw [← Category.assoc, hq, hchart, Category.assoc, htp, ← Category.assoc,
        hyi, Category.id_comp]
    have h2 : f ≫ (𝟙 G) = f := Category.comp_id f
    obtain ⟨d, _, hd⟩ := hdesc ⟨G, hG⟩ f hw
    rw [hd _ h1, hd _ h2]
  have hpq : p ≫ q = 𝟙 ((quotientSheaf J F j).obj) := by
    have key : (⟨p ≫ q⟩ : quotientSheaf J F j ⟶ quotientSheaf J F j) =
        (𝟙 (quotientSheaf J F j)) := by
      rw [quotientSheafDesc_unique J F j (quotientSheaf J F j) (toQuotientSheaf J F j)
        (sourceMap_toQuotientSheaf J F j) ⟨p ≫ q⟩ (by
          change toQuotientSheaf J F j ≫ p ≫ q = toQuotientSheaf J F j
          rw [← Category.assoc, htp, Category.assoc, hq, hchart, ← Category.assoc,
            hyi', Category.id_comp]),
        quotientSheafDesc_unique J F j (quotientSheaf J F j) (toQuotientSheaf J F j)
        (sourceMap_toQuotientSheaf J F j) (𝟙 _) (Category.comp_id _)]
    exact Sheaf.hom_ext_iff.mp key
  exact ⟨⟨q, p, hqp, hpq⟩, hq⟩

omit [HasSheafify J (Type u)] in
/-- **The universal property of a cofork of sheaves, as unique descent of morphisms of
presheaves.** If the cofork on `f` of two morphisms of sheaves of types is a colimit, then
every morphism of presheaves out of the common target which coequalizes the two morphisms
factors uniquely through `f`.

This converts the conclusion of Tag 0262 part (3) into the hypothesis of
`Stacks.Groupoids.exists_iso_quotientSheaf_of_descent`. -/
theorem existsUnique_desc_of_isColimit {RF XF GF : Sheaf J (Type u)}
    (σ τ : RF ⟶ XF) (f : XF ⟶ GF) (w : σ ≫ f = τ ≫ f)
    (hcolim : IsColimit (Cofork.ofπ f w)) (A : Sheaf J (Type u)) (k : XF.obj ⟶ A.obj)
    (hk : σ.hom ≫ k = τ.hom ≫ k) :
    ∃! d : GF.obj ⟶ A.obj, f.hom ≫ d = k := by
  obtain ⟨d, hd, hduniq⟩ :=
    Cofork.IsColimit.existsUnique hcolim (⟨k⟩ : XF ⟶ A) (Sheaf.hom_ext hk)
  refine ⟨d.hom, ?_, ?_⟩
  · have h : f ≫ d = (⟨k⟩ : XF ⟶ A) := by simpa only [Cofork.π_ofπ] using hd
    exact Sheaf.hom_ext_iff.mp h
  · intro y hy
    have h : (⟨y⟩ : GF ⟶ A) = d := by
      refine hduniq _ (Sheaf.hom_ext ?_)
      simpa only [Cofork.π_ofπ, ObjectProperty.FullSubcategory.comp_hom] using hy
    exact Sheaf.hom_ext_iff.mp h

/-- **A sheaf which is the coequalizer of a relation of representables, and whose quotient
sheaf is represented by an object of the site, is itself represented by that object.** With
the hypotheses of `Stacks.Groupoids.exists_iso_quotientSheaf_of_descent`, suppose moreover
that the quotient sheaf of `j` is isomorphic to the restricted functor of points of the image
of an object `V₀` of the site, by an isomorphism carrying the canonical projection to a
morphism `π`. Then `G` is isomorphic to the presheaf represented by `V₀`, by an isomorphism
carrying `f` to the morphism of the site whose image is `π`.

The last comparison is `Stacks.Groupoids.yonedaToPoints`, an isomorphism because the
presenting functor is fully faithful, and its compatibility with `π` is
`Stacks.Groupoids.yonedaToPoints_naturality`. -/
theorem exists_iso_yoneda_of_descent_of_represents (F : C ⥤ Over S) [F.Full] [F.Faithful]
    {R X : C} (s t : R ⟶ X) {j : PreRelation (F.obj R) (F.obj X)}
    (hjs : j.source = F.map s) (hjt : j.target = F.map t)
    {G : Cᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf J G) (f : yoneda.obj X ⟶ G)
    (hw : yoneda.map s ≫ f = yoneda.map t ≫ f)
    (hdesc : ∀ (A : Sheaf J (Type u)) (k : yoneda.obj X ⟶ A.obj),
      yoneda.map s ≫ k = yoneda.map t ≫ k → ∃! d : G ⟶ A.obj, f ≫ d = k)
    (V₀ : C) (π : F.obj X ⟶ F.obj V₀)
    (hM : Presheaf.IsSheaf J (points F (F.obj V₀)))
    (q : quotientSheaf J F j ⟶ (⟨points F (F.obj V₀), hM⟩ : Sheaf J (Type u))) (hq : IsIso q)
    (hqfac : toQuotientSheaf J F j ≫ q.hom = F.op.whiskerLeft (yoneda.map π)) :
    ∃ (π₀ : X ⟶ V₀) (e : G ≅ yoneda.obj V₀), f ≫ e.hom = yoneda.map π₀ := by
  classical
  have _ := hq
  obtain ⟨e₁, he₁⟩ := exists_iso_quotientSheaf_of_descent J F s t hjs hjt hG f hw hdesc
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : X ⟶ V₀, F.map π₀ = π := ⟨F.preimage π, F.map_preimage π⟩
  refine ⟨π₀, e₁ ≪≫ asIso q.hom ≪≫ (asIso (yonedaToPoints F V₀)).symm, ?_⟩
  have hstep : f ≫ e₁.hom ≫ q.hom = yoneda.map π₀ ≫ yonedaToPoints F V₀ := by
    rw [← Category.assoc, he₁]
    change yonedaToPoints F X ≫ toQuotientSheaf J F j ≫ q.hom = _
    rw [hqfac, ← hπ₀]
    exact yonedaToPoints_naturality F π₀
  simp [reassoc_of% hstep]

end Stacks.Groupoids

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms

/-! ### Finite étale morphisms are finite locally free -/

/-- **A finite étale morphism is finite locally free.** Étale morphisms are flat and locally of
finite presentation, so this is
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`.

This is the step of Stacks 082H which turns the finiteness of the two projections of the
kernel pair `R = Z₁ ×_V Z₁` — finiteness coming from the finiteness of `Z₁ ⟶ U` and the
closedness of `R` in `Z₁ ×_U Z₁` — into the finite local freeness that Tag 03BM asks for. -/
@[ega "IV 18.2.7"]
theorem isFiniteLocallyFree_of_etale_of_isFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g]
    [_root_.AlgebraicGeometry.IsFinite g] : IsFiniteLocallyFree g :=
  (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### Tag 03BM for a pre-relation -/

/-- **Tag 03BM for a pre-relation.** Let `j` be an equivalence relation on an affine
`S`-scheme `U` with affine relation scheme `R` and finite locally free source and target maps,
and let `G` be a groupoid scheme extending `j`. Then there are an affine `S`-scheme `M` of
size at most that of `U` and a morphism `π : U ⟶ M` such that the restricted functor of points
of `M` is a sheaf for the big fppf topology of `S` and represents the quotient sheaf of `j`,
compatibly with `π`.

The groupoid scheme carries the object and arrow schemes as fields, so Tag 03BM
(`AlgebraicGeometry.quotientSheaf_isRepresented`) speaks about its own pre-relation
`prod.lift G.target G.source`. Substituting the two object identifications of
`AlgebraicGeometry.ExtendsRelation` makes the `eqToHom` conjugations of its source and target
identifications disappear, and then `CategoryTheory.Limits.prod.hom_ext` identifies the two
pre-relations. The size bound is `AlgebraicGeometry.size_quotientOver_le`. -/
@[sga "3 V 4.1" "special case"]
theorem exists_represents_quotientSheaf_of_extendsRelation {S : Scheme.{u}} {R U : Over S}
    (j : PreRelation R U) (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsAffine U.left] [IsAffine R.left]
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    ∃ (M : Over S) (π : U ⟶ M), IsAffine M.left ∧ M.left.size ≤ U.left.size ∧
      ∃ hM : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (points (Over.post B.inclusion) M),
        ∃ q : quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j ⟶
            (⟨points (Over.post B.inclusion) M, hM⟩ :
              Sheaf (BigFppfOver.topology B S hS) (Type u)),
          IsIso q ∧
            toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j ≫ q.hom =
              (Over.post B.inclusion).op.whiskerLeft (yoneda.map π) := by
  obtain ⟨hobj, harr, hsrc, htgt⟩ := hExt
  subst hobj
  subst harr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  have hj : j = prod.lift G.target G.source := by
    apply prod.hom_ext
    · rw [prod.lift_fst, htgt]
    · rw [prod.lift_snd, hsrc]
  have h1 : IsFiniteLocallyFree G.source.left := by rw [hsrc]; infer_instance
  have h2 : IsFiniteLocallyFree G.target.left := by rw [htgt]; infer_instance
  have h3 : IsEquivalenceRelation G.target G.source := by rw [hsrc, htgt]; infer_instance
  obtain ⟨hM, q, hq, hfac⟩ := quotientSheaf_isRepresented G B hS
  refine ⟨quotientOver G, quotientProjection G, ?_, size_quotientOver_le G, ?_⟩
  · rw [quotientOver_left]; infer_instance
  · rw [hj]
    exact ⟨hM, q, hq, hfac⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open Stacks.Groupoids Stacks.Morphisms

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space with an affine finite flat presentation is representable.** Let
`s, t : R ⟶ Z₁` be morphisms of the big fppf site of `S` whose underlying schemes are affine,
let `j` be a pre-relation on the image of `Z₁` whose source and target are their images, and
suppose `j` is an equivalence relation with finite locally free source and target. Let
`f : h_{Z₁} ⟶ V` be a morphism into a sheaf `V` through which every morphism coequalizing
`yoneda.map s` and `yoneda.map t` factors uniquely. Then there are an object `V₀` of the site
with affine underlying scheme, a morphism `π₀ : Z₁ ⟶ V₀` of the site and an isomorphism
`V ≅ h_{V₀}` carrying `f` to `yoneda.map π₀`.

Tag 0262 part (3) supplies the descent hypothesis for an algebraic space with a surjective
étale atlas; see
`AlgebraicGeometry.Space.exists_iso_yoneda_of_surjectiveEtale_atlas_of_affine_finiteFlat`.

The quotient sheaf of `j` is identified with `V` by
`Stacks.Groupoids.exists_iso_quotientSheaf_of_descent` and with the restricted functor of
points of an affine `S`-scheme `M` by
`AlgebraicGeometry.exists_represents_quotientSheaf_of_extendsRelation`. The size bound of the
latter puts `M` in the site, since membership is a bound on the size, and
`Stacks.Groupoids.yonedaToPoints` identifies the restricted functor of points of the resulting
object of the site with the presheaf it represents. -/
@[sga "3 V 4.1" "special case"]
theorem exists_iso_yoneda_of_affine_finiteFlat_relation
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z₁ R : BigFppfOver B S hS} (s t : R ⟶ Z₁)
    {j : PreRelation ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj Z₁)}
    (hjs : j.source = (Over.post B.inclusion).map s)
    (hjt : j.target = (Over.post B.inclusion).map t)
    (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V) (f : yoneda.obj Z₁ ⟶ V)
    (hw : yoneda.map s ≫ f = yoneda.map t ≫ f)
    (hdesc : ∀ (A : Sheaf (BigFppfOver.topology B S hS) (Type u))
        (k : yoneda.obj Z₁ ⟶ A.obj), yoneda.map s ≫ k = yoneda.map t ≫ k →
      ∃! d : V ⟶ A.obj, f ≫ d = k) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧ f ≫ e.hom = yoneda.map π₀ := by
  classical
  have _ : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj Z₁).left :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)›
  have _ : IsAffine ((Over.post (X := B.obj hS) B.inclusion).obj R).left :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj R)›
  obtain ⟨M, π, hMaff, hMsize, hMsheaf, q, hq, hqfac⟩ :=
    exists_represents_quotientSheaf_of_extendsRelation (S := S) j G hExt B hS
  have hcontains : B.Contains M.left := lt_of_le_of_lt hMsize Z₁.left.property
  obtain ⟨π₀, e, he⟩ := exists_iso_yoneda_of_descent_of_represents
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion) s t hjs hjt hV f hw
    hdesc (Over.mk (X := B.obj hS) (Y := B.obj hcontains) (ObjectProperty.homMk M.hom)) π
    hMsheaf q hq hqfac
  exact ⟨_, π₀, e, hMaff, he⟩

/-- **The same with the coequalizer hypothesis in the form Stacks 0262 part (3) supplies
it.** Let `V` be an algebraic space over `S` with a surjective étale atlas `f : h_{Z₁} ⟶ V`
out of an object of the site with affine underlying scheme, and suppose the kernel pair of `f`
is given by two morphisms `s, t : R ⟶ Z₁` with `R` affine, whose pre-relation `j` is an
equivalence relation with finite locally free source and target. Then `V` is representable by
an object of the site with affine underlying scheme.

In the application to Stacks 082H, `V` is the open-and-closed piece of the decomposition, `Z₁`
is the affine scheme of step 5 which is étale onto it and finite over the base, and `R` is the
kernel pair `Z₁ ×_V Z₁`, affine and finite over `Z₁` because the piece is separated over the
base; finite and étale together is finite locally free. -/
theorem exists_iso_yoneda_of_surjectiveEtale_atlas_of_affine_finiteFlat
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z₁ R : BigFppfOver B S hS} (s t : R ⟶ Z₁)
    {j : PreRelation ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj Z₁)}
    (hjs : j.source = (Over.post B.inclusion).map s)
    (hjt : j.target = (Over.post B.inclusion).map t)
    (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (f : yoneda.obj Z₁ ⟶ V)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧ f ≫ e.hom = yoneda.map π₀ := by
  obtain ⟨hRsh, hUsh, hcolim⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hR hV hsurj hetale
  obtain ⟨hcolim⟩ := hcolim
  refine exists_iso_yoneda_of_affine_finiteFlat_relation B S hS s t hjs hjt G hExt
    hV.isSheaf f hR.w ?_
  intro A k hk
  exact existsUnique_desc_of_isColimit (BigFppfOver.topology B S hS)
    (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      ⟨yoneda.obj Z₁, hUsh⟩)
    ⟨yoneda.map t⟩ (⟨f⟩ : (⟨yoneda.obj Z₁, hUsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨V, hV.isSheaf⟩)
    _ hcolim A k hk

/-- **Representability from a kernel pair with affine, finite locally free projections.** Let
`V` be an algebraic space over `S` with a surjective étale atlas `f : h_{Z₁} ⟶ V` whose kernel
pair is given by `s, t : R ⟶ Z₁`, let the underlying schemes of `Z₁` and `R` be affine, and let
the two projections be finite locally free. Then `V` is representable by an object of the site
with affine underlying scheme, compatibly with the atlas.

This is
`AlgebraicGeometry.Space.exists_iso_yoneda_of_surjectiveEtale_atlas_of_affine_finiteFlat` with
the pre-relation and its groupoid supplied: the pre-relation is
`AlgebraicGeometry.Space.relation`, it is an equivalence relation by Tag 0262 part (1)
(`AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback`), and the groupoid extending it
is the canonical one of Tag 0233
(`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`).

For the finite local freeness of the projections in the situation of Stacks 082H, see
`AlgebraicGeometry.isFiniteLocallyFree_of_etale_of_isFinite`. -/
theorem exists_iso_yoneda_of_kernelPair_of_affine_finiteLocallyFree
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z₁ R : BigFppfOver B S hS} (s t : R ⟶ Z₁)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    (hsFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (htFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (f : yoneda.obj Z₁ ⟶ V)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧ f ≫ e.hom = yoneda.map π₀ := by
  have hequiv : IsEquivalenceRelation ((Over.post B.inclusion).map s)
      ((Over.post B.inclusion).map t) :=
    isEquivalenceRelation_of_isPullback B S hS f s t hR
  have hjt : (relation B S hS t s).target = (Over.post B.inclusion).map s :=
    prod.lift_fst _ _
  have hjs : (relation B S hS t s).source = (Over.post B.inclusion).map t :=
    prod.lift_snd _ _
  have h1 : IsEquivalenceRelation (relation B S hS t s).target
      (relation B S hS t s).source := by rw [hjt, hjs]; exact hequiv
  have h2 : IsFiniteLocallyFree (relation B S hS t s).source.left := by
    rw [hjs]; exact htFLF
  have h3 : IsFiniteLocallyFree (relation B S hS t s).target.left := by
    rw [hjt]; exact hsFLF
  exact exists_iso_yoneda_of_surjectiveEtale_atlas_of_affine_finiteFlat B S hS t s hjs hjt
    (groupoidSchemeOfIsEquivalenceRelation (relation B S hS t s))
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation (relation B S hS t s)) hV f hR.flip
    hsurj hetale

end AlgebraicGeometry.Space

end
