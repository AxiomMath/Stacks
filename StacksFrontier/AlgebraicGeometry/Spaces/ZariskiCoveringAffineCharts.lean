module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints

/-!
# A Zariski covering by algebraic spaces with an affine étale chart

Stacks 03FX gives an algebraic space over a scheme `S` a surjective étale chart which is a
*disjoint union* of affine schemes. A single affine chart exists only over a quasi-compact
space (Stacks 03H6). Tag 03FY is the intermediate statement: the space is covered by open
subspaces, each of which does carry a surjective étale chart from a single affine scheme, and
each of those affine schemes may be taken to map into an affine open of `S`.

The covering is the one swept out by the summands of the chart of Stacks 03FX: the image of
the point set of a summand is open, so it is the point set of an open subspace by Tag 03BZ,
and the summand factors through that subspace surjectively on points.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range`:
  the open subspace swept out by an étale morphism of algebraic spaces over `S`, together
  with the étaleness and the surjectivity on points of the induced factorisation. This is the
  factorisation clause of Tag 06NF, stated for an arbitrary algebraic space source rather
  than only for a scheme.
* `AlgebraicGeometry.Space.isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda`:
  **the factorisation clause of Stacks 06NF** at a source represented by an object of the
  site, which additionally records surjectivity in its relatively representable form. Its
  docstring says which clause of the tag is *not* covered.
* `AlgebraicGeometry.Space.exists_zariskiCovering_affine_etale_chart`: **Stacks 03FY**, with
  the covering condition on point sets. It carries the attribute under the part string
  `"covering on point sets"`, not bare, for the reason in the first implementation note.
* `AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas`: **Stacks 03FY** with
  the covering condition in the repository's own `IsZariskiCover` vocabulary of Tag 02YY.
  This one carries the bare attribute.

## Implementation notes

**The covering condition is stated twice, on point sets and in the repository's own
vocabulary.** "There exists a Zariski covering `X = ⋃ Xᵢ`" is rendered first as: the `Xᵢ` are
open subspaces and the union of their point sets is the whole point set; and then as
`AlgebraicGeometry.Space.IsZariskiCover` (Tag 02YY), which asks that the map from the
coproduct of the members be locally surjective for the fppf topology. The two agree for a
family of open subspaces of an algebraic space, which is the Zariski-coverings part of Stacks
03BZ, `AlgebraicGeometry.Space.isZariskiCover_iff_iUnion_points`. The point-set form
is kept because it is what the proof produces and what a consumer placing a given point in a
member of the family wants; the `IsZariskiCover` form is the one the tag is stated in.

**Surjectivity is given in both of its equivalent forms.** The source's "surjective" is
surjectivity on point sets, which is Tag 03ME (`AlgebraicGeometry.Space.IsSurjective`). The
conclusion also records the relatively representable form — surjectivity of every represented
base change — which is the form Stacks 03FX is stated in and the one a morphism property of
algebraic spaces is usually tested in. The two agree here by Tag 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`, so recording both costs
one line and leaves no conversion to a consumer.

**The clause about the base is given at the member as well as at its chart.** The source says
"each `Xᵢ` maps into an affine open of `S`", and there is no morphism `|Xᵢ| → |S|` of point
sets in this development to say that with. It is said instead of the *sections* of `Xᵢ`:
whenever an object `T` of the site carries a section of `Xᵢ`, the structure morphism of `T`
sends every point of `T` into the affine open `V`. That follows from the same statement for
the chart `Wᵢ` — which is the form Stacks 03FX already supplies — because the chart is
surjective after every represented base change, so a section of `Xᵢ` over `T` pulls the chart
back to a *surjective* morphism of schemes onto `T`, and the structure morphism of `T`
factors through that of `Wᵢ`. Both forms are in the conclusion; Tag 03W7 uses the chart form,
where the clause serves only to make `Wᵢ ×_S Wᵢ` affine.

**No helper of its own.** The one step about structure morphisms — that a morphism of the site
read as a morphism of schemes commutes with the structure morphisms to `S` — is
`AlgebraicGeometry.toScheme_map_comp_inclusion_hom` of
`StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover`, which is already in the import
closure, so nothing is restated here.

**Nothing is proved here about presentations.** The second clause of Tag 06NF — that
`R = U ×_X U` equals `U ×_{X'} U` and that `X'` is the quotient `U/R` — is not addressed, so
no 06NF attribute is carried.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03FY](https://stacks.math.columbia.edu/tag/03FY)
* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The open subspace swept out by an étale morphism -/

/-- **The first clause of Stacks 06NF**, for an arbitrary algebraic space source. Let
`g : A ⟶ F` be an étale morphism of algebraic spaces over `S`. The subspace of `F` cut out by
the image of `|A|` is an open subspace, and `g` factors through it by a morphism which is
again étale and is surjective on points.

The image of `|A|` is open because `|g|` is an open map (Tag 03IR), so Tag 03BZ turns it into
an open subspace whose point set is that image; the factorisation is
`CategoryTheory.Subfunctor.lift`, which is étale because its composite with the inclusion is
and the inclusion is a monomorphism, and which is surjective on points because the point set
of the subspace is by construction the image of `|A|`. -/
theorem isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range
    {A F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    (hF : IsAlgebraicSpace B S hS F) (g : A ⟶ F)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    IsOpenSubspace B S hS
        (openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS A g))) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
        (Subfunctor.lift g (range_le_openSubspaceOfPoints_range_pointsMap g)) ∧
      Function.Surjective (pointsMap B S hS A
        (Subfunctor.lift g (range_le_openSubspaceOfPoints_range_pointsMap g))) := by
  have _hE : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
  have _hQ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine ⟨isOpenSubspace_openSubspaceOfPoints B S hS hF _
      (isOpen_range_pointsMap_of_isEtale B S hS g hA hF
        (isEtale_of_presheaf_etale B S hS hg)),
    MorphismProperty.presheaf_of_comp_mono _
      (m := (openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS A g))).ι) hg,
    isSurjective_lift_openSubspaceOfPoints_range B S hS g⟩

/-- **Stacks 06NF, the whole of its factorisation clause.** Let `U` be an object of the big
fppf category over `S` and `f : h_U ⟶ X` an étale morphism to an algebraic space over `S`.
Then the subspace `X'` of `X` cut out by the image of `|U|` is an open subspace, and `f`
factors through it by a morphism which is surjective — both on point sets and after every
represented base change — and étale.

The four assertions correspond exactly to the four declarations into which the source's
sentence "*then `f` factors through a surjective étale morphism `f' : U → X'`*" is split: the
induced morphism, which here is the canonical `CategoryTheory.Subfunctor.lift` and so needs no
choice; the factorisation `f' ≫ X'.ι = f`, which is `CategoryTheory.Subfunctor.lift_ι` and
holds by `rfl`; surjectivity; and étaleness. That `X'` is an open subspace with point set the
image of `|U|` is the source's own appeal to Tag 03BZ, and is
`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints` together with
`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`.

**What is not proved.** The source's second sentence — that `R = U ×_X U` equals `U ×_{X'} U`,
that it is an étale equivalence relation, and that `X'` is the quotient `U/R` — is not
addressed. So the covering set of Tag 06NF is incomplete and the attribute carries a part
string naming only the factorisation clause. Closing the rest needs Tag 0262, whose three
parts are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair`. -/
@[stacks 06NF "factorisation: induced morphism, factorization, surjective, étale"]
theorem isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsOpenSubspace B S hS
        (openSubspaceOfPoints B S hS X
          (Set.range (pointsMap B S hS (yoneda.obj U) f))) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
        (Subfunctor.lift f (range_le_openSubspaceOfPoints_range_pointsMap f)) ∧
      Function.Surjective (pointsMap B S hS (yoneda.obj U)
        (Subfunctor.lift f (range_le_openSubspaceOfPoints_range_pointsMap f))) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf
        (Subfunctor.lift f (range_le_openSubspaceOfPoints_range_pointsMap f)) :=
  have h := isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range B S hS
    (isAlgebraicSpace_yoneda B S hS U) hX f hf
  ⟨h.1, h.2.1, h.2.2,
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ h.1.1 U _).mpr h.2.2⟩

/-! ### The covering -/

/-- **Stacks 03FY.** An algebraic space over `S` is the union of a family of open subspaces
each of which carries a surjective étale chart from a single affine scheme, and those affine
schemes may be taken to map into affine opens of `S`. Surjectivity of the chart is recorded
both on point sets (Tag 03ME) and in the relatively representable form, the two being
equivalent by Tag 03H5.

The family is indexed by the summands of the affine chart of Stacks 03FX in the form
`AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`, which keeps the summands
as affine objects `W i` of the site. The member of the covering attached to `i` is the open
subspace swept out by `W i`, and the chart of that member is the factorisation of
`yoneda.map (j i) ≫ f` through it, by
`AlgebraicGeometry.Space.isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range`.
The members cover because the chart `f` is surjective on points (Tag 03H5) and every point of
its source lies in one summand.

The attribute carries a part string rather than being bare because the covering clause is the
point-set one; the bare attribute sits on
`AlgebraicGeometry.Space.exists_zariski_cover_affine_etale_atlas`, which states the same
thing with the covering clause in the repository's `AlgebraicGeometry.Space.IsZariskiCover`
vocabulary of Tag 02YY. The two are interchangeable by the Zariski-coverings part of Tag
03BZ. -/
@[stacks 03FY "covering on point sets"]
theorem exists_zariskiCovering_affine_etale_chart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    ∃ (I : Type u) (X : I → Subfunctor F) (W : I → BigFppfOver B S hS)
      (b : ∀ i, yoneda.obj (W i) ⟶ (X i).toFunctor),
      (∀ i, IsOpenSubspace B S hS (X i)) ∧
      (⋃ i, Set.range (pointsMap B S hS (X i).toFunctor (X i).ι)) = Set.univ ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (b i)) ∧
      (∀ i, Function.Surjective (pointsMap B S hS (yoneda.obj (W i)) (b i))) ∧
      (∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (b i)) ∧
      (∀ i, ∃ V : S.Opens, IsAffineOpen V ∧
        (∀ y : (BigFppfOver.toScheme B S hS).obj (W i),
          (B.inclusion.map (W i).hom) y ∈ V) ∧
        ∀ (T : BigFppfOver B S hS) (_x : (X i).toFunctor.obj (Opposite.op T))
          (t : (BigFppfOver.toScheme B S hS).obj T),
          (B.inclusion.map T.hom) t ∈ V) := by
  obtain ⟨U, f, I, W, j, e, hfS, -, hWaff, hιe, -, hjEt, hWover⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  have hkey := fun i ↦ isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda
    B S hS hF (W i) (yoneda.map (j i) ≫ f) (hjEt i)
  refine ⟨I, fun i ↦ openSubspaceOfPoints B S hS F
      (Set.range (pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i) ≫ f))),
    W, fun i ↦ Subfunctor.lift (yoneda.map (j i) ≫ f)
      (range_le_openSubspaceOfPoints_range_pointsMap (yoneda.map (j i) ≫ f)),
    fun i ↦ (hkey i).1, ?_, hWaff, fun i ↦ (hkey i).2.1, fun i ↦ (hkey i).2.2.1,
    fun i ↦ (hkey i).2.2.2, fun i ↦ ?_⟩
  · -- The members cover: the chart is surjective on points and its source is the disjoint
    -- union of the summands.
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    obtain ⟨y, hy⟩ := isSurjective_of_presheafSurjective B S hS f hfS x
    obtain ⟨i, w, hjw⟩ := (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1
      (pointsToScheme B S hS U y)
    obtain ⟨v, hv⟩ := surjective_pointsToScheme B S hS (W i) w
    have hjv : pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i)) v = y :=
      injective_pointsToScheme B S hS U
        (by rw [pointsToScheme_pointsMap_yoneda, hv, hjw])
    refine ⟨i, ?_⟩
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact ⟨v, by rw [pointsMap_comp_apply, hjv, hy]⟩
  · -- The member of the covering lies over an affine open of the base, because its chart
    -- does and its chart is surjective after every represented base change.
    obtain ⟨V, hV, hVover⟩ := hWover i
    have hstr : ∀ {P Q : BigFppfOver B S hS} (φ : P ⟶ Q) (p : (BigFppfOver.toScheme B S hS).obj P),
        (B.inclusion.map P.hom) p =
          (B.inclusion.map Q.hom) ((BigFppfOver.toScheme B S hS).map φ p) := fun φ p ↦ by
      rw [← Scheme.Hom.comp_apply, _root_.AlgebraicGeometry.toScheme_map_comp_inclusion_hom]
    have hWV : ∀ y : (BigFppfOver.toScheme B S hS).obj (W i),
        (B.inclusion.map (W i).hom) y ∈ V := fun y ↦ by
      rw [hstr (j i) y]
      exact hVover y
    refine ⟨V, hV, hWV, fun T x t ↦ ?_⟩
    have hbs := (hkey i).2.2.2
    obtain ⟨p, rfl⟩ := (hbs.property_snd (yonedaEquiv.symm x) : Surjective _).surj t
    rw [← hstr (hbs.rep.snd _) p, hstr (yoneda.preimage (hbs.rep.fst _)) p]
    exact hWV _

end AlgebraicGeometry.Space

end
