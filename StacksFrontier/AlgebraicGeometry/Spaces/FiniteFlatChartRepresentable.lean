module

public import StacksFrontier.AlgebraicGeometry.Properties.FiniteSetInAffineOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientCharts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An algebraic space with a finite locally free chart out of a scheme immersed in an affine

Let `X` be an algebraic space over a scheme `S` and let `f : h_Z ⟶ X` be a chart which is
surjective, étale *and finite locally free*. If the scheme `Z` is isomorphic to a locally
closed subscheme of an affine scheme, then `X` is representable.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_image_preimage_singleton_of_isImmersion`: if the source
  map of a relation on a scheme `U` immersed in an affine scheme is finite locally free, then the
  orbit `t(s⁻¹({u}))` of every point of `U` lies in an affine open of `U`.
* `AlgebraicGeometry.exists_represents_quotientSheaf_of_extendsRelation_of_affineOrbits`: the
  quotient sheaf of an equivalence relation with finite locally free source and target
  satisfying the affine-orbit condition is represented by a scheme belonging to the site.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_finiteFlat_relation_of_affineOrbits`: a sheaf
  which is the coequalizer of such a relation is representable by an object of the site.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_surjectiveEtale_atlas_of_finiteFlat`: an
  algebraic space with a surjective étale atlas whose kernel pair is such a relation is
  representable by an object of the site.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_kernelPair_of_finiteLocallyFree_of_isImmersion`
  and
  `AlgebraicGeometry.Space.isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion`:
  the statement above, with the kernel pair given explicitly and with it produced from the
  relative representability of the chart respectively.

## References

* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### The affine-orbit condition -/

/-- Let `s, t : R ⟶ U` be morphisms of schemes with `s` finite locally free, and let
`i : U ⟶ Y` be an immersion with `Y` affine. Then for every point `u` of `U` the set
`t(s⁻¹({u}))` is contained in an affine open of `U`. -/
theorem exists_isAffineOpen_image_preimage_singleton_of_isImmersion {R U Y : Scheme.{u}}
    [IsAffine Y] (s t : R ⟶ U) (i : U ⟶ Y) [IsImmersion i]
    (hs : IsFiniteLocallyFree s) (u : U) :
    ∃ W : U.Opens, IsAffineOpen W ∧ t.base '' (s.base ⁻¹' {u}) ⊆ (W : Set U) := by
  obtain ⟨hsfin, -, -⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation s).mp hs
  have _ : IsFinite s := hsfin
  exact exists_isAffineOpen_of_isImmersion_of_isAffine i
    ((s.finite_preimage_singleton u).image _)

/-! ### Representing the quotient sheaf of a pre-relation -/

/-- The affine-orbit condition only depends on the source and target maps. -/
private theorem orbit_condition_congr {S : Scheme.{u}} {R U : Over S} {s s' t t' : R ⟶ U}
    (hs : s = s') (ht : t = t')
    (h : ∀ Z : Set U.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : U.left.Opens, IsAffineOpen W ∧
        t.left.base '' (s.left.base ⁻¹' {u}) ⊆ (W : Set U.left)) :
    ∀ Z : Set U.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : U.left.Opens, IsAffineOpen W ∧
        t'.left.base '' (s'.left.base ⁻¹' {u}) ⊆ (W : Set U.left) := by
  subst hs ht
  exact h

/-- Let `j` be an equivalence relation on an `S`-scheme `U`
with finite locally free source and target maps, let `G` be a groupoid scheme extending `j`,
let `U` and the relation scheme `R` belong to a big fppf site `B` of `S`, and assume the
affine-orbit condition: every nonempty closed subset of `U` contains a point whose orbit
`j.target(j.source⁻¹({u}))` lies in an affine open of `U`. Then there are an `S`-scheme `M`
belonging to `B` and a morphism `π : U ⟶ M` such that the restricted functor of points of `M`
is a sheaf for the big fppf topology of `S` and represents the quotient sheaf of `j`,
compatibly with `π`. -/
@[sga "3 V 4.1" "more general"]
theorem exists_represents_quotientSheaf_of_extendsRelation_of_affineOrbits {S : Scheme.{u}}
    {R U : Over S} (j : PreRelation R U) (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains U.left)
    (hR : B.Contains R.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (horbit : ∀ Z : Set U.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : U.left.Opens, IsAffineOpen W ∧
        j.target.left.base '' (j.source.left.base ⁻¹' {u}) ⊆ (W : Set U.left)) :
    ∃ (M : Over S) (π : U ⟶ M), B.Contains M.left ∧
      ∃ hM : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (points (Over.post B.inclusion) M),
        ∃ q : quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j ⟶
            (⟨points (Over.post B.inclusion) M, hM⟩ :
              Sheaf (BigFppfOver.topology B S hS) (Type u)),
          IsIso q ∧
            toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j ≫ q.hom =
              (Over.post B.inclusion).op.whiskerLeft (yoneda.map π) := by
  obtain ⟨hobj, harr, hsrc, htgt⟩ := hExt
  subst hobj harr
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  have hj : j = prod.lift G.target G.source :=
    prod.hom_ext (by rw [prod.lift_fst, htgt]) (by rw [prod.lift_snd, hsrc])
  have h1 : IsFiniteLocallyFree G.source.left := by rw [hsrc]; infer_instance
  have h2 : IsFiniteLocallyFree G.target.left := by rw [htgt]; infer_instance
  have h3 : IsEquivalenceRelation G.target G.source := by rw [hsrc, htgt]; infer_instance
  have horbit' := orbit_condition_congr hsrc.symm htgt.symm horbit
  obtain ⟨M, π, hM, -, -, -, hMsheaf, q, hq, hfac⟩ :=
    Space.exists_quotientMap_isRepresented_of_affineOrbits G B hS hU hR horbit'
  refine ⟨M, π, hM, ?_⟩
  rw [hj]
  exact ⟨hMsheaf, q, hq, hfac⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representability of the quotient -/

/-- Let `s, t : R ⟶ Z` be morphisms of the big fppf site of `S`, let `j` be a
pre-relation on the image of `Z` whose source and target are their images, and suppose `j` is
an equivalence relation with finite locally free source and target satisfying the affine-orbit
condition. Let `f : h_Z ⟶ V` be a morphism into a sheaf `V` through which every
morphism coequalizing `yoneda.map s` and `yoneda.map t` factors uniquely. Then there are an
object `V₀` of the site, a morphism `π₀ : Z ⟶ V₀` of the site and an isomorphism
`V ≅ h_{V₀}` carrying `f` to `yoneda.map π₀`. -/
theorem exists_iso_yoneda_of_finiteFlat_relation_of_affineOrbits
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z R : BigFppfOver B S hS} (s t : R ⟶ Z)
    {j : PreRelation ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj Z)}
    (hjs : j.source = (Over.post B.inclusion).map s)
    (hjt : j.target = (Over.post B.inclusion).map t)
    (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    (horbit : ∀ Y : Set ((BigFppfOver.toScheme B S hS).obj Z), IsClosed Y → Y.Nonempty →
      ∃ u ∈ Y, ∃ W : ((BigFppfOver.toScheme B S hS).obj Z).Opens, IsAffineOpen W ∧
        ((BigFppfOver.toScheme B S hS).map t).base ''
            (((BigFppfOver.toScheme B S hS).map s).base ⁻¹' {u}) ⊆
          (W : Set ((BigFppfOver.toScheme B S hS).obj Z)))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V) (f : yoneda.obj Z ⟶ V)
    (hw : yoneda.map s ≫ f = yoneda.map t ≫ f)
    (hdesc : ∀ (A : Sheaf (BigFppfOver.topology B S hS) (Type u))
        (k : yoneda.obj Z ⟶ A.obj), yoneda.map s ≫ k = yoneda.map t ≫ k →
      ∃! d : V ⟶ A.obj, f ≫ d = k) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      f ≫ e.hom = yoneda.map π₀ := by
  classical
  have horbit' := orbit_condition_congr hjs.symm hjt.symm horbit
  obtain ⟨M, π, hcontains, hMsheaf, q, hq, hqfac⟩ :=
    exists_represents_quotientSheaf_of_extendsRelation_of_affineOrbits (S := S) j G hExt B hS
      Z.left.property R.left.property horbit'
  obtain ⟨π₀, e, he⟩ := exists_iso_yoneda_of_descent_of_represents
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion) s t hjs hjt hV f hw
    hdesc (Over.mk (X := B.obj hS) (Y := (⟨M.left, hcontains⟩ : B.Schemes))
      (ObjectProperty.homMk M.hom)) π hMsheaf q hq hqfac
  exact ⟨_, π₀, e, he⟩

/-- Let `V` be an algebraic space over `S` with a surjective étale atlas `f : h_Z ⟶ V`, and suppose
the kernel pair of `f` is given by two morphisms `s, t : R ⟶ Z` of the site whose pre-relation
`j` is an equivalence relation with finite locally free source and target satisfying the
affine-orbit condition. Then `V` is representable by an object of the site, compatibly with the
atlas. -/
theorem exists_iso_yoneda_of_surjectiveEtale_atlas_of_finiteFlat
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z R : BigFppfOver B S hS} (s t : R ⟶ Z)
    {j : PreRelation ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj Z)}
    (hjs : j.source = (Over.post B.inclusion).map s)
    (hjt : j.target = (Over.post B.inclusion).map t)
    (G : GroupoidScheme S) (hExt : ExtendsRelation j G)
    [IsFiniteLocallyFree j.source.left] [IsFiniteLocallyFree j.target.left]
    [IsEquivalenceRelation j.target j.source]
    (horbit : ∀ Y : Set ((BigFppfOver.toScheme B S hS).obj Z), IsClosed Y → Y.Nonempty →
      ∃ u ∈ Y, ∃ W : ((BigFppfOver.toScheme B S hS).obj Z).Opens, IsAffineOpen W ∧
        ((BigFppfOver.toScheme B S hS).map t).base ''
            (((BigFppfOver.toScheme B S hS).map s).base ⁻¹' {u}) ⊆
          (W : Set ((BigFppfOver.toScheme B S hS).obj Z)))
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (f : yoneda.obj Z ⟶ V)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      f ≫ e.hom = yoneda.map π₀ := by
  obtain ⟨hRsh, hUsh, ⟨hcolim⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hR hV hsurj hetale
  refine exists_iso_yoneda_of_finiteFlat_relation_of_affineOrbits B S hS s t hjs hjt G hExt
    horbit hV.isSheaf f hR.w fun A k hk => ?_
  exact existsUnique_desc_of_isColimit (BigFppfOver.topology B S hS)
    (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      ⟨yoneda.obj Z, hUsh⟩)
    ⟨yoneda.map t⟩ (⟨f⟩ : (⟨yoneda.obj Z, hUsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨V, hV.isSheaf⟩)
    _ hcolim A k hk

/-- An algebraic space `V` with a surjective étale atlas `f : h_Z ⟶ V`, where `Z` admits an
immersion into an affine scheme, is representable by an object of the site, compatibly with
`f`, provided the kernel pair of `f` is given by two morphisms `s, t : R ⟶ Z` of the site whose
underlying morphisms of schemes are finite locally free. -/
theorem exists_iso_yoneda_of_kernelPair_of_finiteLocallyFree_of_isImmersion
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z R : BigFppfOver B S hS} (s t : R ⟶ Z)
    (hsFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (htFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    {Y : Scheme.{u}} [IsAffine Y]
    (i : (BigFppfOver.toScheme B S hS).obj Z ⟶ Y)
    [_root_.AlgebraicGeometry.IsImmersion i]
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (f : yoneda.obj Z ⟶ V)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      f ≫ e.hom = yoneda.map π₀ := by
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
  refine exists_iso_yoneda_of_surjectiveEtale_atlas_of_finiteFlat B S hS t s hjs hjt
    (groupoidSchemeOfIsEquivalenceRelation (relation B S hS t s))
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation (relation B S hS t s)) ?_ hV f
    hR.flip hsurj hetale
  rintro W - ⟨u, hu⟩
  exact ⟨u, hu, exists_isAffineOpen_image_preimage_singleton_of_isImmersion _ _ i htFLF u⟩

/-- An algebraic space `V` with a chart `f : h_Z ⟶ V` which is surjective, étale and finite
locally free in the relative sense of `CategoryTheory.MorphismProperty.presheaf`, where `Z`
admits an immersion into an affine scheme, is representable. -/
theorem isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z : BigFppfOver B S hS} {Y : Scheme.{u}} [IsAffine Y]
    (i : (BigFppfOver.toScheme B S hS).obj Z ⟶ Y)
    [_root_.AlgebraicGeometry.IsImmersion i]
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (f : yoneda.obj Z ⟶ V)
    (hflf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    V.IsRepresentable := by
  set hf := hflf.rep with hfdef
  have htFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hf.snd f)) :=
    hflf.property_snd f
  have hsym : hf.symmetry hf ≫ hf.snd f = hf.fst' f :=
    Functor.relativelyRepresentable.symmetry_snd hf hf
  have hsFLF : IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map (hf.fst' f)) := by
    rw [← hsym, CategoryTheory.Functor.map_comp]
    exact MorphismProperty.RespectsIso.precomp
      (@IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map (hf.symmetry hf)) _ htFLF
  obtain ⟨V₀, π₀, e, -⟩ := exists_iso_yoneda_of_kernelPair_of_finiteLocallyFree_of_isImmersion
    B S hS (hf.fst' f) (hf.snd f) hsFLF htFLF i hV f (hf.isPullback' f) hsurj hetale
  exact CategoryTheory.isRepresentable_of_natIso _ e.symm

end Space

end AlgebraicGeometry

end
