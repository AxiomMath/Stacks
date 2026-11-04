module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.TwistedEtaleChart
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedBaseChangeOfSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SiteCategoricalQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Étale charts of the invariant spectrum on the big fppf site

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` with `U` and `R` affine and `s, t` finite
locally free, whose object scheme, arrow scheme and invariant spectrum `M = Spec C` lie in the big
fppf site of `S`. This file reads the scheme-theoretic results on `G` on the site:

* the canonical morphism `φ : U ⟶ M` is a categorical quotient among the objects of the site
  (`AlgebraicGeometry.Space.isSiteCategoricalQuotient_quotientSite`), so by
  `AlgebraicGeometry.Space.IsSiteCategoricalQuotient.hom_ext` two morphisms from `M` to an
  algebraic space which agree on `U` are equal;
* for an invariant morphism `ψ : U ⟶ Y` to an algebraic space and a separated étale morphism
  `V ⟶ Y`, every point of `U ×_Y V` lies in an étale chart `W ⟶ M` on which `ψ` is read off a
  morphism `W ⟶ V` (`AlgebraicGeometry.Space.exists_siteChart`), the chart being the invariant
  spectrum of a groupoid scheme of the same kind;
* two morphisms from an affine object `Z` étale over `M` to an algebraic space agree as soon as
  they agree on `Z ×_M U` (`AlgebraicGeometry.Space.eq_of_twistedToAux_comp_eq`), by the charts
  of the previous item for `Y = M` and `V = Z`.

These are the three ingredients of the proof of Stacks 0DUR that `φ` is a categorical quotient in
the category of algebraic spaces.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open AlgebraicGeometry.GroupoidScheme

noncomputable section

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale, jointly surjective family of morphisms of the site generates a covering sieve. -/
theorem generate_ofArrows_mem_topology_of_etale {X : BigFppfOver B S hS} {ι : Type*}
    (Z : ι → BigFppfOver B S hS) (u : ∀ i, Z i ⟶ X)
    (he : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (u i)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj X,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u i)).base) :
    Sieve.generate (Presieve.ofArrows Z u) ∈ BigFppfOver.topology B S hS X :=
  BigFppfOver.sieve_generate_ofArrows_mem_topology Z u
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
      ⟨hsurj, fun i => have := he i; ⟨inferInstance, inferInstance⟩⟩)

/-! ### The invariant spectrum on the site -/

/-- **The invariant spectrum of a groupoid scheme with affine object scheme lies in every big
fppf site containing the object scheme**: it is no larger than the object scheme, the invariant
ring being a subring of its global functions. -/
theorem contains_spec_invariantRing_of_contains (G : GroupoidScheme S) [IsAffine G.objects.left]
    (hU : B.Contains G.objects.left) : B.Contains (Spec (.of (invariantRing G))) := by
  refine lt_of_le_of_lt ?_ hU
  rw [Scheme.size_Spec, Scheme.size_of_isAffine G.objects.left]
  exact max_le_max le_rfl (Cardinal.mk_le_of_injective Subtype.val_injective)

section Realization

variable (hS) (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
  (hR : B.Contains G.arrows.left)
  (σ : Spec (.of (invariantRing G)) ⟶ S) (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom)
  (hM : B.Contains (Spec (.of (invariantRing G))))

/-- The source map of `G`, on the site. -/
abbrev sourceSite : schemeSiteObject B hS hR ⟶ schemeSiteObject B hS hU :=
  schemeSiteMap B hS hR hU G.source

/-- The target map of `G`, on the site. -/
abbrev targetSite : schemeSiteObject B hS hR ⟶ schemeSiteObject B hS hU :=
  schemeSiteMap B hS hR hU G.target

/-- The invariant spectrum `M = Spec C` of `G`, as an object of the site over `S` through a descent
`σ : M ⟶ S` of the structure morphism of `U`. -/
abbrev invariantSpectrumSite : BigFppfOver B S hS :=
  schemeSiteObject B hS (X := Over.mk σ) hM

/-- The canonical morphism `φ : U ⟶ M`, on the site. -/
abbrev quotientSite : schemeSiteObject B hS hU ⟶ invariantSpectrumSite hS G σ hM :=
  schemeSiteMap B hS (X := G.objects) (Y := Over.mk σ) hU hM
    (Over.homMk (objectsToInvariantSpectrum G) hσ)

/-- On the site, `φ : U ⟶ M` coequalizes the source and target maps of `G`: `s ≫ φ = t ≫ φ`. -/
theorem sourceSite_comp_quotientSite :
    sourceSite hS G hU hR ≫ quotientSite hS G hU σ hσ hM =
      targetSite hS G hU hR ≫ quotientSite hS G hU σ hσ hM := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact (target_comp_objectsToInvariantSpectrum G).symm

/-- **`φ : U ⟶ M` is a categorical quotient among the objects of the site**, because it is one in
the category of all schemes. -/
theorem isSiteCategoricalQuotient_quotientSite [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] :
    IsSiteCategoricalQuotient (sourceSite hS G hU hR) (targetSite hS G hU hR)
      (quotientSite hS G hU σ hσ hM) :=
  IsSiteCategoricalQuotient.of_scheme (sourceSite_comp_quotientSite hS G hU hR σ hσ hM)
    fun _ ℓ hℓ => existsUnique_comp_objectsToInvariantSpectrum_scheme G ℓ hℓ.symm

end Realization

/-! ### Étale charts on the site -/

section Chart

variable {G : GroupoidScheme S} [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (σ : Spec (.of (invariantRing G)) ⟶ S) (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom)
  (hM : B.Contains (Spec (.of (invariantRing G))))
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ψ : yoneda.obj (schemeSiteObject B hS hU) ⟶ Y)
  (hψ : yoneda.map (sourceSite hS G hU hR) ≫ ψ = yoneda.map (targetSite hS G hU hR) ≫ ψ)
  {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y)

include hσ hR hψ in
/-- **An étale chart of `M` on the site through a point of `U ×_Y V`.** For a separated étale
`v : V ⟶ Y`, every point `u'` of `U ×_Y V` lies in the image of `j : U'' ⟶ U ×_Y V` for an
object `W` of the site étale over `M` with `U'' = W ×_M U`, such that `U'' ⟶ U ×_Y V ⟶ V` factors
through `b : U'' ⟶ W`, and `b` is a categorical quotient among the objects of the site of a pair of
morphisms `R'' ⟶ U''`. -/
theorem exists_siteChart
    (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v)
    [_root_.AlgebraicGeometry.IsSeparated ((siteToOver B hS).obj V).hom]
    (u' : (BigFppfOver.toScheme B S hS).obj (twistedObject hU hY ψ v)) :
    ∃ (W U'' R'' : BigFppfOver B S hS) (e : W ⟶ invariantSpectrumSite hS G σ hM) (k : W ⟶ V)
      (a : U'' ⟶ schemeSiteObject B hS hU) (b : U'' ⟶ W) (j : U'' ⟶ twistedObject hU hY ψ v)
      (s'' t'' : R'' ⟶ U''),
      Etale ((BigFppfOver.toScheme B S hS).map e) ∧
        IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
          ((BigFppfOver.toScheme B S hS).map (quotientSite hS G hU σ hσ hM))
          ((BigFppfOver.toScheme B S hS).map e) ∧
        j ≫ twistedProj hU hY ψ v = a ∧ b ≫ k = j ≫ twistedToAux hU hY ψ v ∧
        IsSiteCategoricalQuotient s'' t'' b ∧
        u' ∈ Set.range ((BigFppfOver.toScheme B S hS).map j).base := by
  classical
  let D := twistedBaseChangeOfSpace hU hR hY ψ hψ v
  have : Etale D.proj.left := etale_twistedBaseChangeOfSpace_proj hU hR hY ψ hψ v hv
  have : _root_.AlgebraicGeometry.IsSeparated D.proj.left :=
    isSeparated_twistedBaseChangeOfSpace_proj hU hR hY ψ hψ v
  obtain ⟨G'', ι, e₀, k₀, hGo, hGa, hGs, hGt, hιo, hιa, he₀, hpb, hk₀, hk₀S, hu'⟩ :=
    D.exists_etale_chart σ hσ u'
  have hU'' : B.Contains G''.objects.left :=
    BigFppfSite.contains_of_isOpenImmersion B ι.mapObjects.left
      (contains_twistedObject hU hY ψ v)
  have hR'' : B.Contains G''.arrows.left :=
    BigFppfSite.contains_of_isOpenImmersion B ι.mapArrows.left
      (contains_twistedArrows hU hR hY ψ v)
  have hW : B.Contains (Spec (.of (invariantRing G''))) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B e₀ hM
  have hσ'' : objectsToInvariantSpectrum G'' ≫ e₀ ≫ σ = G''.objects.hom := by
    rw [← Category.assoc, ← hpb.w, Category.assoc, hσ]
    exact Over.w (ι.mapObjects ≫ D.hom.mapObjects)
  obtain ⟨j₀, hj⟩ : ∃ j₀ : schemeSiteObject B hS hU'' ⟶ twistedObject hU hY ψ v,
      (siteToOver B hS).map j₀ = ι.mapObjects := ⟨_, (siteToOver B hS).map_preimage _⟩
  have hj' : (BigFppfOver.toScheme B S hS).map j₀ = ι.mapObjects.left := congrArg (·.left) hj
  refine ⟨invariantSpectrumSite hS G'' (e₀ ≫ σ) hW, schemeSiteObject B hS hU'',
    schemeSiteObject B hS hR'',
    schemeSiteMap B hS (X := Over.mk (e₀ ≫ σ)) (Y := Over.mk σ) hW hM (Over.homMk e₀ rfl),
    BigFppfOver.homOfCompEq B S hS (T := invariantSpectrumSite hS G'' (e₀ ≫ σ) hW) (W := V) k₀ hk₀S,
    schemeSiteMap B hS hU'' hU (ι.mapObjects ≫ D.hom.mapObjects),
    quotientSite hS G'' hU'' (e₀ ≫ σ) hσ'' hW,
    j₀, sourceSite hS G'' hU'' hR'', targetSite hS G'' hU'' hR'', he₀, hpb, ?_, ?_,
    isSiteCategoricalQuotient_quotientSite hS G'' hU'' hR'' (e₀ ≫ σ) hσ'' hW, ?_⟩
  · apply (siteToOver B hS).map_injective
    rw [Functor.map_comp, siteToOver_map_schemeSiteMap]
    exact congrArg (· ≫ (siteToOver B hS).map (twistedProj hU hY ψ v)) hj
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq B S hS
      (T := invariantSpectrumSite hS G'' (e₀ ≫ σ) hW) (W := V) k₀ hk₀S]
    exact hk₀.trans (congrArg (· ≫ D.toAuxG.left) hj'.symm)
  · rwa [hj']

end Chart

/-! ### Agreement on an affine object étale over `M` -/

/-- A morphism of schemes with affine source is separated. -/
private theorem isSeparated_of_isAffine_source {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] :
    _root_.AlgebraicGeometry.IsSeparated f := by
  have : _root_.AlgebraicGeometry.IsSeparated (f ≫ terminal.from Y) := by
    rw [Subsingleton.elim (f ≫ terminal.from Y) (terminal.from X)]
    infer_instance
  exact _root_.AlgebraicGeometry.IsSeparated.of_comp f (terminal.from Y)

section Overlap

variable (hS) {G : GroupoidScheme S} [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (σ : Spec (.of (invariantRing G)) ⟶ S) (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom)
  (hM : B.Contains (Spec (.of (invariantRing G))))

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The algebraic space represented by `M`. -/
theorem isAlgebraicSpace_invariantSpectrumSite :
    IsAlgebraicSpace B S hS (yoneda.obj (invariantSpectrumSite hS G σ hM)) :=
  isAlgebraicSpace_yoneda B S hS _

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The morphism of representable presheaves induced by `φ : U ⟶ M` coequalizes those induced by
the source and target maps of `G`. -/
theorem quotientSite_invariant :
    yoneda.map (sourceSite hS G hU hR) ≫ yoneda.map (quotientSite hS G hU σ hσ hM) =
      yoneda.map (targetSite hS G hU hR) ≫ yoneda.map (quotientSite hS G hU σ hσ hM) := by
  rw [← Functor.map_comp, ← Functor.map_comp, sourceSite_comp_quotientSite hS]

include hR in
/-- **Two morphisms from an affine object `Z` étale over `M` to an algebraic space which agree on
`Z ×_M U` are equal.** The points of `Z` are covered by the charts of
`AlgebraicGeometry.Space.exists_siteChart` for `Y = M` and `V = Z`; on each chart the two morphisms
agree by uniqueness against algebraic spaces, and the charts form an étale covering of `Z`. -/
theorem eq_of_twistedToAux_comp_eq (Z : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] (ζ : Z ⟶ invariantSpectrumSite hS G σ hM)
    (hζ : Etale ((BigFppfOver.toScheme B S hS).map ζ)) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (α₁ α₂ : yoneda.obj Z ⟶ Y)
    (h : yoneda.map (twistedToAux hU (isAlgebraicSpace_invariantSpectrumSite hS σ hM)
        (yoneda.map (quotientSite hS G hU σ hσ hM)) (yoneda.map ζ)) ≫ α₁ =
      yoneda.map (twistedToAux hU (isAlgebraicSpace_invariantSpectrumSite hS σ hM)
        (yoneda.map (quotientSite hS G hU σ hσ hM)) (yoneda.map ζ)) ≫ α₂) :
    α₁ = α₂ := by
  classical
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  set hYM := isAlgebraicSpace_invariantSpectrumSite hS σ hM
  set φs := quotientSite hS G hU σ hσ hM
  have hvM : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map ζ) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ζ).2 hζ
  have : IsAffine ((siteToOver B hS).obj Z).left :=
    ‹IsAffine ((BigFppfOver.toScheme B S hS).obj Z)›
  have := isSeparated_of_isAffine_source ((siteToOver B hS).obj Z).hom
  have hpbZ := (Functor.relativelyRepresentable.of_diag hYM.diagonal_representable
    (yoneda.map ζ)).isPullback_of_map φs
  have hpbS := hpbZ.map (BigFppfOver.toScheme B S hS)
  have hsurjφ : Surjective ((BigFppfOver.toScheme B S hS).map φs) :=
    ⟨surjective_objectsToInvariantSpectrum G⟩
  have hsurjAux : Surjective ((BigFppfOver.toScheme B S hS).map
      (twistedToAux hU hYM (yoneda.map φs) (yoneda.map ζ))) :=
    MorphismProperty.of_isPullback hpbS.flip hsurjφ
  choose u' hu' using fun z => hsurjAux.surj z
  choose W U'' R'' e k a b j s'' t'' he hpb hja hbk hq hrange using fun z =>
    exists_siteChart hU hR σ hσ hM hYM (yoneda.map φs) (quotientSite_invariant hS hU hR σ hσ hM)
      (yoneda.map ζ) hvM (u' z)
  have hkζ : ∀ z, k z ≫ ζ = e z := by
    intro z
    refine (hq z).epi ?_
    rw [← Category.assoc, hbk z, Category.assoc, hpbZ.w, ← Category.assoc, hja z]
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact (hpb z).w
  have hket : ∀ z, Etale ((BigFppfOver.toScheme B S hS).map (k z)) := fun z =>
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ hζ
      (by simpa only [← Functor.map_comp, hkζ z] using he z)
  have hksurj : ∀ z : (BigFppfOver.toScheme B S hS).obj Z,
      ∃ i, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i)).base := by
    intro z
    obtain ⟨x, hx⟩ := hrange z
    refine ⟨z, ((BigFppfOver.toScheme B S hS).map (b z)).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hbk z, Functor.map_comp,
      Scheme.Hom.comp_apply, hx, hu' z]
  refine hom_ext_of_cover B S hS hY.isSheaf Z W k
    (generate_ofArrows_mem_topology_of_etale W k hket hksurj) fun z => ?_
  refine (hq z).hom_ext hY ?_
  have key : yoneda.map (b z) ≫ yoneda.map (k z) = yoneda.map (j z) ≫
      yoneda.map (twistedToAux hU hYM (yoneda.map φs) (yoneda.map ζ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hbk z]
  rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, h]

end Overlap

end AlgebraicGeometry.Space

end

end
