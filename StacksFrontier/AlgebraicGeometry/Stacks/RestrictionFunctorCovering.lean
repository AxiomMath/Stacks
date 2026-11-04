module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace

/-!
# Local nonemptiness of the comma categories of the functor `F_étale ⥤ 𝒳`

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, fix an equivalence over the site between `𝒳` and the category of elements of the sheaf of
points of `F`, and let `u : F_étale ⥤ 𝒳` be the resulting functor. An object of `𝒳` is a scheme
chart `ξ : yoneda.obj T ⟶ F`, which need not factor through an étale chart, so the comma
category `StructuredArrow X u` may well be empty. It is nonempty *locally*: the base change
`T ×_F U` of a surjective étale atlas `U ⟶ F` of `F` along `ξ` is representable, its projection
to `T` is surjective and étale, and its second projection exhibits it as a chart over the étale
chart `U ⟶ F`. Hence the morphisms into `X` whose source admits a morphism to an object in the
image of `u` form a covering sieve for the étale topology inherited along the structure functor.

The base change `T ×_F U` is itself only a scheme chart of `F`, not an étale one: its morphism
to `F` is the projection to `T` followed by `ξ`. This is why the conclusion is the existence of
a *morphism* into the image of `u`, not that `X` be covered by objects of that image.

## Main definitions

* `CategoryTheory.Functor.structuredArrowSieve`: the sieve of the morphisms into an object
  whose source admits a morphism to an object in the image of a given functor.
* `AlgebraicGeometry.Space.schemeChartFunctor`: the equivalence from the scheme charts of the
  sheaf of points of `F` to `𝒳` determined by an equivalence over the site.

## Main results

* `AlgebraicGeometry.Space.exists_hom_to_etaleChart`: the base change of a surjective étale
  atlas of `F` along an arbitrary scheme chart of `F` is a chart over an étale chart, surjective
  and étale over the given one.
* `AlgebraicGeometry.Space.exists_etale_surjective_hom_to_restrictionFunctor_obj`: every object
  of `𝒳` receives a morphism, surjective and étale over the base, from an object admitting a
  morphism into the image of the functor `F_étale ⥤ 𝒳`.
* `AlgebraicGeometry.Space.structuredArrowSieve_restrictionFunctor_mem`: that family of
  morphisms is a covering sieve for the inherited étale topology.
* `CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_subsingleton`: a locally surjective
  morphism of presheaves of sets out of a subterminal presheaf sheafifies to an isomorphism.
  Together with the previous statement this is what identifies the sheaf `g_!` of the terminal
  sheaf on `F_étale` with the terminal sheaf on `𝒳`, once the presheaf `u_p` of the terminal
  presheaf is known to be subterminal.

## References

* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The sieve on `X` of those morphisms `g : Y ⟶ X` whose source admits a morphism to an object
in the image of `u`, that is, for which the comma category `StructuredArrow Y u` is nonempty. -/
def structuredArrowSieve (u : C ⥤ D) (X : D) : Sieve X where
  arrows Y _ := Nonempty (StructuredArrow Y u)
  downward_closed h g := h.elim fun V ↦ ⟨StructuredArrow.mk (g ≫ V.hom)⟩

/-- A morphism `g : Y ⟶ X` lies in `structuredArrowSieve u X` if and only if the comma category
`StructuredArrow Y u` is nonempty. -/
@[simp]
theorem mem_structuredArrowSieve_iff (u : C ⥤ D) {X Y : D} (g : Y ⟶ X) :
    (structuredArrowSieve u X).arrows g ↔ Nonempty (StructuredArrow Y u) :=
  Iff.rfl

/-- A morphism whose source maps to an object in the image of `u` lies in the sieve. -/
theorem mem_structuredArrowSieve (u : C ⥤ D) {X Y : D} (g : Y ⟶ X) {V : C} (h : Y ⟶ u.obj V) :
    (structuredArrowSieve u X).arrows g :=
  ⟨StructuredArrow.mk h⟩

end CategoryTheory.Functor

namespace CategoryTheory.Presheaf

universe w v₃ u₃

/-- A locally surjective morphism of presheaves of sets whose source is subterminal, i.e. all of
whose sets of sections are subsingletons, becomes an isomorphism after sheafification: such a
morphism is locally injective for free, hence locally bijective. -/
theorem isIso_presheafToSheaf_map_of_subsingleton {C : Type u₃} [Category.{v₃} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)] {P Q : Cᵒᵖ ⥤ Type w} (τ : P ⟶ Q)
    (hP : ∀ X : Cᵒᵖ, Subsingleton (P.obj X)) (hτ : IsLocallySurjective J τ) :
    IsIso ((presheafToSheaf J (Type w)).map τ) := by
  rw [← J.W_iff]
  have : IsLocallyInjective J τ :=
    ⟨fun {X} x y _ ↦ by
      rw [(hP X).allEq x y, equalizerSieve_self_eq_top]
      exact J.top_mem _⟩
  have := hτ
  exact J.W_of_isLocallyBijective τ

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A property of morphisms of schemes stable under composition and under isomorphism holds for
a morphism of the big fppf category of `S` composed with isomorphisms on either side as soon as
it holds for the morphism itself. -/
private theorem prop_map_isos_comp {P : MorphismProperty Scheme.{u}}
    [P.IsMultiplicative] [P.RespectsIso] {X Y Z W : BigFppfOver B S hS}
    (i : X ⟶ Y) [IsIso i] (f : Y ⟶ Z) (j : Z ⟶ W) [IsIso j]
    (hf : P ((BigFppfOver.toScheme B S hS).map f)) :
    P ((BigFppfOver.toScheme B S hS).map (i ≫ f ≫ j)) := by
  rw [Functor.map_comp, Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso P _)
    (MorphismProperty.comp_mem _ _ _ hf (MorphismProperty.of_isIso P _))

/-- A surjective étale atlas of an algebraic space `F`, base changed along an arbitrary scheme
chart `Z` of `F`: the base change is a scheme chart of `F` mapping to the étale chart given by
the atlas, and its projection to `Z` is surjective and étale. -/
theorem exists_hom_to_etaleChart (hF : IsAlgebraicSpace B S hS F)
    (Z : CostructuredArrow yoneda F) :
    ∃ (V : SmallEtale B S hS F) (Z' : CostructuredArrow yoneda F) (β : Z' ⟶ Z),
      Nonempty (Z' ⟶ (SmallEtale.inclusion B S hS F).obj V) ∧
      Etale ((BigFppfOver.toScheme B S hS).map β.left) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map β.left) := by
  obtain ⟨U, φ, hsurj, het⟩ := hF.exists_atlas
  exact ⟨⟨CostructuredArrow.mk φ, het⟩,
    CostructuredArrow.mk (yoneda.map (het.rep.snd Z.hom) ≫ Z.hom),
    CostructuredArrow.homMk (het.rep.snd Z.hom) rfl,
    ⟨CostructuredArrow.homMk (het.rep.fst' Z.hom) (het.rep.isPullback' Z.hom).w⟩,
    het.property_snd Z.hom,
    hsurj.property Z.hom _ _ (het.rep.isPullback' Z.hom)⟩

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- Every object of `𝒳` receives a morphism, surjective and étale over the big fppf category of
`S`, from an object admitting a morphism to the image of an étale chart, for an arbitrary
essentially surjective comparison functor from the scheme charts of `F` lying over the base. -/
private theorem exists_hom_to_image_of_essSurj (hF : IsAlgebraicSpace B S hS F)
    (G : CostructuredArrow yoneda F ⥤ 𝒳) [G.EssSurj]
    (hGp : G ⋙ p = CostructuredArrow.proj yoneda F) (X : 𝒳) :
    ∃ (V : SmallEtale B S hS F) (Y : 𝒳) (α : Y ⟶ X),
      Nonempty (Y ⟶ G.obj ((SmallEtale.inclusion B S hS F).obj V)) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (p.map α)) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map (p.map α)) := by
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.respectsIso
  obtain ⟨V, Z', β, ⟨γ⟩, het, hsurj⟩ := exists_hom_to_etaleChart B S hS F hF (G.objPreimage X)
  have hβ : p.map (G.map β) = eqToHom (Functor.congr_obj hGp Z') ≫ β.left ≫
      eqToHom (Functor.congr_obj hGp (G.objPreimage X)).symm :=
    Functor.congr_hom hGp β
  have hα : p.map (G.map β ≫ (G.objObjPreimageIso X).hom) =
      eqToHom (Functor.congr_obj hGp Z') ≫ β.left ≫
        (eqToHom (Functor.congr_obj hGp (G.objPreimage X)).symm ≫
          p.map (G.objObjPreimageIso X).hom) := by
    rw [p.map_comp, hβ]
    simp only [Category.assoc]
  refine ⟨V, G.obj Z', G.map β ≫ (G.objObjPreimageIso X).hom, ⟨G.map γ⟩, ?_⟩
  rw [hα]
  exact ⟨prop_map_isos_comp B S hS _ _ _ het, prop_map_isos_comp B S hS _ _ _ hsurj⟩

/-- The functor `F_étale ⥤ 𝒳` is the restriction of the functor on all scheme charts. -/
theorem inclusion_comp_schemeChartFunctor
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    SmallEtale.inclusion B S hS F ⋙ schemeChartFunctor B S hS F p e =
      restrictionFunctor B S hS F p e :=
  rfl

/-- Every object of `𝒳` receives a morphism, surjective and étale over the big fppf category of
`S`, from an object admitting a morphism to the image under `F_étale ⥤ 𝒳` of an étale chart of
`F`. The source is the base change of an atlas of `F` along the chart of the given object. -/
theorem exists_etale_surjective_hom_to_restrictionFunctor_obj
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) (X : 𝒳) :
    ∃ (V : SmallEtale B S hS F) (Y : 𝒳) (α : Y ⟶ X),
      Nonempty (Y ⟶ (restrictionFunctor B S hS F p e).obj V) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (p.map α)) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map (p.map α)) :=
  exists_hom_to_image_of_essSurj B S hS F p hF (schemeChartFunctor B S hS F p e)
    (schemeChartFunctor_comp B S hS F p e) X

/-- **Local nonemptiness of the comma categories of `F_étale ⥤ 𝒳`.** For every object `X` of
`𝒳` the morphisms into `X` whose source admits a morphism to the image of an étale chart of `F`
form a covering sieve for the étale topology inherited along the structure functor. -/
theorem structuredArrowSieve_restrictionFunctor_mem
    (hp : p.IsFiberedInGroupoids) (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) (X : 𝒳) :
    (restrictionFunctor B S hS F p e).structuredArrowSieve X ∈
      BigFppfOver.associatedTopology B S hS p .etale X := by
  obtain ⟨V, Y, α, ⟨δ⟩, het, hsurj⟩ :=
    exists_etale_surjective_hom_to_restrictionFunctor_obj B S hS F p hF e X
  have hcov : (Presieve.singleton α).map p ∈
      (BigFppfOver.baseOverTopology B S hS .etale).toPrecoverage (p.obj X) := by
    rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton,
      Presieve.map_singleton]
    have hmem : Presieve.singleton ((Over.forget (B.obj hS)).map (p.map α)) ∈
        AlgebraicGeometry.etalePrecoverage B ((p.obj X).left) := by
      rw [AlgebraicGeometry.etalePrecoverage_eq_comap, Precoverage.mem_comap_iff,
        Presieve.map_singleton]
      exact (Scheme.singleton_mem_precoverage_iff (P := @AlgebraicGeometry.Etale.{u}) _).2
        ⟨hsurj.surj, het⟩
    exact Precoverage.generate_mem_toGrothendieck hmem
  refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_)
    (Precoverage.generate_mem_toGrothendieck
      ⟨fun _ f _ ↦ hp.isStronglyCartesian f, hcov⟩)
  rintro Z g ⟨⟩
  exact ⟨StructuredArrow.mk δ⟩

end AlgebraicGeometry.Space

end
