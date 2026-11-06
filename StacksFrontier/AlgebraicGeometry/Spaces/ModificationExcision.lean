module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The étale covering behind the excision equivalence

Let `f : V ⟶ W` be an étale morphism of algebraic spaces over a scheme `S` and let `T ⊆ W` be
a closed subspace whose preimage `f⁻¹T` is carried isomorphically onto `T` by `f`. The base-change
functor along `f` sends a modification of `W` outside `W⁰ = W ∖ T` to its base change, and `W⁰`
together with the open image of `f` is a Zariski covering of `W` whose second member carries a
surjective étale chart factoring through `f`.

## Main results

* `AlgebraicGeometry.Space.baseChangeFunctor_obj_hom` and
  `AlgebraicGeometry.Space.isPullback_baseChangeFunctor_obj`: the structure morphism of the
  image of a modification under the base-change functor is the second projection of the fibre
  product, so the image is a base change of the original morphism.
* `AlgebraicGeometry.Space.range_pointsMap_ι_subset_of_isIso_fromPreimage`: a closed subspace
  whose preimage maps isomorphically onto it is contained in the image of the morphism.
* `AlgebraicGeometry.Space.exists_openImage_isZariskiCover_openComplement`: the open
  complement of `T` and the open image of `f` form a Zariski covering of `W`, and the image
  carries a surjective étale chart from a scheme which factors through `f`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The image of a modification under the base-change functor -/

variable {V W : AlgebraicSpaces B S hS}

/- Pullback instances of `FibreDegreeStratification`, which instance search does not find
under Lean v4.35.0. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ModificationExcision :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_ModificationExcision
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base-change functor sends a modification `X ⟶ W` of `W` outside `W₀`
to its base change along `f`: the structure morphism of the image is the second projection of
the fibre product of `X ⟶ W` and `f`. -/
theorem baseChangeFunctor_obj_hom (f : V ⟶ W) (W₀ : Subfunctor W.obj)
    (X : Modification B S hS W₀) :
    ((baseChangeFunctor B S hS f W₀).1.obj X).obj.hom = pullback.snd X.obj.hom f.hom :=
  rfl

/-- The image of a modification under the base-change functor sits in a
Cartesian square over the original morphism. -/
theorem isPullback_baseChangeFunctor_obj (f : V ⟶ W) (W₀ : Subfunctor W.obj)
    (X : Modification B S hS W₀) :
    IsPullback (pullback.fst X.obj.hom f.hom)
      ((baseChangeFunctor B S hS f W₀).1.obj X).obj.hom X.obj.hom f.hom :=
  IsPullback.of_hasPullback _ _

/-! ### The Zariski covering by the open complement and the open image -/

/-- If the preimage of a subfunctor `T` of the target is carried isomorphically onto `T`, then
every point of `T` is in the image of the morphism. -/
theorem range_pointsMap_ι_subset_of_isIso_fromPreimage
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (T : Subfunctor G)
    (hp : IsIso (T.fromPreimage p)) :
    Set.range (pointsMap B S hS T.toFunctor T.ι) ⊆ Set.range (pointsMap B S hS F p) := by
  have hsurj : Function.Surjective
      (pointsMap B S hS (T.preimage p).toFunctor (T.fromPreimage p)) := by
    intro t
    refine ⟨pointsMap B S hS T.toFunctor (inv (T.fromPreimage p)) t, ?_⟩
    have h := pointsMap_comp B S hS T.toFunctor (inv (T.fromPreimage p)) (T.fromPreimage p)
    rw [IsIso.inv_hom_id, pointsMap_id] at h
    exact (congrFun h t).symm
  rintro _ ⟨t, rfl⟩
  obtain ⟨z, hz⟩ := hsurj t
  refine ⟨pointsMap B S hS (T.preimage p).toFunctor (T.preimage p).ι z, ?_⟩
  calc pointsMap B S hS F p (pointsMap B S hS (T.preimage p).toFunctor (T.preimage p).ι z)
      = pointsMap B S hS (T.preimage p).toFunctor ((T.preimage p).ι ≫ p) z :=
        (congrFun (pointsMap_comp B S hS (T.preimage p).toFunctor (T.preimage p).ι p) z).symm
    _ = pointsMap B S hS (T.preimage p).toFunctor (T.fromPreimage p ≫ T.ι) z := by
        rw [T.fromPreimage_ι p]
    _ = pointsMap B S hS T.toFunctor T.ι t := by
        rw [congrFun (pointsMap_comp B S hS (T.preimage p).toFunctor
          (T.fromPreimage p) T.ι) z, Function.comp_apply, hz]

/-- Let `f : V ⟶ W` be an étale morphism of algebraic spaces over `S` and let `T` be a closed
subspace of `W` whose preimage is carried isomorphically onto `T`. Then the open complement `W⁰` of
`T` together with the open image `I` of `f` is a Zariski covering of `W`, and there is a scheme `U`
with a surjective étale morphism `q : U ⟶ I` and a morphism `a : U ⟶ V` such that `q` followed by
the inclusion of `I` is `a` followed by `f`. -/
theorem exists_openImage_isZariskiCover_openComplement (f : V ⟶ W) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) :
    ∃ (I : Subfunctor W.obj) (_ : IsOpenSubspace B S hS I) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ V.obj) (q : yoneda.obj U ⟶ I.toFunctor),
      q ≫ I.ι = a ≫ f.hom ∧ IsSurjective B S hS q ∧ IsEtale B S hS q ∧
        IsZariskiCover B S hS (ULift.{u} Bool)
          (fun b ↦ if b.down then openComplement B S hS T else I) := by
  classical
  obtain ⟨U, a, hasurj, haetale⟩ := V.property.exists_atlas
  have hcetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a ≫ f.hom) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS haetale) hf)
  obtain ⟨I, q, hIopen, hq, hqsurj, hqetale, hIimage⟩ :=
    exists_isOpenSubspace_etaleImage B S hS W.property U (a ≫ f.hom) hcetale
  have hrange : Set.range (pointsMap B S hS (yoneda.obj U) (a ≫ f.hom)) =
      Set.range (pointsMap B S hS V.obj f.hom) := by
    have hasurj' : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
      (presheafSurjective_iff_isSurjective_yoneda B S hS V.obj V.property U a).mp hasurj
    rw [pointsMap_comp, Set.range_comp, hasurj'.range_eq, Set.image_univ]
  refine ⟨I, hIopen, U, a, q, hq,
    (presheafSurjective_iff_isSurjective_yoneda B S hS I.toFunctor hIopen.1 U q).mp hqsurj,
    isEtale_of_presheaf_etale B S hS hqetale, ?_⟩
  have hopen : ∀ b : ULift.{u} Bool, IsOpenSubspace B S hS
      (if b.down then openComplement B S hS T else I) := by
    rintro ⟨b⟩
    cases b
    · simpa using hIopen
    · simpa using isOpenSubspace_openComplement B S hS W.property T hT
  refine (isZariskiCover_iff_iUnion_points B S hS W.obj W.property _ _ hopen).mpr ?_
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  by_cases hx : x ∈ Set.range (pointsMap B S hS T.toFunctor T.ι)
  · refine ⟨ULift.up false, ?_⟩
    have : x ∈ Set.range (pointsMap B S hS I.toFunctor I.ι) := by
      rw [hIimage, hrange]
      exact range_pointsMap_ι_subset_of_isIso_fromPreimage B S hS f.hom T hfT hx
    simpa using this
  · refine ⟨ULift.up true, ?_⟩
    have : x ∈ Set.range (pointsMap B S hS (openComplement B S hS T).toFunctor
        (openComplement B S hS T).ι) := by
      rwa [range_pointsMap_ι_openComplement]
    simpa using this

end AlgebraicGeometry.Space

end
