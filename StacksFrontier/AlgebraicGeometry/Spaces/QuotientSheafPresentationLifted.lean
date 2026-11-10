module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# The quotient of a scheme by an étale equivalence relation, sheafified in a larger universe

The quotient sheaf of `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentation` is the
sheafification of the quotient presheaf inside `Type u`, the universe of the morphisms of the
big fppf site of `S`. Sheafification there is available only under a hypothesis; this file
develops the same construction with the values of the quotient presheaf lifted to
`Type (max u v)` *before* sheafification, which for `v = u + 1` makes the ordinary
sheafification of a presheaf on an essentially small site available.

## Main definitions

* `AlgebraicGeometry.Space.uliftQuotientChart` is the canonical map to
  `AlgebraicGeometry.Space.uliftQuotientSheaf`, the sheafification of the lifted quotient
  presheaf, from the lifted presheaf represented by the presenting scheme. That sheaf and the
  presentation structure `AlgebraicGeometry.Space.EtalePresentation` are those of
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation`, re-exported here.

## Main results

* `AlgebraicGeometry.Space.uliftQuotientChart_isPullback` is the kernel-pair property of the
  lifted chart, and carries **no** hypothesis at all.
* `AlgebraicGeometry.Space.uliftQuotientChart_surjective_of_coveringSieveDescent` and
  `AlgebraicGeometry.Space.uliftQuotientChart_etale_of_coveringSieveDescent`: the lifted chart
  is surjective and étale after every representable base change.
* `AlgebraicGeometry.Space.uliftQuotientPresentation_of_coveringSieveDescent` assembles the
  presentation.

## Implementation notes

**Transport of the atlas properties across the lift.** `CategoryTheory.uliftYoneda` is
`CategoryTheory.yoneda` followed by whiskering with `ULift`, and that whiskering functor is
fully faithful, so a relative morphism property for `yoneda` transports to one for
`uliftYoneda` along it: this is `AlgebraicGeometry.Space.relative_ulift_of_presheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation`. What has to be matched up is
sheafification, and that is where the two universes meet: `ULift` preserves sheafification on
an essentially small site, so sheafifying the lifted presheaf agrees with lifting the
sheafified presheaf, and the lifted chart agrees with the lift of the unlifted chart up to the
comparison isomorphism. `AlgebraicGeometry.BigFppfOver.essentiallySmall` supplies both the
smallness and, through `CategoryTheory.hasSheafifyEssentiallySmallSite`, the unlifted
sheafification, so neither is a hypothesis of the statements here.

**The kernel pair needs no hypothesis.** Unlike surjectivity and étaleness, the kernel-pair
property does not go through the unlifted statement, hence not through Stacks 0265 and not
through the descent hypothesis. Before sheafification it is
`AlgebraicGeometry.Space.quotientPresheaf_isPullback`, which holds for any internal
equivalence relation; lifting is a fully faithful whiskering and sheafification is left
exact, so the square stays Cartesian, provided the lifted functors of points of `R` and `U`
are already sheaves. That last point is
`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj` together with
`CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff`, neither of which assumes anything
about the quotient.

**Why nothing here is tagged.** Three of the four results carry the effective-descent
hypothesis of `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentation`, at the
monomorphisms locally of finite type. That hypothesis is a theorem of this development, and the
discharged forms live in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional`, which is where
`@[stacks 02WW]` sits; the conditional forms here stay untagged. The kernel-pair statement
carries no hypothesis, but it is not a statement of Tag 02WW either: it is the kernel-pair half
of Tag 02WV, already tagged on `AlgebraicGeometry.Space.quotientMap_isPullback`, transported to
the lifted construction — so it is left untagged rather than duplicating that tag at a
different statement.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- The unlifted chart of the quotient sheaf, written as the sheafification unit applied to the
canonical map from the presheaf represented by the presenting scheme to the quotient presheaf.
This is the shape in which `relative_ulift_sheafify` consumes it. -/
private theorem quotientMap_eq_toSheafify_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    quotientMap B S hS s t =
      (yonedaToPoints (Over.post B.inclusion) U ≫
          toQuotientPresheaf (Over.post B.inclusion) (relation B S hS s t)) ≫
        toSheafify (BigFppfOver.topology B S hS)
          (quotientPresheaf (Over.post B.inclusion) (relation B S hS s t)) :=
  (yonedaEquiv_symm_app_toQuotientSheaf _ _ U _).trans (Category.assoc _ _ _).symm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type (max u v))]
variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- The canonical map from the lifted presheaf represented by the presenting scheme to the
lifted quotient sheaf. -/
noncomputable def uliftQuotientChart :
    uliftYoneda.{v}.obj U ⟶ (uliftQuotientSheaf.{u, v} B S hS s t).obj :=
  Functor.whiskerRight (yonedaToPoints (Over.post B.inclusion) U ≫
      toQuotientPresheaf (Over.post B.inclusion) (relation B S hS s t)) uliftFunctor.{v} ≫
    toSheafify (BigFppfOver.topology B S hS) _

/-- **The kernel pair of the lifted chart, with no hypothesis.** The relation is the fibre
product of the lifted chart with itself.

It does not carry `@[stacks 02WW]`, nor `@[stacks 02WV]`: see the implementation notes. -/
theorem uliftQuotientChart_isPullback
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    IsPullback (uliftYoneda.{v}.map t) (uliftYoneda.{v}.map s)
      (uliftQuotientChart.{u, v} B S hS s t) (uliftQuotientChart.{u, v} B S hS s t) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F : C ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  have : F.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  have : F.Faithful := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  have htarget : j.target = F.map t := by
    change prod.lift (F.map t) (F.map s) ≫ prod.fst = F.map t
    exact prod.lift_fst _ _
  have hsource : j.source = F.map s := by
    change prod.lift (F.map t) (F.map s) ≫ prod.snd = F.map s
    exact prod.lift_snd _ _
  have hp : IsPullback
      (Functor.whiskerRight (targetMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (sourceMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v}) :=
    (quotientPresheaf_isPullback F j).map
      ((Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max u v))).obj uliftFunctor.{v})
  have hsh : ∀ X : C, Presheaf.IsSheaf J (Stacks.Groupoids.points F (F.obj X) ⋙ uliftFunctor.{v}) :=
    fun X => by
      refine (isSheaf_iff_isSheaf_of_type J _).mpr ?_
      rw [Presieve.isSheaf_comp_uliftFunctor_iff]
      exact (isSheaf_iff_isSheaf_of_type J _).mp
        (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS (F.obj X))
  have hpts : IsPullback
      (Functor.whiskerRight (targetMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (sourceMap F j) uliftFunctor.{v})
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
        toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v}))
      (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
        toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v})) := by
    refine ((hp.map (presheafToSheaf J (Type (max u v)))).map
      (sheafToPresheaf J (Type (max u v)))).of_iso' (isoSheafify J (hsh R))
      (isoSheafify J (hsh U)) (isoSheafify J (hsh U)) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · exact (toSheafify_naturality J (Functor.whiskerRight (targetMap F j) uliftFunctor.{v})).symm
    · exact (toSheafify_naturality J (Functor.whiskerRight (sourceMap F j) uliftFunctor.{v})).symm
  -- the lifted functors of points are the lifted representables
  let eR : Stacks.Groupoids.points F (F.obj R) ⋙ uliftFunctor.{v} ≅ uliftYoneda.{v}.obj R :=
    (Functor.isoWhiskerRight (asIso (yonedaToPoints F R)) uliftFunctor.{v}).symm
  let eU : Stacks.Groupoids.points F (F.obj U) ⋙ uliftFunctor.{v} ≅ uliftYoneda.{v}.obj U :=
    (Functor.isoWhiskerRight (asIso (yonedaToPoints F U)) uliftFunctor.{v}).symm
  have hcan : uliftQuotientChart.{u, v} B S hS s t =
      eU.inv ≫ (Functor.whiskerRight (toQuotientPresheaf F j) uliftFunctor.{v} ≫
        toSheafify J (quotientPresheaf F j ⋙ uliftFunctor.{v})) := by
    rw [uliftQuotientChart, Functor.whiskerRight_comp]
    exact Category.assoc _ _ _
  have hnat : ∀ (m : R ⟶ U) (φ : Stacks.Groupoids.points F (F.obj R) ⟶
      Stacks.Groupoids.points F (F.obj U)), (∀ T x, φ.app T x = x ≫ F.map m) →
      eR.inv ≫ Functor.whiskerRight φ uliftFunctor.{v} = uliftYoneda.{v}.map m ≫ eU.inv := by
    intro m φ h
    ext T x
    obtain ⟨x⟩ := x
    change ULift.up (φ.app T (F.map x)) = ULift.up (F.map (x ≫ m))
    rw [h, Functor.map_comp]
  have ht := hnat t (targetMap F j) fun _ _ => by rw [← htarget]; rfl
  have hs := hnat s (sourceMap F j) fun _ _ => by rw [← hsource]; rfl
  refine hpts.of_iso' eR.symm eU.symm eU.symm (Iso.refl _) ht hs ?_ ?_ <;>
    rw [Iso.refl_hom, Category.comp_id] <;> exact hcan.symm

/-- A property of the unlifted chart of the quotient sheaf transfers to the lifted chart. -/
private theorem relative_uliftQuotientChart_of_quotientMap
    {P : MorphismProperty (BigFppfOver B S hS)}
    (h : (MorphismProperty.relative yoneda P) (quotientMap B S hS s t)) :
    (MorphismProperty.relative uliftYoneda.{v} P) (uliftQuotientChart.{u, v} B S hS s t) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  rw [quotientMap_eq_toSheafify_comp] at h
  exact relative_ulift_sheafify _ _ _ _ h

/-- **Stacks 02WW, surjectivity of the lifted chart**, conditional on effective descent along
the covering sieves of the big fppf site of `S` at the monomorphisms locally of finite type and
on nothing else. It does **not** carry `@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.uliftQuotientChart_surjective_unconditional`. -/
theorem uliftQuotientChart_surjective_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (uliftQuotientChart.{u, v} B S hS s t) := by
  exact relative_uliftQuotientChart_of_quotientMap B S hS s t
    (quotientMap_surjective_of_coveringSieveDescent B S hS s t hdesc)

/-- **Stacks 02WW, étaleness of the lifted chart**, conditional on effective descent along the
covering sieves of the big fppf site of `S` at the monomorphisms locally of finite type and on
nothing else. It does **not** carry `@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.uliftQuotientChart_etale_unconditional`. -/
theorem uliftQuotientChart_etale_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    (MorphismProperty.relative uliftYoneda.{v} (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (uliftQuotientChart.{u, v} B S hS s t) := by
  exact relative_uliftQuotientChart_of_quotientMap B S hS s t
    (quotientMap_etale_of_coveringSieveDescent B S hS s t hdesc)

/-- **Stacks 02WW, the presentation in the lifted universe.** An étale equivalence relation
presents the lifted quotient sheaf, conditional on effective descent along the covering sieves
of the big fppf site of `S` at the monomorphisms locally of finite type and on nothing else. It
does **not** carry `@[stacks 02WW]`: the discharged form is
`AlgebraicGeometry.Space.uliftQuotientPresentation_unconditional`. -/
noncomputable def uliftQuotientPresentation_of_coveringSieveDescent
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    EtalePresentation.{u, v} B S hS (uliftQuotientSheaf.{u, v} B S hS s t).obj where
  isSheaf := (uliftQuotientSheaf.{u, v} B S hS s t).property
  U := U
  R := R
  target := t
  source := s
  isEtaleEquivalenceRelation := inferInstance
  toSpace := uliftQuotientChart.{u, v} B S hS s t
  surjective := uliftQuotientChart_surjective_of_coveringSieveDescent B S hS s t hdesc
  etale := uliftQuotientChart_etale_of_coveringSieveDescent B S hS s t hdesc
  isPullback := uliftQuotientChart_isPullback B S hS s t

end AlgebraicGeometry.Space

end
