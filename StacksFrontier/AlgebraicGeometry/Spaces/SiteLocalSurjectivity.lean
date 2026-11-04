module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Locally surjective maps of presheaves on the big fppf site

Three local-surjectivity facts which the study of quotient sheaves on a big fppf site uses
repeatedly: that the sheafification unit is locally surjective with no relation between the
universe of the values and the universes of the site, that the projection of a scheme onto
the quotient sheaf of a pre-relation on it is locally surjective, and that a flat, surjective
morphism of objects of the big fppf site of `S` which is locally of finite presentation
induces a locally surjective map on functors of points.

## Main results

* `CategoryTheory.Presheaf.toSheafify_isLocallySurjective`: the sheafification unit of a
  presheaf of types is locally surjective.
* `Stacks.Groupoids.toQuotientSheaf_isLocallySurjective`: the canonical projection onto the
  quotient sheaf of a pre-relation is locally surjective.
* `AlgebraicGeometry.Space.points_locallySurjective`: an fppf covering morphism of objects
  of the big fppf site of `S` is locally surjective on functors of points.

## Implementation notes

Mathlib's `CategoryTheory.Presheaf.isLocallySurjective_toSheafify` asks the values of the
presheaf to lie in `Type (max u v)` for `C : Type u` with `Category.{v} C`; the big fppf site
of `S` lives in `Type (u + 1)` with morphisms in `Type u` and its sheaves of interest take
values in `Type u`, so that instance does not apply.  The statement here has three
independent universes and is proved instead from the universal property: the range subfunctor
of the sheafification unit sheafifies to a split epimorphism onto the sheafification, and a
monomorphism which is a split epimorphism is an isomorphism, which is local surjectivity.

Local surjectivity of the projection onto the quotient sheaf is local surjectivity of the
projection onto the quotient *presheaf*, which is objectwise surjective because a coequalizer
of types is, composed with the sheafification unit.

The last statement is Stacks 05VM applied to the representable morphism of sheaves induced by
a morphism of the site, together with full faithfulness of the inclusion of the site into
`S`-schemes, which makes the comparison between the two spellings of the functor of points an
isomorphism.

## References

* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Presheaf

/-- The sheafification unit of a presheaf of types is locally surjective, with no relation
assumed between the universe of its values and the universes of the site. -/
theorem toSheafify_isLocallySurjective {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (P : Cᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  set G := Subfunctor.sheafify J (Subfunctor.range (toSheafify J P))
  have hPsheaf : Presheaf.IsSheaf J (sheafify J P) :=
    ((presheafToSheaf J (Type u)).obj P).property
  have hGsheaf : Presheaf.IsSheaf J G.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range (toSheafify J P)).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp hPsheaf))
  have hfac : Subfunctor.toRangeSheafify J (toSheafify J P) ≫ G.ι = toSheafify J P := by
    ext X x
    rfl
  rw [Subfunctor.eq_top_iff_isIso]
  have hsplit : IsSplitEpi G.ι := by
    refine IsSplitEpi.mk ⟨⟨sheafifyLift J
      (Subfunctor.toRangeSheafify J (toSheafify J P)) hGsheaf, ?_⟩⟩
    refine sheafify_hom_ext J _ _ hPsheaf ?_
    rw [Category.comp_id, ← Category.assoc, toSheafify_sheafifyLift, hfac]
  exact isIso_of_mono_of_isSplitEpi G.ι

end CategoryTheory.Presheaf

namespace Stacks.Groupoids

/-- The canonical projection from the functor of points of `U` onto the quotient sheaf of a
pre-relation on `U` is locally surjective. -/
theorem toQuotientSheaf_isLocallySurjective {S : AlgebraicGeometry.Scheme.{u}} {C : Type v}
    [Category.{w} C] (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    {R U : Over S} (j : PreRelation R U) :
    Presheaf.IsLocallySurjective J (toQuotientSheaf J F j) :=
  isLocallySurjective_toQuotientSheaf J F j

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

/-- The comparison map between the functor of points of an object of a site of `S`-schemes
and the functor of points of its image is an isomorphism when the site is fully faithfully
embedded. -/
private theorem yonedaMap_isIso {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (Y : C) : IsIso (yonedaMap F Y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun _ ↦ (isIso_iff_bijective _).2 ⟨F.map_injective, F.map_surjective⟩

/-- **Stacks 05VM.** A morphism of objects of the big fppf site of `S` which is flat,
surjective and locally of finite presentation induces a locally surjective map on functors
of points. -/
theorem points_locallySurjective (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Flat f.left.hom ∧ LocallyOfFinitePresentation f.left.hom ∧
      Surjective f.left.hom) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post B.inclusion).map f))) := by
  let J := BigFppfOver.topology B S hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let P : MorphismProperty Scheme.{u} :=
    fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f
  let G := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan G := by
    dsimp [G, BigFppfOver.toScheme]
    infer_instance
  have : P.IsStableUnderBaseChange := ⟨fun sq hf => ⟨
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) sq hf.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @LocallyOfFinitePresentation) sq hf.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq hf.2.2⟩⟩
  have : (P.inverseImage G).IsStableUnderBaseChange := ⟨fun sq hf =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (sq.map G) hf⟩
  let Xs : Sheaf J (Type u) := ⟨yoneda.obj X, (isAlgebraicSpace_yoneda B S hS X).isSheaf⟩
  let Ys : Sheaf J (Type u) := ⟨yoneda.obj Y, (isAlgebraicSpace_yoneda B S hS Y).isSheaf⟩
  let fs : Xs ⟶ Ys := ⟨yoneda.map f⟩
  have : Presheaf.IsLocallySurjective J (yoneda.map f) :=
    isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
      B S hS fs (MorphismProperty.relative_map (F := yoneda) (P := P.inverseImage G)
        (f := f) hf)
  have : IsIso (yonedaMap F Y) := yonedaMap_isIso F Y
  have : Presheaf.IsLocallySurjective J (yoneda.map f ≫ yonedaMap F Y) := inferInstance
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := yonedaMap F X) (f₂ := F.op.whiskerLeft (yoneda.map (F.map f)))
    (f₃ := yoneda.map f ≫ yonedaMap F Y)
  ext T a
  exact (F.map_comp a f).symm

end AlgebraicGeometry.Space

end
