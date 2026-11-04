module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid

/-!
# Groupoids in algebraic spaces from groupoid objects of a slice

A groupoid object (`Deformation.GroupoidObject`) is stated with its laws on generalized elements.
This file supplies three conveniences for producing and comparing groupoids in algebraic spaces
(Stacks 043W) when the structure is known only through equations of morphisms.

* `Deformation.GroupoidObject.ofUniversalLaws`: a groupoid object from its laws read on the
  universal composable pairs and triples, each presented by any morphism with the right two
  projections.
* `AlgebraicGeometry.groupoidPresheafObject`: a groupoid in algebraic spaces read as a groupoid
  object of presheaves, so that its laws apply to generalized elements out of any presheaf.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.ofOverGroupoidObject`: the groupoid in algebraic
  spaces over `X` determined by a groupoid object of the slice over `X` whose object and arrow
  spaces are algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mkOfComp`: a morphism of groupoids in
  algebraic spaces from morphisms of presheaves compatible with source, target and composition
  as equations of morphisms.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.GroupoidObject

universe v u

variable {C : Type u} [Category.{v} C]

/-- **A groupoid object from its laws on the universal pairs and triples.** The four laws which
involve a composite are given on one morphism into the object of composable pairs each, with
prescribed projections, and associativity on two morphisms out of the object of composable
triples; the laws on generalized elements follow by factoring a generalized element through
these. -/
noncomputable def ofUniversalLaws (objects arrows pairs triples : C)
    (source target : arrows ⟶ objects) (identity : objects ⟶ arrows)
    (inverse : arrows ⟶ arrows) (fst snd : pairs ⟶ arrows)
    (isPullback_pairs : IsPullback fst snd source target) (comp : pairs ⟶ arrows)
    (fst₃ snd₃ : triples ⟶ pairs) (isPullback_triples : IsPullback fst₃ snd₃ snd fst)
    (identity_source : identity ≫ source = 𝟙 objects)
    (identity_target : identity ≫ target = 𝟙 objects)
    (inverse_source : inverse ≫ source = target) (inverse_target : inverse ≫ target = source)
    (comp_source : comp ≫ source = snd ≫ source) (comp_target : comp ≫ target = fst ≫ target)
    (unitLeft : arrows ⟶ pairs) (unitLeft_fst : unitLeft ≫ fst = target ≫ identity)
    (unitLeft_snd : unitLeft ≫ snd = 𝟙 arrows) (unitLeft_comp : unitLeft ≫ comp = 𝟙 arrows)
    (unitRight : arrows ⟶ pairs) (unitRight_fst : unitRight ≫ fst = 𝟙 arrows)
    (unitRight_snd : unitRight ≫ snd = source ≫ identity)
    (unitRight_comp : unitRight ≫ comp = 𝟙 arrows)
    (inverseLeft : arrows ⟶ pairs) (inverseLeft_fst : inverseLeft ≫ fst = inverse)
    (inverseLeft_snd : inverseLeft ≫ snd = 𝟙 arrows)
    (inverseLeft_comp : inverseLeft ≫ comp = source ≫ identity)
    (inverseRight : arrows ⟶ pairs) (inverseRight_fst : inverseRight ≫ fst = 𝟙 arrows)
    (inverseRight_snd : inverseRight ≫ snd = inverse)
    (inverseRight_comp : inverseRight ≫ comp = target ≫ identity)
    (assocLeft assocRight : triples ⟶ pairs)
    (assocLeft_fst : assocLeft ≫ fst = fst₃ ≫ comp) (assocLeft_snd : assocLeft ≫ snd = snd₃ ≫ snd)
    (assocRight_fst : assocRight ≫ fst = fst₃ ≫ fst)
    (assocRight_snd : assocRight ≫ snd = snd₃ ≫ comp)
    (assoc : assocLeft ≫ comp = assocRight ≫ comp) : GroupoidObject C where
  objects := objects
  arrows := arrows
  pairs := pairs
  triples := triples
  source := source
  target := target
  identity := identity
  inverse := inverse
  fst := fst
  snd := snd
  isPullback_pairs := isPullback_pairs
  comp := comp
  fst₃ := fst₃
  snd₃ := snd₃
  isPullback_triples := isPullback_triples
  identity_source := identity_source
  identity_target := identity_target
  inverse_source := inverse_source
  inverse_target := inverse_target
  comp_source := comp_source
  comp_target := comp_target
  comp_identity_left := by
    intro X a k h₁ h₂
    have hk : k = a ≫ unitLeft := isPullback_pairs.hom_ext
      (by rw [Category.assoc, unitLeft_fst, h₁])
      (by rw [Category.assoc, unitLeft_snd, Category.comp_id, h₂])
    rw [hk, Category.assoc, unitLeft_comp, Category.comp_id]
  comp_identity_right := by
    intro X a k h₁ h₂
    have hk : k = a ≫ unitRight := isPullback_pairs.hom_ext
      (by rw [Category.assoc, unitRight_fst, Category.comp_id, h₁])
      (by rw [Category.assoc, unitRight_snd, h₂])
    rw [hk, Category.assoc, unitRight_comp, Category.comp_id]
  comp_inverse_left := by
    intro X a k h₁ h₂
    have hk : k = a ≫ inverseLeft := isPullback_pairs.hom_ext
      (by rw [Category.assoc, inverseLeft_fst, h₁])
      (by rw [Category.assoc, inverseLeft_snd, Category.comp_id, h₂])
    rw [hk, Category.assoc, inverseLeft_comp]
  comp_inverse_right := by
    intro X a k h₁ h₂
    have hk : k = a ≫ inverseRight := isPullback_pairs.hom_ext
      (by rw [Category.assoc, inverseRight_fst, Category.comp_id, h₁])
      (by rw [Category.assoc, inverseRight_snd, h₂])
    rw [hk, Category.assoc, inverseRight_comp]
  comp_assoc := by
    intro X k l m n hkl hm₁ hm₂ hn₁ hn₂
    have hm : m = isPullback_triples.lift k l hkl ≫ assocLeft := isPullback_pairs.hom_ext
      (by rw [Category.assoc, assocLeft_fst, ← Category.assoc, IsPullback.lift_fst, hm₁])
      (by rw [Category.assoc, assocLeft_snd, ← Category.assoc, IsPullback.lift_snd, hm₂])
    have hn : n = isPullback_triples.lift k l hkl ≫ assocRight := isPullback_pairs.hom_ext
      (by rw [Category.assoc, assocRight_fst, ← Category.assoc, IsPullback.lift_fst, hn₁])
      (by rw [Category.assoc, assocRight_snd, ← Category.assoc, IsPullback.lift_snd, hn₂])
    rw [hm, hn, Category.assoc, Category.assoc, assoc]

end Deformation.GroupoidObject

namespace AlgebraicGeometry

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **A groupoid in algebraic spaces as a groupoid object of presheaves.** The groupoid object
`AlgebraicGeometry.groupoidObject` of the category of algebraic spaces, carried to presheaves by
the inclusion, which preserves its two fibre products. Its laws apply to generalized elements out
of arbitrary presheaves. -/
noncomputable def groupoidPresheafObject (G : GroupoidInAlgebraicSpaces C S hS B) :
    Deformation.GroupoidObject ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  (groupoidObject G).mapOfIsPullback (ObjectProperty.ι _)
    (AlgebraicSpaces.isPullback_hom C S hS (groupoidObject G).isPullback_pairs)
    (AlgebraicSpaces.isPullback_hom C S hS (groupoidObject G).isPullback_triples)

namespace GroupoidInAlgebraicSpaces

variable (X : AlgebraicSpaces C S hS) (Γ : Deformation.GroupoidObject (Over X.obj))

/-- The groupoid object of presheaves underlying a groupoid object of the slice over `X`. -/
noncomputable abbrev overGroupoidPresheafObject :
    Deformation.GroupoidObject ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Γ.map (Over.forget X.obj)

/-- The comparison from the chosen fibre product of the source and target maps of a groupoid
object of the slice to its object of composable pairs. -/
noncomputable def overPairsComparison :
    pullback Γ.source.left Γ.target.left ⟶ Γ.pairs.left :=
  (overGroupoidPresheafObject X Γ).isPullback_pairs.lift (pullback.fst _ _) (pullback.snd _ _)
    pullback.condition

/-- The comparison `overPairsComparison` followed by the first projection of composable pairs is
the first projection of the fibre product. -/
@[reassoc (attr := simp)]
theorem overPairsComparison_fst :
    overPairsComparison X Γ ≫ Γ.fst.left = pullback.fst Γ.source.left Γ.target.left :=
  (overGroupoidPresheafObject X Γ).isPullback_pairs.lift_fst _ _ _

/-- The comparison `overPairsComparison` followed by the second projection of composable pairs is
the second projection of the fibre product. -/
@[reassoc (attr := simp)]
theorem overPairsComparison_snd :
    overPairsComparison X Γ ≫ Γ.snd.left = pullback.snd Γ.source.left Γ.target.left :=
  (overGroupoidPresheafObject X Γ).isPullback_pairs.lift_snd _ _ _

/-- **The groupoid in algebraic spaces over `X` of a groupoid object of the slice over `X`.** Its
object and arrow spaces are those of the groupoid object, which are assumed to be algebraic
spaces; its composition is that of the groupoid object read through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overPairsComparison`; and its pointwise groupoid
condition is `Deformation.GroupoidObject.pointwiseGroupoid` of the underlying groupoid object of
presheaves. -/
noncomputable def ofOverGroupoidObject (hU : IsAlgebraicSpace C S hS Γ.objects.left)
    (hR : IsAlgebraicSpace C S hS Γ.arrows.left) : GroupoidInAlgebraicSpaces C S hS X where
  objects := ⟨Γ.objects.left, hU⟩
  arrows := ⟨Γ.arrows.left, hR⟩
  objectsToBase := ObjectProperty.homMk Γ.objects.hom
  arrowsToBase := ObjectProperty.homMk Γ.arrows.hom
  source := ObjectProperty.homMk Γ.source.left
  target := ObjectProperty.homMk Γ.target.left
  source_over := ObjectProperty.hom_ext _ (Over.w Γ.source)
  target_over := ObjectProperty.hom_ext _ (Over.w Γ.target)
  comp := ObjectProperty.homMk (overPairsComparison X Γ ≫ Γ.comp.left)
  comp_over := ObjectProperty.hom_ext _ (by
    change (overPairsComparison X Γ ≫ Γ.comp.left) ≫ Γ.arrows.hom =
      pullback.fst Γ.source.left Γ.target.left ≫ Γ.arrows.hom
    rw [Category.assoc, Over.w Γ.comp, ← Over.w Γ.fst, overPairsComparison_fst_assoc])
  pointwiseGroupoid := by
    intro T
    let Γp := overGroupoidPresheafObject X Γ
    have hfst : (composableToPullback Γ.source.left Γ.target.left ≫
        overPairsComparison X Γ) ≫ Γp.fst = composableFst Γ.source.left Γ.target.left :=
      (Category.assoc _ _ _).trans ((congrArg (fun k =>
        composableToPullback Γ.source.left Γ.target.left ≫ k)
          (overPairsComparison_fst X Γ)).trans (composableToPullback_comp_pullbackFst _ _))
    have hsnd : (composableToPullback Γ.source.left Γ.target.left ≫
        overPairsComparison X Γ) ≫ Γp.snd = composableSnd Γ.source.left Γ.target.left :=
      (Category.assoc _ _ _).trans ((congrArg (fun k =>
        composableToPullback Γ.source.left Γ.target.left ≫ k)
          (overPairsComparison_snd X Γ)).trans (composableToPullback_comp_pullbackSnd _ _))
    refine ⟨Γp.pointwiseGroupoid T.unop _ fun p => ?_⟩
    have hp := Deformation.GroupoidObject.sectionPairHom_eq_of_comparison Γp _ _ _ hfst hsnd
      T.unop p p rfl rfl
    refine Eq.symm (Eq.trans (congrArg (fun k => yonedaEquiv (k ≫ Γp.comp)) hp) ?_)
    exact (yonedaEquiv_comp _ _).trans
      (congrArg (fun z => Γp.comp.app (Opposite.op T.unop) z)
        (Equiv.apply_symm_apply yonedaEquiv _))

/-- **A morphism of groupoids in algebraic spaces from equations of morphisms.** Maps on object
and arrow spaces over the base, compatible with source and target, whose induced map on the
chosen fibre products of source and target carries the composition of the first groupoid to that
of the second. -/
noncomputable def Hom.mkOfComp {G H : GroupoidInAlgebraicSpaces C S hS B}
    (mapObjects : G.objects.obj ⟶ H.objects.obj) (mapArrows : G.arrows.obj ⟶ H.arrows.obj)
    (map_source : mapArrows ≫ H.source.hom = G.source.hom ≫ mapObjects)
    (map_target : mapArrows ≫ H.target.hom = G.target.hom ≫ mapObjects)
    (map_comp : pullback.map G.source.hom G.target.hom H.source.hom H.target.hom mapArrows
        mapArrows mapObjects map_source.symm map_target.symm ≫ H.comp.hom =
      G.comp.hom ≫ mapArrows)
    (mapObjects_over : mapObjects ≫ H.objectsToBase.hom = G.objectsToBase.hom)
    (mapArrows_over : mapArrows ≫ H.arrowsToBase.hom = G.arrowsToBase.hom) : Hom G H :=
  Hom.mk' mapObjects mapArrows (fun T a => congrArg (fun m => m.app T a) map_source)
    (fun T a => congrArg (fun m => m.app T a) map_target)
    (fun T a b h => by
      let pm := pullback.map G.source.hom G.target.hom H.source.hom H.target.hom mapArrows
        mapArrows mapObjects map_source.symm map_target.symm
      let κ := (composableToPullback G.source.hom G.target.hom).app T ⟨(a, b), h⟩
      have e₁ : pm ≫ pullback.fst H.source.hom H.target.hom =
          pullback.fst G.source.hom G.target.hom ≫ mapArrows := pullback.lift_fst _ _ _
      have e₂ : pm ≫ pullback.snd H.source.hom H.target.hom =
          pullback.snd G.source.hom G.target.hom ≫ mapArrows := pullback.lift_snd _ _ _
      have ha : (pullback.fst H.source.hom H.target.hom).app T (pm.app T κ) =
          mapArrows.app T a :=
        (natTrans_app_congr e₁ T κ).trans
          (congrArg (mapArrows.app T) (pullbackFst_app_composableToPullback _ _ T _))
      have hb : (pullback.snd H.source.hom H.target.hom).app T (pm.app T κ) =
          mapArrows.app T b :=
        (natTrans_app_congr e₂ T κ).trans
          (congrArg (mapArrows.app T) (pullbackSnd_app_composableToPullback _ _ T _))
      exact (comp_hom_app_eq H T (pm.app T κ) _ _ ha hb _).symm.trans
        (natTrans_app_congr map_comp T κ))
    mapObjects_over mapArrows_over

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
