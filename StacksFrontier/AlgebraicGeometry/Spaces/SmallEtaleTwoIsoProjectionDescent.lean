module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction

/-!
# Descending the equality of Stacks 04M6 from a projection-compatible chart morphism

Let `a, b : X ⟶ Y` be two *representable* morphisms of algebraic spaces over a scheme `S` and
let `V` be an étale scheme chart of `Y` which is surjective, that is, an étale scheme atlas.
Base change along `a` and along `b` turns `V` into two étale scheme charts `X ×_{Y,a} V` and
`X ×_{Y,b} V` of `X`, each carrying a cartesian projection to `V`.

This file shows that a morphism of charts `ε : X ×_{Y,b} V ⟶ X ×_{Y,a} V` *commuting with the
two projections to `V`* forces `a = b`. Nothing is assumed about `ε` beyond that: it need not be
an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.IsSurjectiveChart`: an étale scheme chart whose structure morphism is
  surjective.
* `AlgebraicGeometry.Space.IsProjectionCompatible`: the assertion that a 2-isomorphism of the
  morphisms of small étale ringed topoi of two representable morphisms is matched by a morphism
  of the two base-changed charts which commutes with the cartesian projections.

## Main results

* `AlgebraicGeometry.Space.eq_of_chartHom_projection`: a projection-compatible morphism of the
  two base-changed charts of a surjective étale chart forces `a = b`.
* `AlgebraicGeometry.Space.exists_isSurjectiveChart`: every algebraic space has a surjective
  étale scheme chart.
* `AlgebraicGeometry.Space.eq_of_twoIso_of_isProjectionCompatible`: two morphisms of algebraic
  spaces whose morphisms of small étale ringed topoi are 2-isomorphic are equal, granted
  `IsProjectionCompatible`.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Charts of the target that are atlases -/

/-- An étale scheme chart of an algebraic space whose structure morphism is in addition
surjective: an étale scheme atlas, read as an object of the small étale site. -/
def IsSurjectiveChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : SmallEtale B S hS F) : Prop :=
  (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf V.1.hom

/-- Every algebraic space has a surjective étale scheme chart: its atlas. -/
theorem exists_isSurjectiveChart (X : AlgebraicSpaces B S hS) :
    ∃ V : SmallEtale B S hS X.1, IsSurjectiveChart B S hS V := by
  obtain ⟨U, p, hsurj, hetale⟩ := X.property.exists_atlas
  exact ⟨⟨CostructuredArrow.mk p, hetale⟩, hsurj⟩

/-! ### Descending the equality -/

/-- Let `a, b : X ⟶ Y` be two representable morphisms of algebraic spaces and let `V` be a
surjective étale scheme chart of `Y`. A morphism of étale scheme charts of `X` from the base change
of `V` along `b` to the base change of `V` along `a` which commutes with the two cartesian
projections to `V` forces `a = b`. -/
theorem eq_of_chartHom_projection {X Y : AlgebraicSpaces B S hS} (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsSurjectiveChart B S hS V)
    (ε : (smallBaseChange B S hS b hb).obj V ⟶ (smallBaseChange B S hS a ha).obj V)
    (hε : ε.hom.left ≫ ha.snd V.1.hom = hb.snd V.1.hom) :
    a = b := by
  have hw : yoneda.map ε.hom.left ≫ ha.fst V.1.hom = hb.fst V.1.hom := CostructuredArrow.w ε.hom
  have hyε : yoneda.map ε.hom.left ≫ yoneda.map (ha.snd V.1.hom) =
      yoneda.map (hb.snd V.1.hom) :=
    (yoneda.map_comp _ _).symm.trans (congrArg (fun q ↦ yoneda.map q) hε)
  have key : hb.fst V.1.hom ≫ a.hom = hb.fst V.1.hom ≫ b.hom :=
    (congrArg (fun m ↦ m ≫ a.hom) hw.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ yoneda.map ε.hom.left ≫ m) (ha.w V.1.hom)).trans
          (((Category.assoc _ _ _).symm.trans
              (congrArg (fun m ↦ m ≫ V.1.hom) hyε)).trans
            (hb.w V.1.hom).symm)))
  have hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hb.fst V.1.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hb.isPullback V.1.hom).flip hV
  have hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hb.fst V.1.hom) :=
    isEtaleChart_representablePullback B S hS b hb V
  exact ObjectProperty.hom_ext _ (hom_ext_of_etale_atlas B S hS X.property.isSheaf
    Y.property.isSheaf (hb.fst V.1.hom) hsurj hetale key)

/-! ### The remaining content of Stacks 04M6 -/

/-- A 2-isomorphism `t` of the morphisms of small étale ringed topoi of two representable morphisms
`a, b : X ⟶ Y` of algebraic spaces is *projection compatible* when, over every étale scheme chart
`V` of `Y`, it is matched by a morphism of the two base-changed charts of `X` commuting with the
cartesian projections to `V`. -/
def IsProjectionCompatible : Prop :=
  ∀ (X Y : AlgebraicSpaces B S hS) (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom),
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
      (smallEtaleRingedToposHom B S hS b) →
    ∀ V : SmallEtale B S hS Y.1,
      ∃ ε : (smallBaseChange B S hS b hb).obj V ⟶ (smallBaseChange B S hS a ha).obj V,
        ε.hom.left ≫ ha.snd V.1.hom = hb.snd V.1.hom

/-- Two morphisms `a, b : X ⟶ Y` of algebraic spaces over `S` whose morphisms of small étale ringed
topoi are 2-isomorphic are equal, provided the 2-isomorphisms of representable morphisms are
projection compatible. -/
theorem eq_of_twoIso_of_isProjectionCompatible (hcompat : IsProjectionCompatible B S hS)
    {X Y : AlgebraicSpaces B S hS} (a b : X ⟶ Y)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
      (smallEtaleRingedToposHom B S hS b)) :
    a = b := by
  refine eq_of_twoIso_of_schemeSource B S hS (fun U Z a' b' t' ↦ ?_) a b t
  have ha' : yoneda.relativelyRepresentable a'.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS Z.property a'.hom
  have hb' : yoneda.relativelyRepresentable b'.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS Z.property b'.hom
  obtain ⟨V, hV⟩ := exists_isSurjectiveChart B S hS Z
  obtain ⟨ε, hε⟩ := hcompat (schemeSpace U) Z a' b' ha' hb' t' V
  exact eq_of_chartHom_projection B S hS a' b' ha' hb' V hV ε hε

end AlgebraicGeometry.Space

end
