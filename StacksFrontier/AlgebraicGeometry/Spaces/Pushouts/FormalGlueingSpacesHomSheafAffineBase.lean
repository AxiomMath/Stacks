module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesSliceAt
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated

/-!
# The sheaf of glueing-data morphisms over an affine base

In a formal glueing situation over an affine base `X ≅ Spec`, from clause (1) of Stacks 0AF4
over every affine base, the sheaf `W ↦ {(w, φ : Φ(W, w) ⟶ G)}` of glueing-data morphisms into a
triple `G` with affine legs is affine over `X`: it is the space over `X` that clause (1)
produces for `G`.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.AffineBaseEssSurj`: essential surjectivity in
  clause (1) of Stacks 0AF4 for every situation whose ambient space is an affine scheme.
* `AlgebraicGeometry.Space.FormalGlueingSituation.homPresheafMap`: functoriality of the sheaf in
  the triple.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isAffineHom_homPresheafProjection_of_affine`:
  over an affine base, the sheaf is affine over `X`.

## Implementation notes

`AffineBaseEssSurj` is the affine case of clause (1) of Stacks 0AF4, which the source reduces to
Stacks 0AF0. It is proved as `AlgebraicGeometry.Space.FormalGlueingSituation.affineBaseEssSurj`;
the results of this file take it as a hypothesis.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- Essential surjectivity in clause (1) of Stacks 0AF4 for every formal glueing situation whose
ambient space is an affine scheme. -/
def AffineBaseEssSurj : Prop :=
  ∀ D : FormalGlueingSituation B S hS, (∃ Z : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧ Nonempty (D.X ≅ yoneda.obj Z)) →
      (affineGlueingFunctor D).EssSurj

variable (D : FormalGlueingSituation B S hS)

/-- Postcomposition of a pair with a morphism of triples. -/
noncomputable def glueSections.postcomp {G G' : glueingData D} (ε : G ⟶ G')
    {W : BigFppfOver B S hS} (s : glueSections D G W) : glueSections D G' W :=
  ⟨s.1, s.2 ≫ ε.hom⟩

/-- Postcomposition with a morphism of triples commutes with restriction along `W' ⟶ W`. -/
theorem glueSections.restrict_postcomp {G G' : glueingData D} (ε : G ⟶ G')
    {W W' : BigFppfOver B S hS} (g : W' ⟶ W) (s : glueSections D G W) :
    (s.postcomp D ε).restrict g = (s.restrict g).postcomp D ε := by
  simp only [glueSections.postcomp, glueSections.restrict, Category.assoc]

/-- Postcomposition with a morphism of triples, on the pairs `(w, φ)`. -/
noncomputable def homPresheafMap {G G' : glueingData D} (ε : G ⟶ G') :
    homPresheaf D G ⟶ homPresheaf D G' where
  app W := ↾fun s => equivShrink (glueSections D G' W.unop)
    (((equivShrink _).symm s).postcomp D ε)
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change equivShrink _ (((equivShrink (glueSections D G W'.unop)).symm (equivShrink _
        (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop))).postcomp D ε) =
      equivShrink _ (((equivShrink _).symm (equivShrink (glueSections D G' W.unop)
        (((equivShrink (glueSections D G W.unop)).symm s).postcomp D ε))).restrict g.unop)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, glueSections.restrict_postcomp]

/-- Under the identification `equivShrink`, `homPresheafMap` is postcomposition of pairs. -/
private theorem symm_homPresheafMap_app {G G' : glueingData D} (ε : G ⟶ G')
    {W : (BigFppfOver B S hS)ᵒᵖ} (s : (homPresheaf D G).obj W) :
    (equivShrink _).symm ((homPresheafMap D ε).app W s) =
      ((equivShrink _).symm s).postcomp D ε :=
  Equiv.symm_apply_apply _ _

/-- `homPresheafMap` sends a composite of morphisms of triples to the composite. -/
theorem homPresheafMap_comp {G G' G'' : glueingData D} (ε : G ⟶ G') (ε' : G' ⟶ G'') :
    homPresheafMap D ε ≫ homPresheafMap D ε' = homPresheafMap D (ε ≫ ε') := by
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun s => ?_)
  apply (equivShrink _).symm.injective
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, symm_homPresheafMap_app,
    symm_homPresheafMap_app, symm_homPresheafMap_app]
  simp only [glueSections.postcomp, Category.assoc]
  rfl

/-- `homPresheafMap` sends the identity of a triple to the identity. -/
theorem homPresheafMap_id (G : glueingData D) : homPresheafMap D (𝟙 G) = 𝟙 _ := by
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun s => ?_)
  apply (equivShrink _).symm.injective
  simp [symm_homPresheafMap_app, glueSections.postcomp]

/-- Isomorphic triples have isomorphic sheaves of glueing-data morphisms. -/
noncomputable def homPresheafMapIso {G G' : glueingData D} (ε : G ≅ G') :
    homPresheaf D G ≅ homPresheaf D G' where
  hom := homPresheafMap D ε.hom
  inv := homPresheafMap D ε.inv
  hom_inv_id := by rw [homPresheafMap_comp, ε.hom_inv_id, homPresheafMap_id]
  inv_hom_id := by rw [homPresheafMap_comp, ε.inv_hom_id, homPresheafMap_id]

/-- `homPresheafMap` is compatible with the projections of the two sheaves to `X`. -/
theorem homPresheafMap_projection {G G' : glueingData D} (ε : G ⟶ G') :
    homPresheafMap D ε ≫ homPresheafProjection D G' = homPresheafProjection D G := by
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun s => ?_)
  change yonedaEquiv ((equivShrink _).symm ((homPresheafMap D ε).app W s)).1 = _
  rw [symm_homPresheafMap_app]
  rfl

/-- The comparison map `toHomPresheaf` from `T` commutes with the projections to `X`. -/
theorem toHomPresheaf_projection (T : spacesOverX D) :
    toHomPresheaf D T ≫ homPresheafProjection D _ = T.obj.hom := by
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun t => ?_)
  show yonedaEquiv ((equivShrink _).symm (equivShrink _
    (glueSectionsOfSpace D T (yonedaEquiv.symm t)))).1 = T.obj.hom.app W t
  rw [Equiv.symm_apply_apply]
  show yonedaEquiv (yonedaEquiv.symm t ≫ T.obj.hom) = _
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **The restriction functor of Stacks 0AF3 is full on morphisms from an affine scheme to a
space affine over `X`, from clause (1) of Stacks 0AF4 over affine bases.** The graph argument
of Stacks 0AF6 (`exists_map_eq_of_closedSliceRealizationAt`) needs the closed-immersion
construction only over the fibre product `V ×_X T`, which is an affine scheme because `T` is
affine over `X` and `V` is affine; there it is clause (1) for the base change of the situation,
whose ambient space is that affine scheme. -/
theorem exists_map_eq_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (T : spacesOverX D) (hT : affineOverX D T) (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (w : yoneda.obj V ⟶ D.X)
    (φ : (formalGlueingFunctor D).1.obj ⟨Over.mk w, isAlgebraicSpace_yoneda B S hS V⟩ ⟶
      (formalGlueingFunctor D).1.obj T) :
    ∃ a, (formalGlueingFunctor D).1.map a = φ := by
  refine exists_map_eq_of_closedSliceRealizationAt D
    (isSeparated_of_isAffineHom B S hS _ T.property D.algebraicSpace_X hT) ?_ φ
  intro Q p₁ p₂ hQ
  refine closedSliceRealizationAt_of_essSurj_affine D Q (hA _ ?_)
  obtain ⟨W, p, q, hpb⟩ := hT ⟨V, hV⟩ w
  refine ⟨(BigAffineFppf.inclusion B S hS).obj W, W.property, ⟨?_⟩⟩
  exact (Over.forget _).mapIso (hQ.conePointUniqueUpToIso (overProdIsLimit (Over.mk w) T.obj)) ≪≫
    pullbackSymmetry _ _ ≪≫ hpb.isoPullback.symm

/-- **A space affine over `X` is the sheaf of glueing-data morphisms into its triple**, granted
clause (1) of Stacks 0AF4 over affine bases. -/
theorem isIso_toHomPresheaf_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (T : spacesOverX D) (hT : affineOverX D T) : IsIso (toHomPresheaf D T) :=
  isIso_toHomPresheaf D T fun V hV w φ => exists_map_eq_of_affineBaseEssSurj D hA T hT V hV w φ

/-- **The sheaf of glueing-data morphisms into a triple realized by a space affine over `X` is
that space**, as a sheaf over `X`, from clause (1) of Stacks 0AF4 over affine bases. -/
theorem exists_iso_homPresheaf_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (T : spacesOverX D) (hT : affineOverX D T) (G : glueingData D)
    (ε : (formalGlueingFunctor D).1.obj T ≅ G) :
    ∃ e : T.obj.left ≅ homPresheaf D G, e.hom ≫ homPresheafProjection D G = T.obj.hom := by
  have := isIso_toHomPresheaf_of_affineBaseEssSurj D hA T hT
  refine ⟨asIso (toHomPresheaf D T) ≪≫ homPresheafMapIso D ε, ?_⟩
  show (toHomPresheaf D T ≫ homPresheafMap D ε.hom) ≫ _ = _
  rw [Category.assoc, homPresheafMap_projection, toHomPresheaf_projection]

/-- **Over an affine base the sheaf of glueing-data morphisms into a triple with affine legs is
affine over `X`**, from clause (1) of Stacks 0AF4 over affine bases: it is the space that
clause produces. -/
theorem isAffineHom_homPresheafProjection_of_affine (hA : AffineBaseEssSurj B S hS)
    (hX : ∃ Z : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧ Nonempty (D.X ≅ yoneda.obj Z))
    (G : glueingData D) (hG : affineLegs D G) :
    IsAffineHom B S hS (homPresheafProjection D G) := by
  obtain ⟨⟨T, hT⟩, ⟨ε⟩⟩ := (hA D hX).mem_essImage ⟨G, hG⟩
  obtain ⟨e, he⟩ := exists_iso_homPresheaf_of_affineBaseEssSurj D hA T hT G
    ((affineLegs D).ι.mapIso ε)
  have hπ : homPresheafProjection D G = e.inv ≫ T.obj.hom := by rw [← he, e.inv_hom_id_assoc]
  rw [hπ]
  exact ((isAffinePresheaf B S hS).cancel_left_of_respectsIso e.inv _).2 hT

end AlgebraicGeometry.Space.FormalGlueingSituation

end
