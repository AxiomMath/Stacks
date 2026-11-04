module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedOfProperChartRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance

/-!
# Separatedness of a model of a quotient stack from its relation

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `Y` and let
`𝒳` be an algebraic stack identified over `Y` with the quotient stack `[U/R]`
(`AlgebraicGeometry.Stack.QuotientStackModel`), with its atlas `x : U ⟶ [U/R] ≃ 𝒳`. Stacks 04M9
identifies `U ×_𝒳 U` with the arrow space `R`, the two projections becoming `s` and `t`. This file
transports that identification to the model and reads off it the step of the proofs of
Stacks 0CQ2 and Stacks 0CPZ which says that `𝒳 ⟶ Y` is separated exactly when
`(s, t) : R ⟶ U ×_Y U` is proper (Properties of Stacks, Lemma 04XD).

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.relationMap`: the morphism
  `(s, t) : R ⟶ U ×_Y U`.
* `AlgebraicGeometry.Stack.QuotientStackModel.relationSquare`: the square `R ⇉ U ⟶ 𝒳` of the
  model atlas, filled by the 2-isomorphism of Stacks 044S.
* `AlgebraicGeometry.Stack.QuotientStackModel.ofEquivalenceOver`: an algebraic stack identified
  over `Y` with `[U/R]` as a model of it.

## Main results

* `AlgebraicGeometry.Stack.QuotientStackModel.isEquivalence_relationLift`: Stacks 04M9 on the
  model — the comparison from `R` to the canonical 2-fibre product `U ×_𝒳 U` is an equivalence.
* `AlgebraicGeometry.Stack.QuotientStackModel.isProper_mapBase_projection_iff`: the comparison
  `U ×_𝒳 U ⟶ U ×_Y U` of Stacks 050H is proper exactly when `(s, t)` is.
* `AlgebraicGeometry.Stack.QuotientStackModel.isSeparated_structureMorphism_iff`: for a smooth
  groupoid with algebraic quotient, `𝒳 ⟶ Y` is separated exactly when `(s, t)` is proper.
* `AlgebraicGeometry.Stack.QuotientStackModel.isProper_relationMap_of_isSeparated`: the forward
  implication, with no hypothesis on the groupoid.

## Implementation notes

The quotient stack lives one universe up from the model, so Stacks 04M9
(`AlgebraicGeometry.Stack.isEquivalence_arrowToRelativeProduct`, the comparison functor from the
universe-lifted `𝒮_R` to `𝒮_U ×_{[U/R]} 𝒮_U`) is moved to the model by an explicit comparison of
the two 2-fibre products (`atlasComparison`): a change of target along the inverse of the
identification `𝒳 ≃ [U/R]`, a reindexing of each leg along its unit, and the universe lift of
each factor. The resulting square, the comparison functor and the lift of the relation square
commute up to a natural isomorphism with identity components (`relationLiftComparisonIso`),
whose naturality is checked componentwise against one common morphism so that no two objects
which are equal only after unfolding are ever unified.

The representing presheaf of `U ×_Y U` is obtained abstractly and identified with the fibre
product by Stacks 04SD
(`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`); the relation map
read on `R` then has the two components `s` and `t`.

## References

* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Y)

/-- The morphism `(s, t) : R ⟶ U ×_Y U` of a groupoid in algebraic spaces over `Y`. -/
noncomputable abbrev relationMap :
    G.arrows.obj ⟶ pullback G.objectsToBase.hom G.objectsToBase.hom :=
  pullback.lift G.source.hom G.target.hom
    ((congrArg (fun k => k.hom) G.source_over).trans
      (congrArg (fun k => k.hom) G.target_over).symm)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Y)

/-- The 2-isomorphism `π ∘ s ≅ π ∘ t` of Stacks 044S: the canonical 2-morphism
`AlgebraicGeometry.Stack.quotientStackTwoArrow` is invertible, `[U/R]` being fibred in groupoids
and its components lying over identities. -/
noncomputable def quotientStackTwoArrowBasedIso :
    BasedFunctor.comp (associatedMap B S hS G.source.hom).1.hom (quotientStackProjection G) ≅
      BasedFunctor.comp (associatedMap B S hS G.target.hom).1.hom (quotientStackProjection G) :=
  have hiso (x : (fibredCategory B S hS G.arrows.obj).val.obj) :
      IsIso ((quotientStackTwoArrow G).app x) := by
    have hcart := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift
      (𝟙 ((fibredCategory B S hS G.arrows.obj).val.p.obj x)) ((quotientStackTwoArrow G).app x)
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := (quotientStack G).p)
      (f := 𝟙 ((fibredCategory B S hS G.arrows.obj).val.p.obj x))
      ((quotientStackTwoArrow G).app x)
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun x => asIso ((quotientStackTwoArrow G).app x))
      (fun f => (quotientStackTwoArrow G).naturality f))
    (fun x => (quotientStackTwoArrow G).isHomLift' x)

/-- A square `X ≫ i = j ≫ Y` whose four sides are, up to heterogeneous equality, one morphism
`Z` and two identities. Stated with the six objects independent, so that applying it never
compares two objects which are equal only after unfolding. -/
private theorem comp_eq_comp_of_heq {C : Type*} [Category C] {a b c d m n : C} (X : a ⟶ b)
    (i : b ⟶ d) (j : a ⟶ c) (Y : c ⟶ d) (Z : m ⟶ n) (ha : a = m) (hb : b = n) (hc : c = m)
    (hd : d = n) (hX : HEq X Z) (hY : HEq Y Z) (hi : HEq i (𝟙 n)) (hj : HEq j (𝟙 m)) :
    X ≫ i = j ≫ Y := by
  subst ha hb hc hd
  cases hX; cases hY; cases hi; cases hj
  simp

namespace QuotientStackModel

variable {G} (M : QuotientStackModel.{u, w} Y G)

/-- **The relation square of the model atlas** (Stacks 04M9 read on the model): the arrow space
with its source and target maps, over the model atlas `U ⟶ [U/R] ≃ 𝒳` twice, filled by the
2-isomorphism of Stacks 044S. -/
noncomputable def relationSquare :
    Bicategory.TwoCommSq M.projection.hom M.projection.hom where
  pt := fibredCategory B S hS G.arrows.obj
  fst := (associatedMap B S hS G.source.hom).1
  snd := (associatedMap B S hS G.target.hom).1
  iso := Bicategory.InducedBicategory.isoMk
    (BasedCategory.isoWhiskerRight (quotientStackTwoArrowBasedIso G) M.equivOver.equiv.functor)

/-- The reindexing 2-isomorphism `U ⟶ [U/R] ≃ 𝒳 ≃ [U/R]` ≅ `U ⟶ [U/R]` used to compare the
2-fibre product of the model atlas with itself with that of the projection of Stacks 044R. -/
noncomputable abbrev atlasUnitIso :
    (quotientStackProjection G).toFunctor ⋙ M.equivOver.equiv.functor.toFunctor ⋙
        M.equivOver.equiv.inverse.toFunctor ≅
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj) ⋙
        (liftedQuotientStackProjection G).toFunctor :=
  Functor.isoWhiskerLeft (quotientStackProjection G).toFunctor
    (BasedFunctor.toFunctorIso M.equivOver.equiv.functor M.equivOver.equiv.inverse
      M.equivOver.equiv.unitIso)

/-- Each component of `atlasUnitIso` lies over an identity of the base. -/
theorem atlasUnitIso_isHomLift (x : (fibredCategory B S hS G.objects.obj).val.obj) :
    (quotientStack G).p.IsHomLift (𝟙 ((fibredCategory B S hS G.objects.obj).val.p.obj x))
      ((atlasUnitIso M).hom.app x) := by
  have h := M.equivOver.equiv.unitIso.hom.isHomLift' ((quotientStackProjection G).obj x)
  rwa [BasedFunctor.w_obj] at h

/-- **The comparison of the 2-fibre product of the model atlas with itself with the 2-fibre
product `𝒮_U ×_{[U/R]} 𝒮_U` of Stacks 04M9**: change of target along the inverse of the
identification with `[U/R]`, then on each factor a reindexing along `atlasUnitIso` and the
universe lift of the object space. -/
noncomputable def atlasComparison :
    TwoFibreProductOver (fibredCategory B S hS G.objects.obj).val.p
        (fibredCategory B S hS G.objects.obj).val.p M.stack.val.val.p
        M.projection.hom.hom.toFunctor M.projection.hom.hom.toFunctor ⥤
      TwoFibreProductOver (liftedFibredCategory G.objects).p (liftedFibredCategory G.objects).p
        (quotientStack G).p (liftedQuotientStackProjection G).toFunctor
        (liftedQuotientStackProjection G).toFunctor :=
  TwoFibreProductOver.mapBase (pT := (fibredCategory B S hS G.objects.obj).val.p)
      (p𝒜 := (fibredCategory B S hS G.objects.obj).val.p) _ _
      M.equivOver.equiv.inverse.toFunctor M.equivOver.equiv.inverse.w ⋙
  TwoFibreProductOver.reindex (p𝒴 := (fibredCategory B S hS G.objects.obj).val.p)
    (atlasUnitIso M) (atlasUnitIso_isHomLift M) ⋙
  TwoFibreProductOver.precomposeFst (fibredCategory B S hS G.objects.obj).val.p
    (liftedFibredCategory G.objects).p (fibredCategory B S hS G.objects.obj).val.p
    (quotientStack G).p (liftedQuotientStackProjection G).toFunctor
    ((quotientStackProjection G).toFunctor ⋙ M.equivOver.equiv.functor.toFunctor ⋙
        M.equivOver.equiv.inverse.toFunctor)
    (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj) rfl ⋙
  TwoFibreProductOver.swap _ _ _ _ _ ⋙
  TwoFibreProductOver.reindex (p𝒴 := (liftedFibredCategory G.objects).p)
    (atlasUnitIso M) (atlasUnitIso_isHomLift M) ⋙
  TwoFibreProductOver.precomposeFst (fibredCategory B S hS G.objects.obj).val.p
    (liftedFibredCategory G.objects).p (liftedFibredCategory G.objects).p
    (quotientStack G).p (liftedQuotientStackProjection G).toFunctor
    (liftedQuotientStackProjection G).toFunctor
    (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj) rfl ⋙
  TwoFibreProductOver.swap _ _ _ _ _

/-- The comparison is an equivalence: a change of target along a fully faithful functor, two
reindexings along 2-isomorphisms, two changes of a factor along an equivalence, and two exchanges
of factors. -/
theorem isEquivalence_atlasComparison : (atlasComparison M).IsEquivalence := by
  have hU := (fibredCategory B S hS G.objects.obj).isFiberedInGroupoids
  have hQ := isFiberedInGroupoids_quotientStack G
  have hL := isFiberedInGroupoids_liftedFibredCategory G.objects
  have : M.equivOver.equiv.inverse.toFunctor.IsEquivalence :=
    M.equivOver.equiv.symm.equiv.isEquivalence_functor
  have h1 := TwoFibreProductOver.isEquivalence_mapBase
    (pT := (fibredCategory B S hS G.objects.obj).val.p)
    (p𝒜 := (fibredCategory B S hS G.objects.obj).val.p)
    (G := M.projection.hom.hom.toFunctor) (F := M.projection.hom.hom.toFunctor)
    M.equivOver.equiv.inverse.w
  have h2 := TwoFibreProductOver.isEquivalence_reindex
    (p𝒴 := (fibredCategory B S hS G.objects.obj).val.p)
    (G := M.projection.hom.hom.toFunctor ⋙ M.equivOver.equiv.inverse.toFunctor)
    (atlasUnitIso M) (atlasUnitIso_isHomLift M)
  have h3 := TwoFibreProductOver.isEquivalence_precomposeFst
    (fibredCategory B S hS G.objects.obj).val.p
    (liftedFibredCategory G.objects).p (fibredCategory B S hS G.objects.obj).val.p
    (quotientStack G).p (liftedQuotientStackProjection G).toFunctor
    ((quotientStackProjection G).toFunctor ⋙ M.equivOver.equiv.functor.toFunctor ⋙
        M.equivOver.equiv.inverse.toFunctor)
    (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj) rfl hU hU hL
    (ULiftHom.equiv (C := (fibredCategory B S hS G.objects.obj).val.obj)).isEquivalence_functor
    (liftedQuotientStackProjection G).w
  have h5 := TwoFibreProductOver.isEquivalence_reindex
    (p𝒴 := (liftedFibredCategory G.objects).p)
    (G := (liftedQuotientStackProjection G).toFunctor)
    (atlasUnitIso M) (atlasUnitIso_isHomLift M)
  have h6 := TwoFibreProductOver.isEquivalence_precomposeFst
    (fibredCategory B S hS G.objects.obj).val.p
    (liftedFibredCategory G.objects).p (liftedFibredCategory G.objects).p
    (quotientStack G).p (liftedQuotientStackProjection G).toFunctor
    (liftedQuotientStackProjection G).toFunctor
    (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj) rfl hL hU hL
    (ULiftHom.equiv (C := (fibredCategory B S hS G.objects.obj).val.obj)).isEquivalence_functor
    (liftedQuotientStackProjection G).w
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h1 <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h2 <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h3 <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ inferInstance <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h5 <|
    @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h6 inferInstance

/-- The comparison 1-morphism from the arrow space to the 2-fibre product of the model atlas with
itself. -/
noncomputable def relationLift :
    (fibredCategory B S hS G.arrows.obj) ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} M.projection.hom
        M.projection.hom).pt :=
  CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _ M.relationSquare

/-- The 2-isomorphism of the image of `relationLift` at `r` under `atlasComparison`: the 2-arrow
of `[U/R]` at `r`, conjugated by the components of `atlasUnitIso`. -/
theorem relationLiftComparison_obj_iso (r : (fibredCategory B S hS G.arrows.obj).val.obj) :
    ((atlasComparison M).obj (M.relationLift.hom.obj r)).iso.hom =
      ((atlasUnitIso M).inv.app ((associatedMap B S hS G.source.hom).1.hom.obj r) ≫
        M.equivOver.equiv.inverse.map (M.equivOver.equiv.functor.map
          ((quotientStackTwoArrow G).app r))) ≫
        (atlasUnitIso M).hom.app ((associatedMap B S hS G.target.hom).1.hom.obj r) :=
  rfl

/-- The second component of the image of a morphism `f` of the arrow space under `relationLift`
followed by `atlasComparison` is the universe lift of its image under the target map. -/
theorem relationLiftComparison_map_b {r r' : (fibredCategory B S hS G.arrows.obj).val.obj}
    (f : r ⟶ r') :
    ((atlasComparison M).map (M.relationLift.hom.toFunctor.map f)).b =
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
        ((associatedMap B S hS G.target.hom).1.hom.toFunctor.map f) :=
  rfl

/-- The first component of the image of a morphism `f` of the arrow space under `relationLift`
followed by `atlasComparison` is the universe lift of its image under the source map. -/
theorem relationLiftComparison_map_a {r r' : (fibredCategory B S hS G.arrows.obj).val.obj}
    (f : r ⟶ r') :
    ((atlasComparison M).map (M.relationLift.hom.toFunctor.map f)).a =
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
        ((associatedMap B S hS G.source.hom).1.hom.toFunctor.map f) :=
  rfl

/-- The first component of the image of a lifted morphism `f` of the arrow space under
`arrowToRelativeProduct` is the universe lift of its image under the source map. -/
theorem arrowToRelativeProduct_map_a {r r' : (fibredCategory B S hS G.arrows.obj).val.obj}
    (f : r ⟶ r') :
    ((arrowToRelativeProduct G).map ((ULiftHom.up :
      (fibredCategory B S hS G.arrows.obj).val.obj ⥤ _).map f)).a =
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
        ((associatedMap B S hS G.source.hom).1.hom.toFunctor.map f) :=
  rfl

/-- The second component of the image of a lifted morphism `f` of the arrow space under
`arrowToRelativeProduct` is the universe lift of its image under the target map. -/
theorem arrowToRelativeProduct_map_b {r r' : (fibredCategory B S hS G.arrows.obj).val.obj}
    (f : r ⟶ r') :
    ((arrowToRelativeProduct G).map ((ULiftHom.up :
      (fibredCategory B S hS G.arrows.obj).val.obj ⥤ _).map f)).b =
      (ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
        ((associatedMap B S hS G.target.hom).1.hom.toFunctor.map f) :=
  rfl

/-- The component at `r` of `relationLiftComparisonIso`: the identity on both factors. -/
noncomputable def relationLiftComparisonIsoApp (r : (fibredCategory B S hS G.arrows.obj).val.obj) :
    (atlasComparison M).obj (M.relationLift.hom.toFunctor.obj r) ≅
      (arrowToRelativeProduct G).obj
        ((ULiftHom.up : (fibredCategory B S hS G.arrows.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.arrows.obj).val.obj).obj r) :=
  TwoFibreProductOver.isoMkVertical
    (U := ((atlasComparison M).obj (M.relationLift.hom.toFunctor.obj r)).base) (Iso.refl _)
    (Iso.refl _) (IsHomLift.id ((atlasComparison M).obj (M.relationLift.hom.toFunctor.obj r)).hx)
    (IsHomLift.id ((atlasComparison M).obj (M.relationLift.hom.toFunctor.obj r)).hy) (by
      let ε := BasedFunctor.toFunctorIso M.equivOver.equiv.functor M.equivOver.equiv.inverse
        M.equivOver.equiv.unitIso
      let τ := (quotientStackTwoArrow G).app r
      have hn : (M.equivOver.equiv.functor.toFunctor ⋙ M.equivOver.equiv.inverse.toFunctor).map τ ≫
          ε.hom.app _ = ε.hom.app _ ≫ τ := ε.hom.naturality τ
      have hP : ((atlasComparison M).obj (M.relationLift.hom.toFunctor.obj r)).iso.hom = τ := by
        refine (relationLiftComparison_obj_iso M r).trans ?_
        change (ε.inv.app _ ≫ (M.equivOver.equiv.functor.toFunctor ⋙
          M.equivOver.equiv.inverse.toFunctor).map τ) ≫ ε.hom.app _ = τ
        rw [Category.assoc, hn]
        exact ε.inv_hom_id_app_assoc _ τ
      rw [hP]
      refine (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
        ((Category.id_comp _).trans ?_)
      refine Eq.trans ?_ (congrArg (τ ≫ ·) (CategoryTheory.Functor.map_id _ _)).symm
      exact (Category.comp_id _).symm)

/-- **The relation lift followed by the comparison is the comparison functor of Stacks 04M9.** -/
noncomputable def relationLiftComparisonIso :
    M.relationLift.hom.toFunctor ⋙ atlasComparison M ≅
      (ULiftHom.up : (fibredCategory B S hS G.arrows.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.arrows.obj).val.obj) ⋙
        arrowToRelativeProduct G :=
  NatIso.ofComponents (relationLiftComparisonIsoApp M) (by
    intro r r' f
    apply TwoFibreProductOver.Hom.ext'
    · rw [TwoFibreProductOver.comp_a, TwoFibreProductOver.comp_a]
      exact comp_eq_comp_of_heq _ _ _ _
        ((ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
          ((associatedMap B S hS G.source.hom).1.hom.toFunctor.map f)) rfl rfl rfl rfl
        (heq_of_eq (relationLiftComparison_map_a M f))
        (heq_of_eq (arrowToRelativeProduct_map_a f)) HEq.rfl HEq.rfl
    · rw [TwoFibreProductOver.comp_b, TwoFibreProductOver.comp_b]
      exact comp_eq_comp_of_heq _ _ _ _
        ((ULiftHom.up : (fibredCategory B S hS G.objects.obj).val.obj ⥤
        ULiftHom.{u + 1} (fibredCategory B S hS G.objects.obj).val.obj).map
          ((associatedMap B S hS G.target.hom).1.hom.toFunctor.map f)) rfl rfl rfl rfl
        (heq_of_eq (relationLiftComparison_map_b M f))
        (heq_of_eq (arrowToRelativeProduct_map_b f)) HEq.rfl HEq.rfl)

/-- **Stacks 04M9 on the model.** The comparison 1-morphism from the arrow space to the 2-fibre
product of the model atlas with itself is an equivalence. -/
theorem isEquivalence_relationLift : M.relationLift.hom.toFunctor.IsEquivalence := by
  have hA := isEquivalence_arrowToRelativeProduct G
  have hup : (ULiftHom.up : (fibredCategory B S hS G.arrows.obj).val.obj ⥤
      ULiftHom.{u + 1} (fibredCategory B S hS G.arrows.obj).val.obj).IsEquivalence :=
    (ULiftHom.equiv (C := (fibredCategory B S hS G.arrows.obj).val.obj)).isEquivalence_functor
  have hc := @Functor.isEquivalence_of_iso _ _ _ _ _ _ (relationLiftComparisonIso M).symm
    (@Functor.isEquivalence_trans _ _ _ _ _ _ _ _ hup hA)
  exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ (atlasComparison M)
    (isEquivalence_atlasComparison M) hc

open AlgebraicStacks in
/-- The relation map of the model atlas through the arrow space: `R ≃ U ×_𝒳 U ⟶ U ×_Y U`. -/
noncomputable abbrev relationMapBase :
    fibredCategory B S hS G.arrows.obj ⟶
      (AlgebraicStacks.twoFibreProduct B S hS (M.projection ≫ M.structureMorphism)
        (M.projection ≫ M.structureMorphism)).val :=
  M.relationLift ≫ (mapBase B S hS M.projection M.projection M.structureMorphism).hom

open AlgebraicStacks in
/-- The comparison `U ×_𝒳 U ⟶ U ×_Y U` is proper if and only if the relation map
`relationMapBase` read on the arrow space is proper. -/
theorem isProper_mapBase_iff_isProper_relationMapBase :
    Stack.IsProper.{u, u, u + 1} B S hS
        (mapBase B S hS M.projection M.projection M.structureMorphism).hom ↔
      Stack.IsProper.{u, u, u + 1} B S hS M.relationMapBase := by
  have hL := isEquivalence_relationLift M
  have hid : Functor.IsEquivalence (BasedFunctor.id (AlgebraicStacks.twoFibreProduct B S hS
      (M.projection ≫ M.structureMorphism)
      (M.projection ≫ M.structureMorphism)).val.val).toFunctor :=
    Functor.isEquivalence_refl
  let α : BasedFunctor.comp M.relationLift.hom
        (mapBase B S hS M.projection M.projection M.structureMorphism).hom.hom ≅
      BasedFunctor.comp M.relationMapBase.hom (BasedFunctor.id _) :=
    BasedNatIso.mkNatIso (Functor.rightUnitor (M.relationLift.hom.toFunctor ⋙
        (mapBase B S hS M.projection M.projection M.structureMorphism).hom.hom.toFunctor)).symm
      (fun a => (inferInstance : Functor.IsHomLift _ (𝟙 _) (𝟙 ((BasedFunctor.comp M.relationLift.hom
        (mapBase B S hS M.projection M.projection M.structureMorphism).hom.hom).obj a))))
  exact ⟨fun h => @relativeProperty_of_equivalences B S hS _ _ _ _
      (fun _ _ k => Space.IsProper B S hS k.hom) M.relationMapBase.hom
      (mapBase B S hS M.projection M.projection M.structureMorphism).hom.hom
      M.relationLift.hom (BasedFunctor.id _) α hL hid h,
    fun h => @relativeProperty_of_equivalences_symm B S hS _ _ _ _
      (fun _ _ k => Space.IsProper B S hS k.hom) M.relationMapBase.hom
      (mapBase B S hS M.projection M.projection M.structureMorphism).hom.hom
      M.relationLift.hom (BasedFunctor.id _) α hL hid h⟩

open AlgebraicStacks in
/-- **The relation map of the model atlas is represented by `(s, t)`.** Through the identification
of Stacks 04M9 of `U ×_𝒳 U` with the arrow space, the comparison `U ×_𝒳 U ⟶ U ×_Y U` of
Stacks 050H is proper exactly when `(s, t) : R ⟶ U ×_Y U` is. -/
theorem isProper_relationMapBase_iff :
    Stack.IsProper.{u, u, u + 1} B S hS M.relationMapBase ↔
      Space.IsProper B S hS (relationMap G) := by
  have hprBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hprLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  -- `U ×_Y U` is represented by an algebraic space `V`
  have hU := isRepresentableByAlgebraicSpace_fibredCategory B S hS _ G.objects.property
  have hxf : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (M.projection ≫ M.structureMorphism).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).property hU
      (M.projection ≫ M.structureMorphism).hom
  let K₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (M.projection ≫ M.structureMorphism).hom (M.projection ≫ M.structureMorphism).hom
  have hK₁ : Bicategory.IsTwoFibreProduct K₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_of_representable B S hS K₁.pt _
    K₁.fst (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ _ _ K₁ hK₁
      hxf) hU
  have : (twoFibreProductStructureFunctor B S hS
      (fibredCategory B S hS G.objects.obj) (fibredCategory B S hS G.objects.obj)
      (fibredCategory B S hS Y.obj) (M.projection ≫ M.structureMorphism).hom
      (M.projection ≫ M.structureMorphism).hom).IsFibered :=
    K₁.pt.property.isFibered
  have hpb := isPullback_representingMap_twoFibreProductSquare B S hS
    (fibredCategory B S hS G.objects.obj) (fibredCategory B S hS G.objects.obj)
    (fibredCategory B S hS Y.obj) G.objects.obj G.objects.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (M.projection ≫ M.structureMorphism).hom
    (M.projection ≫ M.structureMorphism).hom V eV
  -- the composite `U ⟶ 𝒳 ⟶ Y` is represented by the structure morphism of `U`
  have hrep : representingMap B S hS (fibredCategory B S hS G.objects.obj)
      (fibredCategory B S hS Y.obj) G.objects.obj Y.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (M.projection ≫ M.structureMorphism).hom = G.objectsToBase.hom :=
    (representingMap_congr_twoIso B S hS _ _ _ _
      (Bicategory.InducedBicategory.isoMk M.projectionCompIso)).trans
      (representingMap_associatedMap B S hS _ _ _)
  rw [hrep] at hpb
  -- the two legs of `U ×_𝒳 U ⟶ U ×_Y U`, read on the arrow space, are `s` and `t`
  have hRrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS _ G.arrows.property
  have ha : Stack.IsRepresentableByAlgebraicSpaces B S hS M.relationMapBase.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
      (AlgebraicStacks.twoFibreProduct B S hS (M.projection ≫ M.structureMorphism)
        (M.projection ≫ M.structureMorphism)).property hRrep M.relationMapBase
  have hleg (k : K₁.pt ⟶ fibredCategory B S hS G.objects.obj)
      (h : G.arrows ⟶ G.objects)
      (e : M.relationMapBase ≫ k ≅ (associatedMap B S hS h.hom).1) :
      representingMap B S hS (fibredCategory B S hS G.arrows.obj) K₁.pt G.arrows.obj V
          (StacksRepresentableCFG.EquivalenceOver.refl _) eV M.relationMapBase ≫
        representingMap B S hS K₁.pt (fibredCategory B S hS G.objects.obj) V G.objects.obj eV
          (StacksRepresentableCFG.EquivalenceOver.refl _) k = h.hom :=
    (representingMap_comp B S hS _ _ _ _ _ _ _ _).symm.trans
      ((representingMap_congr_twoIso B S hS _ _ _ _ e).trans
        (representingMap_associatedMap B S hS _ _ _))
  set φ := representingMap B S hS (fibredCategory B S hS G.arrows.obj) K₁.pt G.arrows.obj V
    (StacksRepresentableCFG.EquivalenceOver.refl _) eV M.relationMapBase with hφ
  have h₁ := hleg K₁.fst G.source (Iso.refl _)
  have h₂ := hleg K₁.snd G.target (Iso.refl _)
  have hφe : φ ≫ hpb.isoPullback.hom = relationMap G := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
      exact h₁
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
      exact h₂
  have hPB : IsAlgebraicSpace B S hS (pullback G.objectsToBase.hom G.objectsToBase.hom) :=
    isAlgebraicSpace_pullback B S hS _ _ G.objects.property G.objects.property Y.property
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (spaceProperty B S hS (fun _ _ h => Space.IsProper B S hS h)) M.relationMapBase ha
    G.arrows.obj V G.arrows.property hV (StacksRepresentableCFG.EquivalenceOver.refl _) eV).trans
    ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hφe]
    exact Space.isProper_comp B S hS G.arrows.property hV hPB _ _ h
      (Space.isProper_of_isIso B S hS _)
  · have hφ' : φ = relationMap G ≫ hpb.isoPullback.inv := by
      rw [← hφe, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    show Space.IsProper B S hS φ
    rw [hφ']
    exact Space.isProper_comp B S hS G.arrows.property hPB hV _ _ h
      (Space.isProper_of_isIso B S hS _)

open AlgebraicStacks in
/-- **The comparison `U ×_𝒳 U ⟶ U ×_Y U` of the model atlas is proper exactly when
`(s, t) : R ⟶ U ×_Y U` is.** -/
theorem isProper_mapBase_projection_iff :
    Stack.IsProper.{u, u, u + 1} B S hS
        (mapBase B S hS M.projection M.projection M.structureMorphism).hom ↔
      Space.IsProper B S hS (relationMap G) :=
  (isProper_mapBase_iff_isProper_relationMapBase M).trans (isProper_relationMapBase_iff M)

/-- **A model of the quotient stack of a groupoid is separated over the base exactly when the
relation `(s, t) : R ⟶ U ×_Y U` is proper.** For a smooth groupoid whose quotient stack is
algebraic, the model atlas `U ⟶ 𝒳` is a smooth surjective chart, so separatedness of `𝒳 ⟶ Y` is
properness of `U ×_𝒳 U ⟶ U ×_Y U` (Stacks 04XD), and that comparison is `(s, t)` by Stacks 04M9. -/
theorem isSeparated_structureMorphism_iff
    (halg : IsAlgebraicStack.{u, w} B S hS (quotientStack G))
    (hsm : GroupoidInAlgebraicSpaces.IsSmooth B S hS G) :
    AlgebraicStacks.IsSeparated B S hS M.structureMorphism ↔
      Space.IsProper B S hS (relationMap G) :=
  (AlgebraicStacks.isSeparated_iff_isProper_mapBase B S hS M.structureMorphism M.projection
    (M.representable_projection halg) (M.isSurjective_projection halg)
    (M.isFlat_projection halg hsm) (M.isLocallyOfFinitePresentation_projection halg hsm)).trans
    (isProper_mapBase_projection_iff M)

/-- **The relation of a separated model is proper.** If a model of the quotient stack of a
groupoid is separated over the base, then `(s, t) : R ⟶ U ×_Y U` is proper; no hypothesis on the
groupoid is needed. -/
theorem isProper_relationMap_of_isSeparated
    (h : AlgebraicStacks.IsSeparated B S hS M.structureMorphism) :
    Space.IsProper B S hS (relationMap G) :=
  (isProper_mapBase_projection_iff M).1
    (AlgebraicStacks.isProper_mapBase_of_isSeparated B S hS M.projection M.projection
      M.structureMorphism h)

/-- An algebraic stack identified over `Y` with the quotient stack of a groupoid is a model of
that quotient stack. -/
noncomputable def ofEquivalenceOver (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (e : BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase G)) :
    QuotientStackModel.{u, w} Y G where
  stack := 𝒳
  structureMorphism := f
  equivOver :=
    { equiv := e.equiv.symm
      compIso := BasedCategory.isoWhiskerLeft e.equiv.inverse e.compIso.symm ≪≫
        BasedCategory.isoWhiskerRight e.equiv.counitIso (quotientStackToBase G) }

end QuotientStackModel

end AlgebraicGeometry.Stack

end
