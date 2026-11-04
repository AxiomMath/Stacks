module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentTransport

/-!
# Pullback of descent data for a single morphism of algebraic spaces

A commutative square of algebraic spaces induces a pullback functor on descent data for one
morphism, and two maps completing the same square induce canonically isomorphic functors.

## Main definitions

* `AlgebraicGeometry.Space.Descent.HomDescentData` specialises descent data for a family to
  descent data for one morphism.
* `AlgebraicGeometry.Space.Descent.pullbackDescentDataFunctor` is the pullback functor,
  together with its canonical comparison on underlying algebraic spaces and the base-change
  equation for its gluing isomorphisms.

## Main results

* `AlgebraicGeometry.Space.Descent.pullbackDescentDataFunctor_canonicalIso` identifies the
  pullbacks along any two maps compatible with the square, with components induced by the
  gluing isomorphism.

## Implementation notes

The one-member family is indexed by `PUnit`. The functor carries a natural comparison with
ordinary pullback on the underlying spaces over the source. The equation between gluing
isomorphisms after mapping to the old base says that the new gluing isomorphism is the base
change of the old one; the comparison maps are pinned by their underlying projections. The
canonical isomorphism is likewise characterised by a gluing equation, using the two projections
of the map from the new base to the old pairwise fibre product.

## References

* [Stacks Project, Tag 0ADL](https://stacks.math.columbia.edu/tag/0ADL)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Descent data for one morphism of algebraic spaces, as descent data for the one-member
family indexed by `PUnit`. -/
public abbrev HomDescentData {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Y ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :=
  DescentData (fun _ : PUnit.{v + 1} ↦ a) hX (fun _ ↦ hY)

section PullbackFunctor

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X) (f : Y' ⟶ Y)
    (ha : f ≫ a = a' ≫ h)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')

/-- The move operation of a descent datum for one morphism, reindexed to the one-member family
of the pulled-back datum. -/
private abbrev sourceTransport (D : HomDescentData.{u, v} a hX hY) :
    FamilyTransport (fun _ : PUnit.{w + 1} ↦ (Over.map a).obj (D.obj PUnit.unit))
      (fun _ : PUnit.{w + 1} ↦ Over.mk a)
      (fun _ : PUnit.{w + 1} ↦ structureMap a (D.obj PUnit.unit)) :=
  D.transport.comap (fun _ ↦ PUnit.unit)

/-- The pullback square identifying the base-changed object, as a base-change square. -/
private abbrev pulledSquare (D : HomDescentData.{u, v} a hX hY) (_ : PUnit.{w + 1}) :=
  overBaseChangeSquare a a' h f ha (D.obj PUnit.unit)
    ((Over.pullback f).obj (D.obj PUnit.unit))
    (pullback.fst (D.obj PUnit.unit).hom f)
    (IsPullback.of_hasPullback (D.obj PUnit.unit).hom f).flip

/-- The move operation of the pulled-back datum. -/
private abbrev pulledTransport (D : HomDescentData.{u, v} a hX hY) :=
  FamilyTransport.baseChange (pulledSquare.{u, v, w} a a' h f ha hX hY D)
    (sourceTransport.{u, v, w} a hX hY D)

/-- The pulled-back descent datum. -/
private def pulledDatum (D : HomDescentData.{u, v} a hX hY) :
    HomDescentData.{u, w} a' hX' hY' where
  obj _ := (Over.pullback f).obj (D.obj PUnit.unit)
  obj_isAlgebraicSpace _ := isAlgebraicSpace_pullback B S hS (D.obj PUnit.unit).hom f
    (D.obj_isAlgebraicSpace PUnit.unit) hY' hY
  gluing i j := (pulledTransport.{u, v, w} a a' h f ha hX hY D).gluing i j
  cocycle i j k :=
    FamilyTransport.gluing_cocycle (pulledTransport.{u, v, w} a a' h f ha hX hY D) i j k

/-- The projection of the pulled-back object commutes with a morphism of descent data. -/
private lemma projection_naturality {V W : Over Y} (m : V ⟶ W) :
    (Over.map h).map ((Over.map a').map ((Over.pullback f).map m)) ≫
        overStructureProjection a a' h f ha W ((Over.pullback f).obj W)
          (pullback.fst W.hom f) (IsPullback.of_hasPullback W.hom f).flip =
      overStructureProjection a a' h f ha V ((Over.pullback f).obj V)
          (pullback.fst V.hom f) (IsPullback.of_hasPullback V.hom f).flip ≫
        (Over.map a).map m := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.map_map_left, overStructureProjection_left,
    Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- Base change of a morphism of descent data. -/
private def pulledMap {D E : HomDescentData.{u, v} a hX hY} (φ : D ⟶ E) :
    pulledDatum.{u, v, w} a a' h f ha hX hX' hY hY' D ⟶
      pulledDatum.{u, v, w} a a' h f ha hX hX' hY hY' E where
  hom _ := (Over.pullback f).map (φ.hom PUnit.unit)
  comm i j := by
    refine FamilyTransport.gluing_comm _ _
      (fun _ ↦ (Over.map a').map ((Over.pullback f).map (φ.hom PUnit.unit)))
      (fun _ ↦ structureMap_naturality a' ((Over.pullback f).map (φ.hom PUnit.unit)))
      (fun v y ↦ ?_) i j
    exact BaseChangeSquare.map_move (pulledSquare.{u, v, w} a a' h f ha hX hY E PUnit.unit)
      (r := fun _ ↦ overStructureBase a a' h f ha)
      (q := fun _ ↦ overStructureProjection a a' h f ha (D.obj PUnit.unit)
        ((Over.pullback f).obj (D.obj PUnit.unit)) (pullback.fst (D.obj PUnit.unit).hom f)
        (IsPullback.of_hasPullback (D.obj PUnit.unit).hom f).flip)
      (qE := fun _ ↦ overStructureProjection a a' h f ha (E.obj PUnit.unit)
        ((Over.pullback f).obj (E.obj PUnit.unit)) (pullback.fst (E.obj PUnit.unit).hom f)
        (IsPullback.of_hasPullback (E.obj PUnit.unit).hom f).flip)
      (sourceTransport.{u, v, w} a hX hY D) (sourceTransport.{u, v, w} a hX hY E)
      (pulledTransport.{u, v, w} a a' h f ha hX hY D)
      (pulledTransport.{u, v, w} a a' h f ha hX hY E)
      (fun v y ↦ FamilyTransport.baseChange_move_q
        (pulledSquare.{u, v, w} a a' h f ha hX hY D)
        (sourceTransport.{u, v, w} a hX hY D) v y)
      (fun v y ↦ FamilyTransport.baseChange_move_q
        (pulledSquare.{u, v, w} a a' h f ha hX hY E)
        (sourceTransport.{u, v, w} a hX hY E) v y)
      (fun _ ↦ (Over.map a).map (φ.hom PUnit.unit))
      (fun _ ↦ (Over.map a').map ((Over.pullback f).map (φ.hom PUnit.unit)))
      (structureMap_naturality a' ((Over.pullback f).map (φ.hom PUnit.unit)))
      (fun _ ↦ projection_naturality a a' h f ha (φ.hom PUnit.unit))
      (fun v y ↦ DescentData.move_naturality φ v y) v y

/-- The pullback functor on descent data for one morphism. -/
private def pulledFunctor :
    HomDescentData.{u, v} a hX hY ⥤ HomDescentData.{u, w} a' hX' hY' where
  obj := pulledDatum.{u, v, w} a a' h f ha hX hX' hY hY'
  map := pulledMap.{u, v, w} a a' h f ha hX hX' hY hY'
  map_id _ := DescentData.Hom.ext (funext fun _ ↦ (Over.pullback f).map_id _)
  map_comp _ _ := DescentData.Hom.ext (funext fun _ ↦ (Over.pullback f).map_comp _ _)

end PullbackFunctor

/-- The pullback functor on descent data, with the canonical natural comparison of its
underlying space over `Y'` with ordinary pullback along `f`. -/
@[stacks 0ADL "part (1), pullback functor",
  stacks 0ADM "the functor so constructed is the pullback functor on descent data"]
public def pullbackDescentDataFunctor
    {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X) (f : Y' ⟶ Y)
    (ha : f ≫ a = a' ≫ h)
    (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') :
    { F : HomDescentData.{u, v} a hX hY ⥤ HomDescentData.{u, w} a' hX' hY' //
      ∃ α : ∀ D : HomDescentData.{u, v} a hX hY,
          (F.obj D).obj PUnit.unit ≅ (Over.pullback f).obj (D.obj PUnit.unit),
        (∀ {D E : HomDescentData.{u, v} a hX hY} (φ : D ⟶ E),
          (F.map φ).hom PUnit.unit ≫ (α E).hom =
            (α D).hom ≫ (Over.pullback f).map (φ.hom PUnit.unit)) ∧
        (∀ D : HomDescentData.{u, v} a hX hY,
          let A' := (Over.map a').obj ((F.obj D).obj PUnit.unit)
          let B' := Over.mk a'
          let A := (Over.map a).obj (D.obj PUnit.unit)
          let B := Over.mk a
          ∃ (q : (Over.map h).obj A' ⟶ A)
            (r : (Over.map h).obj B' ⟶ B),
            q.left = (α D).hom.left ≫ pullback.fst (D.obj PUnit.unit).hom f ∧
            r.left = f ∧
            (let s : (Over.map h).obj (A' ⨯ B') ⟶ A ⨯ B :=
                prod.lift ((Over.map h).map (prod.fst : A' ⨯ B' ⟶ A') ≫ q)
                  ((Over.map h).map (prod.snd : A' ⨯ B' ⟶ B') ≫ r)
             let t : (Over.map h).obj (B' ⨯ A') ⟶ B ⨯ A :=
                prod.lift ((Over.map h).map (prod.fst : B' ⨯ A' ⟶ B') ≫ r)
                  ((Over.map h).map (prod.snd : B' ⨯ A' ⟶ A') ≫ q)
             (Over.map h).map ((F.obj D).gluing PUnit.unit PUnit.unit).hom.left ≫ t =
               s ≫ (D.gluing PUnit.unit PUnit.unit).hom.left)) } :=
  private_decl% (by
    refine ⟨pulledFunctor.{u, v, w} a a' h f ha hX hX' hY hY',
      ⟨fun _ ↦ Iso.refl _, ?_, ?_⟩⟩
    · intro D E φ
      rfl
    · intro D
      refine ⟨overStructureProjection a a' h f ha (D.obj PUnit.unit)
          ((Over.pullback f).obj (D.obj PUnit.unit)) (pullback.fst (D.obj PUnit.unit).hom f)
          (IsPullback.of_hasPullback (D.obj PUnit.unit).hom f).flip,
        overStructureBase a a' h f ha, rfl, rfl, ?_⟩
      have he := FamilyTransport.baseChange_gluing
        (pulledSquare.{u, v, w} a a' h f ha hX hY D)
        (sourceTransport.{u, v, w} a hX hY D) PUnit.unit PUnit.unit
      rwa [FamilyTransport.comap_gluing, DescentData.transport_gluing] at he)

section ChosenComparison

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X) (f : Y' ⟶ Y)
    (ha : f ≫ a = a' ≫ h)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')

/-- The comparison isomorphism chosen by the specification of the pullback functor. -/
private abbrev chosenIso (D : HomDescentData.{u, v} a hX hY) :=
  Classical.choose
    (pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').property D

/-- The projection onto the old object determined by the chosen comparison. -/
private abbrev chosenProjection (D : HomDescentData.{u, v} a hX hY) :=
  overStructureProjection a a' h f ha (D.obj PUnit.unit)
    (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.obj D).obj
      PUnit.unit)
    ((chosenIso.{u, v, w} a a' h f ha hX hX' hY hY' D).hom.left ≫
      pullback.fst (D.obj PUnit.unit).hom f)
    (isPullback_of_overPullbackIso f (D.obj PUnit.unit) _
      (chosenIso.{u, v, w} a a' h f ha hX hX' hY hY' D))

/-- The chosen pullback square, as a base-change square. -/
private abbrev chosenSquare (D : HomDescentData.{u, v} a hX hY) (_ : PUnit.{w + 1}) :=
  overBaseChangeSquare a a' h f ha (D.obj PUnit.unit)
    (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.obj D).obj
      PUnit.unit)
    ((chosenIso.{u, v, w} a a' h f ha hX hX' hY hY' D).hom.left ≫
      pullback.fst (D.obj PUnit.unit).hom f)
    (isPullback_of_overPullbackIso f (D.obj PUnit.unit) _
      (chosenIso.{u, v, w} a a' h f ha hX hX' hY hY' D))

private lemma chosen_move (D : HomDescentData.{u, v} a hX hY) {Z : Over X'}
    (v : Z ⟶ (Over.map a').obj
      (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.obj D).obj
        PUnit.unit))
    (y : Z ⟶ Over.mk a') :
    (Over.map h).map
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.obj
          D).transport.move v y) ≫
        chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' D =
      (sourceTransport.{u, v, w} a hX hY D).move (i := PUnit.unit) (j := PUnit.unit)
        ((Over.map h).map v ≫
          chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' D)
        ((Over.map h).map y ≫ overStructureBase a a' h f ha) := by
  obtain ⟨q, r, hq, hr, hg⟩ :=
    (Classical.choose_spec
      (pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').property).2 D
  obtain rfl : q = chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' D :=
    Over.OverMorphism.ext hq
  obtain rfl : r = overStructureBase a a' h f ha := Over.OverMorphism.ext hr
  refine FamilyTransport.move_baseChange (i := PUnit.unit) (j := PUnit.unit)
    (q := fun _ ↦ chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' D)
    (r := fun _ ↦ overStructureBase a a' h f ha)
    (sourceTransport.{u, v, w} a hX hY D)
    (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.obj D).transport)
    (fun i j ↦ ?_) v y
  simp only [FamilyTransport.comap_gluing, DescentData.transport_gluing]
  exact hg

private lemma chosenProjection_naturality {D E : HomDescentData.{u, v} a hX hY} (φ : D ⟶ E) :
    (Over.map h).map ((Over.map a').map
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').val.map φ).hom
          PUnit.unit)) ≫
        chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' E =
      chosenProjection.{u, v, w} a a' h f ha hX hX' hY hY' D ≫
        (Over.map a).map (φ.hom PUnit.unit) := by
  have hn :=
    (Classical.choose_spec
      (pullbackDescentDataFunctor.{u, v, w} a a' h f ha hX hX' hY hY').property).1 φ
  have he := congrArg (fun k ↦ k.left ≫ pullback.fst (E.obj PUnit.unit).hom f) hn
  apply Over.OverMorphism.ext
  simpa [chosenProjection, chosenIso, Over.pullback_map_left, Over.comp_left,
    Over.map_map_left, Over.homMk_left, pullback.lift_fst] using he

end ChosenComparison

/-- A map of the underlying spaces over the base commuting with the move operations is a
morphism of descent data for one morphism. -/
private def homOfMoveHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : Y ⟶ X}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    (D E : HomDescentData.{u, v} a hX hY)
    (m : (Over.map a).obj (D.obj PUnit.unit) ⟶ (Over.map a).obj (E.obj PUnit.unit))
    (hm : m ≫ structureMap a (E.obj PUnit.unit) = structureMap a (D.obj PUnit.unit))
    (ht : ∀ {Z : Over X} (v : Z ⟶ (Over.map a).obj (D.obj PUnit.unit))
      (y : Z ⟶ Over.mk a), D.transport.move v y ≫ m = E.transport.move (v ≫ m) y) :
    D ⟶ E := by
  have hml : m.left ≫ (E.obj PUnit.unit).hom = (D.obj PUnit.unit).hom := by
    simpa only [Over.comp_left, Over.homMk_left] using congrArg Over.Hom.left hm
  exact DescentData.homOfMove (fun _ ↦ Over.homMk m.left hml) fun v y ↦ ht v y

/-- Two morphisms of descent data for one morphism are equal if their underlying maps of total
spaces agree. -/
private lemma hom_ext_left {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : Y ⟶ X}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y}
    {D E : HomDescentData.{u, v} a hX hY} {φ ψ : D ⟶ E}
    (h : (φ.hom PUnit.unit).left = (ψ.hom PUnit.unit).left) : φ = ψ := by
  apply DescentData.Hom.ext
  funext ⟨⟩
  exact Over.OverMorphism.ext h

section Comparison

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X) (f₀ f₁ : Y' ⟶ Y)
    (ha₀ : f₀ ≫ a = a' ≫ h) (ha₁ : f₁ ≫ a = a' ≫ h)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')

/-- The comparison map between the two pullbacks of a descent datum. -/
private def comparisonHom (D : HomDescentData.{u, v} a hX hY) :
    (pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.obj D ⟶
      (pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY').val.obj D :=
  homOfMoveHom _ _
    ((chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D PUnit.unit).compare
      (sourceTransport.{u, v, w} a hX hY D)
      (structureMap a'
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.obj D).obj
          PUnit.unit))
      (chosenProjection.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D))
    (BaseChangeSquare.compare_p _ _ _ _)
    (fun v y ↦ BaseChangeSquare.compare_move
      (R := fun _ ↦ overStructureBase a a' h f₁ ha₁)
      (R₀ := fun _ ↦ overStructureBase a a' h f₀ ha₀)
      (Q := fun _ ↦ chosenProjection.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D)
      (Q₀ := fun _ ↦ chosenProjection.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D)
      (chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D PUnit.unit)
      (sourceTransport.{u, v, w} a hX hY D)
      ((pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY').val.obj D).transport
      ((pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.obj D).transport
      (fun v y ↦ chosen_move.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D v y)
      (fun v y ↦ chosen_move.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D v y) v y)

private lemma comparisonHom_comp (D : HomDescentData.{u, v} a hX hY) :
    comparisonHom.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' D ≫
      comparisonHom.{u, v, w} a a' h f₁ f₀ ha₁ ha₀ hX hX' hY hY' D = 𝟙 _ := by
  apply hom_ext_left
  have he := congrArg (fun k ↦ k.left)
    (BaseChangeSquare.compare_comp (i := PUnit.unit)
      (t := sourceTransport.{u, v, w} a hX hY D)
      (L := chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D PUnit.unit)
      (L₀ := chosenSquare.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D PUnit.unit))
  simpa only [comparisonHom, homOfMoveHom, DescentData.homOfMove, DescentData.comp_hom,
    DescentData.id_hom, Over.homMk_left, Over.comp_left, Over.id_left,
    Over.map_obj_left] using he

private lemma comparisonHom_naturality {D E : HomDescentData.{u, v} a hX hY} (φ : D ⟶ E) :
    (pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.map φ ≫
        comparisonHom.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' E =
      comparisonHom.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' D ≫
        (pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY').val.map φ := by
  apply hom_ext_left
  have he := congrArg (fun k ↦ k.left)
    (BaseChangeSquare.compare_naturality (i := PUnit.unit)
      (t := sourceTransport.{u, v, w} a hX hY D)
      (u := sourceTransport.{u, v, w} a hX hY E)
      (L := chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D PUnit.unit)
      (K := chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' E PUnit.unit)
      (p₀ := structureMap a'
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.obj D).obj
          PUnit.unit))
      (q₀ := chosenProjection.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D)
      (s₀ := structureMap a'
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.obj E).obj
          PUnit.unit))
      (qE₀ := chosenProjection.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' E)
      (m := fun _ ↦ (Over.map a).map (φ.hom PUnit.unit))
      ((Over.map a').map
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val.map φ).hom
          PUnit.unit))
      ((Over.map a').map
        (((pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY').val.map φ).hom
          PUnit.unit))
      (structureMap_naturality a' _) (structureMap_naturality a' _)
      (chosenProjection_naturality.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' φ)
      (chosenProjection_naturality.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' φ)
      (fun v y ↦ DescentData.move_naturality φ v y))
  simpa only [comparisonHom, homOfMoveHom, DescentData.homOfMove, DescentData.comp_hom,
    Over.homMk_left, Over.comp_left, Over.map_map_left] using he

/-- The canonical isomorphism between the two pullback functors. -/
private def comparisonIso :
    (pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY').val ≅
      (pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY').val :=
  NatIso.ofComponents
    (fun D ↦
      { hom := comparisonHom.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' D
        inv := comparisonHom.{u, v, w} a a' h f₁ f₀ ha₁ ha₀ hX hX' hY hY' D
        hom_inv_id := comparisonHom_comp.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' D
        inv_hom_id := comparisonHom_comp.{u, v, w} a a' h f₁ f₀ ha₁ ha₀ hX hX' hY hY' D })
    (fun φ ↦ comparisonHom_naturality.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY' φ)

private lemma comparisonIso_spec :
    let F₀ := pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY'
    let F₁ := pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY'
    let α₀ := Classical.choose F₀.property
    let α₁ := Classical.choose F₁.property
    ∀ D : HomDescentData.{u, v} a hX hY,
      let V₀ := (F₀.val.obj D).obj PUnit.unit
      let V₁ := (F₁.val.obj D).obj PUnit.unit
      let A := (Over.map a).obj (D.obj PUnit.unit)
      let B₀ := Over.mk a
      ∃ (q₀ : (Over.map (a' ≫ h)).obj V₀ ⟶ A)
        (q₁ : (Over.map (a' ≫ h)).obj V₁ ⟶ A)
        (y₁ : (Over.map (a' ≫ h)).obj V₀ ⟶ B₀)
        (y₀ : (Over.map (a' ≫ h)).obj V₁ ⟶ B₀),
        q₀.left = (α₀ D).hom.left ≫ pullback.fst (D.obj PUnit.unit).hom f₀ ∧
        q₁.left = (α₁ D).hom.left ≫ pullback.fst (D.obj PUnit.unit).hom f₁ ∧
        y₁.left = V₀.hom ≫ f₁ ∧ y₀.left = V₁.hom ≫ f₀ ∧
        prod.lift q₀ y₁ ≫ (D.gluing PUnit.unit PUnit.unit).hom.left =
          (Over.map (a' ≫ h)).map
            (((comparisonIso.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY').hom.app D).hom
              PUnit.unit) ≫ prod.lift y₀ q₁ := by
  dsimp only
  intro D
  refine ⟨(Over.mapComp a' h).hom.app _ ≫
      chosenProjection.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D,
    (Over.mapComp a' h).hom.app _ ≫
      chosenProjection.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D,
    (Over.mapComp a' h).hom.app _ ≫ (Over.map h).map (structureMap a' _) ≫
      overStructureBase a a' h f₁ ha₁,
    (Over.mapComp a' h).hom.app _ ≫ (Over.map h).map (structureMap a' _) ≫
      overStructureBase a a' h f₀ ha₀, ?_, ?_, ?_, ?_, ?_⟩
  · simp [chosenProjection]
  · simp [chosenProjection]
  · simp
  · simp
  · have hj := (Over.mapComp a' h).hom.naturality
      (((comparisonIso.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY').hom.app D).hom PUnit.unit)
    have hg := BaseChangeSquare.compare_gluing (i := PUnit.unit)
      (t := sourceTransport.{u, v, w} a hX hY D)
      (L₀ := chosenSquare.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY' D PUnit.unit)
      (L₁ := chosenSquare.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY' D PUnit.unit)
    simp only [FamilyTransport.comap_gluing, DescentData.transport_gluing] at hg
    have he := congrArg (fun k ↦ (Over.mapComp a' h).hom.app _ ≫ k) hg
    erw [reassoc_of% hj.symm] at he
    simpa only [prod.comp_lift_assoc, prod.comp_lift, Category.assoc] using he

/-- Pullback along two maps completing the same square is canonically and naturally
isomorphic, by the gluing isomorphism of the descent datum. -/
@[stacks 0ADL "part (2), canonical isomorphism"]
public def pullbackDescentDataFunctor_canonicalIso :
    let F₀ := pullbackDescentDataFunctor.{u, v, w} a a' h f₀ ha₀ hX hX' hY hY'
    let F₁ := pullbackDescentDataFunctor.{u, v, w} a a' h f₁ ha₁ hX hX' hY hY'
    let α₀ := Classical.choose F₀.property
    let α₁ := Classical.choose F₁.property
    { η : F₀.val ≅ F₁.val //
      ∀ D : HomDescentData.{u, v} a hX hY,
        let V₀ := (F₀.val.obj D).obj PUnit.unit
        let V₁ := (F₁.val.obj D).obj PUnit.unit
        let A := (Over.map a).obj (D.obj PUnit.unit)
        let B₀ := Over.mk a
        ∃ (q₀ : (Over.map (a' ≫ h)).obj V₀ ⟶ A)
          (q₁ : (Over.map (a' ≫ h)).obj V₁ ⟶ A)
          (y₁ : (Over.map (a' ≫ h)).obj V₀ ⟶ B₀)
          (y₀ : (Over.map (a' ≫ h)).obj V₁ ⟶ B₀),
          q₀.left = (α₀ D).hom.left ≫ pullback.fst (D.obj PUnit.unit).hom f₀ ∧
          q₁.left = (α₁ D).hom.left ≫ pullback.fst (D.obj PUnit.unit).hom f₁ ∧
          y₁.left = V₀.hom ≫ f₁ ∧ y₀.left = V₁.hom ≫ f₀ ∧
          prod.lift q₀ y₁ ≫ (D.gluing PUnit.unit PUnit.unit).hom.left =
            (Over.map (a' ≫ h)).map ((η.hom.app D).hom PUnit.unit) ≫
              prod.lift y₀ q₁ } :=
  private_decl% ⟨comparisonIso.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY',
    comparisonIso_spec.{u, v, w} a a' h f₀ f₁ ha₀ ha₁ hX hX' hY hY'⟩

end Comparison

end AlgebraicGeometry.Space.Descent

end
