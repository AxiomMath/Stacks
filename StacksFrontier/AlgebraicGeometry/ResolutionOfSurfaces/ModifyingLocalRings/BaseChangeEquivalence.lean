module

public import StacksFrontier.AlgebraicGeometry.Full.Basic
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeFaithful
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic

/-!
# Base change near finitely many closed points is full

Let `D` be a `FinitePresentationAwayPointsSituation`: a scheme `S` with finitely many pairwise
distinct closed points `s i` whose open complement `U` is quasi-compact. Base change to the
spectra of the local rings `S_i = Spec 𝒪_{S, s i}` is the functor
`AlgebraicGeometry.finitePresentationAwayPointsBaseChange` of [Stacks, Tag 0BFU], from the
category of finitely presented morphisms to `S` that are isomorphisms over `U` to the product
of the corresponding local categories.

[Stacks, Tag 0BFV] asserts that this functor is an equivalence. This file reduces that assertion
to the glueing theorem of [Stacks, Tag 0E8Q], that
`AlgebraicGeometry.canonicalRestrictionFunctor` is an equivalence, stated as the proposition
`AlgebraicGeometry.GlueingNearClosedPointsEquivalence`; the equivalence proved here takes that
proposition as a hypothesis and is not tagged with 0BFV.

Its **fullness** constituent needs no hypothesis, because the restriction functor of the glueing
theorem is fully faithful: it is `AlgebraicGeometry.fullyFaithfulCanonicalRestrictionFunctor`.
The reduction chain is a composite of functors, and the hypothesis is used only to upgrade one of
its factors from fully faithful to an equivalence.

## Main definitions

* `AlgebraicGeometry.GlueingNearClosedPointsEquivalence`: the equivalence assertion of
  [Stacks, Tag 0E8Q], as a proposition about the canonical restriction functor.

## Main results

* `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_full`: the base-change functor of
  [Stacks, Tag 0BFU] is full, with no hypotheses. Together with
  `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_faithful` this makes it fully
  faithful, so a global modification supported at the distinguished points is determined, up to
  a unique isomorphism, by its family of localizations.
* `AlgebraicGeometry.BaseChangeFunctor.fullyFaithful`: that pair of constituents in the form in
  which they are used, taking an isomorphism of families of localizations to an isomorphism
  over `S`.
* `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence`: granted
  `GlueingNearClosedPointsEquivalence`, the base-change functor of [Stacks, Tag 0BFU] is an
  equivalence of categories, which is [Stacks, Tag 0BFV].

## Implementation notes

The reduction is a chain of functors, all but one of them equivalences. The glueing theorem
presents a finitely presented scheme over `S` as a scheme over `U`, a family of schemes over the
`S_i`, and a glueing isomorphism over the punctured local schemes. Cutting that presentation
down to the objects which become isomorphisms over `U` makes the component over `U` the
identity, so a glueing datum is determined by its family of local components; this is the
projection `localAwayProjection` below, shown to be an equivalence by hand. Composing with the
restriction functor of the glueing theorem and with the reindexing that turns the dependent
product over `ULift (Fin n)` into the one over `Fin n` produces a functor with the same
underlying data as the base-change functor — the identification is `Iso.refl` componentwise —
and `CategoryTheory.Functor.Full.of_iso` and
`CategoryTheory.Functor.isEquivalence_iff_of_iso` transfer the conclusions.

The only factor of the chain which is not already an equivalence is the restriction functor cut
down to the glueing data with trivial open component, `trivialOpenRestriction`; it is a
`CategoryTheory.ObjectProperty.lift` of the restriction functor, hence full and faithful because
that functor is, and an equivalence under the glueing hypothesis.

The index type of [Stacks, Tag 0E8Q] lives in the universe of the scheme, while a
`FinitePresentationAwayPointsSituation` indexes its points by `Fin n`; the family of points is
therefore transported along `Equiv.ulift` before the glueing theorem is applied.

## References

* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe w v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S : C}

/-- Invertibility of the structure morphism of an object of `Over S` depends only on its
isomorphism class. -/
private theorem isIso_hom_iff_of_iso {X Y : Over S} (e : X ≅ Y) : IsIso X.hom ↔ IsIso Y.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom, isIso_comp_left_iff]

/-- An object of `Over S` whose structure morphism is invertible is a terminal object, so any
two morphisms into it agree. -/
private theorem hom_ext_of_isIso_hom {X Y : Over S} [IsIso Y.hom] (f g : X ⟶ Y) : f = g :=
  Over.OverMorphism.ext ((cancel_mono Y.hom).mp ((Over.w f).trans (Over.w g).symm))

/-- Two objects of `Over S` with invertible structure morphisms are canonically isomorphic. -/
private noncomputable def isoOfIsIsoHom (X Y : Over S) [IsIso X.hom] [IsIso Y.hom] : X ≅ Y :=
  Over.isoMk (asIso X.hom ≪≫ (asIso Y.hom).symm)

/-- Base change of an isomorphism along any morphism is an isomorphism. -/
theorem isIso_pullback_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (hf : IsIso f) : IsIso (pullback.snd f g) :=
  have : IsIso f := hf
  inferInstance

/-- Pulling back along `e.hom ≫ g` for an isomorphism `e` inverts the structure morphism exactly
when pulling back along `g` does. -/
private theorem isIso_pullback_obj_hom_iff_of_isoComp [HasPullbacks C] {A B : C} (g : B ⟶ S)
    (e : A ≅ B) (X : Over S) :
    IsIso ((Over.pullback (e.hom ≫ g)).obj X).hom ↔ IsIso ((Over.pullback g).obj X).hom := by
  let Y := (Over.pullback g).obj X
  have hbase : IsIso ((Over.pullback e.hom).obj Y).hom ↔ IsIso Y.hom := by
    change IsIso (pullback.snd Y.hom e.hom) ↔ _
    rw [← isIso_comp_left_iff (pullback.fst Y.hom e.hom) Y.hom, pullback.condition]
    exact (isIso_comp_right_iff _ _).symm
  exact (isIso_hom_iff_of_iso ((Over.pullbackComp e.hom g).app X)).trans hbase


end CategoryTheory.Over

namespace CategoryTheory.ObjectProperty

/-- A product of full subcategories is the full subcategory of the product on the objects all of
whose components satisfy the corresponding property. -/
private def piFullSubcategoryEquivalence {I : Type u} {C : I → Type v}
    [∀ i, Category.{w} (C i)] (P : ∀ i, ObjectProperty (C i)) :
    (∀ i, (P i).FullSubcategory) ≌
      (show ObjectProperty (∀ i, C i) from fun X => ∀ i, P i (X i)).FullSubcategory where
  functor :=
    { obj := fun X => ⟨fun i => (X i).obj, fun i => (X i).property⟩
      map := fun f => ObjectProperty.homMk fun i => (f i).hom }
  inverse :=
    { obj := fun X i => ⟨X.obj i, X.property i⟩
      map := fun f i => ObjectProperty.homMk ((f.hom) i) }
  unitIso := NatIso.ofComponents (fun X =>
    { hom := fun i => ObjectProperty.homMk (𝟙 ((X i).obj))
      inv := fun i => ObjectProperty.homMk (𝟙 ((X i).obj))
      hom_inv_id := by ext i; cat_disch
      inv_hom_id := by ext i; cat_disch }) (by
        intro X Y f
        ext i
        cat_disch)
  counitIso := NatIso.ofComponents
    (fun X => ObjectProperty.isoMk
      (fun Z : ∀ i, C i => ∀ i, P i (Z i)) (Iso.refl X.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      ext i
      cat_disch)
  functor_unitIso_comp := by intro X; cat_disch

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

open CategoryTheory.Over CategoryTheory.ObjectProperty

/-- The equivalence assertion of **Stacks Project, Tag 0E8Q**: for every finite family of
pairwise distinct closed points of a scheme whose open complement is quasi-compact, the
canonical restriction functor on schemes of finite presentation is an equivalence onto the
category of glueing data. -/
def GlueingNearClosedPointsEquivalence : Prop :=
  ∀ {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S) (hs : ∀ i, s i ∈ closedPoints S),
    Function.Injective s → QuasiCompact (complementOfClosedPoints s hs).ι →
    (canonicalRestrictionFunctor s hs).IsEquivalence

/-- Restricting an object of `Over X` to equal open subschemes inverts the structure morphism
for one exactly when it does for the other. -/
private theorem isIso_pullback_ι_obj_hom_iff_of_eq {X : Scheme.{u}} {U V : X.Opens} (h : U = V)
    (Y : Over X) :
    IsIso ((Over.pullback U.ι).obj Y).hom ↔ IsIso ((Over.pullback V.ι).obj Y).hom := by
  subst h
  rfl

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- The index type of the distinguished points, lifted to the universe of the scheme. -/
private abbrev PointIndex := ULift.{u} (Fin D.n)

/-- The distinguished points, reindexed by a type in the universe of the scheme. -/
private def liftedPoints : D.PointIndex → D.S := fun i => D.points i.down

/-- The reindexed family of distinguished points consists of closed points. -/
private theorem liftedPoints_mem_closedPoints :
    ∀ i : D.PointIndex, D.liftedPoints i ∈ closedPoints D.S :=
  fun i => mem_closedPoints_iff.mpr (D.points_closed i.down)

/-- The reindexed family of distinguished points is injective. -/
private theorem liftedPoints_injective : Function.Injective D.liftedPoints :=
  fun _ _ h ↦ ULift.ext _ _ (D.points_injective h)

/-- The inverse image of the set of distinguished points under the canonical morphism from the
spectrum of the local ring at `s i` is the closed point. -/
private theorem preimage_fromSpecStalk_range_points (i : Fin D.n) :
    (D.S.fromSpecStalk (D.points i)) ⁻¹' Set.range D.points =
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} := by
  ext x
  constructor
  · rintro ⟨j, hj⟩
    have hr : D.S.fromSpecStalk (D.points i) x ∈
        Set.range (D.S.fromSpecStalk (D.points i)) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hr
    have hspec : D.S.fromSpecStalk (D.points i) x ⤳ D.points i := hr
    have hspec' : D.points j ⤳ D.points i := by simpa [hj] using hspec
    have hm := (specializes_iff_forall_closed.mp hspec') _ (D.points_closed j) (by simp)
    obtain rfl : i = j := D.points_injective (Set.mem_singleton_iff.mp hm)
    have hmap : D.S.fromSpecStalk (D.points i) x =
        D.S.fromSpecStalk (D.points i)
          (IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))) := by
      rw [← hj, Scheme.fromSpecStalk_closedPoint]
    exact Set.mem_singleton_iff.mpr
      ((D.S.fromSpecStalk (D.points i)).isEmbedding.injective hmap)
  · rintro rfl
    exact ⟨i, (Scheme.fromSpecStalk_closedPoint (x := D.points i)).symm⟩

/-- The open complement formed from the reindexed family is the open complement of the
situation. -/
private theorem complementOfClosedPoints_liftedPoints :
    complementOfClosedPoints D.liftedPoints D.liftedPoints_mem_closedPoints = D.complement := by
  apply Opens.ext
  apply Set.ext
  intro x
  change x ∈ (⋂ i : D.PointIndex, ({D.points i.down} : Set D.S)ᶜ) ↔
    x ∈ (Set.range D.points)ᶜ
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
  exact ⟨fun h ⟨i, hi⟩ ↦ h (ULift.up i) hi.symm, fun h i hi ↦ h ⟨i.down, hi.symm⟩⟩

/-- The punctured local scheme formed from the reindexed family is the punctured local scheme of
the situation. -/
private theorem preimage_complementOfClosedPoints_liftedPoints (i : Fin D.n) :
    ((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
      complementOfClosedPoints D.liftedPoints D.liftedPoints_mem_closedPoints) =
        D.puncturedLocalScheme i := by
  have hOpen : ((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ D.complement) =
      D.puncturedLocalScheme i := by
    apply Opens.ext
    apply Set.ext
    intro x
    change D.S.fromSpecStalk (D.points i) x ∈ (Set.range D.points)ᶜ ↔
      x ∈ ({IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))}ᶜ :
        Set ↥(D.localScheme i))
    have hx := congrArg (fun t => x ∈ t) (D.preimage_fromSpecStalk_range_points i)
    simp only [Set.mem_preimage] at hx
    exact not_congr (Iff.of_eq hx)
  rw [D.complementOfClosedPoints_liftedPoints]
  exact hOpen

/-- The open complement formed from the reindexed family has quasi-compact inclusion. -/
private theorem quasiCompact_complementOfClosedPoints_liftedPoints :
    QuasiCompact (complementOfClosedPoints D.liftedPoints D.liftedPoints_mem_closedPoints).ι := by
  have := D.complement_quasiCompact
  rw [← Scheme.isoOfEq_hom_ι D.S D.complementOfClosedPoints_liftedPoints]
  infer_instance

/-- The category of glueing data attached to the reindexed family of distinguished points. -/
private abbrev GlueingDatum :=
  glueingData D.liftedPoints D.liftedPoints_mem_closedPoints

/-- Families of finitely presented schemes over the local schemes, indexed by the reindexed
family of points. -/
private abbrev LocalFamily :=
  (j : D.PointIndex) → FinitePresentationOver (D.localScheme j.down)

/-- The property of a family of local objects that every restriction to a punctured local scheme
is an isomorphism. -/
private def localAwayProperty : ObjectProperty D.LocalFamily := fun X => ∀ j,
  IsIso ((((restrictLocalsToPuncturedLocals D.liftedPoints
    D.liftedPoints_mem_closedPoints).obj X) j).obj.hom)

/-- The property of a glueing datum that its component over the open complement is trivial. -/
private def trivialOpenProperty : ObjectProperty D.GlueingDatum := fun X =>
  IsIso (((openComponent D.liftedPoints D.liftedPoints_mem_closedPoints).obj X).obj.hom)

private instance trivialOpenProperty_isClosedUnderIsomorphisms :
    D.trivialOpenProperty.IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    change IsIso (((openComponent D.liftedPoints
      D.liftedPoints_mem_closedPoints).obj X).obj.hom) at h
    refine (isIso_hom_iff_of_iso (C := Scheme)
      (S := (complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).toScheme) ?_).mp h
    exact (isFinitePresentationOver
      ((complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).toScheme)).ι.mapIso
          ((openComponent D.liftedPoints D.liftedPoints_mem_closedPoints).mapIso e)

/-- The projection of a glueing datum with trivial open component to its family of local
components. -/
private noncomputable def localAwayProjection :
    D.trivialOpenProperty.FullSubcategory ⥤ D.localAwayProperty.FullSubcategory where
  obj X := ⟨X.obj.obj.right, by
    intro j
    let A := (restrictOpenToPuncturedLocals D.liftedPoints
      D.liftedPoints_mem_closedPoints).obj X.obj.obj.left
    let B := (restrictLocalsToPuncturedLocals D.liftedPoints
      D.liftedPoints_mem_closedPoints).obj X.obj.obj.right
    have hA₀ : IsIso X.obj.obj.left.obj.hom := X.property
    have hA : IsIso (A j).obj.hom := by
      dsimp [A, restrictOpenToPuncturedLocals, finitePresentationBaseChange]
      exact isIso_pullback_snd _ _ hA₀
    have : IsIso X.obj.obj.hom := X.obj.property
    let isoJ : (A j).obj ≅ (B j).obj :=
      (isFinitePresentationOver (_root_.AlgebraicGeometry.puncturedLocalScheme
        D.liftedPoints D.liftedPoints_mem_closedPoints j)).ι.mapIso
          ((Pi.eval _ j).mapIso (asIso X.obj.obj.hom))
    exact (isIso_hom_iff_of_iso (C := Scheme)
      (S := _root_.AlgebraicGeometry.puncturedLocalScheme D.liftedPoints
        D.liftedPoints_mem_closedPoints j)
      isoJ).mp hA⟩
  map := fun f => ObjectProperty.homMk f.hom.hom.right

private theorem localAwayProjection_faithful : D.localAwayProjection.Faithful := by
  constructor
  intro X Y f g h
  apply D.trivialOpenProperty.hom_ext
  apply (show ObjectProperty (CategoryTheory.Comma
      (restrictOpenToPuncturedLocals D.liftedPoints D.liftedPoints_mem_closedPoints)
      (restrictLocalsToPuncturedLocals D.liftedPoints D.liftedPoints_mem_closedPoints)) from
    fun Z => IsIso Z.hom).hom_ext
  apply Comma.hom_ext
  · apply (isFinitePresentationOver
      ((complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).toScheme)).hom_ext
    have : IsIso Y.obj.obj.left.obj.hom := Y.property
    exact hom_ext_of_isIso_hom f.hom.hom.left.hom g.hom.hom.left.hom
  · exact congrArg (fun k => k.hom) h

private theorem localAwayProjection_full : D.localAwayProjection.Full := by
  constructor
  intro X Y f
  have : IsIso X.obj.obj.left.obj.hom := X.property
  have : IsIso Y.obj.obj.left.obj.hom := Y.property
  let leftIso : X.obj.obj.left.obj ≅ Y.obj.obj.left.obj := isoOfIsIsoHom _ _
  let cmp : X.obj.obj ⟶ Y.obj.obj :=
    { left := ObjectProperty.homMk leftIso.hom
      right := f.hom
      w := by
        funext j
        apply (isFinitePresentationOver
          (_root_.AlgebraicGeometry.puncturedLocalScheme D.liftedPoints
            D.liftedPoints_mem_closedPoints j)).hom_ext
        have : IsIso (((restrictLocalsToPuncturedLocals D.liftedPoints
          D.liftedPoints_mem_closedPoints).obj Y.obj.obj.right j).obj.hom) :=
            (D.localAwayProjection.obj Y).property j
        exact hom_ext_of_isIso_hom _ _ }
  exact ⟨ObjectProperty.homMk (ObjectProperty.homMk cmp), D.localAwayProperty.hom_ext rfl⟩

/-- The identity, as a finitely presented scheme over the open complement. -/
private noncomputable def trivialOpenObject :
    FinitePresentationOver
      ((complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).toScheme) :=
  ⟨Over.mk (𝟙 ((complementOfClosedPoints D.liftedPoints
      D.liftedPoints_mem_closedPoints).toScheme)), by
      change FinitePresentation (𝟙 ((complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).toScheme))
      exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

private theorem localAwayProjection_essSurj : D.localAwayProjection.EssSurj := by
  constructor
  intro X
  let O := D.trivialOpenObject
  let A := (restrictOpenToPuncturedLocals D.liftedPoints
    D.liftedPoints_mem_closedPoints).obj O
  let B := (restrictLocalsToPuncturedLocals D.liftedPoints
    D.liftedPoints_mem_closedPoints).obj X.obj
  have hId : IsIso O.obj.hom := inferInstanceAs (IsIso (𝟙 _))
  have : ∀ j, IsIso (A j).obj.hom := by
    intro j
    dsimp [A, restrictOpenToPuncturedLocals, finitePresentationBaseChange, O,
      trivialOpenObject]
    exact isIso_pullback_snd _ _ hId
  have : ∀ j, IsIso (B j).obj.hom := X.property
  let α : A ⟶ B := fun j =>
    ((isFinitePresentationOver (_root_.AlgebraicGeometry.puncturedLocalScheme D.liftedPoints
      D.liftedPoints_mem_closedPoints j)).isoMk
        (isoOfIsIsoHom (A j).obj (B j).obj)).hom
  have : IsIso α := (isIso_pi_iff α).2 fun j =>
    ((isFinitePresentationOver (_root_.AlgebraicGeometry.puncturedLocalScheme D.liftedPoints
      D.liftedPoints_mem_closedPoints j)).isoMk
        (isoOfIsIsoHom (A j).obj (B j).obj)).isIso_hom
  let Z : D.GlueingDatum := ⟨⟨O, X.obj, α⟩, by infer_instance⟩
  refine ⟨⟨Z, show IsIso O.obj.hom from hId⟩, ?_⟩
  exact ⟨ObjectProperty.isoMk D.localAwayProperty (Iso.refl X.obj)⟩

private theorem localAwayProjection_isEquivalence : D.localAwayProjection.IsEquivalence :=
  Functor.IsEquivalence.mk D.localAwayProjection_faithful D.localAwayProjection_full
    D.localAwayProjection_essSurj

/-- The property of an object of `Over (localScheme i)` that its restriction to the punctured
local scheme of the situation is an isomorphism. -/
private def punctureAwayProperty (i : Fin D.n) : ObjectProperty (Over (D.localScheme i)) :=
  fun X => IsIso ((Over.pullback (D.puncturedLocalScheme i).ι).obj X).hom

/-- The property of a finitely presented scheme over the `i`th local scheme that its restriction
to the punctured local scheme formed from the reindexed family is an isomorphism. -/
private def localAwayFactorProperty (i : Fin D.n) :
    ObjectProperty (FinitePresentationOver (D.localScheme i)) := fun X =>
  IsIso ((Over.pullback (((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
    complementOfClosedPoints D.liftedPoints
      D.liftedPoints_mem_closedPoints)).ι).obj X.obj).hom

private theorem localAwayFactorProperty_eq (i : Fin D.n) :
    D.localAwayFactorProperty i =
      (D.punctureAwayProperty i).inverseImage
        (isFinitePresentationOver (D.localScheme i)).ι := by
  ext X
  exact isIso_pullback_ι_obj_hom_iff_of_eq
    (D.preimage_complementOfClosedPoints_liftedPoints i) X.obj

/-- The componentwise away-property on the product of the categories of finitely presented
schemes over the local schemes. -/
private def localAwayPiProperty :
    ObjectProperty (∀ i : Fin D.n, FinitePresentationOver (D.localScheme i)) :=
  fun X => ∀ i, D.localAwayFactorProperty i (X i)

private instance localAwayFactorProperty_isClosedUnderIsomorphisms (i : Fin D.n) :
    (D.localAwayFactorProperty i).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    change IsIso ((Over.pullback
      (((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
        complementOfClosedPoints D.liftedPoints
          D.liftedPoints_mem_closedPoints).ι)).obj Y.obj).hom
    refine (isIso_hom_iff_of_iso ?_).mp h
    exact (Over.pullback (((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
      complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).ι)).mapIso
          ((isFinitePresentationOver (D.localScheme i)).ι.mapIso e)

private instance localAwayPiProperty_isClosedUnderIsomorphisms :
    D.localAwayPiProperty.IsClosedUnderIsomorphisms where
  of_iso e h i :=
    ObjectProperty.IsClosedUnderIsomorphisms.of_iso ((Pi.eval _ i).mapIso e) (h i)

/-- The `i`th factor of the away-category formed from the reindexed family is the `i`th local
category of the situation. -/
private noncomputable def localFactorEquivalence (i : Fin D.n) :
    (D.localAwayFactorProperty i).FullSubcategory ≌ D.localCategory i := by
  let A := isFinitePresentationOver (D.localScheme i)
  let B := D.punctureAwayProperty i
  let Q := B.inverseImage A.ι
  let c : (D.localAwayFactorProperty i).FullSubcategory ≌ Q.FullSubcategory :=
    ObjectProperty.fullSubcategoryCongr (D.localAwayFactorProperty_eq i)
  let n : Q.FullSubcategory ≌ (A ⊓ B).FullSubcategory := nestedFullSubcategoryEquivalence A B
  exact c.trans n

/-- The away-category of local families formed from the reindexed family is the product of the
local categories of the situation. -/
private noncomputable def localAwayToLocalCategoryEquivalence :
    D.localAwayProperty.FullSubcategory ≌ (∀ i, D.localCategory i) := by
  let C : D.PointIndex → Type (u + 1) := fun j =>
    FinitePresentationOver (D.localScheme j.down)
  let R := (Pi.equivalenceOfEquiv C Equiv.ulift.symm).symm
  have hP : D.localAwayPiProperty.inverseImage R.functor = D.localAwayProperty := by
    ext X
    change (∀ i, D.localAwayFactorProperty i (X (ULift.up i))) ↔
      ∀ j, IsIso ((((restrictLocalsToPuncturedLocals D.liftedPoints
        D.liftedPoints_mem_closedPoints).obj X) j).obj.hom)
    dsimp [localAwayFactorProperty, restrictLocalsToPuncturedLocals,
      finitePresentationBaseChange, ObjectProperty.lift]
    exact ⟨fun h j ↦ h j.down, fun h i ↦ h (ULift.up i)⟩
  exact (R.congrFullSubcategory (Q := D.localAwayPiProperty) (P := D.localAwayProperty) hP).trans
    ((piFullSubcategoryEquivalence D.localAwayFactorProperty).symm.trans
      (Equivalence.pi D.localFactorEquivalence))

/-- The property of an object of `Over S` that its restriction to the open complement is an
isomorphism. -/
private def openAwayProperty : ObjectProperty (Over D.S) := fun X =>
  IsIso ((Over.pullback D.complement.ι).obj X).hom

/-- The canonical restriction functor of Stacks Tag 0E8Q for the reindexed family of
distinguished points. -/
private noncomputable abbrev restriction : FinitePresentationOver D.S ⥤ D.GlueingDatum :=
  canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints

/-- The canonical restriction functor of Stacks Tag 0E8Q is fully faithful. -/
private noncomputable def restrictionFullyFaithful : D.restriction.FullyFaithful :=
  fullyFaithfulCanonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints
    D.liftedPoints_injective D.quasiCompact_complementOfClosedPoints_liftedPoints

/-- The property of a finitely presented scheme over `S` that it becomes an isomorphism over the
open complement of the situation. -/
private def openAwayFinitePresentationProperty :
    ObjectProperty (FinitePresentationOver D.S) :=
  D.openAwayProperty.inverseImage (isFinitePresentationOver D.S).ι

/-- The property of a finitely presented scheme over `S` that its glueing datum has trivial open
component. -/
private noncomputable def trivialOpenGlueProperty :
    ObjectProperty (FinitePresentationOver D.S) :=
  D.trivialOpenProperty.inverseImage D.restriction

/-- The global category of the situation is the full subcategory of the finitely presented
schemes over `S` on those which become isomorphisms over the open complement. -/
private noncomputable def globalToOpenAway :
    D.globalCategory ≌ D.openAwayFinitePresentationProperty.FullSubcategory :=
  have hGlobal : (isFinitePresentationOver D.S ⊓ D.openAwayProperty) =
      IsFinitePresentationAway D.complement := by
    ext X
    rfl
  ((nestedFullSubcategoryEquivalence (isFinitePresentationOver D.S) D.openAwayProperty).trans
    (ObjectProperty.fullSubcategoryCongr hGlobal)).symm

/-- For a finitely presented scheme over `S`, becoming an isomorphism over the open complement
of the situation is the same as having trivial open component in its glueing datum: the open
complement formed from the reindexed family is the one of the situation. -/
private theorem openAwayFinitePresentationProperty_eq :
    D.openAwayFinitePresentationProperty = D.trivialOpenGlueProperty := by
  ext X
  exact isIso_pullback_ι_obj_hom_iff_of_eq D.complementOfClosedPoints_liftedPoints.symm X.obj

/-- The restriction functor of Stacks Tag 0E8Q, cut down to the glueing data with trivial open
component. -/
private noncomputable abbrev trivialOpenRestriction :
    D.trivialOpenGlueProperty.FullSubcategory ⥤ D.trivialOpenProperty.FullSubcategory :=
  D.trivialOpenProperty.lift (D.trivialOpenGlueProperty.ι ⋙ D.restriction) fun X => X.property

/-- Base change to the spectra of the local rings, as the composite of the reduction chain: the
global category is the category of glueing data with trivial open component, and such a datum is
its family of local components. -/
private noncomputable abbrev localRestrictionFunctor :
    D.globalCategory ⥤ (∀ i, D.localCategory i) :=
  D.globalToOpenAway.functor ⋙
    (ObjectProperty.fullSubcategoryCongr D.openAwayFinitePresentationProperty_eq).functor ⋙
      D.trivialOpenRestriction ⋙
        D.localAwayProjection ⋙ D.localAwayToLocalCategoryEquivalence.functor

/-- The restriction functor cut down to the glueing data with trivial open component is full: it
is a lift of the restriction functor, which is full. -/
private theorem trivialOpenRestriction_full : D.trivialOpenRestriction.Full := by
  have := D.restrictionFullyFaithful.full
  have := D.restrictionFullyFaithful.faithful
  exact Functor.Full.of_comp_faithful_iso
    (D.trivialOpenProperty.liftCompιIso (D.trivialOpenGlueProperty.ι ⋙ D.restriction)
      fun X => X.property)

/-- The composite of the reduction chain is full: every factor is, the one coming from the
glueing theorem because the restriction functor is fully faithful and the others because they
are equivalences. -/
private theorem localRestrictionFunctor_full : D.localRestrictionFunctor.Full := by
  have := D.trivialOpenRestriction_full
  have := D.localAwayProjection_full
  change (D.globalToOpenAway.functor ⋙
    (ObjectProperty.fullSubcategoryCongr D.openAwayFinitePresentationProperty_eq).functor ⋙
      D.trivialOpenRestriction ⋙
        D.localAwayProjection ⋙ D.localAwayToLocalCategoryEquivalence.functor).Full
  infer_instance

/-- Granted the glueing theorem of Stacks Tag 0E8Q, the restriction functor cut down to the
glueing data with trivial open component is an equivalence. -/
private theorem trivialOpenRestriction_isEquivalence
    (hE : GlueingNearClosedPointsEquivalence.{u}) :
    D.trivialOpenRestriction.IsEquivalence :=
  have : D.restriction.IsEquivalence := hE D.liftedPoints D.liftedPoints_mem_closedPoints
    D.liftedPoints_injective D.quasiCompact_complementOfClosedPoints_liftedPoints
  (D.restriction.asEquivalence.congrFullSubcategory
    (Q := D.trivialOpenProperty) (P := D.trivialOpenGlueProperty) rfl).isEquivalence_functor

/-- Granted the glueing theorem of Stacks Tag 0E8Q, the composite of the reduction chain is an
equivalence. -/
private theorem localRestrictionFunctor_isEquivalence
    (hE : GlueingNearClosedPointsEquivalence.{u}) :
    D.localRestrictionFunctor.IsEquivalence := by
  have := D.trivialOpenRestriction_isEquivalence hE
  have := D.localAwayProjection_isEquivalence
  infer_instance

/-- Every component of the composite of the reduction chain is base change along the canonical
morphism from the spectrum of the corresponding local ring. -/
private noncomputable def localRestrictionFunctorComponentIso (i : Fin D.n) :
    D.localRestrictionFunctor ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ≅
      ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i)) := by
  refine NatIso.ofComponents (fun X => Iso.refl _) ?_
  intro X Y f
  simp only [Iso.refl_hom]
  exact rfl

/-- Two functors to the product of the local categories which agree componentwise, after
passage to the ambient over-categories, are isomorphic: an isomorphism of a dependent product
is a family of isomorphisms, and a morphism of a full subcategory is one of the ambient
category. -/
private noncomputable def isoOfComponentIsos {G G' : D.globalCategory ⥤ (∀ i, D.localCategory i)}
    (γ : ∀ i, G ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
          ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ≅
        G' ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
          ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))) :
    G ≅ G' := by
  apply NatIso.ofComponents (fun X => by
    let f : G.obj X ⟶ G'.obj X := fun i =>
      (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i))
        ((γ i).app X)).hom
    have : IsIso f := (isIso_pi_iff f).2 fun i =>
      (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i))
        ((γ i).app X)).isIso_hom
    exact asIso f) (by
      intro X Y f
      funext i
      apply ObjectProperty.hom_ext
      change ((G ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
          ObjectProperty.ι (IsFinitePresentationAway
            (D.puncturedLocalScheme i))).map f ≫ (γ i).hom.app Y) =
        ((γ i).hom.app X ≫
          (G' ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
            ObjectProperty.ι (IsFinitePresentationAway
              (D.puncturedLocalScheme i))).map f)
      exact (γ i).hom.naturality f)

/-- The composite of the reduction chain is isomorphic to any functor carrying the canonical
identifications with base change to the spectra of the local rings. -/
private noncomputable def localRestrictionFunctorIso (B : BaseChangeFunctor D) :
    D.localRestrictionFunctor ≅ B.functor :=
  D.isoOfComponentIsos fun i =>
    D.localRestrictionFunctorComponentIso i ≪≫ (B.pullbackIso i).symm

/-- Granted the glueing theorem of Stacks Tag 0E8Q, the global category of the situation is the
category of glueing data with trivial open component. This is the reduction chain stopped before
the projection to the local components, with its one non-equivalence factor
`trivialOpenRestriction` upgraded by the glueing hypothesis. -/
private noncomputable def globalToTrivialOpenGlueing
    (hE : GlueingNearClosedPointsEquivalence.{u}) :
    D.globalCategory ≌ D.trivialOpenProperty.FullSubcategory :=
  haveI := D.trivialOpenRestriction_isEquivalence hE
  (D.globalToOpenAway.trans
      (ObjectProperty.fullSubcategoryCongr D.openAwayFinitePresentationProperty_eq)).trans
    D.trivialOpenRestriction.asEquivalence

/-- Granted the glueing theorem of Stacks Tag 0E8Q, base change to the spectra of the local
rings is an equivalence from the global category onto the product of the local categories. This
is the whole reduction chain, read as an equivalence. -/
private noncomputable def baseChangeEquivalence (hE : GlueingNearClosedPointsEquivalence.{u}) :
    D.globalCategory ≌ (∀ i, D.localCategory i) :=
  haveI := D.localRestrictionFunctor_isEquivalence hE
  D.localRestrictionFunctor.asEquivalence

/-- Every component of the constructed equivalence is base change along the canonical morphism
from the spectrum of the corresponding local ring. -/
private noncomputable def baseChangeEquivalenceComponentIso
    (hE : GlueingNearClosedPointsEquivalence.{u}) (i : Fin D.n) :
    (D.baseChangeEquivalence hE).functor ⋙ Pi.eval (fun i => D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ≅
      ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i)) :=
  D.localRestrictionFunctorComponentIso i

end FinitePresentationAwayPointsSituation

/-- **Stacks Project, Tag 0BFV**, the fullness constituent of the equivalence. Any functor
carrying the canonical identifications with base change to the spectra of the local rings — in
particular the one of [Stacks, Tag 0BFU] — is full, with no hypotheses.

The restriction functor of the glueing theorem [Stacks, Tag 0E8Q] is fully faithful by
`AlgebraicGeometry.fullyFaithfulCanonicalRestrictionFunctor`, and every other factor of the
reduction chain is an equivalence, so the chain is full; the chain and this functor are
isomorphic.

Essential surjectivity, which Tag 0BFV deduces from [Stacks, Tag 0B3X] and its glueing input
[Stacks, Tag 0BPA], is not part of this statement.

The tag is carried by `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_full`, the
specialization of this statement to the functor Tag 0BFU displays. -/
theorem BaseChangeFunctor.full {D : FinitePresentationAwayPointsSituation.{u}}
    (B : BaseChangeFunctor D) : B.functor.Full :=
  have := D.localRestrictionFunctor_full
  Functor.Full.of_iso (D.localRestrictionFunctorIso B)

/-- **Stacks Project, Tag 0BFV**, the fullness constituent of the equivalence. Base change from
finitely presented modifications supported at finitely many closed points to the corresponding
local modifications is full.

With `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_faithful` this says that the
functor is fully faithful: a global modification supported at the distinguished points is
determined by its family of localizations, up to a unique isomorphism over `S`. -/
@[stacks 0BFV "full"]
theorem finitePresentationAwayPointsBaseChange_full
    (D : FinitePresentationAwayPointsSituation.{u}) :
    (finitePresentationAwayPointsBaseChange D).functor.Full :=
  (finitePresentationAwayPointsBaseChange D).full

/-- Base change to the spectra of the local rings is fully faithful: it is full by
`AlgebraicGeometry.BaseChangeFunctor.full` and faithful by
`AlgebraicGeometry.BaseChangeFunctor.faithful`, both unconditionally. This is the form in which
the two constituents are used: it takes an isomorphism between the families of localizations of
two global modifications to an isomorphism over `S`. -/
noncomputable def BaseChangeFunctor.fullyFaithful {D : FinitePresentationAwayPointsSituation.{u}}
    (B : BaseChangeFunctor D) : B.functor.FullyFaithful :=
  haveI := B.full
  haveI := B.faithful
  .ofFullyFaithful _

/-- **Stacks Project, Tag 0BFV**, granted the glueing theorem of Tag 0E8Q. Any functor carrying
the canonical identifications with base change to the spectra of the local rings — in
particular the one of [Stacks, Tag 0BFU] — is an equivalence of categories.

The hypothesis is the equivalence assertion of [Stacks, Tag 0E8Q]; this declaration does not
carry the tag 0BFV. -/
theorem BaseChangeFunctor.isEquivalence (hE : GlueingNearClosedPointsEquivalence.{u})
    {D : FinitePresentationAwayPointsSituation.{u}} (B : BaseChangeFunctor D) :
    B.functor.IsEquivalence :=
  have := D.localRestrictionFunctor_isEquivalence hE
  (Functor.isEquivalence_iff_of_iso (D.localRestrictionFunctorIso B)).mp inferInstance

/-- **Stacks Project, Tag 0BFV**, granted the glueing theorem of Tag 0E8Q. Base change from
finitely presented modifications supported at finitely many closed points to the corresponding
local modifications is an equivalence of categories.

The hypothesis is the equivalence assertion of [Stacks, Tag 0E8Q]; this declaration does not
carry the tag 0BFV. -/
theorem finitePresentationAwayPointsBaseChange_isEquivalence
    (hE : GlueingNearClosedPointsEquivalence.{u})
    (D : FinitePresentationAwayPointsSituation.{u}) :
    (finitePresentationAwayPointsBaseChange D).functor.IsEquivalence :=
  (finitePresentationAwayPointsBaseChange D).isEquivalence hE

end AlgebraicGeometry

end
