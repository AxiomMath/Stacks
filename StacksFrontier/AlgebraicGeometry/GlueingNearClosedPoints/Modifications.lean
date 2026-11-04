module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Germ
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.FibreProduct
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalence

/-!
# Modifications of a scheme at a closed point

Let `S` be a scheme and let `s` be a closed point of `S` whose open complement
`U = S ∖ {s}` has quasi-compact inclusion.  Write `S_s = Spec 𝒪_{S, s}` for the local scheme at
`s` and `V = S_s ∖ {𝔪_s}` for the punctured spectrum of the local ring, which is the preimage of
`U` in `S_s`.  A *modification of `S` at `s`* is a morphism `X ⟶ S` of finite presentation which
restricts to an isomorphism over `U`.

This file proves that base change along `Spec 𝒪_{S, s} ⟶ S` is an equivalence from the category
of modifications of `S` at `s` onto the category of modifications of `Spec 𝒪_{S, s}` at its
closed point.

## Main definitions

* `AlgebraicGeometry.GlueingNearPoint.finitePresentationAwayBaseChange`: base change along
  `Spec 𝒪_{S, s} ⟶ S`, from finitely presented morphisms to `S` which are isomorphisms over
  `S ∖ {s}` to finitely presented morphisms to `Spec 𝒪_{S, s}` which are isomorphisms over the
  punctured spectrum.

## Main results

* `AlgebraicGeometry.GlueingNearPoint.preimage_puncturedOpen`: the preimage of `S ∖ {s}` in
  `Spec 𝒪_{S, s}` is the complement of the closed point.
* `AlgebraicGeometry.GlueingNearPoint.finitePresentationAwayBaseChange_isEquivalence`:
  [Stacks, Tag 0B3X], that base-change functor is an equivalence of categories.

## Implementation notes

The proof is the reduction of [Stacks, Tag 0B3X] to the glueing theorem of
[Stacks, Tag 0BPA], which presents a scheme of finite presentation over `S` as a scheme over
`U`, a scheme over `S_s`, and a glueing isomorphism over `V`.  Cutting that presentation down to
the objects which become isomorphisms over `U` makes the component over `U` the identity, so a
glueing datum is then determined by its component over `S_s`; this is the projection
`localAwayProjection` below, shown to be an equivalence by hand.  Composing produces an
equivalence whose underlying functor is literally the base-change functor, so the conclusion
transfers along an equality of functors.

## References

* [Stacks Project, Lemma 32.21.1 (0B3X)](https://stacks.math.columbia.edu/tag/0B3X)
* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry.GlueingNearPoint

/-! ### Generalities on over-categories and full subcategories -/

/-- Invertibility of the structure morphism of an object of `Over T` depends only on its
isomorphism class. -/
private alias over_isIso_hom_iff_of_iso := CategoryTheory.Over.isIso_hom_iff_isIso_hom_of_iso

/-- An object of `Over T` whose structure morphism is invertible is terminal, so any two
morphisms into it agree. -/
private theorem over_hom_ext_of_isIso_hom {C : Type u} [Category.{v} C] {T : C} {X Y : Over T}
    [IsIso Y.hom] (f g : X ⟶ Y) : f = g := by
  apply CostructuredArrow.hom_ext
  exact (cancel_mono Y.hom).mp (by rw [Over.w f, Over.w g])

/-- Two objects of `Over T` with invertible structure morphisms are canonically isomorphic. -/
private noncomputable def overIsoOfIsIsoHom {C : Type u} [Category.{v} C] {T : C} (X Y : Over T)
    [IsIso X.hom] [IsIso Y.hom] : X ≅ Y :=
  Over.isoMk (asIso X.hom ≪≫ (asIso Y.hom).symm)

/-- Alias of `CategoryTheory.Over.isIso_pullback_snd`. -/
private alias isIso_pullback_snd := CategoryTheory.Over.isIso_pullback_snd

/-! ### The punctured spectrum of the local ring -/

/-- The preimage in `Spec 𝒪_{S, s}` of the complement of `s` is the complement of the closed
point, that is, the punctured spectrum of the local ring at `s`. -/
theorem preimage_puncturedOpen {S : Scheme.{u}} {s : S} (hs : IsClosed ({s} : Set S)) :
    (S.fromSpecStalk s) ⁻¹ᵁ (puncturedOpen hs) =
      ⟨{IsLocalRing.closedPoint (S.presheaf.stalk s)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩ := by
  ext p
  show S.fromSpecStalk s p ∈ ({s} : Set S)ᶜ ↔
    p ∈ ({IsLocalRing.closedPoint (S.presheaf.stalk s)}ᶜ :
      Set (Spec (S.presheaf.stalk s)))
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro h rfl
    exact h Scheme.fromSpecStalk_closedPoint
  · intro h hp
    exact h ((S.fromSpecStalk s).isEmbedding.injective
      (hp.trans Scheme.fromSpecStalk_closedPoint.symm))

/-! ### The base-change functor -/

/-- The property of an object of `Over S` that its restriction to the open `U` is an
isomorphism. -/
private def openAwayProperty (S : Scheme.{u}) (U : S.Opens) : ObjectProperty (Over S) :=
  fun X ↦ IsIso ((Over.pullback U.ι).obj X).hom

/-- Modifications away from `U` are the finitely presented objects of `Over S` which are
isomorphisms over `U`. -/
private noncomputable def finitePresentationAwayEquivalence (S : Scheme.{u}) (U : S.Opens) :
    FinitePresentationAway U ≌
      ((openAwayProperty S U).inverseImage (isFinitePresentationOver S).ι).FullSubcategory :=
  ((nestedFullSubcategoryEquivalence (isFinitePresentationOver S) (openAwayProperty S U)).trans
    (ObjectProperty.fullSubcategoryCongr (rfl :
      (isFinitePresentationOver S ⊓ openAwayProperty S U) =
        IsFinitePresentationAway U))).symm

/-- Base change of a finitely presented morphism which is an isomorphism over `U` is a finitely
presented morphism which is an isomorphism over the preimage of `U`. -/
theorem isFinitePresentationAway_pullback {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Opens)
    (X : Over S) (hX : IsFinitePresentationAway U X) :
    IsFinitePresentationAway (g ⁻¹ᵁ U) ((Over.pullback g).obj X) := by
  refine ⟨?_, ?_⟩
  · have : LocallyOfFinitePresentation X.hom := hX.1.1
    have : QuasiCompact X.hom := hX.1.2.1
    have : QuasiSeparated X.hom := hX.1.2.2
    show FinitePresentation (pullback.snd X.hom g)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · have : IsIso ((Over.pullback U.ι).obj X).hom := hX.2
    have hB : IsIso ((Over.pullback (g ∣_ U)).obj ((Over.pullback U.ι).obj X)).hom := by
      show IsIso (pullback.snd ((Over.pullback U.ι).obj X).hom (g ∣_ U))
      infer_instance
    let iso₁ : (Over.pullback ((g ∣_ U) ≫ U.ι)).obj X ≅
        (Over.pullback (g ∣_ U)).obj ((Over.pullback U.ι).obj X) :=
      (Over.pullbackComp (g ∣_ U) U.ι).app X
    let iso₂ : (Over.pullback ((g ⁻¹ᵁ U).ι ≫ g)).obj X ≅
        (Over.pullback (g ⁻¹ᵁ U).ι).obj ((Over.pullback g).obj X) :=
      (Over.pullbackComp (g ⁻¹ᵁ U).ι g).app X
    let isoW : (Over.pullback ((g ∣_ U) ≫ U.ι)).obj X ≅
        (Over.pullback ((g ⁻¹ᵁ U).ι ≫ g)).obj X :=
      (eqToIso (congrArg (fun f ↦ Over.pullback f) (morphismRestrict_ι g U))).app X
    exact (over_isIso_hom_iff_of_iso (iso₁.symm ≪≫ isoW ≪≫ iso₂)).mp hB

/-- **Stacks Project, Tag 0B3X**, the functor.  Base change along `Spec 𝒪_{S, s} ⟶ S` takes a
finitely presented morphism to `S` which is an isomorphism over `S ∖ {s}` to a finitely
presented morphism to `Spec 𝒪_{S, s}` which is an isomorphism over the punctured spectrum. -/
noncomputable def finitePresentationAwayBaseChange (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) :
    FinitePresentationAway (puncturedOpen hs) ⥤
      FinitePresentationAway ((S.fromSpecStalk s) ⁻¹ᵁ (puncturedOpen hs)) :=
  ObjectProperty.lift _
    ((IsFinitePresentationAway (puncturedOpen hs)).ι ⋙ Over.pullback (S.fromSpecStalk s))
    (fun X ↦ isFinitePresentationAway_pullback (S.fromSpecStalk s) (puncturedOpen hs)
      X.obj X.property)

/-! ### Discarding the trivial component of a glueing datum -/

/-- The property of a glueing datum near `s` that its component over `U` is trivial, that is,
that the structure morphism of its component over `U` is an isomorphism. -/
private def trivialOpenProperty (S : Scheme.{u}) (U : S.Opens) (s : S) :
    ObjectProperty (glueingDataNearPoint S U s) :=
  fun Z ↦ IsIso ((openComponent S U s).obj Z).hom

private instance trivialOpenProperty_isClosedUnderIsomorphisms (S : Scheme.{u}) (U : S.Opens)
    (s : S) : (trivialOpenProperty S U s).IsClosedUnderIsomorphisms where
  of_iso e h := (over_isIso_hom_iff_of_iso ((openComponent S U s).mapIso e)).mp h

/-- The property of a finitely presented scheme over `Spec 𝒪_{S, s}` that its restriction to the
preimage of `U` is an isomorphism. -/
private def localAwayProperty (S : Scheme.{u}) (U : S.Opens) (s : S) :
    ObjectProperty (FinitePresentationOver (Spec (S.presheaf.stalk s))) :=
  (openAwayProperty (Spec (S.presheaf.stalk s)) ((S.fromSpecStalk s) ⁻¹ᵁ U)).inverseImage
    (isFinitePresentationOver (Spec (S.presheaf.stalk s))).ι

/-- The projection of a glueing datum with trivial component over `U` to its component over
`Spec 𝒪_{S, s}`. -/
private noncomputable def localAwayProjection (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (trivialOpenProperty S U s).FullSubcategory ⥤ (localAwayProperty S U s).FullSubcategory where
  obj X := ⟨X.obj.obj.right, by
    have : IsIso X.obj.obj.left.obj.hom := X.property
    have hA : IsIso ((restrictOpenToPuncturedLocal S U s).obj X.obj.obj.left).obj.hom := by
      change IsIso (pullback.snd X.obj.obj.left.obj.hom ((S.fromSpecStalk s) ∣_ U))
      infer_instance
    have : IsIso X.obj.obj.hom := X.obj.property
    exact (over_isIso_hom_iff_of_iso (asIso X.obj.obj.hom.hom)).mp hA⟩
  map f := ObjectProperty.homMk f.hom.hom.right

private theorem localAwayProjection_faithful (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (localAwayProjection S U s).Faithful := by
  constructor
  intro X Y f g h
  apply (trivialOpenProperty S U s).hom_ext
  apply (show ObjectProperty (Comma (restrictOpenToPuncturedLocal S U s)
    (restrictLocalToPuncturedLocal S U s)) from fun Z ↦ IsIso Z.hom).hom_ext
  apply Comma.hom_ext
  · apply (isFinitePresentationOver U.toScheme).hom_ext
    have : IsIso Y.obj.obj.left.obj.hom := Y.property
    exact over_hom_ext_of_isIso_hom f.hom.hom.left.hom g.hom.hom.left.hom
  · exact congrArg (fun k ↦ k.hom) h

private theorem localAwayProjection_full (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (localAwayProjection S U s).Full := by
  constructor
  intro X Y f
  have : IsIso X.obj.obj.left.obj.hom := X.property
  have : IsIso Y.obj.obj.left.obj.hom := Y.property
  let leftIso : X.obj.obj.left.obj ≅ Y.obj.obj.left.obj := overIsoOfIsIsoHom _ _
  let cmp : X.obj.obj ⟶ Y.obj.obj :=
    { left := ObjectProperty.homMk leftIso.hom
      right := f.hom
      w := by
        apply (isFinitePresentationOver (puncturedLocalScheme S U s)).hom_ext
        have : IsIso ((restrictLocalToPuncturedLocal S U s).obj Y.obj.obj.right).obj.hom :=
          ((localAwayProjection S U s).obj Y).property
        exact over_hom_ext_of_isIso_hom _ _ }
  refine ⟨ObjectProperty.homMk (ObjectProperty.homMk cmp), ?_⟩
  apply (localAwayProperty S U s).hom_ext
  rfl

/-- The identity, as a finitely presented scheme over `U`. -/
private noncomputable def trivialOpenObject {S : Scheme.{u}} (U : S.Opens) :
    FinitePresentationOver U.toScheme :=
  ⟨Over.mk (𝟙 U.toScheme), by
    change FinitePresentation (𝟙 U.toScheme)
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

private theorem localAwayProjection_essSurj (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (localAwayProjection S U s).EssSurj := by
  constructor
  intro X
  let O := trivialOpenObject U
  let A := (restrictOpenToPuncturedLocal S U s).obj O
  let B := (restrictLocalToPuncturedLocal S U s).obj X.obj
  have hId : IsIso O.obj.hom := by
    show IsIso (𝟙 U.toScheme)
    infer_instance
  have : IsIso A.obj.hom := by
    show IsIso (pullback.snd O.obj.hom ((S.fromSpecStalk s) ∣_ U))
    infer_instance
  have : IsIso B.obj.hom := X.property
  let e : A ≅ B := (isFinitePresentationOver (puncturedLocalScheme S U s)).isoMk
    (overIsoOfIsIsoHom A.obj B.obj)
  let Z : glueingDataNearPoint S U s := ⟨⟨O, X.obj, e.hom⟩, inferInstance⟩
  exact ⟨⟨Z, show IsIso O.obj.hom from hId⟩,
    ⟨ObjectProperty.isoMk (localAwayProperty S U s) (Iso.refl X.obj)⟩⟩

private theorem localAwayProjection_isEquivalence (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (localAwayProjection S U s).IsEquivalence :=
  Functor.IsEquivalence.mk (localAwayProjection_faithful S U s)
    (localAwayProjection_full S U s) (localAwayProjection_essSurj S U s)

/-! ### The equivalence -/

/-- The category of modifications of `S` at the closed point `s` is the category of glueing data
of Stacks Tag 0BPA whose component over `S ∖ {s}` is trivial. -/
private noncomputable def globalToTrivialOpenGlueing (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    FinitePresentationAway (puncturedOpen hs) ≌
      (trivialOpenProperty S (puncturedOpen hs) s).FullSubcategory := by
  have hF := restrictionFunctorAtPoint_isEquivalence S s hs hqc
  let E : FinitePresentationOver S ≌ glueingDataNearPoint S (puncturedOpen hs) s :=
    (restrictionFunctorAtPoint S (puncturedOpen hs) s).asEquivalence
  let Popen : ObjectProperty (FinitePresentationOver S) :=
    (openAwayProperty S (puncturedOpen hs)).inverseImage (isFinitePresentationOver S).ι
  let Pglue : ObjectProperty (FinitePresentationOver S) :=
    (trivialOpenProperty S (puncturedOpen hs) s).inverseImage E.functor
  have hP : Popen = Pglue := rfl
  let p := ObjectProperty.fullSubcategoryCongr hP
  let e := E.congrFullSubcategory (Q := trivialOpenProperty S (puncturedOpen hs) s)
    (P := Pglue) rfl
  exact (finitePresentationAwayEquivalence S (puncturedOpen hs)).trans (p.trans e)

/-- Finitely presented schemes over `Spec 𝒪_{S, s}` which are isomorphisms over the preimage of
`U` are the modifications of `Spec 𝒪_{S, s}` away from that preimage. -/
private noncomputable def localAwayToAwayEquivalence (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (localAwayProperty S U s).FullSubcategory ≌
      FinitePresentationAway ((S.fromSpecStalk s) ⁻¹ᵁ U) :=
  (finitePresentationAwayEquivalence _ _).symm

/-- The equivalence of Stacks Tag 0B3X, obtained from the glueing theorem of Stacks Tag 0BPA by
discarding the trivial component of a glueing datum. -/
private noncomputable def awayBaseChangeEquivalence (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    FinitePresentationAway (puncturedOpen hs) ≌
      FinitePresentationAway ((S.fromSpecStalk s) ⁻¹ᵁ (puncturedOpen hs)) :=
  have : (localAwayProjection S (puncturedOpen hs) s).IsEquivalence :=
    localAwayProjection_isEquivalence S (puncturedOpen hs) s
  (globalToTrivialOpenGlueing S s hs hqc).trans
    ((localAwayProjection S (puncturedOpen hs) s).asEquivalence.trans
      (localAwayToAwayEquivalence S (puncturedOpen hs) s))

/-- The equivalence constructed from Stacks Tag 0BPA is base change along
`Spec 𝒪_{S, s} ⟶ S`. -/
private theorem awayBaseChangeEquivalence_functor (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (awayBaseChangeEquivalence S s hs hqc).functor =
      finitePresentationAwayBaseChange S s hs :=
  rfl

/-- **Stacks Project, Tag 0B3X.** Let `s` be a closed point of a scheme `S` whose open
complement `U = S ∖ {s}` has quasi-compact inclusion.  Base change along
`Spec 𝒪_{S, s} ⟶ S` is an equivalence from the category of finitely presented morphisms to `S`
which are isomorphisms over `U` onto the category of finitely presented morphisms to
`Spec 𝒪_{S, s}` which are isomorphisms over the punctured spectrum. -/
@[stacks 0B3X]
theorem finitePresentationAwayBaseChange_isEquivalence (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (finitePresentationAwayBaseChange S s hs).IsEquivalence := by
  rw [← awayBaseChangeEquivalence_functor S s hs hqc]
  exact (awayBaseChangeEquivalence S s hs hqc).isEquivalence_functor

end AlgebraicGeometry.GlueingNearPoint

end
