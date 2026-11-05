module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChangeGeneric
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeGluingMorphism
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal
import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.SquareGlueing
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeInitial
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Glueing schemes of finite presentation near a point

Let `S` be a scheme, let `U ⊆ S` be a retrocompact open and let `s` be a point of `S` outside
`U`.  Write `S_s = Spec 𝒪_{S, s}` for the local scheme at `s` and `V` for the preimage of `U`
in `S_s`.  A scheme of finite presentation over an open neighbourhood `U'` of `U ∪ {s}`
restricts to one over `U` and to one over `S_s`, and these restrictions agree over `V`.  This
file proves that, after passing to the germ at `s` on the left, that assignment is an
equivalence of categories.

## Main definitions

* `AlgebraicGeometry.GlueingNearPoint.OpenNeighborhood`: an open neighbourhood of `s`
  containing `U`.
* `AlgebraicGeometry.GlueingNearPoint.FinitePresentationNeighborhoodModel`: a scheme of finite
  presentation over such a neighbourhood, together with the neighbourhood it lives over.
* `AlgebraicGeometry.GlueingNearPoint.FinitePresentationNeighborhoodModel.restrictionMorphisms`:
  the morphisms of models which exhibit the source as the restriction of the target.
* `AlgebraicGeometry.GlueingNearPoint.FinitePresentationGerm`: the filtered 2-colimit on the
  left of the source statement, modelled as the localization of the category of neighbourhood
  models at the restriction morphisms.
* `AlgebraicGeometry.GlueingNearPoint.puncturedLocalScheme`: the preimage of `U` in `S_s`.
* `AlgebraicGeometry.GlueingNearPoint.glueingDataNearPoint`: the category on the right of the
  source statement, namely the iso-comma category of the two restriction functors into schemes
  of finite presentation over `V`.
* `AlgebraicGeometry.GlueingNearPoint.canonicalOverlapIso`: the canonical comparison between
  the two iterated base changes of a scheme over `S` to `V`.
* `AlgebraicGeometry.GlueingNearPoint.overlapComparisonCompatible`: the condition that an
  equivalence intertwines the comparison carried by a glueing datum with
  `canonicalOverlapIso`.

## Main results

* `AlgebraicGeometry.GlueingNearPoint.glueingEquivalenceNearPoint`: Stacks 0BQ5.  The germ of
  the categories of schemes of finite presentation over the open neighbourhoods of `U ∪ {s}` is
  equivalent to the category of glueing data on `U` and `S_s`, by an equivalence whose two
  projections are identified with base change along `U ⟶ S` and along `S_s ⟶ S`, compatibly
  with the canonical comparison over `V`.

## Implementation notes

The filtered 2-colimit on the left of the source statement is represented by the localization
of the total category of neighbourhood models at the morphisms whose square over an inclusion
of neighbourhoods is cartesian.  That morphism property admits a calculus of right fractions,
so the localization is computed by `Localization.Construction` and the equivalence is obtained
from `localizationLift_isEquivalence_of_rightFractions`: it suffices to exhibit the comparison
functor out of the category of models as essentially surjective, and full and faithful up to
right fractions.

On the right, the two cartesian squares of the source statement are equivalently recorded by a
single isomorphism between the two restrictions to `V`; that is the iso-comma category
`glueingDataNearPoint`.  Because an object of an iso-comma category carries its comparison
isomorphism as data, the equivalence must be asserted together with natural identifications of
its two component functors with base change *and* with the compatibility of those
identifications with `canonicalOverlapIso` on the overlap; otherwise only the two vertices of
the restriction diagram, and not the diagram, would be pinned down.

Essential surjectivity is where the hypotheses enter.  `Spec 𝒪_{S, s}` is the limit of the
affine open neighbourhoods of `s` (`affineNeighborhoodIsLimit`), and retrocompactness of `U`
makes `V` the limit of the quasi-compact quasi-separated schemes `W ∩ U`
(`affineNeighborhoodOverlapIsLimit`), so Stacks 01ZM descends a glueing datum to a finite
stage; glueing the descended data along `U ∩ W` over `U ∪ W` produces a neighbourhood model,
using the relative glueing of Stacks 01LG in the form of
`AlgebraicGeometry.CompatibleRelativeGluingData`.

## References

* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Lemma 32.14.3 (0BQ5)](https://stacks.math.columbia.edu/tag/0BQ5)
* [Stacks Project, Proposition 32.5.4 (01ZM)](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Lemma 32.4.5 (01YX)](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.GenericFlatness (finitePresentation_pullback)

namespace AlgebraicGeometry.GlueingNearPoint


universe u

/-- An open neighbourhood of `s` which contains the fixed open `U`. -/
public structure OpenNeighborhood (S : Scheme.{u}) (U : S.Opens) (s : S) where
  /-- The underlying open neighbourhood. -/
  V : S.Opens
  /-- The fixed open is contained in the neighbourhood. -/
  le_V : U ≤ V
  /-- The distinguished point belongs to the neighbourhood. -/
  mem_V : s ∈ V

/-- A scheme of finite presentation over an open neighbourhood of `U ∪ {s}`. -/
public structure FinitePresentationNeighborhoodModel
    (S : Scheme.{u}) (U : S.Opens) (s : S) where
  /-- An open neighbourhood on which the model is defined. -/
  neighborhood : OpenNeighborhood S U s
  /-- The source scheme of the model. -/
  source : Scheme.{u}
  /-- The structure morphism to the neighbourhood. -/
  hom : source ⟶ neighborhood.V.toScheme
  /-- The structure morphism is of finite presentation. -/
  finitePresentation : FinitePresentation hom

namespace FinitePresentationNeighborhoodModel

variable {S : Scheme.{u}} {U : S.Opens} {s : S}

/-- A map of neighbourhood models consists of an inclusion of their bases and a compatible map
of their source schemes. -/
public structure Hom (X Y : FinitePresentationNeighborhoodModel S U s) where
  /-- Inclusion of the neighbourhood of the source into that of the target. -/
  base_le : X.neighborhood.V ≤ Y.neighborhood.V
  /-- The map between the source schemes. -/
  left : X.source ⟶ Y.source
  /-- Compatibility with the structure maps. -/
  w : left ≫ Y.hom = X.hom ≫ S.homOfLE base_le

/-- Two maps of neighbourhood models agree once their maps of source schemes agree. -/
@[ext]
public lemma Hom.ext {X Y : FinitePresentationNeighborhoodModel S U s}
    (f g : Hom X Y) (h : f.left = g.left) : f = g := by
  cases f
  cases g
  simp_all

/-- Neighbourhood models of `U ∪ {s}` form a category, with the maps of `Hom`. -/
public instance : Category.{u} (FinitePresentationNeighborhoodModel S U s) where
  Hom := Hom
  id X := ⟨le_rfl, 𝟙 _, by simp⟩
  comp f g := ⟨f.base_le.trans g.base_le, f.left ≫ g.left, by
    rw [Category.assoc, g.w, ← Category.assoc, f.w]
    simp⟩
  id_comp f := Hom.ext _ _ (by change (𝟙 _) ≫ f.left = f.left; simp)
  comp_id f := Hom.ext _ _ (by change f.left ≫ (𝟙 _) = f.left; simp)
  assoc f g h := Hom.ext _ _ (by change (f.left ≫ g.left) ≫ h.left = _; simp)

/-- The morphisms which exhibit one neighbourhood model as the restriction of another. -/
public def restrictionMorphisms :
    MorphismProperty (FinitePresentationNeighborhoodModel S U s) :=
  fun X Y f => IsPullback f.left X.hom Y.hom (S.homOfLE f.base_le)

private noncomputable def restrictNeighborhood
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s)
    (N : OpenNeighborhood S U s) (hN : N.V ≤ X.neighborhood.V) :
    FinitePresentationNeighborhoodModel S U s where
  neighborhood := N
  source := pullback X.hom (S.homOfLE hN)
  hom := pullback.snd X.hom (S.homOfLE hN)
  finitePresentation := by
    have := X.finitePresentation.1
    have := X.finitePresentation.2.1
    have := X.finitePresentation.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩
private noncomputable def restrictNeighborhoodHom
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s)
    (N : OpenNeighborhood S U s) (hN : N.V ≤ X.neighborhood.V) :
    X.restrictNeighborhood N hN ⟶ X :=
  ⟨hN, pullback.fst _ _, pullback.condition⟩
private lemma restrictNeighborhoodHom_mem
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s)
    (N : OpenNeighborhood S U s) (hN : N.V ≤ X.neighborhood.V) :
    restrictionMorphisms (X.restrictNeighborhoodHom N hN) :=
  IsPullback.of_hasPullback _ _
private lemma restrictionMorphisms_multiplicative
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (restrictionMorphisms (S := S) (U := U) (s := s)).IsMultiplicative where
  id_mem X := by
    show IsPullback (𝟙 _) X.hom X.hom (S.homOfLE le_rfl)
    simpa using IsPullback.id_horiz X.hom
  comp_mem f g hf hg := by
    show IsPullback (f.left ≫ g.left) _ _ _
    simpa using hf.paste_horiz hg
attribute [local instance] restrictionMorphisms_multiplicative
private lemma restrictionMorphisms_rightCalculus
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (restrictionMorphisms (S := S) (U := U) (s := s)).HasRightCalculusOfFractions where
  exists_rightFraction {X Y} φ := by
    let N : OpenNeighborhood S U s :=
      ⟨X.neighborhood.V ⊓ Y.neighborhood.V,
        le_inf X.neighborhood.le_V Y.neighborhood.le_V,
        ⟨X.neighborhood.mem_V, Y.neighborhood.mem_V⟩⟩
    let P := X.restrictNeighborhood N inf_le_left
    let t : P ⟶ X := X.restrictNeighborhoodHom N inf_le_left
    have hs : IsPullback φ.s.left Y.hom φ.Y'.hom (S.homOfLE φ.s.base_le) := φ.hs
    have hw : (t.left ≫ φ.f.left) ≫ φ.Y'.hom =
        (P.hom ≫ S.homOfLE (show N.V ≤ Y.neighborhood.V from inf_le_right)) ≫
          S.homOfLE φ.s.base_le := by
      rw [Category.assoc, φ.f.w, ← Category.assoc, t.w]
      apply (cancel_mono φ.Y'.neighborhood.V.ι).1
      simp only [Category.assoc, Scheme.homOfLE_ι]
      exact congrArg (fun k ↦ P.hom ≫ k)
        (S.homOfLE_ι (show N.V ≤ Y.neighborhood.V from inf_le_right)).symm
    let f : P ⟶ Y :=
      ⟨inf_le_right, hs.lift (t.left ≫ φ.f.left) (P.hom ≫ S.homOfLE inf_le_right) hw,
        hs.lift_snd _ _ hw⟩
    refine ⟨⟨t, X.restrictNeighborhoodHom_mem N inf_le_left, f⟩, ?_⟩
    apply Hom.ext
    exact (hs.lift_fst _ _ hw).symm
  ext {X Y Y'} f g t ht hfg := by
    have : Mono t.left := (show IsPullback t.left Y.hom Y'.hom _ from ht).mono_fst_of_mono
    have h : f = g := by
      apply Hom.ext
      apply (cancel_mono t.left).1
      exact congrArg (fun k ↦ k.left) hfg
    exact ⟨X, 𝟙 X, MorphismProperty.id_mem _ X, by rw [h]⟩

end FinitePresentationNeighborhoodModel

/-- The filtered 2-colimit of categories of finite-presentation schemes over open
neighbourhoods of `U ∪ {s}`.  It is modeled by inverting cartesian restriction morphisms in
the total category of neighbourhood models. -/
public abbrev FinitePresentationGerm (S : Scheme.{u}) (U : S.Opens) (s : S) :=
  (FinitePresentationNeighborhoodModel.restrictionMorphisms
    (S := S) (U := U) (s := s)).Localization

/-- The intersection of `U` with the local scheme of `S` at `s`. -/
public noncomputable abbrev puncturedLocalScheme
    (S : Scheme.{u}) (U : S.Opens) (s : S) : Scheme.{u} :=
  ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme

/-- Restriction from `U` to its pullback to the local scheme at `s`. -/
public noncomputable def restrictOpenToPuncturedLocal
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationOver U.toScheme ⥤
      FinitePresentationOver (puncturedLocalScheme S U s) :=
  finitePresentationBaseChange ((S.fromSpecStalk s) ∣_ U)

/-- Restriction from the local scheme at `s` to the inverse image of `U`. -/
public noncomputable def restrictLocalToPuncturedLocal
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationOver (Spec (S.presheaf.stalk s)) ⥤
      FinitePresentationOver (puncturedLocalScheme S U s) :=
  finitePresentationBaseChange (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)

/-- Compatible finite-presentation schemes over `U` and over the local scheme at `s`.

The comparison isomorphism on the punctured local scheme is equivalent to the pair of
cartesian squares appearing in the source. -/
public abbrev glueingDataNearPoint (S : Scheme.{u}) (U : S.Opens) (s : S) :=
  IsoComma (restrictOpenToPuncturedLocal S U s) (restrictLocalToPuncturedLocal S U s)

/-- Forget the neighbourhood, retaining the scheme's map to the ambient scheme. -/
public def neighborhoodModelToAmbient (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤ Over S where
  obj X := Over.mk (X.hom ≫ X.neighborhood.V.ι)
  map := fun {X Y} f => Over.homMk f.left (by
    change f.left ≫ (Y.hom ≫ Y.neighborhood.V.ι) =
      X.hom ≫ X.neighborhood.V.ι
    rw [← Category.assoc, f.w, Category.assoc, S.homOfLE_ι])

/-- The open component of compatible gluing data, with its finite-presentation proof forgotten. -/
public noncomputable def openComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    glueingDataNearPoint S U s ⥤ Over U.toScheme where
  obj Z := Z.1.left.obj
  map f := f.hom.left.hom

/-- The local component of compatible gluing data, with its finite-presentation proof forgotten. -/
public noncomputable def localComponent (S : Scheme.{u}) (U : S.Opens) (s : S) :
    glueingDataNearPoint S U s ⥤ Over (Spec (S.presheaf.stalk s)) where
  obj Z := Z.1.right.obj
  map f := f.hom.right.hom

/-- The canonical comparison between restricting an `S`-scheme first to `U` and first to
`Spec 𝒪_{S,s}`, and then to their common pullback. -/
public noncomputable def canonicalOverlapIso (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : Over S) :
    (Over.pullback ((S.fromSpecStalk s) ∣_ U)).obj ((Over.pullback U.ι).obj X) ≅
      (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).obj
        ((Over.pullback (S.fromSpecStalk s)).obj X) :=
  ((Over.pullbackComp ((S.fromSpecStalk s) ∣_ U) U.ι).app X).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj X)
      (morphismRestrict_ι (S.fromSpecStalk s) U)) ≪≫
    (Over.pullbackComp (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) (S.fromSpecStalk s)).app X

@[reducible] private noncomputable def FinitePresentationNeighborhoodModel.localBase
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    Spec (S.presheaf.stalk s) ⟶ X.neighborhood.V.toScheme :=
  IsOpenImmersion.lift X.neighborhood.V.ι (S.fromSpecStalk s) (by
    intro y hy
    rw [Scheme.range_fromSpecStalk] at hy
    exact ⟨⟨y, hy.mem_open X.neighborhood.V.isOpen X.neighborhood.mem_V⟩, rfl⟩)

private lemma FinitePresentationNeighborhoodModel.localBase_fac
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    X.localBase ≫ X.neighborhood.V.ι = S.fromSpecStalk s := by
  dsimp [localBase]
  exact IsOpenImmersion.lift_fac _ _ _

private lemma FinitePresentationNeighborhoodModel.openBase_comp
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s}
    (f : X ⟶ Y) :
    S.homOfLE X.neighborhood.le_V ≫ S.homOfLE f.base_le =
      S.homOfLE Y.neighborhood.le_V := by
  apply (cancel_mono Y.neighborhood.V.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι]

private lemma FinitePresentationNeighborhoodModel.localBase_comp
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s}
    (f : X ⟶ Y) :
    X.localBase ≫ S.homOfLE f.base_le = Y.localBase := by
  apply (cancel_mono Y.neighborhood.V.ι).1
  calc
    (X.localBase ≫ S.homOfLE f.base_le) ≫ Y.neighborhood.V.ι =
        X.localBase ≫ X.neighborhood.V.ι := by
          rw [Category.assoc, Scheme.homOfLE_ι]
    _ = S.fromSpecStalk s := X.localBase_fac
    _ = Y.localBase ≫ Y.neighborhood.V.ι := Y.localBase_fac.symm

private lemma FinitePresentationNeighborhoodModel.id_left
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    (𝟙 X : X ⟶ X).left = 𝟙 X.source := rfl

private lemma FinitePresentationNeighborhoodModel.comp_left
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y Z : FinitePresentationNeighborhoodModel S U s}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).left = f.left ≫ g.left := rfl

private noncomputable def FinitePresentationNeighborhoodModel.asFinitePresentationOver
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    FinitePresentationOver X.neighborhood.V.toScheme :=
  ⟨Over.mk X.hom, X.finitePresentation⟩

@[reducible] private noncomputable def FinitePresentationNeighborhoodModel.openRestriction
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) : FinitePresentationOver U.toScheme :=
  (finitePresentationBaseChange (S.homOfLE X.neighborhood.le_V)).obj X.asFinitePresentationOver

@[reducible] private noncomputable def FinitePresentationNeighborhoodModel.localRestriction
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    FinitePresentationOver (Spec (S.presheaf.stalk s)) :=
  (finitePresentationBaseChange X.localBase).obj X.asFinitePresentationOver

private noncomputable def FinitePresentationNeighborhoodModel.restrictMap
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s}
    (f : X ⟶ Y) {T : Scheme.{u}}
    (p : T ⟶ X.neighborhood.V.toScheme) (q : T ⟶ Y.neighborhood.V.toScheme)
    (hpq : p ≫ S.homOfLE f.base_le = q) :
    (Over.pullback p).obj (Over.mk X.hom) ⟶ (Over.pullback q).obj (Over.mk Y.hom) := by
  let k : pullback X.hom p ⟶ pullback Y.hom q :=
    pullback.lift (pullback.fst X.hom p ≫ f.left) (pullback.snd X.hom p) (by
      calc
        (pullback.fst X.hom p ≫ f.left) ≫ Y.hom =
            pullback.fst X.hom p ≫ X.hom ≫ S.homOfLE f.base_le := by
              rw [Category.assoc, f.w]
        _ = (pullback.snd X.hom p ≫ p) ≫ S.homOfLE f.base_le := by
              rw [← Category.assoc, pullback.condition]
        _ = pullback.snd X.hom p ≫ q := by rw [Category.assoc, hpq])
  exact Over.homMk k (by
    change k ≫ pullback.snd Y.hom q = pullback.snd X.hom p
    dsimp [k]
    exact pullback.lift_snd _ _ _)

private noncomputable def neighborhoodModelOpenPullback
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤ Over U.toScheme where
  obj X := (Over.pullback (S.homOfLE X.neighborhood.le_V)).obj (Over.mk X.hom)
  map := fun {X Y} f => FinitePresentationNeighborhoodModel.restrictMap f
    (S.homOfLE X.neighborhood.le_V) (S.homOfLE Y.neighborhood.le_V)
    (FinitePresentationNeighborhoodModel.openBase_comp f)
  map_id X := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [FinitePresentationNeighborhoodModel.restrictMap,
        FinitePresentationNeighborhoodModel.id_left]
  map_comp f g := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [FinitePresentationNeighborhoodModel.restrictMap,
        FinitePresentationNeighborhoodModel.comp_left, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, Category.assoc]

private noncomputable def neighborhoodModelLocalPullback
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤
      Over (Spec (S.presheaf.stalk s)) where
  obj X := (Over.pullback X.localBase).obj (Over.mk X.hom)
  map := fun {X Y} f => FinitePresentationNeighborhoodModel.restrictMap f
    X.localBase Y.localBase (FinitePresentationNeighborhoodModel.localBase_comp f)
  map_id X := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [FinitePresentationNeighborhoodModel.restrictMap,
        FinitePresentationNeighborhoodModel.id_left]
  map_comp f g := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [FinitePresentationNeighborhoodModel.restrictMap,
        FinitePresentationNeighborhoodModel.comp_left, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, Category.assoc]

private lemma FinitePresentationNeighborhoodModel.overlapBase_eq
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    (S.fromSpecStalk s ∣_ U) ≫ S.homOfLE X.neighborhood.le_V =
      (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ X.localBase := by
  apply (cancel_mono X.neighborhood.V.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι,
    FinitePresentationNeighborhoodModel.localBase_fac, morphismRestrict_ι]

private noncomputable def FinitePresentationNeighborhoodModel.overlapIso
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    (restrictOpenToPuncturedLocal S U s).obj X.openRestriction ≅
      (restrictLocalToPuncturedLocal S U s).obj X.localRestriction := by
  let p := S.fromSpecStalk s ∣_ U
  let q := ((S.fromSpecStalk s) ⁻¹ᵁ U).ι
  let j := S.homOfLE X.neighborhood.le_V
  let l := X.localBase
  have h : p ≫ j = q ≫ l := X.overlapBase_eq
  let e₁ : pullback (pullback.snd X.hom j) p ≅ pullback X.hom (p ≫ j) :=
    pullbackLeftPullbackSndIso X.hom j p
  let e₂ : pullback (pullback.snd X.hom l) q ≅ pullback X.hom (q ≫ l) :=
    pullbackLeftPullbackSndIso X.hom l q
  let e : pullback (pullback.snd X.hom j) p ≅ pullback (pullback.snd X.hom l) q :=
    e₁ ≪≫ pullback.congrHom rfl h ≪≫ e₂.symm
  exact (show ObjectProperty (Over ((puncturedLocalScheme S U s))) from
    fun Y ↦ FinitePresentation Y.hom).isoMk (Over.isoMk e (by
      have hh : (pullback.congrHom rfl h).hom ≫ pullback.snd X.hom (q ≫ l) =
          pullback.snd X.hom (p ≫ j) := by
        simp [pullback.congrHom, pullback.map, pullback.lift_snd]
      change e₁.hom ≫ (pullback.congrHom rfl h).hom ≫ e₂.inv ≫
        pullback.snd (pullback.snd X.hom l) q =
          pullback.snd (pullback.snd X.hom j) p
      calc
        _ = e₁.hom ≫ (pullback.congrHom rfl h).hom ≫ pullback.snd X.hom (q ≫ l) := by
          simp [e₂, pullbackLeftPullbackSndIso_inv_snd_snd]
        _ = e₁.hom ≫ pullback.snd X.hom (p ≫ j) := by rw [hh]
        _ = _ := by simp [e₁, pullbackLeftPullbackSndIso_hom_snd]))

@[reducible] private noncomputable def neighborhoodModelOpenRestrictionFunctor
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤ FinitePresentationOver U.toScheme :=
  (show ObjectProperty (Over U.toScheme) from
    fun Y ↦ FinitePresentation Y.hom).lift
      (neighborhoodModelOpenPullback S U s)
      (fun X ↦ X.openRestriction.property)

@[reducible] private noncomputable def neighborhoodModelLocalRestrictionFunctor
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤
      FinitePresentationOver (Spec (S.presheaf.stalk s)) :=
  (show ObjectProperty (Over (Spec (S.presheaf.stalk s))) from
    fun Y ↦ FinitePresentation Y.hom).lift
      (neighborhoodModelLocalPullback S U s)
      (fun X ↦ X.localRestriction.property)

private lemma FinitePresentationNeighborhoodModel.overlapIso_hom_fst
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
        X.overlapIso.hom.hom.left ≫
        pullback.fst (pullback.snd X.hom X.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          pullback.fst X.hom X.localBase =
      pullback.fst (pullback.snd X.hom (S.homOfLE X.neighborhood.le_V))
          (S.fromSpecStalk s ∣_ U) ≫
        pullback.fst X.hom (S.homOfLE X.neighborhood.le_V) := by
  let p := S.fromSpecStalk s ∣_ U
  let q := ((S.fromSpecStalk s) ⁻¹ᵁ U).ι
  let j := S.homOfLE X.neighborhood.le_V
  let l := X.localBase
  let e₁ := pullbackLeftPullbackSndIso X.hom j p
  let e₂ := pullbackLeftPullbackSndIso X.hom l q
  let e₃ : pullback X.hom (p ≫ j) ≅ pullback X.hom (q ≫ l) :=
    pullback.congrHom rfl X.overlapBase_eq
  show (e₁.hom ≫ e₃.hom ≫ e₂.inv) ≫
      pullback.fst (pullback.snd X.hom l) q ≫ pullback.fst X.hom l =
    pullback.fst (pullback.snd X.hom j) p ≫ pullback.fst X.hom j
  calc
    _ = e₁.hom ≫ e₃.hom ≫ pullback.fst X.hom (q ≫ l) := by
      simp [Category.assoc, e₂, pullbackLeftPullbackSndIso_inv_fst]
    _ = e₁.hom ≫ pullback.fst X.hom (p ≫ j) := by
      simp only [e₃, pullback.congrHom_hom, pullback.map]
      rw [pullback.lift_fst]
      simp [p, j]
    _ = _ := by simp [e₁, pullbackLeftPullbackSndIso_hom_fst]

private lemma FinitePresentationNeighborhoodModel.openOverlapMap_fst
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y) :
    ((restrictOpenToPuncturedLocal S U s).map
      ((neighborhoodModelOpenRestrictionFunctor S U s).map f)).hom.left ≫
      pullback.fst (pullback.snd Y.hom (S.homOfLE Y.neighborhood.le_V))
        (S.fromSpecStalk s ∣_ U) ≫
      pullback.fst Y.hom (S.homOfLE Y.neighborhood.le_V) =
      pullback.fst (pullback.snd X.hom (S.homOfLE X.neighborhood.le_V))
      (S.fromSpecStalk s ∣_ U) ≫
      pullback.fst X.hom (S.homOfLE X.neighborhood.le_V) ≫ f.left := by
  simp only [Lean.Elab.WF.paramLet, restrictOpenToPuncturedLocal, finitePresentationBaseChange,
    ObjectProperty.lift, ObjectProperty.ι, Over.pullback, Over.mk_left, Over.Hom.left,
    Over.homMk, Functor.comp_obj, inducedFunctor_obj, Functor.comp_map, inducedFunctor_map,
    ObjectProperty.homMk, neighborhoodModelOpenRestrictionFunctor, neighborhoodModelOpenPullback,
    Over.mk_hom, restrictMap, CostructuredArrow.homMk_left, pullback.lift_fst_assoc,
    Category.assoc]
  rw [pullback.lift_fst]

private lemma FinitePresentationNeighborhoodModel.localOverlapMap_fst
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y) :
    ((restrictLocalToPuncturedLocal S U s).map
      ((neighborhoodModelLocalRestrictionFunctor S U s).map f)).hom.left ≫
      pullback.fst (pullback.snd Y.hom Y.localBase)
        (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
      pullback.fst Y.hom Y.localBase =
      pullback.fst (pullback.snd X.hom X.localBase)
      (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
      pullback.fst X.hom X.localBase ≫ f.left := by
  simp only [Lean.Elab.WF.paramLet, restrictLocalToPuncturedLocal, finitePresentationBaseChange,
    ObjectProperty.lift, ObjectProperty.ι, Over.pullback, Over.mk_left, Over.Hom.left,
    Over.homMk, Functor.comp_obj, inducedFunctor_obj, Functor.comp_map, inducedFunctor_map,
    ObjectProperty.homMk, neighborhoodModelLocalRestrictionFunctor, neighborhoodModelLocalPullback,
    Over.mk_hom, restrictMap, CostructuredArrow.homMk_left, pullback.lift_fst_assoc,
    Category.assoc]
  rw [pullback.lift_fst]

private lemma FinitePresentationNeighborhoodModel.overlapIso_naturality
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y) :
    (restrictOpenToPuncturedLocal S U s).map
        ((neighborhoodModelOpenRestrictionFunctor S U s).map f) ≫
      Y.overlapIso.hom =
    X.overlapIso.hom ≫ (restrictLocalToPuncturedLocal S U s).map
        ((neighborhoodModelLocalRestrictionFunctor S U s).map f) := by
  let mL := (restrictOpenToPuncturedLocal S U s).map
    ((neighborhoodModelOpenRestrictionFunctor S U s).map f) ≫ Y.overlapIso.hom
  let mR := X.overlapIso.hom ≫ (restrictLocalToPuncturedLocal S U s).map
    ((neighborhoodModelLocalRestrictionFunctor S U s).map f)
  have hBase :
      mL.hom.left ≫ ((restrictLocalToPuncturedLocal S U s).obj Y.localRestriction).obj.hom =
      mR.hom.left ≫ ((restrictLocalToPuncturedLocal S U s).obj
        ((neighborhoodModelLocalRestrictionFunctor S U s).obj Y)).obj.hom :=
    mL.hom.w.trans mR.hom.w.symm
  show mL = mR
  apply (show ObjectProperty (Over (puncturedLocalScheme S U s)) from
    fun Z ↦ FinitePresentation Z.hom).ι.map_injective
  apply CategoryTheory.Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change
        ((restrictOpenToPuncturedLocal S U s).map
          ((neighborhoodModelOpenRestrictionFunctor S U s).map f)).hom.left ≫
            Y.overlapIso.hom.hom.left ≫
              pullback.fst (pullback.snd Y.hom Y.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
                pullback.fst Y.hom Y.localBase =
        X.overlapIso.hom.hom.left ≫
          ((restrictLocalToPuncturedLocal S U s).map
            ((neighborhoodModelLocalRestrictionFunctor S U s).map f)).hom.left ≫
              pullback.fst (pullback.snd Y.hom Y.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
                pullback.fst Y.hom Y.localBase
      refine Eq.trans (congrArg (fun k ↦
        ((restrictOpenToPuncturedLocal S U s).map
          ((neighborhoodModelOpenRestrictionFunctor S U s).map f)).hom.left ≫ k)
        Y.overlapIso_hom_fst) ?_
      refine Eq.trans (FinitePresentationNeighborhoodModel.openOverlapMap_fst f) ?_
      refine Eq.trans ?_ (congrArg (fun k ↦ X.overlapIso.hom.hom.left ≫ k)
        (FinitePresentationNeighborhoodModel.localOverlapMap_fst f)).symm
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun g ↦ g ≫ f.left) X.overlapIso_hom_fst.symm) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact congrArg (fun k ↦ X.overlapIso.hom.hom.left ≫ k) (Category.assoc _ _ _)
    · show mL.hom.left ≫ (pullback.fst (pullback.snd Y.hom Y.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ pullback.snd Y.hom Y.localBase) =
        mR.hom.left ≫ (pullback.fst (pullback.snd Y.hom Y.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ pullback.snd Y.hom Y.localBase)
      refine Eq.trans (congrArg (fun k ↦ mL.hom.left ≫ k)
        (pullback.condition (f := pullback.snd Y.hom Y.localBase)
          (g := (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun k ↦ k ≫ (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) hBase) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      exact (congrArg (fun k ↦ mR.hom.left ≫ k)
        (pullback.condition (f := pullback.snd Y.hom Y.localBase)
          (g := (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)))).symm
  · show mL.hom.left ≫
        ((restrictLocalToPuncturedLocal S U s).obj Y.localRestriction).obj.hom =
      mR.hom.left ≫
        ((restrictLocalToPuncturedLocal S U s).obj
          ((neighborhoodModelLocalRestrictionFunctor S U s).obj Y)).obj.hom
    exact hBase


private lemma pullback_map_isIso_of_isPullback
    {P X B C T : Scheme.{u}}
    {f₁ : P ⟶ X} {f₂ : P ⟶ B} {g₁ : X ⟶ C} {g₂ : B ⟶ C}
    (h : IsPullback f₁ f₂ g₁ g₂) (p : T ⟶ B) (q : T ⟶ C)
    (hq : p ≫ g₂ = q) [HasPullback f₂ p] [HasPullback g₁ q] :
    IsIso (pullback.lift (pullback.fst f₂ p ≫ f₁) (pullback.snd f₂ p) (by
      calc
        (pullback.fst f₂ p ≫ f₁) ≫ g₁ =
            pullback.fst f₂ p ≫ f₂ ≫ g₂ := by rw [Category.assoc, h.w]
        _ = (pullback.snd f₂ p ≫ p) ≫ g₂ := by rw [← Category.assoc, pullback.condition]
        _ = pullback.snd f₂ p ≫ q := by rw [Category.assoc, hq])) := by
  let m := pullback.lift (pullback.fst f₂ p ≫ f₁) (pullback.snd f₂ p) (by
      calc
        (pullback.fst f₂ p ≫ f₁) ≫ g₁ =
            pullback.fst f₂ p ≫ f₂ ≫ g₂ := by rw [Category.assoc, h.w]
        _ = (pullback.snd f₂ p ≫ p) ≫ g₂ := by rw [← Category.assoc, pullback.condition]
        _ = pullback.snd f₂ p ≫ q := by rw [Category.assoc, hq])
  have hmFst : m ≫ pullback.fst g₁ q = pullback.fst f₂ p ≫ f₁ := by
    dsimp [m]
    exact pullback.lift_fst _ _ _
  have hmSnd : m ≫ pullback.snd g₁ q = pullback.snd f₂ p := by
    dsimp [m]
    exact pullback.lift_snd _ _ _
  have hw : m ≫ pullback.snd g₁ q = pullback.snd f₂ p ≫ 𝟙 T := by
    rw [hmSnd]
    simp
  have hExt : ∀ ⦃Z : Scheme.{u}⦄ ⦃a b : Z ⟶ pullback f₂ p⦄,
      a ≫ m = b ≫ m → a ≫ pullback.snd f₂ p = b ≫ pullback.snd f₂ p → a = b := by
    intro Z a b hak hbk
    apply pullback.hom_ext
    · apply h.hom_ext
      · have hh := congrArg (fun t => t ≫ pullback.fst g₁ q) hak
        simpa only [Category.assoc, hmFst] using hh
      · have hh := congrArg (fun t => t ≫ p) hbk
        calc
          (a ≫ pullback.fst f₂ p) ≫ f₂ = a ≫ (pullback.fst f₂ p ≫ f₂) := by
            simp only [Category.assoc]
          _ = a ≫ (pullback.snd f₂ p ≫ p) := congrArg (fun t => a ≫ t) pullback.condition
          _ = b ≫ (pullback.snd f₂ p ≫ p) := by simpa only [Category.assoc] using hh
          _ = b ≫ (pullback.fst f₂ p ≫ f₂) := (congrArg (fun t => b ≫ t) pullback.condition).symm
          _ = (b ≫ pullback.fst f₂ p) ≫ f₂ := by simp only [Category.assoc]
    · exact hbk
  have hLift : ∀ ⦃Z : Scheme.{u}⦄ (a : Z ⟶ pullback g₁ q) (b : Z ⟶ T),
      a ≫ pullback.snd g₁ q = b ≫ 𝟙 T →
      ∃ l : Z ⟶ pullback f₂ p, l ≫ m = a ∧ l ≫ pullback.snd f₂ p = b := by
    intro Z a b hab
    let x := h.lift (a ≫ pullback.fst g₁ q) (b ≫ p) (by
      calc
        (a ≫ pullback.fst g₁ q) ≫ g₁ = (a ≫ pullback.snd g₁ q) ≫ q := by
          simp [Category.assoc, pullback.condition]
        _ = (b ≫ p) ≫ g₂ := by
          calc
            _ = (b ≫ 𝟙 T) ≫ q := by rw [hab]
            _ = (b ≫ p) ≫ g₂ := by rw [Category.assoc, ← hq]; simp)
    have hx : x ≫ f₂ = b ≫ p := by simp [x]
    let l := pullback.lift x b hx
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · calc
          l ≫ m ≫ pullback.fst g₁ q = l ≫ pullback.fst f₂ p ≫ f₁ := by
            simp only [hmFst]
          _ = x ≫ f₁ := by
            calc
              _ = (l ≫ pullback.fst f₂ p) ≫ f₁ := by simp only [Category.assoc]
              _ = x ≫ f₁ := by rw [pullback.lift_fst x b hx]
          _ = a ≫ pullback.fst g₁ q := by simp [x]
      · calc
          l ≫ m ≫ pullback.snd g₁ q = l ≫ pullback.snd f₂ p := by
            simp only [hmSnd]
          _ = b := pullback.lift_snd x b hx
          _ = a ≫ pullback.snd g₁ q := by simpa using hab.symm
    · exact pullback.lift_snd x b hx
  have hm : IsPullback m (pullback.snd f₂ p) (pullback.snd g₁ q) (𝟙 T) :=
    IsPullback.mk' hw hExt hLift
  show IsIso m
  exact hm.isIso_fst_of_isIso

private lemma FinitePresentationNeighborhoodModel.openRestrictionMap_isIso
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y)
    (hf : FinitePresentationNeighborhoodModel.restrictionMorphisms f) :
    IsIso ((neighborhoodModelOpenRestrictionFunctor S U s).map f) := by
  rw [← ObjectProperty.isIso_hom_iff]
  rw [← isIso_iff_of_reflects_iso _ (Over.forget U.toScheme)]
  change IsPullback f.left X.hom Y.hom (S.homOfLE f.base_le) at hf
  rw [Over.forget_map]
  dsimp [neighborhoodModelOpenRestrictionFunctor, neighborhoodModelOpenPullback,
    FinitePresentationNeighborhoodModel.openRestriction,
    FinitePresentationNeighborhoodModel.asFinitePresentationOver,
    FinitePresentationNeighborhoodModel.restrictMap,
    CategoryTheory.ObjectProperty.ι, CategoryTheory.ObjectProperty.lift,
    CategoryTheory.ObjectProperty.homMk, CategoryTheory.Over.Hom.left,
    CategoryTheory.Over.homMk, Over.pullback]
  exact pullback_map_isIso_of_isPullback
    (f₁ := f.left) (f₂ := X.hom) (g₁ := Y.hom)
    (g₂ := S.homOfLE f.base_le) (h := hf)
    (p := S.homOfLE X.neighborhood.le_V) (q := S.homOfLE Y.neighborhood.le_V)
    (hq := FinitePresentationNeighborhoodModel.openBase_comp f)

private lemma FinitePresentationNeighborhoodModel.localRestrictionMap_isIso
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y)
    (hf : FinitePresentationNeighborhoodModel.restrictionMorphisms f) :
    IsIso ((neighborhoodModelLocalRestrictionFunctor S U s).map f) := by
  rw [← ObjectProperty.isIso_hom_iff]
  rw [← isIso_iff_of_reflects_iso _ (Over.forget (Spec (S.presheaf.stalk s)))]
  change IsPullback f.left X.hom Y.hom (S.homOfLE f.base_le) at hf
  rw [Over.forget_map]
  dsimp [neighborhoodModelLocalRestrictionFunctor, neighborhoodModelLocalPullback,
    FinitePresentationNeighborhoodModel.localRestriction,
    FinitePresentationNeighborhoodModel.asFinitePresentationOver,
    FinitePresentationNeighborhoodModel.restrictMap,
    CategoryTheory.ObjectProperty.ι, CategoryTheory.ObjectProperty.lift,
    CategoryTheory.ObjectProperty.homMk, CategoryTheory.Over.Hom.left,
    CategoryTheory.Over.homMk, Over.pullback]
  exact pullback_map_isIso_of_isPullback
    (f₁ := f.left) (f₂ := X.hom) (g₁ := Y.hom)
    (g₂ := S.homOfLE f.base_le) (h := hf)
    (p := X.localBase) (q := Y.localBase)
    (hq := FinitePresentationNeighborhoodModel.localBase_comp f)

private noncomputable def neighborhoodModelToGlueingData
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationNeighborhoodModel S U s ⥤ glueingDataNearPoint S U s :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocal S U s)
      (restrictLocalToPuncturedLocal S U s)) from fun X ↦ IsIso X.hom).lift
    { obj := fun X ↦ ⟨(neighborhoodModelOpenRestrictionFunctor S U s).obj X,
        (neighborhoodModelLocalRestrictionFunctor S U s).obj X, X.overlapIso.hom⟩
      map := fun f ↦ ⟨(neighborhoodModelOpenRestrictionFunctor S U s).map f,
        (neighborhoodModelLocalRestrictionFunctor S U s).map f,
        FinitePresentationNeighborhoodModel.overlapIso_naturality f⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp }
    (fun X ↦ by change IsIso X.overlapIso.hom; infer_instance)

private lemma commaMorphism_isIso_of_isIso_left_right
    {A B T : Type*} [Category A] [Category B] [Category T]
    {L : A ⥤ T} {R : B ⥤ T} {X Y : Comma L R} (f : X ⟶ Y)
    (hL : IsIso f.left) (hR : IsIso f.right) : IsIso f := by
  let := hL
  let := hR
  have hw : L.map (inv f.left) ≫ X.hom = Y.hom ≫ R.map (inv f.right) := by
    have hh' : Y.hom ≫ R.map (inv f.right) = L.map (inv f.left) ≫ X.hom := by
      simp
    exact hh'.symm
  let g : Y ⟶ X := ⟨inv f.left, inv f.right, hw⟩
  refine ⟨g, ?_, ?_⟩
  · apply Comma.hom_ext <;> simp [g]
  · apply Comma.hom_ext <;> simp [g]

private lemma neighborhoodModelToGlueingData_inverts_restriction
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    {X Y : FinitePresentationNeighborhoodModel S U s} (f : X ⟶ Y)
    (hf : FinitePresentationNeighborhoodModel.restrictionMorphisms f) :
    IsIso ((neighborhoodModelToGlueingData S U s).map f) := by
  rw [← ObjectProperty.isIso_hom_iff]
  apply commaMorphism_isIso_of_isIso_left_right
  · exact FinitePresentationNeighborhoodModel.openRestrictionMap_isIso f hf
  · exact FinitePresentationNeighborhoodModel.localRestrictionMap_isIso f hf

private noncomputable def finitePresentationGermToGlueingData
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationGerm S U s ⥤ glueingDataNearPoint S U s :=
  Localization.Construction.lift
      (W := FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s))
      (neighborhoodModelToGlueingData S U s)
      (by
        intro X Y f hf
        exact neighborhoodModelToGlueingData_inverts_restriction S U s f hf)

private lemma finitePresentationGermToGlueingData_fac
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙ finitePresentationGermToGlueingData S U s =
      neighborhoodModelToGlueingData S U s :=
  Localization.Construction.fac _ _

private noncomputable def pullback_factorization_iso
    {X V S B : Scheme.{u}} (f : X ⟶ V) (j : V ⟶ S)
    (k : B ⟶ V) (b : B ⟶ S) (hkj : k ≫ j = b)
    [Mono j] [HasPullback f k] [HasPullback (f ≫ j) b] :
    pullback f k ≅ pullback (f ≫ j) b := by
  let a : pullback f k ⟶ pullback (f ≫ j) b :=
    pullback.lift (pullback.fst f k) (pullback.snd f k) (by
      calc
        pullback.fst f k ≫ (f ≫ j) = (pullback.fst f k ≫ f) ≫ j := by
          simp [Category.assoc]
        _ = (pullback.snd f k ≫ k) ≫ j := by rw [pullback.condition]
        _ = pullback.snd f k ≫ b := by rw [Category.assoc, hkj])
  have hback : pullback.fst (f ≫ j) b ≫ f = pullback.snd (f ≫ j) b ≫ k :=
    (cancel_mono j).1 (by
      calc
        (pullback.fst (f ≫ j) b ≫ f) ≫ j =
            pullback.fst (f ≫ j) b ≫ (f ≫ j) := by simp [Category.assoc]
        _ = pullback.snd (f ≫ j) b ≫ b := pullback.condition
        _ = pullback.snd (f ≫ j) b ≫ (k ≫ j) := by rw [hkj]
        _ = (pullback.snd (f ≫ j) b ≫ k) ≫ j := by simp [Category.assoc])
  let c : pullback (f ≫ j) b ⟶ pullback f k :=
    pullback.lift (pullback.fst (f ≫ j) b) (pullback.snd (f ≫ j) b) hback
  refine ⟨a, c, ?_, ?_⟩
  · apply pullback.hom_ext
    · calc
        (a ≫ c) ≫ pullback.fst f k = a ≫ pullback.fst (f ≫ j) b := by
          dsimp [c]
          rw [Category.assoc, pullback.lift_fst]
        _ = pullback.fst f k := by
          dsimp [a]
          rw [pullback.lift_fst]
    · calc
        (a ≫ c) ≫ pullback.snd f k = a ≫ pullback.snd (f ≫ j) b := by
          dsimp [c]
          rw [Category.assoc, pullback.lift_snd]
        _ = pullback.snd f k := by
          dsimp [a]
          rw [pullback.lift_snd]
  · apply pullback.hom_ext
    · calc
        (c ≫ a) ≫ pullback.fst (f ≫ j) b = c ≫ pullback.fst f k := by
          dsimp [a]
          rw [Category.assoc, pullback.lift_fst]
        _ = pullback.fst (f ≫ j) b := by
          dsimp [c]
          rw [pullback.lift_fst]
    · calc
        (c ≫ a) ≫ pullback.snd (f ≫ j) b = c ≫ pullback.snd f k := by
          dsimp [a]
          rw [Category.assoc, pullback.lift_snd]
        _ = pullback.snd (f ≫ j) b := by
          dsimp [c]
          rw [pullback.lift_snd]

private noncomputable def FinitePresentationNeighborhoodModel.openAmbientIso
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    (Over.pullback (S.homOfLE X.neighborhood.le_V)).obj (Over.mk X.hom) ≅
      (Over.pullback U.ι).obj
        (Over.mk (X.hom ≫ X.neighborhood.V.ι)) :=
  Over.isoMk (pullback_factorization_iso X.hom X.neighborhood.V.ι
    (S.homOfLE X.neighborhood.le_V) U.ι (by simp)) (by
      dsimp [pullback_factorization_iso]
      exact pullback.lift_snd _ _ _)

private noncomputable def FinitePresentationNeighborhoodModel.localAmbientIso
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    (Over.pullback X.localBase).obj (Over.mk X.hom) ≅
      (Over.pullback (S.fromSpecStalk s)).obj
        (Over.mk (X.hom ≫ X.neighborhood.V.ι)) :=
  Over.isoMk (pullback_factorization_iso X.hom X.neighborhood.V.ι
    X.localBase (S.fromSpecStalk s) X.localBase_fac) (by
      dsimp [pullback_factorization_iso]
      exact pullback.lift_snd _ _ _)

private alias pullbackComp_hom_fst := AlgebraicGeometry.pullbackComp_hom_app_left_fst

private alias pullbackComp_inv_fst := AlgebraicGeometry.pullbackComp_inv_app_left_fst

private lemma pullback_eqToIso_fst {C : Type*} [Category C] [HasPullbacks C]
    {A B : C} {f g : A ⟶ B} (h : f = g) (X : Over B) :
    (eqToIso (congrArg (fun k ↦ (Over.pullback k).obj X) h)).hom.left ≫
      pullback.fst X.hom g = pullback.fst X.hom f := by
  subst g
  simp

private lemma canonicalOverlapIso_hom_fst
    (S : Scheme.{u}) (U : S.Opens) (s : S) (X : Over S) :
    (canonicalOverlapIso S U s X).hom.left ≫
      pullback.fst (pullback.snd X.hom (S.fromSpecStalk s))
        (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
      pullback.fst X.hom (S.fromSpecStalk s) =
    pullback.fst (pullback.snd X.hom U.ι) ((S.fromSpecStalk s) ∣_ U) ≫
      pullback.fst X.hom U.ι := by
  simp only [canonicalOverlapIso, Iso.trans_hom, Iso.symm_hom, Over.comp_left,
    Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [pullbackComp_hom_fst, pullback_eqToIso_fst, pullbackComp_inv_fst]
  exact morphismRestrict_ι _ _

private noncomputable def neighborhoodModelOpenAmbientIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    neighborhoodModelToGlueingData S U s ⋙ openComponent S U s ≅
      neighborhoodModelToAmbient S U s ⋙ Over.pullback U.ι :=
  NatIso.ofComponents (fun X ↦ X.openAmbientIso) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      dsimp [neighborhoodModelToGlueingData, openComponent,
        neighborhoodModelOpenRestrictionFunctor, neighborhoodModelOpenPullback,
        neighborhoodModelToAmbient, FinitePresentationNeighborhoodModel.openAmbientIso,
        FinitePresentationNeighborhoodModel.restrictMap, pullback_factorization_iso,
        Over.pullback, ObjectProperty.lift, ObjectProperty.homMk,
        Over.Hom.left, Over.homMk, Over.isoMk, CostructuredArrow.isoMk,
        CostructuredArrow.homMk, Comma.isoMk]
      <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc])

private noncomputable def neighborhoodModelLocalAmbientIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    neighborhoodModelToGlueingData S U s ⋙ localComponent S U s ≅
      neighborhoodModelToAmbient S U s ⋙ Over.pullback (S.fromSpecStalk s) :=
  NatIso.ofComponents (fun X ↦ X.localAmbientIso) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      dsimp [neighborhoodModelToGlueingData, localComponent,
        neighborhoodModelLocalRestrictionFunctor, neighborhoodModelLocalPullback,
        neighborhoodModelToAmbient, FinitePresentationNeighborhoodModel.localAmbientIso,
        FinitePresentationNeighborhoodModel.restrictMap, pullback_factorization_iso,
        Over.pullback, ObjectProperty.lift, ObjectProperty.homMk,
        Over.Hom.left, Over.homMk, Over.isoMk, CostructuredArrow.isoMk,
        CostructuredArrow.homMk, Comma.isoMk]
      <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc])

/-- The first projection of a base change, computed on a morphism of objects over the base. -/
public lemma over_pullback_map_fst {C : Type*} [Category C] [HasPullbacks C]
    {B T : C} (p : T ⟶ B) {X Y : Over B} (f : X ⟶ Y) :
    ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p =
      pullback.fst X.hom p ≫ f.left := by
  simp [Over.pullback, pullback.lift_fst]

private lemma FinitePresentationNeighborhoodModel.openAmbientIso_hom_fst
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    X.openAmbientIso.hom.left ≫ pullback.fst (X.hom ≫ X.neighborhood.V.ι) U.ι =
      pullback.fst X.hom (S.homOfLE X.neighborhood.le_V) := by
  simp [FinitePresentationNeighborhoodModel.openAmbientIso, pullback_factorization_iso,
    pullback.lift_fst]

private lemma FinitePresentationNeighborhoodModel.localAmbientIso_hom_fst
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    (X : FinitePresentationNeighborhoodModel S U s) :
    X.localAmbientIso.hom.left ≫
      pullback.fst (X.hom ≫ X.neighborhood.V.ι) (S.fromSpecStalk s) =
      pullback.fst X.hom X.localBase := by
  simp [FinitePresentationNeighborhoodModel.localAmbientIso, pullback_factorization_iso,
    pullback.lift_fst]

private lemma neighborhoodModel_overlapComparison
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (X : FinitePresentationNeighborhoodModel S U s) :
    (Over.pullback ((S.fromSpecStalk s) ∣_ U)).map X.openAmbientIso.hom ≫
      (canonicalOverlapIso S U s (Over.mk (X.hom ≫ X.neighborhood.V.ι))).hom =
    X.overlapIso.hom.hom ≫
      (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).map X.localAmbientIso.hom := by
  let a := (Over.pullback ((S.fromSpecStalk s) ∣_ U)).map X.openAmbientIso.hom ≫
    (canonicalOverlapIso S U s (Over.mk (X.hom ≫ X.neighborhood.V.ι))).hom
  let b := X.overlapIso.hom.hom ≫
    (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).map X.localAmbientIso.hom
  have hb := a.w.trans b.w.symm
  show a = b
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · dsimp only [a, b, Over.comp_left]
      simp only [Category.assoc, Over.pullback_obj_hom]
      rw [canonicalOverlapIso_hom_fst]
      have hp := congrArg
        (fun k ↦ k ≫ pullback.fst (X.hom ≫ X.neighborhood.V.ι) U.ι)
        (over_pullback_map_fst ((S.fromSpecStalk s) ∣_ U) X.openAmbientIso.hom)
      have hq := congrArg
        (fun k ↦ k ≫ pullback.fst (X.hom ≫ X.neighborhood.V.ι) (S.fromSpecStalk s))
        (over_pullback_map_fst (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) X.localAmbientIso.hom)
      simp only [Category.assoc, FinitePresentationNeighborhoodModel.openAmbientIso_hom_fst]
        at hp
      simp only [Category.assoc, FinitePresentationNeighborhoodModel.localAmbientIso_hom_fst]
        at hq
      exact hp.trans (X.overlapIso_hom_fst.symm.trans
        (congrArg (fun k ↦ X.overlapIso.hom.hom.left ≫ k) hq.symm))
    · show a.left ≫ (pullback.fst _ _ ≫ pullback.snd _ _) =
        b.left ≫ (pullback.fst _ _ ≫ pullback.snd _ _)
      dsimp only [Over.pullback_obj_hom, neighborhoodModelToAmbient] at *
      rw [pullback.condition]
      exact congrArg (fun k ↦ k ≫ (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) hb
  · exact hb

/-- Compatibility of projection isomorphisms with the actual cartesian comparison on the
punctured local scheme. This ensures that the equivalence identifies the whole restriction
diagram, rather than only its open and local vertices. -/
public def overlapComparisonCompatible (S : Scheme.{u}) (U : S.Opens) (s : S)
    (e : FinitePresentationGerm S U s ≌ glueingDataNearPoint S U s)
    (a : ((FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ openComponent S U s) ≅
      (neighborhoodModelToAmbient S U s ⋙ Over.pullback U.ι))
    (b : ((FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ localComponent S U s) ≅
      (neighborhoodModelToAmbient S U s ⋙ Over.pullback (S.fromSpecStalk s))) : Prop :=
  ∀ X : FinitePresentationNeighborhoodModel S U s,
    let Z := ((FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙ e.functor).obj X
    let c : (Over.pullback ((S.fromSpecStalk s) ∣_ U)).obj
        ((openComponent S U s).obj Z) ⟶
        (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).obj
          ((localComponent S U s).obj Z) :=
      Z.1.hom.hom
    let aX : (openComponent S U s).obj Z ⟶
        (Over.pullback U.ι).obj ((neighborhoodModelToAmbient S U s).obj X) := by
      simpa only [Z, Functor.comp_obj] using (a.app X).hom
    let bX : (localComponent S U s).obj Z ⟶
        (Over.pullback (S.fromSpecStalk s)).obj
          ((neighborhoodModelToAmbient S U s).obj X) := by
      simpa only [Z, Functor.comp_obj] using (b.app X).hom
    (Over.pullback ((S.fromSpecStalk s) ∣_ U)).map aX ≫
      (canonicalOverlapIso S U s ((neighborhoodModelToAmbient S U s).obj X)).hom =
    c ≫
      (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).map bX

private abbrev AffineNeighborhood (S : Scheme.{u}) (s : S) :=
  {V : S.Opens // IsAffineOpen V ∧ s ∈ V}
private lemma affineNeighborhood_nonempty (S : Scheme.{u}) (s : S) :
    Nonempty (AffineNeighborhood S s) := by
  obtain ⟨V, hV, hs, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
  exact ⟨⟨V, hV, hs⟩⟩
attribute [local instance] affineNeighborhood_nonempty
private lemma affineNeighborhood_isCofiltered (S : Scheme.{u}) (s : S) :
    IsCofiltered (AffineNeighborhood S s) where
  cone_objs V W := by
    obtain ⟨T, hT, hs, hle⟩ := exists_isAffineOpen_mem_and_subset
      (U := V.1 ⊓ W.1) (x := s) ⟨V.2.2, W.2.2⟩
    exact ⟨⟨T, hT, hs⟩, homOfLE (hle.trans inf_le_left),
      homOfLE (hle.trans inf_le_right), trivial⟩
  cone_maps {V W} f g := ⟨V, 𝟙 V, Subsingleton.elim _ _⟩
attribute [local instance] affineNeighborhood_isCofiltered
private def affineNeighborhoodInclusion (S : Scheme.{u}) (s : S) :
    AffineNeighborhood S s ⥤ OpenNhds s :=
  (show Monotone (fun V : AffineNeighborhood S s ↦
    (⟨V.1, V.2.2⟩ : OpenNhds s)) from fun _ _ h ↦ h).functor
private lemma affineNeighborhoodInclusion_initial (S : Scheme.{u}) (s : S) :
    (affineNeighborhoodInclusion S s).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro V
    obtain ⟨W, hW, hs, hle⟩ := exists_isAffineOpen_mem_and_subset V.2
    exact ⟨⟨W, hW, hs⟩, ⟨homOfLE hle⟩⟩
  · intro V W f g
    exact ⟨W, 𝟙 _, Subsingleton.elim _ _⟩
attribute [local instance] affineNeighborhoodInclusion_initial
@[reducible] private noncomputable def affineNeighborhoodDiagram (S : Scheme.{u}) (s : S) :
    AffineNeighborhood S s ⥤ Scheme.{u} where
  obj V := V.1.toScheme
  map f := S.homOfLE (leOfHom f)
  map_id V := by simp
  map_comp f g := by simp
@[reducible] private noncomputable def affineNeighborhoodCone (S : Scheme.{u}) (s : S) :
    Cone (affineNeighborhoodDiagram S s) where
  pt := Spec (S.presheaf.stalk s)
  π :=
    { app := fun V ↦ V.1.fromSpecStalkOfMem s V.2.2
      naturality := by
        intro V W f
        dsimp [affineNeighborhoodDiagram]
        apply (cancel_mono W.1.ι).1
        simp }
private noncomputable def affineNeighborhoodRingCocone (S : Scheme.{u}) (s : S) :=
  (colimit.cocone ((OpenNhds.inclusion s).op ⋙ S.presheaf)).whisker
    (affineNeighborhoodInclusion S s).op
private noncomputable def affineNeighborhoodRingIsColimit (S : Scheme.{u}) (s : S) :
    IsColimit (affineNeighborhoodRingCocone S s) :=
  (Functor.Final.isColimitWhiskerEquiv (affineNeighborhoodInclusion S s).op _).symm
    (colimit.isColimit _)
private noncomputable def affineNeighborhoodSpecCone (S : Scheme.{u}) (s : S) :=
  Scheme.Spec.mapCone (coneRightOpOfCocone (affineNeighborhoodRingCocone S s))
private noncomputable def affineNeighborhoodSpecIsLimit (S : Scheme.{u}) (s : S) :
    IsLimit (affineNeighborhoodSpecCone S s) :=
  isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone _ (affineNeighborhoodRingIsColimit S s))
private noncomputable def affineNeighborhoodToSpec (S : Scheme.{u}) (s : S) :
    affineNeighborhoodDiagram S s ≅
      (((affineNeighborhoodInclusion S s).op ⋙
        ((OpenNhds.inclusion s).op ⋙ S.presheaf)).rightOp ⋙ Scheme.Spec) :=
  NatIso.ofComponents (fun V ↦ V.2.1.isoSpec) (by
    intro V W f
    dsimp [affineNeighborhoodDiagram]
    exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map V.1 W.1 (leOfHom f)).symm)
private noncomputable def affineNeighborhoodIsLimit (S : Scheme.{u}) (s : S) :
    IsLimit (affineNeighborhoodCone S s) := by
  apply (IsLimit.postcomposeHomEquiv (affineNeighborhoodToSpec S s) _).1
  apply (affineNeighborhoodSpecIsLimit S s).ofIsoLimit
  refine Cone.ext (Iso.refl _) ?_
  intro V
  dsimp [affineNeighborhoodSpecCone, affineNeighborhoodCone, affineNeighborhoodRingCocone,
    affineNeighborhoodToSpec, affineNeighborhoodInclusion]
  change Spec.map (S.presheaf.germ V.1 s V.2.2) =
    𝟙 _ ≫ V.1.fromSpecStalkOfMem s V.2.2 ≫ V.2.1.isoSpec.hom
  simpa only [Category.id_comp, IsAffineOpen.isoSpec_hom] using
    (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ V.1 s V.2.2).symm
private lemma affineNeighborhoodDiagram_isAffine (S : Scheme.{u}) (s : S)
    (V : AffineNeighborhood S s) : IsAffine ((affineNeighborhoodDiagram S s).obj V) :=
  V.2.1
attribute [local instance] affineNeighborhoodDiagram_isAffine
private lemma affineNeighborhoodDiagram_isAffineHom (S : Scheme.{u}) (s : S)
    {V W : AffineNeighborhood S s} (f : V ⟶ W) :
    IsAffineHom ((affineNeighborhoodDiagram S s).map f) := by infer_instance
attribute [local instance] affineNeighborhoodDiagram_isAffineHom
private lemma exists_affineNeighborhood_model (S : Scheme.{u}) (s : S)
    (X : Over (Spec (S.presheaf.stalk s))) (hX : FinitePresentation X.hom) :
    ∃ (V : AffineNeighborhood S s) (Y : Over V.1.toScheme),
      FinitePresentation Y.hom ∧
      Nonempty (X ≅ (Over.pullback (V.1.fromSpecStalkOfMem s V.2.2)).obj Y) :=
  AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation
    (affineNeighborhoodDiagram S s)
    (affineNeighborhoodCone S s) (affineNeighborhoodIsLimit S s) X hX

private lemma eventually_eq_affineNeighborhood_morphism
    (S : Scheme.{u}) (s : S) (V : AffineNeighborhood S s)
    (X Y : Over ((affineNeighborhoodDiagram S s).obj V))
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback ((affineNeighborhoodCone S s).π.app V)).map f =
      (Over.pullback ((affineNeighborhoodCone S s).π.app V)).map g) :
    ∃ (W : AffineNeighborhood S s) (e : W ⟶ V),
      (Over.pullback ((affineNeighborhoodDiagram S s).map e)).map f =
      (Over.pullback ((affineNeighborhoodDiagram S s).map e)).map g :=
  AlgebraicGeometry.eventually_eq_of_baseChange_eq
    (affineNeighborhoodDiagram S s) (affineNeighborhoodCone S s)
    (affineNeighborhoodIsLimit S s) V X Y hX hY f g hfg

private lemma overPullback_hom_ext_of_fst
    {S T : Scheme.{u}} (p : T ⟶ S) (X : Over S) {Y : Over T}
    (f g : Y ⟶ (Over.pullback p).obj X)
    (h : f.left ≫ pullback.fst X.hom p = g.left ≫ pullback.fst X.hom p) :
    f = g :=
  CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext h (f.w.trans g.w.symm))

/-- The comparison between iterated pullback to a cone point and direct pullback to that
point. -/
private noncomputable def conePullbackComparison
    {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {j i : I} (e : j ⟶ i) (X : Over (D.obj i)) :
    (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
      (Over.pullback (c.π.app i)).obj X :=
  ((Over.pullbackComp (c.π.app j) (D.map e)).app X).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj X) (c.w e))

private lemma conePullbackComparison_hom_fst
    {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {j i : I} (e : j ⟶ i) (X : Over (D.obj i)) :
    (conePullbackComparison D c e X).hom.left ≫
      pullback.fst X.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
        pullback.fst X.hom (D.map e) := by
  simp only [conePullbackComparison, Iso.trans_hom, Iso.symm_hom, Over.comp_left,
    Category.assoc, Iso.app_inv]
  rw [pullback_eqToIso_fst, pullbackComp_inv_fst]
  · rfl
  · exact c.w e

private lemma conePullbackComparison_eq_of_hom_fst
    {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {j i : I} (e : j ⟶ i) (X : Over (D.obj i))
    (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
      (Over.pullback (c.π.app i)).obj X)
    (hα : α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
        pullback.fst X.hom (D.map e)) :
    α = conePullbackComparison D c e X := by
  apply Iso.ext
  exact overPullback_hom_ext_of_fst (c.π.app i) X α.hom
    (conePullbackComparison D c e X).hom
    (hα.trans (conePullbackComparison_hom_fst D c e X).symm)

private lemma conePullbackComparison_naturality
    {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {j i : I} (e : j ⟶ i) {X Y : Over (D.obj i)} (f : X ⟶ Y) :
    (conePullbackComparison D c e X).hom ≫ (Over.pullback (c.π.app i)).map f =
      (Over.pullback (c.π.app j)).map ((Over.pullback (D.map e)).map f) ≫
        (conePullbackComparison D c e Y).hom := by
  apply overPullback_hom_ext_of_fst (c.π.app i) Y
  simp only [Over.comp_left, Category.assoc]
  rw [over_pullback_map_fst (c.π.app i) f,
    conePullbackComparison_hom_fst D c e Y]
  conv_rhs => rw [← Category.assoc]
  rw [over_pullback_map_fst (c.π.app j) ((Over.pullback (D.map e)).map f)]
  conv_rhs => rw [Category.assoc]
  rw [over_pullback_map_fst (D.map e) f]
  conv_lhs => rw [← Category.assoc, conePullbackComparison_hom_fst D c e X]
  simp only [Category.assoc]

private lemma exists_morphism_after_baseChange_canonical
    {I : Type*} [Category I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶
      (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (D.map e)).obj X ⟶ (Over.pullback (D.map e)).obj Y),
      (conePullbackComparison D c e X).hom ≫ f =
        (Over.pullback (c.π.app j)).map g ≫
          (conePullbackComparison D c e Y).hom := by
  obtain ⟨j, e, g, α, β, hα, hβ, hfg⟩ :=
    AlgebraicGeometry.exists_morphism_after_baseChange D c hc i X Y hX hY f
  refine ⟨j, e, g, ?_⟩
  rw [conePullbackComparison_eq_of_hom_fst D c e X α hα,
    conePullbackComparison_eq_of_hom_fst D c e Y β hβ] at hfg
  exact hfg

attribute [local instance] IsCofiltered.isConnected

@[reducible] private noncomputable def affineNeighborhoodOverlapDiagram
    (S : Scheme.{u}) (U : S.Opens) (s : S) : AffineNeighborhood S s ⥤ Scheme.{u} where
  obj V := (V.1.ι ⁻¹ᵁ U).toScheme
  map {V W} f := (S.homOfLE (leOfHom f)).resLE _ _ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι])
  map_id V := by
    apply (cancel_mono (V.1.ι ⁻¹ᵁ U).ι).1
    simp
  map_comp {V W T} f g := by
    apply (cancel_mono (T.1.ι ⁻¹ᵁ U).ι).1
    simp [Category.assoc]
@[reducible] private noncomputable def affineNeighborhoodOverlapInclusion
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    affineNeighborhoodOverlapDiagram S U s ⟶ affineNeighborhoodDiagram S s where
  app V := (V.1.ι ⁻¹ᵁ U).ι
  naturality := by intro V W f; simp [affineNeighborhoodOverlapDiagram, affineNeighborhoodDiagram]
@[reducible] private noncomputable def affineNeighborhoodOverlapCone
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    Cone (affineNeighborhoodOverlapDiagram S U s) where
  pt := (S.fromSpecStalk s ⁻¹ᵁ U).toScheme
  π :=
    { app := fun V ↦ ((affineNeighborhoodCone S s).π.app V).resLE _ _ (by
        change S.fromSpecStalk s ⁻¹ᵁ U ≤
          V.1.fromSpecStalkOfMem s V.2.2 ⁻¹ᵁ (V.1.ι ⁻¹ᵁ U)
        rw [← Scheme.Hom.comp_preimage, Scheme.Opens.fromSpecStalkOfMem_ι])
      naturality := by
        intro V W f
        apply (cancel_mono (W.1.ι ⁻¹ᵁ U).ι).1
        dsimp [affineNeighborhoodDiagram, affineNeighborhoodCone, Functor.const]
        simp only [Category.id_comp, Category.assoc, Scheme.Hom.resLE_comp_ι]
        apply (cancel_mono W.1.ι).1
        simp }
private noncomputable def affineNeighborhoodOverlapIsLimit
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    IsLimit (affineNeighborhoodOverlapCone S U s) := by
  apply isLimitOfIsPullbackOfIsConnected (affineNeighborhoodOverlapInclusion S U s)
    (affineNeighborhoodOverlapCone S U s) (affineNeighborhoodCone S s)
    (show (Cone.postcompose (affineNeighborhoodOverlapInclusion S U s)).obj
        (affineNeighborhoodOverlapCone S U s) ⟶ affineNeighborhoodCone S s from
      { hom := (S.fromSpecStalk s ⁻¹ᵁ U).ι
        w := by
          intro V
          simp [affineNeighborhoodOverlapInclusion, affineNeighborhoodOverlapCone,
            Scheme.Hom.resLE_comp_ι] })
  · intro V
    have : IsOpenImmersion ((affineNeighborhoodOverlapInclusion S U s).app V) := by
      dsimp [affineNeighborhoodOverlapInclusion]
      infer_instance
    apply IsOpenImmersion.isPullback
    · simp [affineNeighborhoodOverlapCone]
    · dsimp [affineNeighborhoodOverlapCone, affineNeighborhoodOverlapInclusion,
        affineNeighborhoodCone]
      simp only [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
        Scheme.Opens.fromSpecStalkOfMem_ι]
  · exact affineNeighborhoodIsLimit S s
private lemma affineNeighborhoodOverlap_compactSpace
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (V : AffineNeighborhood S s) :
    CompactSpace ((affineNeighborhoodOverlapDiagram S U s).obj V) := by
  have : IsAffine V.1.toScheme := V.2.1
  exact isCompact_iff_compactSpace.mp
    (IsRetrocompact.preimage_of_isOpenEmbedding V.1.ι.isOpenEmbedding hU).isCompact
private lemma affineNeighborhoodOverlap_quasiSeparatedSpace
    (S : Scheme.{u}) (U : S.Opens) (s : S) (V : AffineNeighborhood S s) :
    QuasiSeparatedSpace ((affineNeighborhoodOverlapDiagram S U s).obj V) := by
  have : IsAffine V.1.toScheme := V.2.1
  show QuasiSeparatedSpace (V.1.ι ⁻¹ᵁ U).toScheme
  exact (V.1.ι ⁻¹ᵁ U).ι.isOpenEmbedding.quasiSeparatedSpace
private lemma affineNeighborhoodOverlap_isAffineHom
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    {V W : AffineNeighborhood S s} (f : V ⟶ W) :
    IsAffineHom ((affineNeighborhoodOverlapDiagram S U s).map f) := by
  have : IsAffine V.1.toScheme := V.2.1
  have : IsAffine W.1.toScheme := W.2.1
  have h : IsPullback ((affineNeighborhoodOverlapDiagram S U s).map f)
      (V.1.ι ⁻¹ᵁ U).ι (W.1.ι ⁻¹ᵁ U).ι (S.homOfLE (leOfHom f)) := by
    apply IsOpenImmersion.isPullback
    · simp [affineNeighborhoodOverlapDiagram]
    · simp [← Scheme.Hom.comp_preimage]
  apply MorphismProperty.of_isPullback h.flip
  infer_instance
attribute [local instance] affineNeighborhoodOverlap_isAffineHom
private lemma exists_affineNeighborhood_overlapModel
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (X : Over (S.fromSpecStalk s ⁻¹ᵁ U).toScheme)
    (hX : FinitePresentation X.hom) :
    ∃ (V : AffineNeighborhood S s)
      (Y : Over ((affineNeighborhoodOverlapDiagram S U s).obj V)),
      FinitePresentation Y.hom ∧
      Nonempty (X ≅ (Over.pullback
        ((affineNeighborhoodOverlapCone S U s).π.app V)).obj Y) := by
  let := affineNeighborhoodOverlap_compactSpace S U s hU
  let := affineNeighborhoodOverlap_quasiSeparatedSpace S U s
  exact AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation
    (affineNeighborhoodOverlapDiagram S U s)
    (affineNeighborhoodOverlapCone S U s) (affineNeighborhoodOverlapIsLimit S U s) X hX

private lemma exists_affineNeighborhood_overlapMorphism
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (V : AffineNeighborhood S s)
    (X Y : Over ((affineNeighborhoodOverlapDiagram S U s).obj V))
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f : (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).obj X ⟶
      (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).obj Y) :
    ∃ (W : AffineNeighborhood S s) (e : W ⟶ V)
      (g : (Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj X ⟶
        (Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj Y)
      (α : (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app W)).obj
          ((Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj X) ≅
          (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).obj X)
      (β : (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app W)).obj
          ((Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj Y) ≅
          (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).obj Y),
      α.hom.left ≫ pullback.fst X.hom ((affineNeighborhoodOverlapCone S U s).π.app V) =
        pullback.fst ((Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj X).hom
          ((affineNeighborhoodOverlapCone S U s).π.app W) ≫
          pullback.fst X.hom ((affineNeighborhoodOverlapDiagram S U s).map e) ∧
      β.hom.left ≫ pullback.fst Y.hom ((affineNeighborhoodOverlapCone S U s).π.app V) =
        pullback.fst ((Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).obj Y).hom
          ((affineNeighborhoodOverlapCone S U s).π.app W) ≫
          pullback.fst Y.hom ((affineNeighborhoodOverlapDiagram S U s).map e) ∧
      α.hom ≫ f =
        (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app W)).map g ≫ β.hom := by
  let := affineNeighborhoodOverlap_compactSpace S U s hU
  let := affineNeighborhoodOverlap_quasiSeparatedSpace S U s
  exact AlgebraicGeometry.exists_morphism_after_baseChange
    (affineNeighborhoodOverlapDiagram S U s) (affineNeighborhoodOverlapCone S U s)
    (affineNeighborhoodOverlapIsLimit S U s) V X Y hX hY f

private lemma eventually_eq_affineNeighborhood_overlapMorphism
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (V : AffineNeighborhood S s)
    (X Y : Over ((affineNeighborhoodOverlapDiagram S U s).obj V))
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f g : X ⟶ Y)
    (hfg : (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).map f =
      (Over.pullback ((affineNeighborhoodOverlapCone S U s).π.app V)).map g) :
    ∃ (W : AffineNeighborhood S s) (e : W ⟶ V),
      (Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).map f =
      (Over.pullback ((affineNeighborhoodOverlapDiagram S U s).map e)).map g := by
  let := affineNeighborhoodOverlap_compactSpace S U s hU
  let := affineNeighborhoodOverlap_quasiSeparatedSpace S U s
  exact AlgebraicGeometry.eventually_eq_of_baseChange_eq
    (affineNeighborhoodOverlapDiagram S U s) (affineNeighborhoodOverlapCone S U s)
    (affineNeighborhoodOverlapIsLimit S U s) V X Y hX hY f g hfg

private noncomputable def germOpenAmbientIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙
      finitePresentationGermToGlueingData S U s ⋙ openComponent S U s ≅
      neighborhoodModelToAmbient S U s ⋙ Over.pullback U.ι :=
  Functor.isoWhiskerRight (eqToIso (finitePresentationGermToGlueingData_fac S U s))
    (openComponent S U s) ≪≫ neighborhoodModelOpenAmbientIso S U s

private noncomputable def germLocalAmbientIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).Q ⋙
      finitePresentationGermToGlueingData S U s ⋙ localComponent S U s ≅
      neighborhoodModelToAmbient S U s ⋙ Over.pullback (S.fromSpecStalk s) :=
  Functor.isoWhiskerRight (eqToIso (finitePresentationGermToGlueingData_fac S U s))
    (localComponent S U s) ≪≫ neighborhoodModelLocalAmbientIso S U s

private lemma germAmbientIso_overlapComparisonCompatible
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    [(finitePresentationGermToGlueingData S U s).IsEquivalence] :
    overlapComparisonCompatible S U s
      (finitePresentationGermToGlueingData S U s).asEquivalence
      (germOpenAmbientIso S U s) (germLocalAmbientIso S U s) := by
  intro X
  show (Over.pullback ((S.fromSpecStalk s) ∣_ U)).map
      ((germOpenAmbientIso S U s).hom.app X) ≫
        (canonicalOverlapIso S U s (Over.mk (X.hom ≫ X.neighborhood.V.ι))).hom =
    X.overlapIso.hom.hom ≫
      (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).map
        ((germLocalAmbientIso S U s).hom.app X)
  have ha : (germOpenAmbientIso S U s).hom.app X = X.openAmbientIso.hom := by
    have h1 : (germOpenAmbientIso S U s).hom.app X
        = (openComponent S U s).map (𝟙 _) ≫ X.openAmbientIso.hom := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  have hb : (germLocalAmbientIso S U s).hom.app X = X.localAmbientIso.hom := by
    have h1 : (germLocalAmbientIso S U s).hom.app X
        = (localComponent S U s).map (𝟙 _) ≫ X.localAmbientIso.hom := rfl
    rw [h1, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [ha, hb]
  exact neighborhoodModel_overlapComparison S U s X

private lemma locallyOfFinitePresentation_isZariskiLocal :
    IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) := by
  let : HasAffineProperty (@LocallyOfFinitePresentation.{u})
      (sourceAffineLocally RingHom.FinitePresentation) :=
    HasRingHomProperty.HasAffineProperty _
  exact HasRingHomProperty.instIsZariskiLocalAtTarget _

lemma quasiCompact_isZariskiLocal :
    IsZariskiLocalAtTarget (@QuasiCompact.{u}) := by
  let h : HasAffineProperty (@QuasiCompact.{u})
      (fun X _ _ _ ↦ CompactSpace X) :=
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  exact (HasAffineProperty.iff.mp h).1

private lemma quasiSeparated_isZariskiLocal :
    IsZariskiLocalAtTarget (@QuasiSeparated.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat

private lemma finitePresentation_of_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Y.OpenCover)
    (h : ∀ i, FinitePresentation (𝒰.pullbackHom f i)) :
    FinitePresentation f := by
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    locallyOfFinitePresentation_isZariskiLocal
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    quasiCompact_isZariskiLocal
  let : IsZariskiLocalAtTarget (@QuasiSeparated.{u}) :=
    quasiSeparated_isZariskiLocal
  exact ⟨IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i ↦ (h i).1),
    IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i ↦ (h i).2.1),
    IsZariskiLocalAtTarget.of_openCover 𝒰 (fun i ↦ (h i).2.2)⟩

private lemma finitePresentation_of_twoOpenPullbacks
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (h : U ⊔ V = ⊤)
    (hU : FinitePresentation (pullback.snd f U.ι))
    (hV : FinitePresentation (pullback.snd f V.ι)) :
    FinitePresentation f := by
  let W : Bool → Y.Opens := fun b ↦ if b then U else V
  have hW : IsOpenCover W := by
    show (⨆ b, W b) = ⊤
    simpa [W, iSup_bool_eq] using h
  apply finitePresentation_of_openCover f (Y.openCoverOfIsOpenCover W hW)
  intro b
  cases b
  · exact hV
  · exact hU

/-- Alias of `AlgebraicGeometry.morphismProperty_congr`. -/
private alias morphismProperty_congr := AlgebraicGeometry.morphismProperty_congr

private lemma property_relativeGluing_toBase
    {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (d : 𝒰.RelativeGluingData) (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (h : ∀ i, P (d.natTrans.app i)) : P d.toBase := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰
  intro i
  show P (pullback.snd d.toBase (𝒰.f i))
  exact (MorphismProperty.cancel_left_of_respectsIso P
      (d.isPullback_natTrans_ι_toBase i).flip.isoPullback.hom
      (pullback.snd d.toBase (𝒰.f i))).mp
    (morphismProperty_congr P
      (IsPullback.isoPullback_hom_snd (d.isPullback_natTrans_ι_toBase i).flip).symm (h i))

private lemma relativeGluingData_finitePresentation
    {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
    [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (d : 𝒰.RelativeGluingData)
    (h : ∀ i, FinitePresentation (d.natTrans.app i)) :
    FinitePresentation d.toBase := by
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    locallyOfFinitePresentation_isZariskiLocal
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) := quasiCompact_isZariskiLocal
  let : IsZariskiLocalAtTarget (@QuasiSeparated.{u}) := quasiSeparated_isZariskiLocal
  exact ⟨property_relativeGluing_toBase d _ (fun i ↦ (h i).1),
    property_relativeGluing_toBase d _ (fun i ↦ (h i).2.1),
    property_relativeGluing_toBase d _ (fun i ↦ (h i).2.2)⟩

section CompatibleRelativeGluing

variable (D : AlgebraicGeometry.CompatibleRelativeGluingData.{u})
/-- The category structure on the indexing set of the cover recorded in `D`. -/
local instance : Category D.cover.I₀ := D.category
/-- The cover is locally directed, as recorded in `D`. -/
local instance : D.cover.LocallyDirected := D.locallyDirected
/-- There is at most one inclusion between two members of the cover, as recorded in `D`. -/
local instance : Quiver.IsThin D.cover.I₀ := D.thin
/-- The indexing category of the cover is small, as recorded in `D`. -/
local instance : Small.{u} D.cover.I₀ := D.small

private noncomputable def compatibleRelativeGluingData_overHom :
    Over.mk D.source.toBase ⟶ Over.mk D.target.toBase :=
  Over.homMk (colimMap D.localHom)
    (AlgebraicGeometry.CompatibleRelativeGluingData.colimMap_localHom_toBase D)

end CompatibleRelativeGluing

private lemma hom_ext_of_sup_eq_top {X Y : Scheme.{u}}
    (U V : X.Opens) (h : U ⊔ V = ⊤) (f g : X ⟶ Y)
    (hU : U.ι ≫ f = U.ι ≫ g) (hV : V.ι ≫ f = V.ι ≫ g) : f = g := by
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : IsOpenCover W := by
    show (⨆ b, W b) = ⊤
    simpa [W, iSup_bool_eq] using h
  apply (X.openCoverOfIsOpenCover W hW).hom_ext
  intro b
  cases b
  · show V.ι ≫ f = V.ι ≫ g
    exact hV
  · show U.ι ≫ f = U.ι ≫ g
    exact hU

private lemma exists_gluedHom_of_sup_eq_top {X Y : Scheme.{u}}
    (U V : X.Opens) (h : U ⊔ V = ⊤)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (hUV : pullback.fst U.ι V.ι ≫ fU = pullback.snd U.ι V.ι ≫ fV) :
    ∃ f : X ⟶ Y, U.ι ≫ f = fU ∧ V.ι ≫ f = fV := by
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : IsOpenCover W := by
    show (⨆ b, W b) = ⊤
    simpa [W, iSup_bool_eq] using h
  let C := X.openCoverOfIsOpenCover W hW
  let fs : ∀ b : C.I₀, C.X b ⟶ Y := by
    intro b
    cases b
    · exact fV
    · exact fU
  have hfs : ∀ b c, pullback.fst (C.f b) (C.f c) ≫ fs b =
      pullback.snd (C.f b) (C.f c) ≫ fs c := by
    intro b c
    cases b <;> cases c
    · show pullback.fst V.ι V.ι ≫ fV = pullback.snd V.ι V.ι ≫ fV
      congr 1
      exact (cancel_mono V.ι).1 (pullback.condition)
    · show pullback.fst V.ι U.ι ≫ fV = pullback.snd V.ι U.ι ≫ fU
      apply (cancel_epi (pullbackSymmetry U.ι V.ι).hom).1
      simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd] using hUV.symm
    · show pullback.fst U.ι V.ι ≫ fU = pullback.snd U.ι V.ι ≫ fV
      exact hUV
    · show pullback.fst U.ι U.ι ≫ fU = pullback.snd U.ι U.ι ≫ fU
      congr 1
      exact (cancel_mono U.ι).1 (pullback.condition)
  refine ⟨C.glueMorphisms fs hfs, ?_, ?_⟩
  · exact C.ι_glueMorphisms fs hfs true
  · exact C.ι_glueMorphisms fs hfs false

private noncomputable def glueAlongTwoOpens
    {X Y W : Scheme.{u}} (i₁ : W ⟶ X) (i₂ : W ⟶ Y)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] : Scheme.GlueData.{u} := by
  classical
  have noThree (i j k : ULift.{u} Bool) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      False := by
    rcases i with ⟨i⟩; rcases j with ⟨j⟩; rcases k with ⟨k⟩
    cases i <;> cases j <;> cases k <;> simp_all
  let D : CategoryTheory.GlueData' Scheme.{u} := {
    J := ULift.{u} Bool
    U := fun i => if i.down then Y else X
    V := fun _ _ _ => W
    f := fun i _ _ => by
      rcases i with ⟨i⟩
      cases i
      · exact i₁
      · exact i₂
    f_mono := by rintro ⟨i⟩ j h; cases i <;> infer_instance
    t := fun _ _ _ => 𝟙 W
    t' := fun i j k hij hik hjk => (noThree i j k hij hik hjk).elim
    t_fac := fun i j k hij hik hjk => (noThree i j k hij hik hjk).elim
    t_inv := by intros; simp
    cocycle := fun i j k hij hik hjk => (noThree i j k hij hik hjk).elim }
  refine ⟨CategoryTheory.GlueData.ofGlueData' D, ?_⟩
  intro i j
  dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
  split_ifs
  · infer_instance
  · rcases i with ⟨i⟩; cases i <;> dsimp [D] <;> infer_instance


private theorem exists_gluedScheme_of_openImmersions
    {A B W S : Scheme.{u}} (f₁ : A ⟶ S) (f₂ : B ⟶ S)
    (i₁ : W ⟶ A) (i₂ : W ⟶ B) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (h : i₁ ≫ f₁ = i₂ ≫ f₂) :
    ∃ (X : Scheme.{u}) (j₁ : A ⟶ X) (j₂ : B ⟶ X) (f : X ⟶ S),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      i₁ ≫ j₁ = i₂ ≫ j₂ ∧ j₁ ≫ f = f₁ ∧ j₂ ≫ f = f₂ ∧
      (∀ x : X, x ∈ Set.range j₁ ∨ x ∈ Set.range j₂) := by
  let D := glueAlongTwoOpens i₁ i₂
  let F : ∀ i, D.U i ⟶ S := fun i => by
    rcases i with ⟨i⟩
    cases i
    · exact f₁
    · exact f₂
  have hF (ij : D.J × D.J) :
      D.toGlueData.diagram.fst ij ≫ F ij.1 = D.toGlueData.diagram.snd ij ≫ F ij.2 := by
    dsimp only [CategoryTheory.GlueData.diagram]
    rcases ij with ⟨⟨i⟩, ⟨j⟩⟩
    cases i <;> cases j
    · simp [D, glueAlongTwoOpens, F, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f']
    · simp [D, glueAlongTwoOpens, F, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', Category.assoc, h]
    · simp [D, glueAlongTwoOpens, F, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', Category.assoc, h]
    · simp [D, glueAlongTwoOpens, F, CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f']
  let f : D.glued ⟶ S := Multicoequalizer.desc D.toGlueData.diagram S F hF
  have hf (i : D.J) : D.ι i ≫ f = F i :=
    Multicoequalizer.π_desc _ _ _ _ _
  let j₁ : A ⟶ D.glued := D.ι ⟨false⟩
  let j₂ : B ⟶ D.glued := D.ι ⟨true⟩
  have h₁ : j₁ ≫ f = f₁ := hf ⟨false⟩
  have h₂ : j₂ ≫ f = f₂ := hf ⟨true⟩
  have hj₁ : IsOpenImmersion j₁ := D.ι_isOpenImmersion ⟨false⟩
  have hj₂ : IsOpenImmersion j₂ := D.ι_isOpenImmersion ⟨true⟩
  have hV : D.V (⟨false⟩, ⟨true⟩) = W := by
    simp [D, glueAlongTwoOpens, CategoryTheory.GlueData.ofGlueData']
  let e : W ≅ D.V (⟨false⟩, ⟨true⟩) := eqToIso hV.symm
  have he₁ : e.hom ≫ D.f ⟨false⟩ ⟨true⟩ = i₁ := by
    simp only [glueAlongTwoOpens, ne_eq, GlueData.ofGlueData', dite_eq_ite, GlueData'.f',
      Bool.false_eq_true, ↓dreduceIte, ULift.up.injEq, ↓reduceDIte, ← Category.assoc, D, e]
    show (eqToHom hV.symm ≫ eqToHom hV) ≫ i₁ = i₁
    simp
  have he₂ : e.hom ≫ D.t ⟨false⟩ ⟨true⟩ ≫ D.f ⟨true⟩ ⟨false⟩ = i₂ := by
    simp only [glueAlongTwoOpens, ne_eq, GlueData.ofGlueData', dite_eq_ite, GlueData'.f',
      ↓dreduceIte, ULift.up.injEq, Bool.false_eq_true, Bool.true_eq_false, ↓reduceDIte,
      ↓reduceIte, eqToHom_naturality, Category.comp_id, eqToHom_trans, ← Category.assoc, D, e]
    show (eqToHom hV.symm ≫ eqToHom hV) ≫ i₂ = i₂
    simp
  have hglue : i₁ ≫ j₁ = i₂ ≫ j₂ := by
    rw [← he₁, ← he₂]
    calc
      _ = e.hom ≫ (D.f ⟨false⟩ ⟨true⟩ ≫ D.ι ⟨false⟩) :=
        Category.assoc _ _ _
      _ = e.hom ≫ (D.t ⟨false⟩ ⟨true⟩ ≫ D.f ⟨true⟩ ⟨false⟩ ≫
          D.ι ⟨true⟩) :=
        congrArg (e.hom ≫ ·) (D.glue_condition ⟨false⟩ ⟨true⟩).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hcover (x : D.glued) : x ∈ Set.range j₁ ∨ x ∈ Set.range j₂ := by
    obtain ⟨⟨i⟩, y, rfl⟩ := D.ι_jointly_surjective x
    cases i
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  exact ⟨D.glued, j₁, j₂, f, hj₁, hj₂, hglue, h₁, h₂, hcover⟩

private lemma overlapOpenImmersions
    {A B T : Scheme.{u}} (i : T ⟶ A) (j : T ⟶ B)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (X : Over A) (Y : Over B)
    (e : (Over.pullback i).obj X ≅ (Over.pullback j).obj Y) :
    IsOpenImmersion (pullback.fst X.hom i) ∧
      IsOpenImmersion (e.hom.left ≫ pullback.fst Y.hom j) := by
  have : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  exact ⟨inferInstance, inferInstance⟩

private theorem exists_gluedOver_of_openOverlap
    {A B T S : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    (i : T ⟶ A) (j : T ⟶ B)
    [IsOpenImmersion i] [IsOpenImmersion j] (hbase : i ≫ a = j ≫ b)
    (X : Over A) (Y : Over B)
    (e : (Over.pullback i).obj X ≅ (Over.pullback j).obj Y) :
    ∃ (Z : Over S) (k₁ : X.left ⟶ Z.left) (k₂ : Y.left ⟶ Z.left),
      IsOpenImmersion k₁ ∧ IsOpenImmersion k₂ ∧
      pullback.fst X.hom i ≫ k₁ =
        (e.hom.left ≫ pullback.fst Y.hom j) ≫ k₂ ∧
      k₁ ≫ Z.hom = X.hom ≫ a ∧ k₂ ≫ Z.hom = Y.hom ≫ b ∧
      (∀ z : Z.left, z ∈ Set.range k₁ ∨ z ∈ Set.range k₂) := by
  let p : pullback X.hom i ⟶ X.left := pullback.fst X.hom i
  let q : pullback X.hom i ⟶ Y.left := e.hom.left ≫ pullback.fst Y.hom j
  have hmaps : p ≫ (X.hom ≫ a) = q ≫ (Y.hom ≫ b) := by
    have he : e.hom.left ≫ pullback.snd Y.hom j = pullback.snd X.hom i :=
      e.hom.w
    calc
      p ≫ (X.hom ≫ a) = pullback.snd X.hom i ≫ (i ≫ a) := by
        simp only [p, ← Category.assoc, pullback.condition]
      _ = pullback.snd X.hom i ≫ (j ≫ b) := by rw [hbase]
      _ = q ≫ (Y.hom ≫ b) := by
        have h : pullback.snd X.hom i ≫ j = q ≫ Y.hom := by
          rw [← he]
          dsimp [q]
          rw [Category.assoc, ← pullback.condition]
          rfl
        calc
          pullback.snd X.hom i ≫ (j ≫ b) =
              (pullback.snd X.hom i ≫ j) ≫ b := (Category.assoc _ _ _).symm
          _ = (q ≫ Y.hom) ≫ b := congrArg (· ≫ b) h
          _ = q ≫ (Y.hom ≫ b) := Category.assoc _ _ _
  have hpq := overlapOpenImmersions i j X Y e
  let : IsOpenImmersion p := hpq.1
  let : IsOpenImmersion q := hpq.2
  obtain ⟨Z, k₁, k₂, f, hk₁, hk₂, hk, hf₁, hf₂, hcover⟩ :=
    exists_gluedScheme_of_openImmersions (X.hom ≫ a) (Y.hom ≫ b) p q hmaps
  exact ⟨Over.mk f, k₁, k₂, hk₁, hk₂, hk, hf₁, hf₂, hcover⟩

universe uC vC uD vD

private theorem localizationLift_isEquivalence_of_rightFractions
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (F : C ⥤ D) (hF : W.IsInvertedBy F)
    (hess : F.EssSurj)
    (hfull : ∀ (X Y : C) (f : F.obj X ⟶ F.obj Y),
      ∃ φ : W.RightFraction X Y, φ.map F hF = f)
    (hfaith : ∀ (X Y : C) (φ ψ : W.RightFraction X Y),
      φ.map F hF = ψ.map F hF → W.RightFractionRel φ ψ) :
    (Localization.Construction.lift F hF).IsEquivalence := by
  let G := Localization.Construction.lift F hF
  let η : W.Q ⋙ G ≅ F := eqToIso (Localization.Construction.fac F hF)
  have hmap {X Y : C} (φ : W.RightFraction X Y) :
      G.map (φ.map W.Q W.Q_inverts) ≫ η.hom.app Y = η.hom.app X ≫ φ.map F hF := by
    have hs : G.map (W.Q.map φ.s) ≫ η.hom.app X = η.hom.app φ.X' ≫ F.map φ.s := by
      simpa only [Functor.comp_map] using η.hom.naturality φ.s
    have hf : G.map (W.Q.map φ.f) ≫ η.hom.app Y = η.hom.app φ.X' ≫ F.map φ.f := by
      simpa only [Functor.comp_map] using η.hom.naturality φ.f
    have : IsIso (F.map φ.s) := hF _ φ.hs
    have : IsIso (W.Q.map φ.s) := W.Q_inverts _ φ.hs
    have : IsIso (G.map (W.Q.map φ.s)) := Functor.map_isIso G (W.Q.map φ.s)
    have hstep : inv (G.map (W.Q.map φ.s)) ≫ η.hom.app φ.X' =
        η.hom.app X ≫ inv (F.map φ.s) := by
      apply (cancel_mono (F.map φ.s)).1
      calc
        (inv (G.map (W.Q.map φ.s)) ≫ η.hom.app φ.X') ≫ F.map φ.s =
            inv (G.map (W.Q.map φ.s)) ≫ (η.hom.app φ.X' ≫ F.map φ.s) := by
              simp [Category.assoc]
        _ = inv (G.map (W.Q.map φ.s)) ≫ (G.map (W.Q.map φ.s) ≫ η.hom.app X) := by rw [hs]
        _ = η.hom.app X := by simp
        _ = (η.hom.app X ≫ inv (F.map φ.s)) ≫ F.map φ.s := by simp
    dsimp [MorphismProperty.RightFraction.map]
    simp only [Functor.map_comp, Functor.map_inv]
    calc
      (inv (G.map (W.Q.map φ.s)) ≫ G.map (W.Q.map φ.f)) ≫ η.hom.app Y =
          inv (G.map (W.Q.map φ.s)) ≫ (G.map (W.Q.map φ.f) ≫ η.hom.app Y) := by
            simp [Category.assoc]
      _ = inv (G.map (W.Q.map φ.s)) ≫ (η.hom.app φ.X' ≫ F.map φ.f) := by rw [hf]
      _ = (inv (G.map (W.Q.map φ.s)) ≫ η.hom.app φ.X') ≫ F.map φ.f := by
            simp [Category.assoc]
      _ = (η.hom.app X ≫ inv (F.map φ.s)) ≫ F.map φ.f := by rw [hstep]
      _ = η.hom.app X ≫ (inv (F.map φ.s) ≫ F.map φ.f) := by simp [Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    intro X Y f g h
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction W.Q W f
    obtain ⟨ψ, rfl⟩ := Localization.exists_rightFraction W.Q W g
    apply (MorphismProperty.RightFraction.map_eq_iff W.Q W φ ψ).2
    apply hfaith X Y φ ψ
    apply (cancel_epi (η.hom.app X)).1
    rw [← hmap φ, ← hmap ψ]
    exact congrArg (fun k ↦ k ≫ η.hom.app Y) h
  · refine ⟨?_⟩
    intro X Y f
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    obtain ⟨φ, hφ⟩ := hfull X Y (η.inv.app X ≫ f ≫ η.hom.app Y)
    refine ⟨φ.map W.Q W.Q_inverts, ?_⟩
    apply (cancel_mono (η.hom.app Y)).1
    refine Eq.trans (hmap φ) ?_
    refine Eq.trans (congrArg (fun k ↦ η.hom.app X ≫ k) hφ) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k ↦ k ≫ (f ≫ η.hom.app Y)) (η.hom_inv_id_app X)) ?_
    exact Category.id_comp _
  · refine ⟨?_⟩
    intro Y
    obtain ⟨X, ⟨e⟩⟩ := hess.mem_essImage Y
    exact ⟨W.Q.obj X,
      ⟨(⟨η.hom.app X, η.inv.app X, by simp, by simp⟩ : _ ≅ F.obj X).trans e⟩⟩

private noncomputable def glueingEquivalenceNearPoint_of_isEquivalence
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (h : (finitePresentationGermToGlueingData S U s).IsEquivalence) :
    { e : FinitePresentationGerm S U s ≌ glueingDataNearPoint S U s //
      ∃ a : (((FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ openComponent S U s) ≅
        (neighborhoodModelToAmbient S U s ⋙ Over.pullback U.ι)),
      ∃ b : (((FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ localComponent S U s) ≅
        (neighborhoodModelToAmbient S U s ⋙ Over.pullback (S.fromSpecStalk s))),
      overlapComparisonCompatible S U s e a b } := by
  let := h
  exact ⟨(finitePresentationGermToGlueingData S U s).asEquivalence,
    germOpenAmbientIso S U s, germLocalAmbientIso S U s,
    germAmbientIso_overlapComparisonCompatible S U s⟩

private lemma comp_eq_of_range_eq {X Y A B : Scheme.{u}} (p : A ⟶ X) (q : B ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion q] (hr : Set.range p = Set.range q)
    {a b : X ⟶ Y} (h : p ≫ a = p ≫ b) : q ≫ a = q ≫ b := by
  have he := IsOpenImmersion.isoOfRangeEq_hom_fac p q hr
  apply (cancel_epi (IsOpenImmersion.isoOfRangeEq p q hr).hom).1
  rw [← Category.assoc, ← Category.assoc, he]
  exact h

private lemma hom_ext_of_range_union {X Y A B : Scheme.{u}} (p : A ⟶ X) (q : B ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion q]
    (hcover : Set.range p ∪ Set.range q = Set.univ)
    {a b : X ⟶ Y} (ha : p ≫ a = p ≫ b) (hb : q ≫ a = q ≫ b) : a = b := by
  have hsup : p.opensRange ⊔ q.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simpa using hcover
  refine hom_ext_of_sup_eq_top _ _ hsup a b ?_ ?_
  · exact comp_eq_of_range_eq p _ (by simp) ha
  · exact comp_eq_of_range_eq q _ (by simp) hb

private lemma exists_glued_hom_of_range_union {X Y A B : Scheme.{u}} (p : A ⟶ X) (q : B ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion q]
    (hcover : Set.range p ∪ Set.range q = Set.univ)
    (fA : A ⟶ Y) (fB : B ⟶ Y)
    (hAB : pullback.fst p q ≫ fA = pullback.snd p q ≫ fB) :
    ∃ f : X ⟶ Y, p ≫ f = fA ∧ q ≫ f = fB := by
  have hsup : p.opensRange ⊔ q.opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simpa using hcover
  let eA := IsOpenImmersion.isoOfRangeEq p p.opensRange.ι (by simp)
  let eB := IsOpenImmersion.isoOfRangeEq q q.opensRange.ι (by simp)
  have hA : eA.hom ≫ p.opensRange.ι = p := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hB : eB.hom ≫ q.opensRange.ι = q := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hpA : eA.inv ≫ p = p.opensRange.ι := by rw [Iso.inv_comp_eq]; exact hA.symm
  have hpB : eB.inv ≫ q = q.opensRange.ι := by rw [Iso.inv_comp_eq]; exact hB.symm
  have hcond : pullback.fst p.opensRange.ι q.opensRange.ι ≫ (eA.inv ≫ fA) =
      pullback.snd p.opensRange.ι q.opensRange.ι ≫ (eB.inv ≫ fB) := by
    let m : pullback p.opensRange.ι q.opensRange.ι ⟶ pullback p q :=
      pullback.lift (pullback.fst p.opensRange.ι q.opensRange.ι ≫ eA.inv)
        (pullback.snd p.opensRange.ι q.opensRange.ι ≫ eB.inv) (by
          rw [Category.assoc, Category.assoc, hpA, hpB]
          exact pullback.condition)
    have h1 : m ≫ pullback.fst p q =
        pullback.fst p.opensRange.ι q.opensRange.ι ≫ eA.inv := pullback.lift_fst _ _ _
    have h2 : m ≫ pullback.snd p q =
        pullback.snd p.opensRange.ι q.opensRange.ι ≫ eB.inv := pullback.lift_snd _ _ _
    calc pullback.fst p.opensRange.ι q.opensRange.ι ≫ eA.inv ≫ fA
        = (pullback.fst p.opensRange.ι q.opensRange.ι ≫ eA.inv) ≫ fA :=
          (Category.assoc _ _ _).symm
      _ = (m ≫ pullback.fst p q) ≫ fA := by rw [h1]
      _ = m ≫ pullback.fst p q ≫ fA := Category.assoc _ _ _
      _ = m ≫ pullback.snd p q ≫ fB := congrArg (fun k ↦ m ≫ k) hAB
      _ = (m ≫ pullback.snd p q) ≫ fB := (Category.assoc _ _ _).symm
      _ = (pullback.snd p.opensRange.ι q.opensRange.ι ≫ eB.inv) ≫ fB := by rw [h2]
      _ = _ := Category.assoc _ _ _
  obtain ⟨f, h₁, h₂⟩ := exists_gluedHom_of_sup_eq_top p.opensRange q.opensRange hsup
    (eA.inv ≫ fA) (eB.inv ≫ fB) hcond
  refine ⟨f, ?_, ?_⟩
  · rw [← hA, Category.assoc, h₁, Iso.hom_inv_id_assoc]
  · rw [← hB, Category.assoc, h₂, Iso.hom_inv_id_assoc]

private noncomputable def pullbackCompIsoOver {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Over.pullback (f ≫ g) ≅ Over.pullback g ⋙ Over.pullback f := by
  classical
  refine NatIso.ofComponents (fun A => ?_) ?_
  · let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Z :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
    exact (MorphismProperty.Over.forget (⊤ : MorphismProperty (Scheme.{u})) (⊤) X).mapIso
      ((MorphismProperty.Over.pullbackComp
        (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) f g).app A')
  · intro A B m
    let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Z :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
    let B' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Z :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) B.hom (by trivial)
    let m' : A' ⟶ B' := MorphismProperty.Over.Hom.mk (P := ⊤) (Q := ⊤) m trivial
    let F := MorphismProperty.Over.forget (⊤ : MorphismProperty (Scheme.{u})) (⊤) X
    let c := (MorphismProperty.Over.pullbackComp
      (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) f g)
    change F.map (((MorphismProperty.Over.pullback (⊤ : MorphismProperty (Scheme.{u})) (⊤)
        (f ≫ g)).map m') ≫ c.hom.app B') =
      F.map (c.hom.app A' ≫
        ((MorphismProperty.Over.pullback (⊤ : MorphismProperty (Scheme.{u})) (⊤) g) ⋙
          MorphismProperty.Over.pullback (⊤ : MorphismProperty (Scheme.{u})) (⊤) f).map m')
    exact congrArg F.map (c.hom.naturality m')

private lemma pullbackCompIsoOver_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Over Z) :
    ((pullbackCompIsoOver f g).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
    pullback.fst A.hom (f ≫ g) := by
  let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Z :=
    MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
  dsimp [pullbackCompIsoOver]
  show ((MorphismProperty.Over.pullbackComp
    (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) f g).hom.app A').left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
    pullback.fst A.hom (f ≫ g)
  exact MorphismProperty.Over.pullbackComp_left_fst_fst
    (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) f g A'

private lemma pullbackCompIsoOver_inv_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((pullbackCompIsoOver f g).inv.app A).left ≫ pullback.fst A.hom (f ≫ g) =
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g := by
  calc
    _ = ((pullbackCompIsoOver f g).inv.app A).left ≫
        ((pullbackCompIsoOver f g).hom.app A).left ≫
          pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g := by
      rw [pullbackCompIsoOver_fst]
    _ = _ := by
      have hcancel : ((pullbackCompIsoOver f g).inv.app A).left ≫
          ((pullbackCompIsoOver f g).hom.app A).left = 𝟙 _ := by
        show ((pullbackCompIsoOver f g).app A).inv.left ≫
            ((pullbackCompIsoOver f g).app A).hom.left = 𝟙 _
        exact congrArg (fun q :
          ((Over.pullback g ⋙ Over.pullback f).obj A ⟶
            (Over.pullback g ⋙ Over.pullback f).obj A) => q.left)
          ((pullbackCompIsoOver f g).app A).inv_hom_id
      rw [← Category.assoc, hcancel, Category.id_comp]

private noncomputable def pullbackCongrIsoOver {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    (Over.pullback f : Over Y ⥤ Over X) ≅ (Over.pullback g : Over Y ⥤ Over X) := by
  classical
  refine NatIso.ofComponents (fun A => ?_) ?_
  · let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Y :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
    exact (MorphismProperty.Over.forget (⊤ : MorphismProperty (Scheme.{u})) (⊤) X).mapIso
      ((MorphismProperty.Over.pullbackCongr
        (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) (f := f) (g := g) h).app A')
  · intro A B m
    let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Y :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
    let B' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Y :=
      MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) B.hom (by trivial)
    let m' : A' ⟶ B' := MorphismProperty.Over.Hom.mk (P := ⊤) (Q := ⊤) m trivial
    let F := MorphismProperty.Over.forget (⊤ : MorphismProperty (Scheme.{u})) (⊤) X
    let c := MorphismProperty.Over.pullbackCongr
      (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) (f := f) (g := g) h
    change F.map
        (((MorphismProperty.Over.pullback (⊤ : MorphismProperty (Scheme.{u})) (⊤) f).map m') ≫
          c.hom.app B') =
      F.map (c.hom.app A' ≫
        (MorphismProperty.Over.pullback (⊤ : MorphismProperty (Scheme.{u})) (⊤) g).map m')
    exact congrArg F.map (c.hom.naturality m')

private lemma pullbackCongrIsoOver_fst {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (A : Over Y) :
    ((pullbackCongrIsoOver h).hom.app A).left ≫ pullback.fst A.hom g =
      pullback.fst A.hom f := by
  let A' : (⊤ : MorphismProperty (Scheme.{u})).Over (⊤) Y :=
    MorphismProperty.Over.mk (P := ⊤) (Q := ⊤) A.hom (by trivial)
  dsimp [pullbackCongrIsoOver]
  show ((MorphismProperty.Over.pullbackCongr
    (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) h).hom.app A').left ≫
      pullback.fst A.hom g = pullback.fst A.hom f
  exact MorphismProperty.Over.pullbackCongr_hom_app_left_fst
    (P := (⊤ : MorphismProperty (Scheme.{u}))) (Q := ⊤) h A'

/-- A morphism of schemes over `T` landing in a base change along `g` is pinned down by its
composite with the first projection. -/
lemma overPullback_hom_ext_fst {T B : Scheme.{u}} (g : T ⟶ B) {Y : Over B} {A : Over T}
    {m n : A ⟶ (Over.pullback g).obj Y}
    (h : m.left ≫ pullback.fst Y.hom g = n.left ≫ pullback.fst Y.hom g) : m = n := by
  apply Over.OverMorphism.ext
  refine pullback.hom_ext h ?_
  have hm : m.left ≫ pullback.snd Y.hom g = A.hom := m.w
  have hn : n.left ≫ pullback.snd Y.hom g = A.hom := n.w
  rw [hm, hn]

/-- The canonical comparison between an iterated base change and a single one exists and is
determined by its composite with the first projection. -/
private lemma exists_nestedPullbackIso {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) (X : Over B) :
    ∃ N : (Over.pullback f).obj ((Over.pullback g).obj X) ≅ (Over.pullback h).obj X,
      N.hom.left ≫ pullback.fst X.hom h =
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  refine ⟨((pullbackCompIsoOver f g).app X).symm ≪≫ (pullbackCongrIsoOver hfg).app X, ?_⟩
  have h1 : ((pullbackCompIsoOver f g).inv.app X).left ≫ pullback.fst X.hom (f ≫ g) =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g :=
    pullbackCompIsoOver_inv_fst f g X
  have h2 : ((pullbackCongrIsoOver hfg).hom.app X).left ≫ pullback.fst X.hom h =
      pullback.fst X.hom (f ≫ g) := pullbackCongrIsoOver_fst hfg X
  show (((pullbackCompIsoOver f g).inv.app X) ≫
    ((pullbackCongrIsoOver hfg).hom.app X)).left ≫ pullback.fst X.hom h = _
  rw [Over.comp_left, Category.assoc, h2, h1]

/-- The canonical comparison between an iterated base change and a single one. -/
private noncomputable def nestedPullbackIso {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) (X : Over B) :
    (Over.pullback f).obj ((Over.pullback g).obj X) ≅ (Over.pullback h).obj X :=
  (exists_nestedPullbackIso f g h hfg X).choose

private lemma nestedPullbackIso_fst {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) (X : Over B) :
    (nestedPullbackIso f g h hfg X).hom.left ≫ pullback.fst X.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g :=
  (exists_nestedPullbackIso f g h hfg X).choose_spec

private lemma nestedPullbackIso_inv_fst {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) (X : Over B) :
    (nestedPullbackIso f g h hfg X).inv.left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
      pullback.fst X.hom h := by
  rw [← nestedPullbackIso_fst f g h hfg X, ← Category.assoc,
    ← Over.comp_left, Iso.inv_hom_id]
  simp

private lemma nestedPullbackIso_eq_of_fst {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) (X : Over B)
    (N : (Over.pullback f).obj ((Over.pullback g).obj X) ≅ (Over.pullback h).obj X)
    (hN : N.hom.left ≫ pullback.fst X.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g) :
    N = nestedPullbackIso f g h hfg X := by
  apply Iso.ext
  apply overPullback_hom_ext_fst h
  rw [hN, nestedPullbackIso_fst]

private lemma nestedPullbackIso_naturality {T B' B : Scheme.{u}}
    (f : T ⟶ B') (g : B' ⟶ B) (h : T ⟶ B) (hfg : f ≫ g = h) {X Y : Over B} (m : X ⟶ Y) :
    (Over.pullback f).map ((Over.pullback g).map m) ≫ (nestedPullbackIso f g h hfg Y).hom =
      (nestedPullbackIso f g h hfg X).hom ≫ (Over.pullback h).map m := by
  have h1 : ((Over.pullback f).map ((Over.pullback g).map m)).left ≫
      pullback.fst (pullback.snd Y.hom g) f =
      pullback.fst (pullback.snd X.hom g) f ≫ ((Over.pullback g).map m).left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback g).map m).left ≫ pullback.fst Y.hom g =
      pullback.fst X.hom g ≫ m.left := pullback.lift_fst _ _ _
  have h3 : ((Over.pullback h).map m).left ≫ pullback.fst Y.hom h =
      pullback.fst X.hom h ≫ m.left := pullback.lift_fst _ _ _
  apply overPullback_hom_ext_fst h
  have hL : ((Over.pullback f).map ((Over.pullback g).map m) ≫
        (nestedPullbackIso f g h hfg Y).hom).left ≫ pullback.fst Y.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g ≫ m.left := by
    rw [Over.comp_left, Category.assoc, nestedPullbackIso_fst, ← Category.assoc, h1,
      Category.assoc, h2]
  have hR : ((nestedPullbackIso f g h hfg X).hom ≫ (Over.pullback h).map m).left ≫
        pullback.fst Y.hom h =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g ≫ m.left := by
    rw [Over.comp_left, Category.assoc, h3, ← Category.assoc, nestedPullbackIso_fst,
      Category.assoc]
  exact hL.trans hR.symm

/-- The two ways of comparing a triply iterated base change with a single one agree. -/
private lemma nestedPullbackIso_assoc {T B₂ B₁ B : Scheme.{u}}
    (f : T ⟶ B₂) (g : B₂ ⟶ B₁) (k : B₁ ⟶ B)
    (fg : T ⟶ B₁) (gk : B₂ ⟶ B) (fgk : T ⟶ B)
    (hfg : f ≫ g = fg) (hgk : g ≫ k = gk) (hfgk₁ : fg ≫ k = fgk) (hfgk₂ : f ≫ gk = fgk)
    (X : Over B) :
    (Over.pullback f).map (nestedPullbackIso g k gk hgk X).hom ≫
        (nestedPullbackIso f gk fgk hfgk₂ X).hom =
      (nestedPullbackIso f g fg hfg ((Over.pullback k).obj X)).hom ≫
        (nestedPullbackIso fg k fgk hfgk₁ X).hom := by
  have h1 : ((Over.pullback f).map (nestedPullbackIso g k gk hgk X).hom).left ≫
      pullback.fst (pullback.snd X.hom gk) f =
      pullback.fst (pullback.snd (pullback.snd X.hom k) g) f ≫
        (nestedPullbackIso g k gk hgk X).hom.left :=
    pullback.lift_fst _ _ _
  have h2 : (nestedPullbackIso f g fg hfg ((Over.pullback k).obj X)).hom.left ≫
      pullback.fst (pullback.snd X.hom k) fg =
      pullback.fst (pullback.snd (pullback.snd X.hom k) g) f ≫
        pullback.fst (pullback.snd X.hom k) g :=
    nestedPullbackIso_fst f g fg hfg ((Over.pullback k).obj X)
  apply overPullback_hom_ext_fst fgk
  have hL : ((Over.pullback f).map (nestedPullbackIso g k gk hgk X).hom ≫
        (nestedPullbackIso f gk fgk hfgk₂ X).hom).left ≫ pullback.fst X.hom fgk =
      pullback.fst (pullback.snd (pullback.snd X.hom k) g) f ≫
        pullback.fst (pullback.snd X.hom k) g ≫ pullback.fst X.hom k := by
    rw [Over.comp_left, Category.assoc, nestedPullbackIso_fst, ← Category.assoc, h1,
      Category.assoc, nestedPullbackIso_fst]
  have hR : ((nestedPullbackIso f g fg hfg ((Over.pullback k).obj X)).hom ≫
        (nestedPullbackIso fg k fgk hfgk₁ X).hom).left ≫ pullback.fst X.hom fgk =
      pullback.fst (pullback.snd (pullback.snd X.hom k) g) f ≫
        pullback.fst (pullback.snd X.hom k) g ≫ pullback.fst X.hom k := by
    rw [Over.comp_left, Category.assoc, nestedPullbackIso_fst, ← Category.assoc, h2,
      Category.assoc]
  exact hL.trans hR.symm

private lemma locallyOfFinitePresentation_of_comp
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  let P : MorphismProperty Scheme.{u} := @LocallyOfFinitePresentation
  have : P.ContainsIdentities := ⟨fun X => inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩
  have : P.IsMultiplicative := ⟨⟩
  have : P.HasOfPostcompProperty (@LocallyOfFiniteType) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ g hg => @AlgebraicGeometry.locallyOfFinitePresentation_diagonal _ _ g hg)
  exact MorphismProperty.of_postcomp P (W' := @LocallyOfFiniteType) f g
    (inferInstance : LocallyOfFiniteType g)
    (inferInstance : LocallyOfFinitePresentation (f ≫ g))

section Descent

universe vI wI

private lemma exists_isIso_baseChange_of_iso
    {I : Type vI} [Category.{wI} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : X ⟶ Y) [IsIso ((Over.pullback (c.π.app i)).map f)] :
    ∃ (j : I) (a : j ⟶ i), IsIso ((Over.pullback (D.map a)).map f) := by
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiCompact Y.hom := hY.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : QuasiSeparated Y.hom := hY.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : LocallyOfFinitePresentation Y.hom := hY.1
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by rw [f.w]; exact hX.1
  have : LocallyOfFinitePresentation f.left := locallyOfFinitePresentation_of_comp f.left Y.hom
  have : IsIso ((Over.forget _).map ((Over.pullback (c.π.app i)).map f)) := inferInstance
  change IsIso ((Over.pullback (c.π.app i)).map f).left at this
  obtain ⟨j, a, ha⟩ :=
    AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange D c hc i X Y f
  have : IsIso ((Over.forget _).map ((Over.pullback (D.map a)).map f)) := ha
  exact ⟨j, a, isIso_of_reflects_iso _ (Over.forget _)⟩

private lemma exists_eventually_isIso_model
    {I : Type vI} [Category.{wI} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (e : (Over.pullback (c.π.app i)).obj X ≅ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (a : j ⟶ i)
      (g : (Over.pullback (D.map a)).obj X ⟶ (Over.pullback (D.map a)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map a)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map a)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map a)).obj X).hom (c.π.app j) ≫
          pullback.fst X.hom (D.map a) ∧
      β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map a)).obj Y).hom (c.π.app j) ≫
          pullback.fst Y.hom (D.map a) ∧
      α.hom ≫ e.hom = (Over.pullback (c.π.app j)).map g ≫ β.hom ∧
      ∃ (k : I) (b : k ⟶ j), IsIso ((Over.pullback (D.map b)).map g) := by
  obtain ⟨j, a, g, α, β, hα, hβ, he⟩ :=
    AlgebraicGeometry.exists_morphism_after_baseChange D c hc i X Y hX hY e.hom
  refine ⟨j, a, g, α, β, hα, hβ, he, ?_⟩
  have hg : (Over.pullback (c.π.app j)).map g = α.hom ≫ e.hom ≫ β.inv := by
    rw [← Category.assoc, he, Category.assoc, β.hom_inv_id, Category.comp_id]
  have : IsIso ((Over.pullback (c.π.app j)).map g) := by
    rw [hg]
    infer_instance
  exact exists_isIso_baseChange_of_iso D c hc j
    ((Over.pullback (D.map a)).obj X) ((Over.pullback (D.map a)).obj Y)
    (finitePresentation_pullback _ X hX) (finitePresentation_pullback _ Y hY) g

/-- The isomorphism descended to a stage of the diagram can be chosen so that its own base
change to the limit is the given isomorphism, modulo the canonical comparisons. -/
private lemma exists_compatible_iso_of_iso_limit
    {I : Type vI} [Category.{wI} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (e : (Over.pullback (c.π.app i)).obj X ≅ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (a : j ⟶ i)
      (ε : (Over.pullback (D.map a)).obj X ≅ (Over.pullback (D.map a)).obj Y),
      (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) X).inv ≫
          (Over.pullback (c.π.app j)).map ε.hom ≫
          (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) Y).hom = e.hom := by
  obtain ⟨j, a, g, α, β, hα, hβ, he, k, b, hg⟩ :=
    exists_eventually_isIso_model D c hc i X Y hX hY e
  have hαI : α = nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) X := by
    refine Iso.ext (overPullback_hom_ext_fst (c.π.app i) ?_)
    rw [hα]
    exact (nestedPullbackIso_fst (c.π.app j) (D.map a) (c.π.app i) (c.w a) X).symm
  have hβI : β = nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) Y := by
    refine Iso.ext (overPullback_hom_ext_fst (c.π.app i) ?_)
    rw [hβ]
    exact (nestedPullbackIso_fst (c.π.app j) (D.map a) (c.π.app i) (c.w a) Y).symm
  rw [hαI, hβI] at he
  have hba : D.map b ≫ D.map a = D.map (b ≫ a) := (D.map_comp b a).symm
  have hgiso : IsIso ((Over.pullback (D.map b)).map g) := hg
  refine ⟨k, b ≫ a,
    (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba X).symm ≪≫
      asIso ((Over.pullback (D.map b)).map g) ≪≫
      nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba Y, ?_⟩
  have hC₁ : (Over.pullback (c.π.app k)).map
        (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba X).hom ≫
      (nestedPullbackIso (c.π.app k) (D.map (b ≫ a)) (c.π.app i) (c.w (b ≫ a)) X).hom =
      (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
          ((Over.pullback (D.map a)).obj X)).hom ≫
        (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) X).hom :=
    nestedPullbackIso_assoc (c.π.app k) (D.map b) (D.map a) (c.π.app j) (D.map (b ≫ a))
      (c.π.app i) (c.w b) hba (c.w a) (c.w (b ≫ a)) X
  have hC : (Over.pullback (c.π.app k)).map
        (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba Y).hom ≫
      (nestedPullbackIso (c.π.app k) (D.map (b ≫ a)) (c.π.app i) (c.w (b ≫ a)) Y).hom =
      (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
          ((Over.pullback (D.map a)).obj Y)).hom ≫
        (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) Y).hom :=
    nestedPullbackIso_assoc (c.π.app k) (D.map b) (D.map a) (c.π.app j) (D.map (b ≫ a))
      (c.π.app i) (c.w b) hba (c.w a) (c.w (b ≫ a)) Y
  have hB : (Over.pullback (c.π.app k)).map ((Over.pullback (D.map b)).map g) ≫
      (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
        ((Over.pullback (D.map a)).obj Y)).hom =
      (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
        ((Over.pullback (D.map a)).obj X)).hom ≫ (Over.pullback (c.π.app j)).map g :=
    nestedPullbackIso_naturality (c.π.app k) (D.map b) (c.π.app j) (c.w b) g
  have hA : (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) X).hom ≫
      (nestedPullbackIso (c.π.app k) (D.map (b ≫ a)) (c.π.app i) (c.w (b ≫ a)) X).inv ≫
      (Over.pullback (c.π.app k)).map
        (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba X).inv =
      (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
        ((Over.pullback (D.map a)).obj X)).inv := by
    rw [← cancel_epi (nestedPullbackIso (c.π.app k) (D.map b) (c.π.app j) (c.w b)
      ((Over.pullback (D.map a)).obj X)).hom, ← Category.assoc, ← hC₁]
    simp
  rw [← cancel_epi (nestedPullbackIso (c.π.app j) (D.map a) (c.π.app i) (c.w a) X).hom, he]
  have hε : ((nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba X).symm ≪≫
      asIso ((Over.pullback (D.map b)).map g) ≪≫
      nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba Y).hom =
      (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba X).inv ≫
        (Over.pullback (D.map b)).map g ≫
        (nestedPullbackIso (D.map b) (D.map a) (D.map (b ≫ a)) hba Y).hom := rfl
  rw [hε, Functor.map_comp (Over.pullback (c.π.app k)),
    Functor.map_comp (Over.pullback (c.π.app k))]
  simp only [Category.assoc]
  rw [hC, reassoc_of% hB, reassoc_of% hA, Iso.inv_hom_id_assoc]

end Descent

private lemma morphismRestrict_opens_apply {S : Scheme.{u}} (U W : S.Opens)
    (y : (W.ι ⁻¹ᵁ U).toScheme) : U.ι ((W.ι ∣_ U) y) = W.ι ((W.ι ⁻¹ᵁ U).ι y) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

private lemma range_morphismRestrict_opens {S : Scheme.{u}} (U W : S.Opens) :
    (W.ι ∣_ U).opensRange = U.ι ⁻¹ᵁ W := by
  have hinj : Function.Injective U.ι := fun _ _ h => Subtype.ext h
  apply TopologicalSpace.Opens.ext
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨y, rfl⟩
    show U.ι ((W.ι ∣_ U) y) ∈ W
    rw [morphismRestrict_opens_apply U W y]
    exact ((W.ι ⁻¹ᵁ U).ι y).2
  · intro x hx
    change U.ι x ∈ W at hx
    let t : (W.ι ⁻¹ᵁ U).toScheme :=
      ⟨⟨x.1, hx⟩, (x.2 : W.ι (⟨x.1, hx⟩ : W.toScheme) ∈ U)⟩
    exact ⟨t, hinj ((morphismRestrict_opens_apply U W t).trans rfl)⟩

/-- Two finite-presentation schemes over two opens, identified over the intersection, glue to a
scheme over the union whose restrictions to the two opens are cartesian. -/
private lemma exists_gluing_of_overlap_iso_on_sup
    {S : Scheme.{u}} (U W : S.Opens)
    (X : Over U.toScheme) (Y : Over W.toScheme)
    (e : (Over.pullback (W.ι ∣_ U)).obj X ≅ (Over.pullback (W.ι ⁻¹ᵁ U).ι).obj Y) :
    ∃ (H : Over (U ⊔ W : S.Opens).toScheme) (jX : X.left ⟶ H.left) (jY : Y.left ⟶ H.left),
      IsPullback jX X.hom H.hom (S.homOfLE (le_sup_left : U ≤ U ⊔ W)) ∧
      IsPullback jY Y.hom H.hom (S.homOfLE (le_sup_right : W ≤ U ⊔ W)) ∧
      e.hom.left ≫ pullback.fst Y.hom (W.ι ⁻¹ᵁ U).ι ≫ jY =
        pullback.fst X.hom (W.ι ∣_ U) ≫ jX := by
  let Ω : S.Opens := U ⊔ W
  let a : U.toScheme ⟶ Ω.toScheme := S.homOfLE (le_sup_left : U ≤ Ω)
  let b : W.toScheme ⟶ Ω.toScheme := S.homOfLE (le_sup_right : W ≤ Ω)
  let i : (W.ι ⁻¹ᵁ U).toScheme ⟶ U.toScheme := W.ι ∣_ U
  let j : (W.ι ⁻¹ᵁ U).toScheme ⟶ W.toScheme := (W.ι ⁻¹ᵁ U).ι
  have hbase : i ≫ a = j ≫ b := by
    apply (cancel_mono Ω.ι).1
    simp only [a, b, Category.assoc, Scheme.homOfLE_ι]
    exact morphismRestrict_ι W.ι U
  obtain ⟨Z, k₁, k₂, hk₁, hk₂, hk, hf₁, hf₂, hcover⟩ :=
    exists_gluedOver_of_openOverlap a b i j hbase X Y e
  have _ := hk₁
  have _ := hk₂
  have hei : IsIso e.hom.left := (Over.forget (W.ι ⁻¹ᵁ U).toScheme).map_isIso e.hom
  have hesurj : Function.Surjective e.hom.left :=
    (surjective_iff _).mp (inferInstanceAs (Surjective e.hom.left))
  have hk' : pullback.fst X.hom i ≫ k₁ =
      e.hom.left ≫ pullback.fst Y.hom j ≫ k₂ := by rw [hk, Category.assoc]
  have hkpt : ∀ x, k₁ ((pullback.fst X.hom i) x) =
      k₂ ((pullback.fst Y.hom j) (e.hom.left x)) := by
    intro x
    have h : (pullback.fst X.hom i ≫ k₁) x =
        (e.hom.left ≫ pullback.fst Y.hom j ≫ k₂) x := by rw [hk']
    simpa only [Scheme.Hom.comp_apply] using h
  have hrangeI : i.opensRange = U.ι ⁻¹ᵁ W := range_morphismRestrict_opens U W
  have haι : ∀ v, Ω.ι (a v) = U.ι v := fun v => by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have hbι : ∀ w, Ω.ι (b w) = W.ι w := fun w => by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have hz₁ : ∀ x, Z.hom (k₁ x) = a (X.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hf₁, Scheme.Hom.comp_apply]
  have hz₂ : ∀ y, Z.hom (k₂ y) = b (Y.hom y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hf₂, Scheme.Hom.comp_apply]
  have hpreU : ∀ z, (Z.hom z ∈ (Ω.ι ⁻¹ᵁ U : Ω.toScheme.Opens)) ↔ z ∈ Set.range k₁ := by
    intro z
    constructor
    · intro hz
      rcases hcover z with h | ⟨y, rfl⟩
      · exact h
      · have hyU : Y.hom y ∈ W.ι ⁻¹ᵁ U := by
          change Ω.ι (Z.hom (k₂ y)) ∈ U at hz
          rw [hz₂ y, hbι] at hz
          exact hz
        have hy : y ∈ Set.range (pullback.fst Y.hom j) := by
          rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
          exact hyU
        obtain ⟨w, rfl⟩ := hy
        obtain ⟨w', rfl⟩ := hesurj w
        exact ⟨pullback.fst X.hom i w', hkpt w'⟩
    · rintro ⟨x, rfl⟩
      show Ω.ι (Z.hom (k₁ x)) ∈ U
      rw [hz₁ x, haι]
      exact (X.hom x).2
  have hpreW : ∀ z, (Z.hom z ∈ (Ω.ι ⁻¹ᵁ W : Ω.toScheme.Opens)) ↔ z ∈ Set.range k₂ := by
    intro z
    constructor
    · intro hz
      rcases hcover z with ⟨x, rfl⟩ | h
      · have hxW : X.hom x ∈ U.ι ⁻¹ᵁ W := by
          change Ω.ι (Z.hom (k₁ x)) ∈ W at hz
          rw [hz₁ x, haι] at hz
          exact hz
        have hx : x ∈ Set.range (pullback.fst X.hom i) := by
          rw [IsOpenImmersion.range_pullbackFst, hrangeI]
          exact hxW
        obtain ⟨x', rfl⟩ := hx
        exact ⟨pullback.fst Y.hom j (e.hom.left x'), (hkpt x').symm⟩
      · exact h
    · rintro ⟨y, rfl⟩
      show Ω.ι (Z.hom (k₂ y)) ∈ W
      rw [hz₂ y, hbι]
      exact (Y.hom y).2
  refine ⟨Z, k₁, k₂, ?_, ?_, ?_⟩
  · apply (IsOpenImmersion.isPullback X.hom k₁ a Z.hom hf₁ ?_).flip
    apply TopologicalSpace.Opens.ext
    rw [show a.opensRange = Ω.ι ⁻¹ᵁ U from Scheme.opensRange_homOfLE _]
    exact Set.ext hpreU
  · apply (IsOpenImmersion.isPullback Y.hom k₂ b Z.hom hf₂ ?_).flip
    apply TopologicalSpace.Opens.ext
    rw [show b.opensRange = Ω.ι ⁻¹ᵁ W from Scheme.opensRange_homOfLE _]
    exact Set.ext hpreW
  · rw [← Category.assoc]
    exact hk.symm

/-- A comparison descended to a finite stage, once glued, still intertwines the limiting
comparison with the glued maps. -/
private lemma gluing_compatibility_of_descended_map
    {T Q R CU CL CW VV H : Scheme.{u}}
    (τ : T ⟶ Q) (v : Q ⟶ R) (t : T ⟶ R) (ht : τ ≫ v = t)
    (f : Q ⟶ CU) (k : T ⟶ CU) (hk : τ ≫ f = k) (p : T ⟶ CL) (g : Q ⟶ CW)
    (X : Over CU) (A B : Over R) (Zl : Over CL) (Yw : Over CW)
    (axx : A.left ⟶ X.left) (bz : B.left ⟶ VV) (yv : Yw.left ⟶ VV) [Mono yv]
    (z : Zl.left ⟶ Yw.left)
    (α : (Over.pullback t).obj A ≅ (Over.pullback k).obj X)
    (β : (Over.pullback p).obj Zl ≅ (Over.pullback t).obj B)
    (c : (Over.pullback k).obj X ⟶ (Over.pullback p).obj Zl)
    (a : (Over.pullback f).obj X ≅ (Over.pullback v).obj A)
    (b : (Over.pullback g).obj Yw ≅ (Over.pullback v).obj B)
    (ε : (Over.pullback v).obj A ⟶ (Over.pullback v).obj B)
    (hα : α.hom.left ≫ pullback.fst X.hom k = pullback.fst A.hom t ≫ axx)
    (hβ : β.hom.left ≫ pullback.fst B.hom t ≫ bz = pullback.fst Zl.hom p ≫ z ≫ yv)
    (ha : a.hom.left ≫ pullback.fst A.hom v ≫ axx = pullback.fst X.hom f)
    (hb : b.hom.left ≫ pullback.fst B.hom v ≫ bz = pullback.fst Yw.hom g ≫ yv)
    (hε : (nestedPullbackIso τ v t ht A).inv ≫ (Over.pullback τ).map ε ≫
      (nestedPullbackIso τ v t ht B).hom = α.hom ≫ c ≫ β.hom)
    (jX : X.left ⟶ H) (jY : Yw.left ⟶ H)
    (hj : (a.hom ≫ ε ≫ b.inv).left ≫ pullback.fst Yw.hom g ≫ jY =
      pullback.fst X.hom f ≫ jX) :
    c.left ≫ pullback.fst Zl.hom p ≫ z ≫ jY = pullback.fst X.hom k ≫ jX := by
  let δ := nestedPullbackIso τ f k hk X
  let N₁ := nestedPullbackIso τ v t ht A
  let N₂ := nestedPullbackIso τ v t ht B
  have hmapA : ((Over.pullback τ).map a.hom).left ≫
      pullback.fst (pullback.snd A.hom v) τ =
      pullback.fst (pullback.snd X.hom f) τ ≫ a.hom.left := pullback.lift_fst _ _ _
  have hmapE : ((Over.pullback τ).map ε).left ≫
      pullback.fst (pullback.snd B.hom v) τ =
      pullback.fst (pullback.snd A.hom v) τ ≫ ε.left := pullback.lift_fst _ _ _
  have hsource : (Over.pullback τ).map a.hom ≫ N₁.hom ≫ α.hom = δ.hom := by
    apply overPullback_hom_ext_fst k
    simp only [Over.comp_left, Category.assoc]
    rw [hα, reassoc_of% (nestedPullbackIso_fst τ v t ht A),
      reassoc_of% hmapA, ha]
    exact (nestedPullbackIso_fst τ f k hk X).symm
  have he : (Over.pullback τ).map ε ≫ N₂.hom = N₁.hom ≫ α.hom ≫ c ≫ β.hom := by
    rw [← hε]
    simp [N₁, N₂]
  have hmiddle : δ.hom.left ≫ c.left ≫ pullback.fst Zl.hom p ≫ z =
      pullback.fst (pullback.snd X.hom f) τ ≫
        (a.hom ≫ ε ≫ b.inv).left ≫ pullback.fst Yw.hom g := by
    apply (cancel_mono yv).mp
    simp only [Category.assoc]
    rw [← hβ]
    have hs := congrArg (fun m => m.left) hsource
    simp only [Over.comp_left] at hs
    rw [← hs]
    simp only [Category.assoc]
    have he' := congrArg (fun m => m.left) he
    simp only [Over.comp_left] at he'
    rw [← reassoc_of% he']
    rw [reassoc_of% (nestedPullbackIso_fst τ v t ht B),
      reassoc_of% hmapE,
      reassoc_of% hmapA]
    have hb' : b.inv.left ≫ pullback.fst Yw.hom g ≫ yv =
        pullback.fst B.hom v ≫ bz := by
      rw [← hb, ← Category.assoc, ← Over.comp_left, b.inv_hom_id]
      simp
    simp only [Over.comp_left, Category.assoc, hb']
  have : IsIso δ.hom.left := (Over.forget T).map_isIso δ.hom
  apply (cancel_epi δ.hom.left).mp
  rw [reassoc_of% hmiddle, hj, reassoc_of% (nestedPullbackIso_fst τ f k hk X)]

/-- A neighbourhood model whose restrictions to `U` and to the local scheme are cartesian over
the two components of a gluing datum, compatibly on the punctured local scheme, realizes that
gluing datum. -/
private lemma nonempty_iso_neighborhoodModel_of_pullbacks
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (Z : glueingDataNearPoint S U s) (M : FinitePresentationNeighborhoodModel S U s)
    (jU : Z.obj.left.obj.left ⟶ M.source) (jL : Z.obj.right.obj.left ⟶ M.source)
    (hcU : IsPullback jU Z.obj.left.obj.hom M.hom (S.homOfLE M.neighborhood.le_V))
    (hcL : IsPullback jL Z.obj.right.obj.hom M.hom M.localBase)
    (hc : Z.obj.hom.hom.left ≫
        pullback.fst Z.obj.right.obj.hom ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ jL =
      pullback.fst Z.obj.left.obj.hom ((S.fromSpecStalk s) ∣_ U) ≫ jU) :
    Nonempty ((neighborhoodModelToGlueingData S U s).obj M ≅ Z) := by
  have : Mono M.localBase := mono_of_mono_fac M.localBase_fac
  have : Mono jL := hcL.mono_fst_of_mono
  have : Mono (pullback.fst Z.obj.right.obj.hom ((S.fromSpecStalk s) ⁻¹ᵁ U).ι) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  let aa : (neighborhoodModelOpenRestrictionFunctor S U s).obj M ≅ Z.obj.left :=
    ObjectProperty.isoMk _ (Over.isoMk hcU.isoPullback.symm hcU.isoPullback_inv_snd)
  let bb : (neighborhoodModelLocalRestrictionFunctor S U s).obj M ≅ Z.obj.right :=
    ObjectProperty.isoMk _ (Over.isoMk hcL.isoPullback.symm hcL.isoPullback_inv_snd)
  refine ⟨ObjectProperty.isoMk _ (Comma.isoMk aa bb ?_)⟩
  have ha : aa.hom.hom.left ≫ jU =
      pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) := hcU.isoPullback_inv_fst
  have hb : bb.hom.hom.left ≫ jL = pullback.fst M.hom M.localBase :=
    hcL.isoPullback_inv_fst
  have hmA : ((restrictOpenToPuncturedLocal S U s).map aa.hom).hom.left ≫
      pullback.fst Z.obj.left.obj.hom ((S.fromSpecStalk s) ∣_ U) =
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        ((S.fromSpecStalk s) ∣_ U) ≫ aa.hom.hom.left := pullback.lift_fst _ _ _
  have hmB : ((restrictLocalToPuncturedLocal S U s).map bb.hom).hom.left ≫
      pullback.fst Z.obj.right.obj.hom (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) =
      pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
        bb.hom.hom.left := pullback.lift_fst _ _ _
  have stepL := (congrArg (fun k => k ≫ jU) hmA).trans
    ((Category.assoc
        (pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
          ((S.fromSpecStalk s) ∣_ U)) aa.hom.hom.left jU).trans
      (congrArg (fun k => pullback.fst (pullback.snd M.hom
        (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk s) ∣_ U) ≫ k) ha))
  have stepR := (congrArg (fun k => k ≫ jL) hmB).trans
    ((Category.assoc
        (pullback.fst (pullback.snd M.hom M.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) bb.hom.hom.left jL).trans
      (congrArg (fun k => pullback.fst (pullback.snd M.hom M.localBase)
        (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ k) hb))
  have stepL' := (Category.assoc
      ((restrictOpenToPuncturedLocal S U s).map aa.hom).hom.left
      (pullback.fst Z.obj.left.obj.hom ((S.fromSpecStalk s) ∣_ U)) jU).symm.trans stepL
  have stepR' := (Category.assoc
      ((restrictLocalToPuncturedLocal S U s).map bb.hom).hom.left
      (pullback.fst Z.obj.right.obj.hom (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) jL).symm.trans stepR
  have key := ((congrArg
      (fun k => ((restrictOpenToPuncturedLocal S U s).map aa.hom).hom.left ≫ k)
      hc).trans stepL').trans
    ((FinitePresentationNeighborhoodModel.overlapIso_hom_fst M).symm.trans
      (congrArg (fun k => M.overlapIso.hom.hom.left ≫ k) stepR').symm)
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (pullback.fst Z.obj.right.obj.hom
    ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ jL)).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  exact ((Category.assoc _ _ _).trans key).trans (Category.assoc _ _ _).symm

private lemma exists_affineNeighborhood_le (S : Scheme.{u}) (s : S) (V : S.Opens)
    (hs : s ∈ V) : ∃ W : AffineNeighborhood S s, W.1 ≤ V := by
  obtain ⟨T, hT, hsT, hle⟩ := exists_isAffineOpen_mem_and_subset hs
  exact ⟨⟨T, hT, hsT⟩, hle⟩

/-- The canonical morphism from the local scheme at `s` to an affine neighbourhood of `s`. -/
private noncomputable def stalkπ (S : Scheme.{u}) (s : S) (V : AffineNeighborhood S s) :
    Spec (S.presheaf.stalk s) ⟶ V.1.toScheme :=
  (affineNeighborhoodCone S s).π.app V

private lemma stalkπ_comp_ι (S : Scheme.{u}) (s : S) (V : AffineNeighborhood S s) :
    stalkπ S s V ≫ V.1.ι = S.fromSpecStalk s :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

private lemma stalkπ_comp_homOfLE (S : Scheme.{u}) (s : S) {V V' : AffineNeighborhood S s}
    (h : V'.1 ≤ V.1) : stalkπ S s V' ≫ S.homOfLE h = stalkπ S s V := by
  apply (cancel_mono V.1.ι).1
  rw [Category.assoc, Scheme.homOfLE_ι, stalkπ_comp_ι, stalkπ_comp_ι]

/-- A morphism to the intersection of `U` with an affine neighbourhood of `s` which is
compatible with the inclusions is the restriction of the canonical one. -/
private lemma comp_restrict_of_comp_ι_stalk (S : Scheme.{u}) (U : S.Opens) (s : S)
    (V : AffineNeighborhood S s)
    (τ : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V.1.ι ⁻¹ᵁ U).toScheme)
    (hτ : τ ≫ (V.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V) :
    τ ≫ (V.1.ι ∣_ U) = (S.fromSpecStalk s) ∣_ U := by
  apply (cancel_mono U.ι).1
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hτ, Category.assoc,
    stalkπ_comp_ι, morphismRestrict_ι]

private lemma comp_restrict_of_comp_ι_le (S : Scheme.{u}) (U : S.Opens) {V V' : S.Opens}
    (h : V' ≤ V) (v : (V'.ι ⁻¹ᵁ U).toScheme ⟶ (V.ι ⁻¹ᵁ U).toScheme)
    (hv : v ≫ (V.ι ⁻¹ᵁ U).ι = (V'.ι ⁻¹ᵁ U).ι ≫ S.homOfLE h) :
    v ≫ (V.ι ∣_ U) = V'.ι ∣_ U := by
  apply (cancel_mono U.ι).1
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hv, Category.assoc,
    Scheme.homOfLE_ι, morphismRestrict_ι]

private lemma localBase_eq_stalkπ_comp (S : Scheme.{u}) (U : S.Opens) (s : S)
    (M : FinitePresentationNeighborhoodModel S U s) (V : AffineNeighborhood S s)
    (hV : V.1 ≤ M.neighborhood.V) :
    stalkπ S s V ≫ S.homOfLE hV = M.localBase := by
  apply (cancel_mono M.neighborhood.V.ι).1
  rw [Category.assoc, Scheme.homOfLE_ι, stalkπ_comp_ι, M.localBase_fac]

private lemma exists_affineNeighborhood_model' (S : Scheme.{u}) (s : S)
    (X : Over (Spec (S.presheaf.stalk s))) (hX : FinitePresentation X.hom) :
    ∃ (V : AffineNeighborhood S s) (Y : Over V.1.toScheme),
      FinitePresentation Y.hom ∧
      Nonempty (X ≅ (Over.pullback (stalkπ S s V)).obj Y) :=
  exists_affineNeighborhood_model S s X hX

/-- An isomorphism between two finite-presentation schemes over the intersection of `U` with the
local scheme at `s`, pulled back from an affine neighbourhood, descends to a smaller affine
neighbourhood, compatibly with the canonical comparisons. -/
private lemma exists_overlap_descent
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (V : AffineNeighborhood S s) (A B : Over (V.1.ι ⁻¹ᵁ U).toScheme)
    (hA : FinitePresentation A.hom) (hB : FinitePresentation B.hom)
    (τ : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V.1.ι ⁻¹ᵁ U).toScheme)
    (hτ : τ ≫ (V.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V)
    (e : (Over.pullback τ).obj A ≅ (Over.pullback τ).obj B) :
    ∃ (V' : AffineNeighborhood S s) (h : V'.1 ≤ V.1)
      (τ' : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V'.1.ι ⁻¹ᵁ U).toScheme)
      (v : (V'.1.ι ⁻¹ᵁ U).toScheme ⟶ (V.1.ι ⁻¹ᵁ U).toScheme),
      τ' ≫ (V'.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V' ∧
      v ≫ (V.1.ι ⁻¹ᵁ U).ι = (V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE h ∧
      τ' ≫ v = τ ∧
      ∃ (ε : (Over.pullback v).obj A ≅ (Over.pullback v).obj B)
        (N₁ : (Over.pullback τ').obj ((Over.pullback v).obj A) ≅ (Over.pullback τ).obj A)
        (N₂ : (Over.pullback τ').obj ((Over.pullback v).obj B) ≅ (Over.pullback τ).obj B),
        N₁.hom.left ≫ pullback.fst A.hom τ =
          pullback.fst (pullback.snd A.hom v) τ' ≫ pullback.fst A.hom v ∧
        N₂.hom.left ≫ pullback.fst B.hom τ =
          pullback.fst (pullback.snd B.hom v) τ' ≫ pullback.fst B.hom v ∧
        N₁.inv ≫ (Over.pullback τ').map ε.hom ≫ N₂.hom = e.hom := by
  have hτeq : τ = (affineNeighborhoodOverlapCone S U s).π.app V := by
    apply (cancel_mono (V.1.ι ⁻¹ᵁ U).ι).1
    rw [hτ]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm
  subst hτeq
  let := affineNeighborhoodOverlap_compactSpace S U s hU
  let := affineNeighborhoodOverlap_quasiSeparatedSpace S U s
  obtain ⟨V', aa, ε, hε⟩ := exists_compatible_iso_of_iso_limit
    (affineNeighborhoodOverlapDiagram S U s) (affineNeighborhoodOverlapCone S U s)
    (affineNeighborhoodOverlapIsLimit S U s) V A B hA hB e
  exact ⟨V', leOfHom aa, (affineNeighborhoodOverlapCone S U s).π.app V',
    (affineNeighborhoodOverlapDiagram S U s).map aa,
    Scheme.Hom.resLE_comp_ι _ _, Scheme.Hom.resLE_comp_ι _ _,
    (affineNeighborhoodOverlapCone S U s).w aa, ε, _, _,
    nestedPullbackIso_fst _ _ _ _ _, nestedPullbackIso_fst _ _ _ _ _, hε⟩

/-- Every compatible pair of finite-presentation schemes on `U` and on the local scheme at `s`
comes from a finite-presentation scheme on an open neighbourhood of `U ∪ {s}`. -/
private lemma exists_neighborhoodModel_of_glueingData
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (XO : Over U.toScheme) (hXO : FinitePresentation XO.hom)
    (YO : Over (Spec (S.presheaf.stalk s))) (hYO : FinitePresentation YO.hom)
    (c : (Over.pullback ((S.fromSpecStalk s) ∣_ U)).obj XO ≅
      (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).obj YO) :
    ∃ (M : FinitePresentationNeighborhoodModel S U s)
      (jU : XO.left ⟶ M.source) (jL : YO.left ⟶ M.source),
      IsPullback jU XO.hom M.hom (S.homOfLE M.neighborhood.le_V) ∧
      IsPullback jL YO.hom M.hom M.localBase ∧
      c.hom.left ≫ pullback.fst YO.hom (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ jL =
        pullback.fst XO.hom ((S.fromSpecStalk s) ∣_ U) ≫ jU := by
  classical
  obtain ⟨V₀, Y₀, hY₀, ⟨eY⟩⟩ := exists_affineNeighborhood_model' S s YO hYO
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V₀.1.ι ⁻¹ᵁ U).toScheme,
      τ ≫ (V₀.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V₀ :=
    ⟨(affineNeighborhoodOverlapCone S U s).π.app V₀, Scheme.Hom.resLE_comp_ι _ _⟩
  have hτ₀q : τ₀ ≫ (V₀.1.ι ∣_ U) = (S.fromSpecStalk s) ∣_ U :=
    comp_restrict_of_comp_ι_stalk S U s V₀ τ₀ hτ₀
  let α : (Over.pullback τ₀).obj ((Over.pullback (V₀.1.ι ∣_ U)).obj XO) ≅
      (Over.pullback ((S.fromSpecStalk s) ∣_ U)).obj XO :=
    nestedPullbackIso τ₀ (V₀.1.ι ∣_ U) ((S.fromSpecStalk s) ∣_ U) hτ₀q XO
  let β : (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).obj YO ≅
      (Over.pullback τ₀).obj ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀) :=
    (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).mapIso eY ≪≫
      nestedPullbackIso (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) (stalkπ S s V₀)
        ((((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ stalkπ S s V₀) rfl Y₀ ≪≫
      (nestedPullbackIso τ₀ ((V₀.1.ι ⁻¹ᵁ U).ι)
        ((((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ stalkπ S s V₀) hτ₀ Y₀).symm
  obtain ⟨V₁, hWV₀, τ₁, v, hτ₁, hv, hτv, ε, N₁, N₂, hN₁, hN₂, hcomp⟩ :=
    exists_overlap_descent S U s hU V₀
      ((Over.pullback (V₀.1.ι ∣_ U)).obj XO) ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀)
      (finitePresentation_pullback _ XO hXO) (finitePresentation_pullback _ Y₀ hY₀)
      τ₀ hτ₀ (α ≪≫ c ≪≫ β)
  rw [nestedPullbackIso_eq_of_fst τ₁ v τ₀ hτv _ N₁ hN₁,
    nestedPullbackIso_eq_of_fst τ₁ v τ₀ hτv _ N₂ hN₂] at hcomp
  have hvq : v ≫ (V₀.1.ι ∣_ U) = V₁.1.ι ∣_ U := comp_restrict_of_comp_ι_le S U hWV₀ v hv
  have hτ₁q : τ₁ ≫ (V₁.1.ι ∣_ U) = (S.fromSpecStalk s) ∣_ U :=
    comp_restrict_of_comp_ι_stalk S U s V₁ τ₁ hτ₁
  let YW : Over V₁.1.toScheme := (Over.pullback (S.homOfLE hWV₀)).obj Y₀
  have hYW : FinitePresentation YW.hom := finitePresentation_pullback _ Y₀ hY₀
  let a' : (Over.pullback (V₁.1.ι ∣_ U)).obj XO ≅
      (Over.pullback v).obj ((Over.pullback (V₀.1.ι ∣_ U)).obj XO) :=
    (nestedPullbackIso v (V₀.1.ι ∣_ U) (V₁.1.ι ∣_ U) hvq XO).symm
  let b' : (Over.pullback (V₁.1.ι ⁻¹ᵁ U).ι).obj YW ≅
      (Over.pullback v).obj ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀) :=
    nestedPullbackIso ((V₁.1.ι ⁻¹ᵁ U).ι) (S.homOfLE hWV₀)
      (((V₁.1.ι ⁻¹ᵁ U).ι) ≫ S.homOfLE hWV₀) rfl Y₀ ≪≫
    (nestedPullbackIso v ((V₀.1.ι ⁻¹ᵁ U).ι) (((V₁.1.ι ⁻¹ᵁ U).ι) ≫ S.homOfLE hWV₀) hv Y₀).symm
  obtain ⟨H, jX, jY, hcartX, hcartY, hglue⟩ :=
    exists_gluing_of_overlap_iso_on_sup U V₁.1 XO YW (a' ≪≫ ε ≪≫ b'.symm)
  let O : (U ⊔ V₁.1 : S.Opens).toScheme.OpenCover.{u} :=
    { I₀ := ULift.{u} Bool
      X := fun b => match b with
        | ⟨true⟩ => U.toScheme
        | ⟨false⟩ => V₁.1.toScheme
      f := fun b => match b with
        | ⟨true⟩ => S.homOfLE (le_sup_left : U ≤ U ⊔ V₁.1)
        | ⟨false⟩ => S.homOfLE (le_sup_right : V₁.1 ≤ U ⊔ V₁.1)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        constructor
        · intro x
          rcases x.2 with hx | hx
          · exact ⟨⟨true⟩, ⟨x.1, hx⟩,
              Subtype.ext (Scheme.homOfLE_apply (le_sup_left : U ≤ U ⊔ V₁.1) _)⟩
          · exact ⟨⟨false⟩, ⟨x.1, hx⟩,
              Subtype.ext (Scheme.homOfLE_apply (le_sup_right : V₁.1 ≤ U ⊔ V₁.1) _)⟩
        · rintro ⟨b⟩
          cases b <;> exact inferInstance }
  have hfp : ∀ b : O.I₀, FinitePresentation (O.pullbackHom H.hom b) := by
    rintro ⟨b⟩
    cases b
    · show FinitePresentation (pullback.snd H.hom
        (S.homOfLE (le_sup_right : V₁.1 ≤ U ⊔ V₁.1)))
      rw [← hcartY.isoPullback_inv_snd]
      have : LocallyOfFinitePresentation YW.hom := hYW.1
      have : QuasiCompact YW.hom := hYW.2.1
      have : QuasiSeparated YW.hom := hYW.2.2
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    · show FinitePresentation (pullback.snd H.hom
        (S.homOfLE (le_sup_left : U ≤ U ⊔ V₁.1)))
      rw [← hcartX.isoPullback_inv_snd]
      have : LocallyOfFinitePresentation XO.hom := hXO.1
      have : QuasiCompact XO.hom := hXO.2.1
      have : QuasiSeparated XO.hom := hXO.2.2
      exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hFp : FinitePresentation H.hom :=
    finitePresentation_of_openCover H.hom O hfp
  let M : FinitePresentationNeighborhoodModel S U s :=
    { neighborhood := ⟨U ⊔ V₁.1, le_sup_left, Or.inr V₁.2.2⟩
      source := H.left
      hom := H.hom
      finitePresentation := hFp }
  let eYW : YO ≅ (Over.pullback (stalkπ S s V₁)).obj YW :=
    eY ≪≫ (nestedPullbackIso (stalkπ S s V₁) (S.homOfLE hWV₀) (stalkπ S s V₀)
      (stalkπ_comp_homOfLE S s hWV₀) Y₀).symm
  let zL : YO.left ⟶ YW.left := eYW.hom.left ≫ pullback.fst YW.hom (stalkπ S s V₁)
  have hw : eYW.hom.left ≫ pullback.snd YW.hom (stalkπ S s V₁) = YO.hom := eYW.hom.w
  have hcomm : zL ≫ YW.hom = YO.hom ≫ stalkπ S s V₁ := by
    dsimp only [zL]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hz : IsPullback zL YO.hom YW.hom (stalkπ S s V₁) :=
    IsPullback.of_iso_pullback ⟨hcomm⟩
      ((Over.forget (Spec (S.presheaf.stalk s))).mapIso eYW) rfl hw
  have hzL : zL ≫ pullback.fst Y₀.hom (S.homOfLE hWV₀) =
      eY.hom.left ≫ pullback.fst Y₀.hom (stalkπ S s V₀) := by
    have hn : (nestedPullbackIso (stalkπ S s V₁) (S.homOfLE hWV₀) (stalkπ S s V₀)
        (stalkπ_comp_homOfLE S s hWV₀) Y₀).inv.left ≫
        pullback.fst YW.hom (stalkπ S s V₁) ≫ pullback.fst Y₀.hom (S.homOfLE hWV₀) =
        pullback.fst Y₀.hom (stalkπ S s V₀) :=
      nestedPullbackIso_inv_fst _ _ _ _ _
    dsimp only [zL, eYW]
    simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc]
    rw [hn]
  have hcartL : IsPullback (zL ≫ jY) YO.hom M.hom M.localBase := by
    have h := hz.paste_horiz hcartY
    rwa [localBase_eq_stalkπ_comp S U s M V₁ le_sup_right] at h
  refine ⟨M, jX, zL ≫ jY, hcartX, hcartL, ?_⟩
  have : Mono (pullback.fst Y₀.hom (S.homOfLE hWV₀)) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hβ : β.hom.left ≫
      pullback.fst ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀).hom τ₀ ≫
        pullback.fst Y₀.hom ((V₀.1.ι ⁻¹ᵁ U).ι) =
      pullback.fst YO.hom (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ zL ≫
        pullback.fst Y₀.hom (S.homOfLE hWV₀) := by
    have hn : (nestedPullbackIso τ₀ ((V₀.1.ι ⁻¹ᵁ U).ι)
        ((((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ stalkπ S s V₀) hτ₀ Y₀).inv.left ≫
        pullback.fst ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀).hom τ₀ ≫
          pullback.fst Y₀.hom ((V₀.1.ι ⁻¹ᵁ U).ι) =
        pullback.fst Y₀.hom ((((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ stalkπ S s V₀) :=
      nestedPullbackIso_inv_fst _ _ _ _ _
    have hm : ((Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)).map eY.hom).left ≫
        pullback.fst (pullback.snd Y₀.hom (stalkπ S s V₀))
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) =
        pullback.fst YO.hom (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ eY.hom.left :=
      pullback.lift_fst _ _ _
    dsimp only [β]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.comp_left,
      Category.assoc]
    rw [hn, nestedPullbackIso_fst (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) (stalkπ S s V₀)
      ((((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ stalkπ S s V₀) rfl Y₀, reassoc_of% hm, hzL]
  have hb : b'.hom.left ≫
      pullback.fst ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀).hom v ≫
        pullback.fst Y₀.hom ((V₀.1.ι ⁻¹ᵁ U).ι) =
      pullback.fst YW.hom ((V₁.1.ι ⁻¹ᵁ U).ι) ≫ pullback.fst Y₀.hom (S.homOfLE hWV₀) := by
    have hn : (nestedPullbackIso v ((V₀.1.ι ⁻¹ᵁ U).ι)
        (((V₁.1.ι ⁻¹ᵁ U).ι) ≫ S.homOfLE hWV₀) hv Y₀).inv.left ≫
        pullback.fst ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀).hom v ≫
          pullback.fst Y₀.hom ((V₀.1.ι ⁻¹ᵁ U).ι) =
        pullback.fst Y₀.hom (((V₁.1.ι ⁻¹ᵁ U).ι) ≫ S.homOfLE hWV₀) :=
      nestedPullbackIso_inv_fst _ _ _ _ _
    dsimp only [b']
    simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc]
    rw [hn, nestedPullbackIso_fst ((V₁.1.ι ⁻¹ᵁ U).ι) (S.homOfLE hWV₀)
      (((V₁.1.ι ⁻¹ᵁ U).ι) ≫ S.homOfLE hWV₀) rfl Y₀]
    rfl
  exact gluing_compatibility_of_descended_map
    τ₁ v τ₀ hτv
    (V₁.1.ι ∣_ U) ((S.fromSpecStalk s) ∣_ U) hτ₁q
    (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ((V₁.1.ι ⁻¹ᵁ U).ι)
    XO ((Over.pullback (V₀.1.ι ∣_ U)).obj XO)
    ((Over.pullback (V₀.1.ι ⁻¹ᵁ U).ι).obj Y₀) YO YW
    (pullback.fst XO.hom (V₀.1.ι ∣_ U))
    (pullback.fst Y₀.hom ((V₀.1.ι ⁻¹ᵁ U).ι))
    (pullback.fst Y₀.hom (S.homOfLE hWV₀)) zL
    α β c.hom a' b' ε.hom
    (nestedPullbackIso_fst _ _ _ _ _) hβ
    (nestedPullbackIso_inv_fst _ _ _ _ _) hb hcomp jX jY hglue

/-- Maps out of `X` which agree on the restriction along `m` agree on the iterated restriction
along `j` and then `l`, when `l ≫ j = m`. -/
private lemma restrict_comp_eq_of {X Y Z T W : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) (a b : X ⟶ W)
    (h : pullback.fst f m ≫ a = pullback.fst f m ≫ b) :
    pullback.fst (pullback.snd f j) l ≫ pullback.fst f j ≫ a =
      pullback.fst (pullback.snd f j) l ≫ pullback.fst f j ≫ b := by
  subst hm
  simp only [← Category.assoc, ← pullbackLeftPullbackSndIso_hom_fst f j l]
  simp only [Category.assoc, h]

private lemma exists_eventually_eq_restriction
    (S : Scheme.{u}) (s : S) (V : AffineNeighborhood S s)
    (X Y : Over V.1.toScheme) (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) (f g : X ⟶ Y)
    (hfg : (Over.pullback (stalkπ S s V)).map f = (Over.pullback (stalkπ S s V)).map g) :
    ∃ (V' : AffineNeighborhood S s) (h : V'.1 ≤ V.1),
      (Over.pullback (S.homOfLE h)).map f = (Over.pullback (S.homOfLE h)).map g := by
  obtain ⟨V', e, he⟩ := eventually_eq_affineNeighborhood_morphism S s V X Y hX hY f g hfg
  exact ⟨V', leOfHom e, he⟩

/-- Two morphisms of neighbourhood models with the same image in the gluing-data category agree
after restricting the source to a smaller neighbourhood. -/
private lemma exists_restriction_eq_of_map_eq
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (M N : FinitePresentationNeighborhoodModel S U s) (g g' : M ⟶ N)
    (hg : (neighborhoodModelToGlueingData S U s).map g =
      (neighborhoodModelToGlueingData S U s).map g') :
    ∃ (P : FinitePresentationNeighborhoodModel S U s) (t : P ⟶ M),
      FinitePresentationNeighborhoodModel.restrictionMorphisms t ∧ t ≫ g = t ≫ g' := by
  have h1 : (neighborhoodModelOpenRestrictionFunctor S U s).map g =
      (neighborhoodModelOpenRestrictionFunctor S U s).map g' :=
    congrArg (fun m => m.hom.left) hg
  have h2 : (neighborhoodModelLocalRestrictionFunctor S U s).map g =
      (neighborhoodModelLocalRestrictionFunctor S U s).map g' :=
    congrArg (fun m => m.hom.right) hg
  have hi : pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) ≫ g.left =
      pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) ≫ g'.left := by
    have e1 : ((neighborhoodModelOpenRestrictionFunctor S U s).map g).hom.left ≫
        pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) =
        pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) ≫ g.left :=
      pullback.lift_fst _ _ _
    have e2 : ((neighborhoodModelOpenRestrictionFunctor S U s).map g').hom.left ≫
        pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) =
        pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) ≫ g'.left :=
      pullback.lift_fst _ _ _
    exact e1.symm.trans ((congrArg (fun m =>
      m.hom.left ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V)) h1).trans e2)
  have hii : pullback.fst M.hom M.localBase ≫ g.left =
      pullback.fst M.hom M.localBase ≫ g'.left := by
    have e1 : ((neighborhoodModelLocalRestrictionFunctor S U s).map g).hom.left ≫
        pullback.fst N.hom N.localBase =
        pullback.fst M.hom M.localBase ≫ g.left := pullback.lift_fst _ _ _
    have e2 : ((neighborhoodModelLocalRestrictionFunctor S U s).map g').hom.left ≫
        pullback.fst N.hom N.localBase =
        pullback.fst M.hom M.localBase ≫ g'.left := pullback.lift_fst _ _ _
    exact e1.symm.trans ((congrArg (fun m =>
      m.hom.left ≫ pullback.fst N.hom N.localBase) h2).trans e2)
  obtain ⟨V, hVMN⟩ := exists_affineNeighborhood_le S s
    (M.neighborhood.V ⊓ N.neighborhood.V) ⟨M.neighborhood.mem_V, N.neighborhood.mem_V⟩
  have hVM : V.1 ≤ M.neighborhood.V := hVMN.trans inf_le_left
  have hVN : V.1 ≤ N.neighborhood.V := hVMN.trans inf_le_right
  have hbase : S.homOfLE hVM ≫ S.homOfLE g.base_le = S.homOfLE hVN :=
    S.homOfLE_homOfLE _ _
  have hbase' : S.homOfLE hVM ≫ S.homOfLE g'.base_le = S.homOfLE hVN :=
    S.homOfLE_homOfLE _ _
  let gV := FinitePresentationNeighborhoodModel.restrictMap g
    (S.homOfLE hVM) (S.homOfLE hVN) hbase
  let g'V := FinitePresentationNeighborhoodModel.restrictMap g'
    (S.homOfLE hVM) (S.homOfLE hVN) hbase'
  have hgVfst : gV.left ≫ pullback.fst N.hom (S.homOfLE hVN) =
      pullback.fst M.hom (S.homOfLE hVM) ≫ g.left := pullback.lift_fst _ _ _
  have hg'Vfst : g'V.left ≫ pullback.fst N.hom (S.homOfLE hVN) =
      pullback.fst M.hom (S.homOfLE hVM) ≫ g'.left := pullback.lift_fst _ _ _
  have hgVsnd : gV.left ≫ pullback.snd N.hom (S.homOfLE hVN) =
      pullback.snd M.hom (S.homOfLE hVM) := pullback.lift_snd _ _ _
  have hg'Vsnd : g'V.left ≫ pullback.snd N.hom (S.homOfLE hVN) =
      pullback.snd M.hom (S.homOfLE hVM) := pullback.lift_snd _ _ _
  have hstar : pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        pullback.fst M.hom (S.homOfLE hVM) ≫ g.left =
      pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        pullback.fst M.hom (S.homOfLE hVM) ≫ g'.left :=
    restrict_comp_eq_of M.hom (S.homOfLE hVM) (stalkπ S s V) M.localBase
      (localBase_eq_stalkπ_comp S U s M V hVM) g.left g'.left hii
  have hmid0 : (pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        gV.left) ≫ pullback.fst N.hom (S.homOfLE hVN) =
      (pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        g'V.left) ≫ pullback.fst N.hom (S.homOfLE hVN) := by
    rw [Category.assoc, Category.assoc, hgVfst, hg'Vfst]
    exact hstar
  have hmid1 : (pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        gV.left) ≫ pullback.snd N.hom (S.homOfLE hVN) =
      (pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
        g'V.left) ≫ pullback.snd N.hom (S.homOfLE hVN) := by
    rw [Category.assoc, Category.assoc, hgVsnd, hg'Vsnd]
  have hmid := pullback.hom_ext (f := N.hom) (g := S.homOfLE hVN) hmid0 hmid1
  have hbc : (Over.pullback (stalkπ S s V)).map gV =
      (Over.pullback (stalkπ S s V)).map g'V := by
    refine overPullback_hom_ext_fst (stalkπ S s V) ?_
    have e1 : ((Over.pullback (stalkπ S s V)).map gV).left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (stalkπ S s V) =
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫ gV.left :=
      pullback.lift_fst _ _ _
    have e2 : ((Over.pullback (stalkπ S s V)).map g'V).left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (stalkπ S s V) =
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫ g'V.left :=
      pullback.lift_fst _ _ _
    exact e1.trans (hmid.trans e2.symm)
  obtain ⟨V', hV'V, hres⟩ := exists_eventually_eq_restriction S s V
    ((Over.pullback (S.homOfLE hVM)).obj (Over.mk M.hom))
    ((Over.pullback (S.homOfLE hVN)).obj (Over.mk N.hom))
    (finitePresentation_pullback _ _ M.finitePresentation)
    (finitePresentation_pullback _ _ N.finitePresentation) gV g'V hbc
  have hV'M : V'.1 ≤ M.neighborhood.V := hV'V.trans hVM
  have hV' : pullback.fst M.hom (S.homOfLE hV'V ≫ S.homOfLE hVM) ≫ g.left =
      pullback.fst M.hom (S.homOfLE hV'V ≫ S.homOfLE hVM) ≫ g'.left := by
    have e1 : ((Over.pullback (S.homOfLE hV'V)).map gV).left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE hV'V) =
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE hV'V) ≫ gV.left :=
      pullback.lift_fst _ _ _
    have e2 : ((Over.pullback (S.homOfLE hV'V)).map g'V).left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE hV'V) =
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE hV'V) ≫ g'V.left :=
      pullback.lift_fst _ _ _
    have key : pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE hV'V) ≫
        gV.left =
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE hV'V) ≫ g'V.left :=
      e1.symm.trans ((congrArg (fun m => m.left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE hV'V)) hres).trans e2)
    have key2 := congrArg (fun k => k ≫ pullback.fst N.hom (S.homOfLE hVN)) key
    simp only [Category.assoc, hgVfst, hg'Vfst] at key2
    simp only [← Category.assoc,
      ← pullbackLeftPullbackSndIso_hom_fst M.hom (S.homOfLE hVM) (S.homOfLE hV'V)] at key2
    simp only [Category.assoc] at key2
    exact (cancel_epi (pullbackLeftPullbackSndIso M.hom (S.homOfLE hVM)
      (S.homOfLE hV'V)).hom).1 key2
  have hmem : s ∈ U ⊔ V'.1 := Or.inr V'.2.2
  have hV''M : U ⊔ V'.1 ≤ M.neighborhood.V := sup_le M.neighborhood.le_V hV'M
  refine ⟨M.restrictNeighborhood ⟨U ⊔ V'.1, le_sup_left, hmem⟩ hV''M,
    M.restrictNeighborhoodHom _ hV''M, M.restrictNeighborhoodHom_mem _ hV''M, ?_⟩
  apply FinitePresentationNeighborhoodModel.Hom.ext
  show pullback.fst M.hom (S.homOfLE hV''M) ≫ g.left =
    pullback.fst M.hom (S.homOfLE hV''M) ≫ g'.left
  refine hom_ext_of_range_union
    (pullback.fst (pullback.snd M.hom (S.homOfLE hV''M))
      (S.homOfLE (le_sup_left : U ≤ U ⊔ V'.1)))
    (pullback.fst (pullback.snd M.hom (S.homOfLE hV''M))
      (S.homOfLE (le_sup_right : V'.1 ≤ U ⊔ V'.1))) ?_ ?_ ?_
  · rw [IsOpenImmersion.range_pullbackFst, IsOpenImmersion.range_pullbackFst,
      Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
    apply Set.eq_univ_of_forall
    intro x
    rcases (pullback.snd M.hom (S.homOfLE hV''M) x).2 with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  · exact restrict_comp_eq_of M.hom (S.homOfLE hV''M)
      (S.homOfLE (le_sup_left : U ≤ U ⊔ V'.1)) (S.homOfLE M.neighborhood.le_V)
      (S.homOfLE_homOfLE _ _) g.left g'.left hi
  · exact restrict_comp_eq_of M.hom (S.homOfLE hV''M)
      (S.homOfLE (le_sup_right : V'.1 ≤ U ⊔ V'.1)) (S.homOfLE hV'V ≫ S.homOfLE hVM)
      ((S.homOfLE_homOfLE _ _).trans (S.homOfLE_homOfLE _ _).symm) g.left g'.left hV'

/-- The canonical comparison from the restriction of `f` along `m` to its restriction along
`j`, when `m` factors as `l ≫ j`. -/
private noncomputable def restrictLift {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) : pullback f m ⟶ pullback f j :=
  pullback.lift (pullback.fst f m) (pullback.snd f m ≫ l) (by
    rw [Category.assoc, hm]
    exact pullback.condition)

private lemma restrictLift_fst {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) :
    restrictLift f j l m hm ≫ pullback.fst f j = pullback.fst f m :=
  pullback.lift_fst _ _ _

/-- The canonical comparison from an iterated restriction to a single one. -/
private noncomputable def doubleRestrictLift {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) :
    pullback (pullback.snd f j) l ⟶ pullback f m :=
  pullback.lift (pullback.fst (pullback.snd f j) l ≫ pullback.fst f j)
    (pullback.snd (pullback.snd f j) l) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hm])

private lemma doubleRestrictLift_fst {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) :
    doubleRestrictLift f j l m hm ≫ pullback.fst f m =
      pullback.fst (pullback.snd f j) l ≫ pullback.fst f j :=
  pullback.lift_fst _ _ _

private lemma exists_eventually_eq_overlap_restriction
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (V : AffineNeighborhood S s) (X Y : Over (V.1.ι ⁻¹ᵁ U).toScheme)
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) (m₁ m₂ : X ⟶ Y)
    (τ : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V.1.ι ⁻¹ᵁ U).toScheme)
    (hτ : τ ≫ (V.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V)
    (hm : (Over.pullback τ).map m₁ = (Over.pullback τ).map m₂) :
    ∃ (V' : AffineNeighborhood S s) (h : V'.1 ≤ V.1)
      (v : (V'.1.ι ⁻¹ᵁ U).toScheme ⟶ (V.1.ι ⁻¹ᵁ U).toScheme),
      v ≫ (V.1.ι ⁻¹ᵁ U).ι = (V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE h ∧
      (Over.pullback v).map m₁ = (Over.pullback v).map m₂ := by
  have hτeq : τ = (affineNeighborhoodOverlapCone S U s).π.app V := by
    apply (cancel_mono (V.1.ι ⁻¹ᵁ U).ι).1
    rw [hτ]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm
  subst hτeq
  obtain ⟨V', e, he⟩ := eventually_eq_affineNeighborhood_overlapMorphism S U s hU V X Y
    hX hY m₁ m₂ hm
  exact ⟨V', leOfHom e, (affineNeighborhoodOverlapDiagram S U s).map e,
    Scheme.Hom.resLE_comp_ι _ _, he⟩

/-- For two open immersions into `X`, the gluing condition for a pair of maps follows from their
agreement on any scheme whose image is the intersection. -/
private lemma glue_cond_of_range_inter {X Y A B T : Scheme.{u}} (p : A ⟶ X) (q : B ⟶ X)
    [IsOpenImmersion p] [IsOpenImmersion q] (w : T ⟶ X) [IsOpenImmersion w]
    (u : T ⟶ A) (v : T ⟶ B) (hu : u ≫ p = w) (hv : v ≫ q = w)
    (hr : Set.range w = Set.range p ∩ Set.range q)
    (fA : A ⟶ Y) (fB : B ⟶ Y) (h : u ≫ fA = v ≫ fB) :
    pullback.fst p q ≫ fA = pullback.snd p q ≫ fB := by
  have : IsOpenImmersion (pullback.fst p q ≫ p) := inferInstance
  have hr2 : Set.range (pullback.fst p q ≫ p) = Set.range p ∩ Set.range q := by
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨z, rfl⟩
      refine ⟨⟨pullback.fst p q z, (Scheme.Hom.comp_apply _ _ z).symm⟩,
        ⟨pullback.snd p q z, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
    · rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback a b hb.symm
      refine ⟨z, ?_⟩
      rw [Scheme.Hom.comp_apply, hz1]
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst p q ≫ p) w (hr2.trans hr.symm)
  have he : e.hom ≫ w = pullback.fst p q ≫ p :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hfst : pullback.fst p q = e.hom ≫ u := by
    apply (cancel_mono p).1
    rw [Category.assoc, hu]
    exact he.symm
  have hsnd : pullback.snd p q = e.hom ≫ v := by
    apply (cancel_mono q).1
    rw [Category.assoc, hv, ← pullback.condition, hfst, Category.assoc, hu]
  rw [hfst, hsnd, Category.assoc, Category.assoc, h]

private lemma exists_morphism_after_restriction
    (S : Scheme.{u}) (s : S) (V : AffineNeighborhood S s)
    (X Y : Over V.1.toScheme) (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (m : (Over.pullback (stalkπ S s V)).obj X ⟶ (Over.pullback (stalkπ S s V)).obj Y) :
    ∃ (V' : AffineNeighborhood S s) (h : V'.1 ≤ V.1)
      (g : (Over.pullback (S.homOfLE h)).obj X ⟶ (Over.pullback (S.homOfLE h)).obj Y)
      (α : (Over.pullback (stalkπ S s V')).obj ((Over.pullback (S.homOfLE h)).obj X) ≅
        (Over.pullback (stalkπ S s V)).obj X)
      (β : (Over.pullback (stalkπ S s V')).obj ((Over.pullback (S.homOfLE h)).obj Y) ≅
        (Over.pullback (stalkπ S s V)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (stalkπ S s V) =
        pullback.fst ((Over.pullback (S.homOfLE h)).obj X).hom (stalkπ S s V') ≫
          pullback.fst X.hom (S.homOfLE h) ∧
      β.hom.left ≫ pullback.fst Y.hom (stalkπ S s V) =
        pullback.fst ((Over.pullback (S.homOfLE h)).obj Y).hom (stalkπ S s V') ≫
          pullback.fst Y.hom (S.homOfLE h) ∧
      α.hom ≫ m = (Over.pullback (stalkπ S s V')).map g ≫ β.hom := by
  obtain ⟨V', e, g, α, β, hα, hβ, hg⟩ := AlgebraicGeometry.exists_morphism_after_baseChange
    (affineNeighborhoodDiagram S s) (affineNeighborhoodCone S s)
    (affineNeighborhoodIsLimit S s) V X Y hX hY m
  exact ⟨V', leOfHom e, g, α, β, hα, hβ, hg⟩

/-- A restriction morphism into `M` can be pulled back along any smaller neighbourhood of the
source. -/
private lemma exists_restrict_rightFraction
    {S : Scheme.{u}} {U : S.Opens} {s : S}
    {M X' : FinitePresentationNeighborhoodModel S U s} (σ : X' ⟶ M)
    (hσ : FinitePresentationNeighborhoodModel.restrictionMorphisms σ)
    (Nb : OpenNeighborhood S U s) (hNb : Nb.V ≤ X'.neighborhood.V)
    (h₁ : Nb.V ≤ M.neighborhood.V) :
    ∃ r : M.restrictNeighborhood Nb h₁ ⟶ X',
      r ≫ σ = M.restrictNeighborhoodHom Nb h₁ := by
  have hp : IsPullback σ.left X'.hom M.hom (S.homOfLE σ.base_le) := hσ
  have hcomp : S.homOfLE hNb ≫ S.homOfLE σ.base_le = S.homOfLE h₁ :=
    S.homOfLE_homOfLE _ _
  have hw : (M.restrictNeighborhoodHom Nb h₁).left ≫ M.hom =
      ((M.restrictNeighborhood Nb h₁).hom ≫ S.homOfLE hNb) ≫ S.homOfLE σ.base_le :=
    pullback.condition.trans
      ((congrArg (fun k => (M.restrictNeighborhood Nb h₁).hom ≫ k) hcomp).symm.trans
        (Category.assoc _ _ _).symm)
  refine ⟨⟨hNb, hp.lift (M.restrictNeighborhoodHom Nb h₁).left
    ((M.restrictNeighborhood Nb h₁).hom ≫ S.homOfLE hNb) hw, hp.lift_snd _ _ hw⟩, ?_⟩
  apply FinitePresentationNeighborhoodModel.Hom.ext
  exact hp.lift_fst _ _ hw

private lemma restrictionMorphisms_rightFractionRel
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (hF : (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).IsInvertedBy (neighborhoodModelToGlueingData S U s))
    (M N : FinitePresentationNeighborhoodModel S U s)
    (φ ψ : (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).RightFraction M N)
    (h : φ.map (neighborhoodModelToGlueingData S U s) hF =
      ψ.map (neighborhoodModelToGlueingData S U s) hF) :
    (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).RightFractionRel φ ψ := by
  have := FinitePresentationNeighborhoodModel.restrictionMorphisms_multiplicative S U s
  let Nb : OpenNeighborhood S U s :=
    ⟨φ.X'.neighborhood.V ⊓ ψ.X'.neighborhood.V,
      le_inf φ.X'.neighborhood.le_V ψ.X'.neighborhood.le_V,
      ⟨φ.X'.neighborhood.mem_V, ψ.X'.neighborhood.mem_V⟩⟩
  have h₁ : Nb.V ≤ M.neighborhood.V := inf_le_left.trans φ.s.base_le
  obtain ⟨t₁, ht₁⟩ := exists_restrict_rightFraction φ.s φ.hs Nb inf_le_left h₁
  obtain ⟨t₂, ht₂⟩ := exists_restrict_rightFraction ψ.s ψ.hs Nb inf_le_right h₁
  have hR : FinitePresentationNeighborhoodModel.restrictionMorphisms
      (M.restrictNeighborhoodHom Nb h₁) := M.restrictNeighborhoodHom_mem Nb h₁
  have e₁ : (neighborhoodModelToGlueingData S U s).map
        (M.restrictNeighborhoodHom Nb h₁) ≫
        φ.map (neighborhoodModelToGlueingData S U s) hF =
      (neighborhoodModelToGlueingData S U s).map (t₁ ≫ φ.f) := by
    rw [← ht₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [MorphismProperty.RightFraction.map_s_comp_map]
  have e₂ : (neighborhoodModelToGlueingData S U s).map
        (M.restrictNeighborhoodHom Nb h₁) ≫
        ψ.map (neighborhoodModelToGlueingData S U s) hF =
      (neighborhoodModelToGlueingData S U s).map (t₂ ≫ ψ.f) := by
    rw [← ht₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [MorphismProperty.RightFraction.map_s_comp_map]
  have key : (neighborhoodModelToGlueingData S U s).map (t₁ ≫ φ.f) =
      (neighborhoodModelToGlueingData S U s).map (t₂ ≫ ψ.f) :=
    e₁.symm.trans ((congrArg (fun k => (neighborhoodModelToGlueingData S U s).map
      (M.restrictNeighborhoodHom Nb h₁) ≫ k) h).trans e₂)
  obtain ⟨P, r, hr, hre⟩ := exists_restriction_eq_of_map_eq S U s
    (M.restrictNeighborhood Nb h₁) N (t₁ ≫ φ.f) (t₂ ≫ ψ.f) key
  refine ⟨P, r ≫ t₁, r ≫ t₂, ?_, ?_, ?_⟩
  · rw [Category.assoc, ht₁, Category.assoc, ht₂]
  · rw [Category.assoc, Category.assoc]
    exact hre
  · rw [Category.assoc, ht₁]
    exact MorphismProperty.comp_mem _ _ _ hr hR

/-- A morphism defined on the restriction of `M` to the local scheme at `s` descends to the
restriction of `M` to an affine neighbourhood of `s`. -/
private lemma exists_local_descent
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (M N : FinitePresentationNeighborhoodModel S U s)
    (aL : pullback M.hom M.localBase ⟶ N.source)
    (haL : aL ≫ N.hom = pullback.snd M.hom M.localBase ≫ N.localBase)
    (V : AffineNeighborhood S s) (hVM : V.1 ≤ M.neighborhood.V)
    (hVN : V.1 ≤ N.neighborhood.V) :
    ∃ (V' : AffineNeighborhood S s) (h : V'.1 ≤ V.1)
      (b : pullback M.hom (S.homOfLE (h.trans hVM)) ⟶ N.source),
      b ≫ N.hom = pullback.snd M.hom (S.homOfLE (h.trans hVM)) ≫
          S.homOfLE (h.trans hVN) ∧
      restrictLift M.hom (S.homOfLE (h.trans hVM)) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' (h.trans hVM)) ≫ b = aL := by
  classical
  have : Mono M.localBase := mono_of_mono_fac M.localBase_fac
  let nM := nestedPullbackIso (stalkπ S s V) (S.homOfLE hVM) M.localBase
    (localBase_eq_stalkπ_comp S U s M V hVM) (Over.mk M.hom)
  let nN := nestedPullbackIso (stalkπ S s V) (S.homOfLE hVN) N.localBase
    (localBase_eq_stalkπ_comp S U s N V hVN) (Over.mk N.hom)
  let kL : (Over.pullback M.localBase).obj (Over.mk M.hom) ⟶
      (Over.pullback N.localBase).obj (Over.mk N.hom) :=
    Over.homMk (pullback.lift aL (pullback.snd M.hom M.localBase) haL)
      (pullback.lift_snd _ _ _)
  have hkL : kL.left ≫ pullback.fst N.hom N.localBase = aL := pullback.lift_fst _ _ _
  obtain ⟨V', h, g₀, α, β, hα, hβ, hcomp⟩ := exists_morphism_after_restriction S s V
    ((Over.pullback (S.homOfLE hVM)).obj (Over.mk M.hom))
    ((Over.pullback (S.homOfLE hVN)).obj (Over.mk N.hom))
    (finitePresentation_pullback _ _ M.finitePresentation)
    (finitePresentation_pullback _ _ N.finitePresentation)
    (nM.hom ≫ kL ≫ nN.inv)
  have hV'M : V'.1 ≤ M.neighborhood.V := h.trans hVM
  have hV'N : V'.1 ≤ N.neighborhood.V := h.trans hVN
  have hα' : α.hom.left ≫ pullback.fst (pullback.snd M.hom (S.homOfLE hVM))
      (stalkπ S s V) =
      pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h))
        (stalkπ S s V') ≫
        pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) := hα
  have hβ' : β.hom.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
      (stalkπ S s V) =
      pullback.fst (pullback.snd (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h))
        (stalkπ S s V') ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) := hβ
  have hϖcond : restrictLift M.hom (S.homOfLE hVM) (S.homOfLE h) (S.homOfLE hV'M)
      (S.homOfLE_homOfLE _ _) ≫ pullback.snd M.hom (S.homOfLE hVM) =
      pullback.snd M.hom (S.homOfLE hV'M) ≫ S.homOfLE h := pullback.lift_snd _ _ _
  let ϖ := pullback.lift (restrictLift M.hom (S.homOfLE hVM) (S.homOfLE h)
    (S.homOfLE hV'M) (S.homOfLE_homOfLE _ _)) (pullback.snd M.hom (S.homOfLE hV'M)) hϖcond
  have hϖfst : ϖ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) =
      restrictLift M.hom (S.homOfLE hVM) (S.homOfLE h) (S.homOfLE hV'M)
        (S.homOfLE_homOfLE _ _) := pullback.lift_fst _ _ _
  have hϖsnd : ϖ ≫ pullback.snd (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) =
      pullback.snd M.hom (S.homOfLE hV'M) := pullback.lift_snd _ _ _
  refine ⟨V', h, ϖ ≫ g₀.left ≫
    pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) ≫
      pullback.fst N.hom (S.homOfLE hVN), ?_, ?_⟩
  · -- the glued map is a map over the base
    have h1 : g₀.left ≫ pullback.snd (pullback.snd N.hom (S.homOfLE hVN))
        (S.homOfLE h) =
        pullback.snd (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) := g₀.w
    have h2 : pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) ≫
        pullback.fst N.hom (S.homOfLE hVN) ≫ N.hom =
        pullback.snd (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) ≫
          S.homOfLE hV'N := by
      rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        S.homOfLE_homOfLE]
    calc (ϖ ≫ g₀.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h) ≫ pullback.fst N.hom (S.homOfLE hVN)) ≫ N.hom
        = ϖ ≫ g₀.left ≫ (pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h) ≫ pullback.fst N.hom (S.homOfLE hVN) ≫ N.hom) := by
          simp only [Category.assoc]
      _ = ϖ ≫ g₀.left ≫ (pullback.snd (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h) ≫ S.homOfLE hV'N) := by rw [h2]
      _ = ϖ ≫ (g₀.left ≫ pullback.snd (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h)) ≫ S.homOfLE hV'N := by simp only [Category.assoc]
      _ = ϖ ≫ pullback.snd (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) ≫
            S.homOfLE hV'N := by rw [h1]
      _ = _ := by rw [← Category.assoc, hϖsnd]
  · -- compatibility with the given map over the local scheme
    have hnN : nN.inv.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
        (stalkπ S s V) ≫ pullback.fst N.hom (S.homOfLE hVN) =
        pullback.fst N.hom N.localBase := nestedPullbackIso_inv_fst _ _ _ _ _
    have hmΞ : nM.hom.left ≫ kL.left ≫ nN.inv.left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (stalkπ S s V) ≫
          pullback.fst N.hom (S.homOfLE hVN) = nM.hom.left ≫ aL := by
      rw [hnN, hkL]
    have hβΞ : β.hom.left ≫
        pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (stalkπ S s V) ≫
          pullback.fst N.hom (S.homOfLE hVN) =
        pullback.fst (pullback.snd (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h)) (stalkπ S s V') ≫
          pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) ≫
            pullback.fst N.hom (S.homOfLE hVN) := by
      rw [← Category.assoc, hβ', Category.assoc]
    have hg₀Ξ : ((Over.pullback (stalkπ S s V')).map g₀).left ≫
        pullback.fst (pullback.snd (pullback.snd N.hom (S.homOfLE hVN))
          (S.homOfLE h)) (stalkπ S s V') =
        pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
          (S.homOfLE h)) (stalkπ S s V') ≫ g₀.left := pullback.lift_fst _ _ _
    have hdesc := congrArg (fun k => k.left ≫
      pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (stalkπ S s V) ≫
        pullback.fst N.hom (S.homOfLE hVN)) hcomp
    simp only [Over.comp_left, Category.assoc] at hdesc
    rw [hmΞ] at hdesc
    rw [hβΞ, ← Category.assoc _ (pullback.fst (pullback.snd (pullback.snd N.hom
      (S.homOfLE hVN)) (S.homOfLE h)) (stalkπ S s V')) _, hg₀Ξ] at hdesc
    simp only [Category.assoc] at hdesc
    -- the canonical section of the comparison
    have hϑcond : (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ ϖ) ≫
        pullback.snd (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) =
        pullback.snd M.hom M.localBase ≫ stalkπ S s V' := by
      rw [Category.assoc, hϖsnd]
      exact pullback.lift_snd _ _ _
    let ϑ := pullback.lift (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V')
      M.localBase (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ ϖ)
      (pullback.snd M.hom M.localBase) hϑcond
    have hϑfst : ϑ ≫ pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
        (S.homOfLE h)) (stalkπ S s V') =
        restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ ϖ := pullback.lift_fst _ _ _
    have hunit : ϑ ≫ α.hom.left ≫ nM.hom.left = 𝟙 _ := by
      apply (cancel_mono (pullback.fst M.hom M.localBase)).1
      rw [Category.id_comp]
      have hnM : nM.hom.left ≫ pullback.fst M.hom M.localBase =
          pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (stalkπ S s V) ≫
            pullback.fst M.hom (S.homOfLE hVM) := nestedPullbackIso_fst _ _ _ _ _
      calc (ϑ ≫ α.hom.left ≫ nM.hom.left) ≫ pullback.fst M.hom M.localBase
          = ϑ ≫ α.hom.left ≫ (nM.hom.left ≫ pullback.fst M.hom M.localBase) := by
            simp only [Category.assoc]
        _ = ϑ ≫ α.hom.left ≫ (pullback.fst (pullback.snd M.hom (S.homOfLE hVM))
              (stalkπ S s V) ≫ pullback.fst M.hom (S.homOfLE hVM)) := by rw [hnM]
        _ = ϑ ≫ (α.hom.left ≫ pullback.fst (pullback.snd M.hom (S.homOfLE hVM))
              (stalkπ S s V)) ≫ pullback.fst M.hom (S.homOfLE hVM) := by
            simp only [Category.assoc]
        _ = ϑ ≫ (pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
              (S.homOfLE h)) (stalkπ S s V') ≫ pullback.fst
                (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h)) ≫
              pullback.fst M.hom (S.homOfLE hVM) := by rw [hα']
        _ = (ϑ ≫ pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
              (S.homOfLE h)) (stalkπ S s V')) ≫ pullback.fst
                (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) ≫
              pullback.fst M.hom (S.homOfLE hVM) := by simp only [Category.assoc]
        _ = (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
              (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ ϖ) ≫ pullback.fst
                (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h) ≫
              pullback.fst M.hom (S.homOfLE hVM) := by rw [hϑfst]
        _ = restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
              (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫
              (ϖ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE hVM)) (S.homOfLE h)) ≫
                pullback.fst M.hom (S.homOfLE hVM) := by simp only [Category.assoc]
        _ = restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
              (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫
              pullback.fst M.hom (S.homOfLE hV'M) := by
            rw [hϖfst, restrictLift_fst]
        _ = pullback.fst M.hom M.localBase := restrictLift_fst _ _ _ _ _
    calc restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
            (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫
          (ϖ ≫ g₀.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
            (S.homOfLE h) ≫ pullback.fst N.hom (S.homOfLE hVN))
        = (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
            (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ ϖ) ≫
            (g₀.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
              (S.homOfLE h) ≫ pullback.fst N.hom (S.homOfLE hVN)) := by
          simp only [Category.assoc]
      _ = (ϑ ≫ pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
            (S.homOfLE h)) (stalkπ S s V')) ≫
            (g₀.left ≫ pullback.fst (pullback.snd N.hom (S.homOfLE hVN))
              (S.homOfLE h) ≫ pullback.fst N.hom (S.homOfLE hVN)) := by rw [hϑfst]
      _ = ϑ ≫ (pullback.fst (pullback.snd (pullback.snd M.hom (S.homOfLE hVM))
            (S.homOfLE h)) (stalkπ S s V') ≫ g₀.left ≫
            pullback.fst (pullback.snd N.hom (S.homOfLE hVN)) (S.homOfLE h) ≫
              pullback.fst N.hom (S.homOfLE hVN)) := by simp only [Category.assoc]
      _ = ϑ ≫ (α.hom.left ≫ nM.hom.left ≫ aL) := by rw [← hdesc]
      _ = (ϑ ≫ α.hom.left ≫ nM.hom.left) ≫ aL := by simp only [Category.assoc]
      _ = aL := by rw [hunit, Category.id_comp]

private lemma doubleRestrictLift_snd {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) :
    doubleRestrictLift f j l m hm ≫ pullback.snd f m =
      pullback.snd (pullback.snd f j) l :=
  pullback.lift_snd _ _ _

private lemma restrictLift_snd {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    (l : T ⟶ Y) (m : T ⟶ Z) (hm : l ≫ j = m) :
    restrictLift f j l m hm ≫ pullback.snd f j = pullback.snd f m ≫ l :=
  pullback.lift_snd _ _ _

/-- The open and local components of a morphism of gluing data, once the local one has been
descended to an affine neighbourhood, agree on the intersection with `U` after shrinking that
neighbourhood. -/
private lemma exists_overlap_agreement
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (M N : FinitePresentationNeighborhoodModel S U s)
    (aU : pullback M.hom (S.homOfLE M.neighborhood.le_V) ⟶ N.source)
    (haU : aU ≫ N.hom = pullback.snd M.hom (S.homOfLE M.neighborhood.le_V) ≫
      S.homOfLE N.neighborhood.le_V)
    (aLm : pullback M.hom M.localBase ⟶ N.source)
    (hstar : pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        ((S.fromSpecStalk s) ∣_ U) ≫ aU =
      M.overlapIso.hom.hom.left ≫
        pullback.fst (pullback.snd M.hom M.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ aLm)
    (V' : AffineNeighborhood S s) (hV'M : V'.1 ≤ M.neighborhood.V)
    (hV'N : V'.1 ≤ N.neighborhood.V)
    (b : pullback M.hom (S.homOfLE hV'M) ⟶ N.source)
    (hbN : b ≫ N.hom = pullback.snd M.hom (S.homOfLE hV'M) ≫ S.homOfLE hV'N)
    (hDESC : restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
      (localBase_eq_stalkπ_comp S U s M V' hV'M) ≫ b = aLm) :
    ∃ (W : AffineNeighborhood S s) (hWV' : W.1 ≤ V'.1)
      (cU : pullback M.hom ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE (hWV'.trans hV'M)) ⟶
        pullback M.hom (S.homOfLE M.neighborhood.le_V))
      (cV : pullback M.hom ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE (hWV'.trans hV'M)) ⟶
        pullback M.hom (S.homOfLE hV'M)),
      cU ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) =
        pullback.fst M.hom ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE (hWV'.trans hV'M)) ∧
      cV ≫ pullback.fst M.hom (S.homOfLE hV'M) =
        pullback.fst M.hom ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE (hWV'.trans hV'M)) ∧
      cU ≫ aU = cV ≫ b := by
  classical
  have : Mono M.localBase := mono_of_mono_fac M.localBase_fac
  obtain ⟨τ, hτ⟩ : ∃ τ : ((S.fromSpecStalk s) ⁻¹ᵁ U).toScheme ⟶ (V'.1.ι ⁻¹ᵁ U).toScheme,
      τ ≫ (V'.1.ι ⁻¹ᵁ U).ι = ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ stalkπ S s V' :=
    ⟨(affineNeighborhoodOverlapCone S U s).π.app V', Scheme.Hom.resLE_comp_ι _ _⟩
  have hτU : τ ≫ (V'.1.ι ∣_ U) = (S.fromSpecStalk s) ∣_ U :=
    comp_restrict_of_comp_ι_stalk S U s V' τ hτ
  -- the inclusions of the overlap into the two neighbourhoods
  have hρMU : (V'.1.ι ∣_ U) ≫ S.homOfLE M.neighborhood.le_V =
      (V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M := by
    apply (cancel_mono M.neighborhood.V.ι).1
    rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      morphismRestrict_ι]
  have hρNU : (V'.1.ι ∣_ U) ≫ S.homOfLE N.neighborhood.le_V =
      (V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N := by
    apply (cancel_mono N.neighborhood.V.ι).1
    rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      morphismRestrict_ι]
  have hτρ : τ ≫ ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) =
      ((S.fromSpecStalk s) ⁻¹ᵁ U).ι ≫ M.localBase := by
    rw [← Category.assoc, hτ, Category.assoc,
      localBase_eq_stalkπ_comp S U s M V' hV'M]
  have hτρM : τ ≫ ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) =
      ((S.fromSpecStalk s) ∣_ U) ≫ S.homOfLE M.neighborhood.le_V := by
    rw [← hρMU, ← Category.assoc, hτU]
  -- the two morphisms over the overlap
  let kU : (Over.pullback (S.homOfLE M.neighborhood.le_V)).obj (Over.mk M.hom) ⟶
      (Over.pullback (S.homOfLE N.neighborhood.le_V)).obj (Over.mk N.hom) :=
    Over.homMk (pullback.lift aU (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) haU)
      (pullback.lift_snd _ _ _)
  have hkU : kU.left ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) = aU :=
    pullback.lift_fst _ _ _
  let kb : (Over.pullback (S.homOfLE hV'M)).obj (Over.mk M.hom) ⟶
      (Over.pullback (S.homOfLE hV'N)).obj (Over.mk N.hom) :=
    Over.homMk (pullback.lift b (pullback.snd M.hom (S.homOfLE hV'M)) hbN)
      (pullback.lift_snd _ _ _)
  have hkb : kb.left ≫ pullback.fst N.hom (S.homOfLE hV'N) = b := pullback.lift_fst _ _ _
  let θMU := nestedPullbackIso (V'.1.ι ∣_ U) (S.homOfLE M.neighborhood.le_V)
    ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) hρMU (Over.mk M.hom)
  let θNU := nestedPullbackIso (V'.1.ι ∣_ U) (S.homOfLE N.neighborhood.le_V)
    ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) hρNU (Over.mk N.hom)
  let θMI := nestedPullbackIso ((V'.1.ι ⁻¹ᵁ U).ι) (S.homOfLE hV'M)
    ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) rfl (Over.mk M.hom)
  let θNI := nestedPullbackIso ((V'.1.ι ⁻¹ᵁ U).ι) (S.homOfLE hV'N)
    ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) rfl (Over.mk N.hom)
  have hθNU : θNU.hom.left ≫
      pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) =
      pullback.fst (pullback.snd N.hom (S.homOfLE N.neighborhood.le_V)) (V'.1.ι ∣_ U) ≫
        pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) :=
    nestedPullbackIso_fst _ _ _ _ _
  have hθNI : θNI.hom.left ≫
      pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) =
      pullback.fst (pullback.snd N.hom (S.homOfLE hV'N)) ((V'.1.ι ⁻¹ᵁ U).ι) ≫
        pullback.fst N.hom (S.homOfLE hV'N) :=
    nestedPullbackIso_fst _ _ _ _ _
  have hθMUinv : θMU.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        (V'.1.ι ∣_ U) ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) =
      pullback.fst M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) :=
    nestedPullbackIso_inv_fst _ _ _ _ _
  have hθMIinv : θMI.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE hV'M)) ((V'.1.ι ⁻¹ᵁ U).ι) ≫
        pullback.fst M.hom (S.homOfLE hV'M) =
      pullback.fst M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) :=
    nestedPullbackIso_inv_fst _ _ _ _ _
  have hmapU : ((Over.pullback (V'.1.ι ∣_ U)).map kU).left ≫
      pullback.fst (pullback.snd N.hom (S.homOfLE N.neighborhood.le_V))
        (V'.1.ι ∣_ U) =
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        (V'.1.ι ∣_ U) ≫ kU.left := pullback.lift_fst _ _ _
  have hmapI : ((Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb).left ≫
      pullback.fst (pullback.snd N.hom (S.homOfLE hV'N)) ((V'.1.ι ⁻¹ᵁ U).ι) =
      pullback.fst (pullback.snd M.hom (S.homOfLE hV'M)) ((V'.1.ι ⁻¹ᵁ U).ι) ≫
        kb.left := pullback.lift_fst _ _ _
  have hm₁ : (θMU.inv ≫ (Over.pullback (V'.1.ι ∣_ U)).map kU ≫ θNU.hom).left ≫
      pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) =
      θMU.inv.left ≫ pullback.fst (pullback.snd M.hom
        (S.homOfLE M.neighborhood.le_V)) (V'.1.ι ∣_ U) ≫ aU := by
    simp only [Over.comp_left, Category.assoc]
    rw [hθNU, ← Category.assoc _ (pullback.fst (pullback.snd N.hom
      (S.homOfLE N.neighborhood.le_V)) (V'.1.ι ∣_ U)) _, hmapU, Category.assoc, hkU]
  have hm₂ : (θMI.inv ≫ (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom).left ≫
      pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N) =
      θMI.inv.left ≫ pullback.fst (pullback.snd M.hom (S.homOfLE hV'M))
        ((V'.1.ι ⁻¹ᵁ U).ι) ≫ b := by
    simp only [Over.comp_left, Category.assoc]
    rw [hθNI, ← Category.assoc _ (pullback.fst (pullback.snd N.hom (S.homOfLE hV'N))
      ((V'.1.ι ⁻¹ᵁ U).ι)) _, hmapI, Category.assoc, hkb]
  have : Mono (S.homOfLE M.neighborhood.le_V) := inferInstance
  have hmjM : Mono (pullback.fst M.hom (S.homOfLE M.neighborhood.le_V)) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hmrM : Mono (pullback.fst M.hom (S.homOfLE hV'M)) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hmrhoN : Mono (pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hmloc : Mono (pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ
      U).ι) ≫
      pullback.fst M.hom M.localBase) := by
    have : Mono (pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) :=
      (IsPullback.of_hasPullback _ _).mono_fst_of_mono
    infer_instance
  have hdM : pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫
      pullback.fst M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) ≫ M.hom =
      pullback.snd (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ τ ≫ ((V'.1.ι ⁻¹ᵁ
          U).ι ≫ S.homOfLE hV'M) := by
    rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  let innerδ := pullback.lift
    (pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ pullback.fst M.hom
        ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M))
    (pullback.snd (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ ((S.fromSpecStalk
        s) ∣_ U))
    (by rw [Category.assoc, hdM, hτρM, Category.assoc])
  have hinnerfst : innerδ ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) =
      pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ pullback.fst M.hom
          ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) :=
    pullback.lift_fst _ _ _
  let δ := pullback.lift innerδ (pullback.snd (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE
      hV'M)) τ)
    (pullback.lift_snd _ _ _)
  have hδfst : δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
      ((S.fromSpecStalk s) ∣_ U) = innerδ :=
    pullback.lift_fst _ _ _
  let innerδ' := pullback.lift
    (pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ pullback.fst M.hom
        ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M))
    (pullback.snd (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ ((S.fromSpecStalk
        s) ⁻¹ᵁ U).ι)
    (by rw [Category.assoc, hdM, hτρ, Category.assoc])
  have hinnerfst' : innerδ' ≫ pullback.fst M.hom M.localBase =
      pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ pullback.fst M.hom
          ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) :=
    pullback.lift_fst _ _ _
  let δ' := pullback.lift innerδ' (pullback.snd (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE
      hV'M)) τ)
    (pullback.lift_snd _ _ _)
  have hδ'fst : δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)
      = innerδ' :=
    pullback.lift_fst _ _ _
  have hδM : pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫
      θMU.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) (V'.1.ι ∣_ U) =
      δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk s)
          ∣_ U) := by
    apply (cancel_mono (pullback.fst M.hom (S.homOfLE M.neighborhood.le_V))).1
    rw [hδfst, hinnerfst]
    simp only [Category.assoc]
    rw [hθMUinv]
  have hδ'M : pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫
      θMI.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE hV'M)) ((V'.1.ι ⁻¹ᵁ U).ι) =
      δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' hV'M)) := by
    apply (cancel_mono (pullback.fst M.hom (S.homOfLE hV'M))).1
    simp only [Category.assoc]
    rw [hθMIinv, restrictLift_fst, ← Category.assoc, hδ'fst, hinnerfst']
  have hov : δ ≫ M.overlapIso.hom.hom.left = δ' := by
    apply (cancel_mono (pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ
        U).ι) ≫ pullback.fst M.hom M.localBase)).1
    calc (δ ≫ M.overlapIso.hom.hom.left) ≫ (pullback.fst (pullback.snd M.hom M.localBase)
        (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ pullback.fst M.hom M.localBase)
        = δ ≫ M.overlapIso.hom.hom.left ≫ pullback.fst (pullback.snd M.hom M.localBase)
            (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ pullback.fst M.hom M.localBase := Category.assoc _ _
            _
      _ = δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk
          s) ∣_ U) ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) :=
          congrArg (fun k => δ ≫ k)
            (FinitePresentationNeighborhoodModel.overlapIso_hom_fst M)
      _ = (δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk
          s) ∣_ U)) ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) := (Category.assoc _ _
          _).symm
      _ = innerδ ≫ pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) := congrArg (fun k => k ≫
          pullback.fst M.hom (S.homOfLE M.neighborhood.le_V)) hδfst
      _ = pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ pullback.fst
          M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) := hinnerfst
      _ = innerδ' ≫ pullback.fst M.hom M.localBase := hinnerfst'.symm
      _ = (δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι)) ≫
          pullback.fst M.hom M.localBase := congrArg (fun k => k ≫ pullback.fst M.hom M.localBase)
          hδ'fst.symm
      _ = δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          pullback.fst M.hom M.localBase := Category.assoc _ _ _
  have hmain : (Over.pullback τ).map (θMU.inv ≫ (Over.pullback (V'.1.ι ∣_ U)).map kU ≫ θNU.hom) =
      (Over.pullback τ).map (θMI.inv ≫ (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom) := by
    refine overPullback_hom_ext_fst τ ?_
    have e1 : ((Over.pullback τ).map (θMU.inv ≫ (Over.pullback (V'.1.ι ∣_ U)).map kU ≫
        θNU.hom)).left ≫
        pullback.fst (pullback.snd N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) τ =
        pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ (θMU.inv ≫
            (Over.pullback (V'.1.ι ∣_ U)).map kU ≫ θNU.hom).left :=
      pullback.lift_fst _ _ _
    have e2 : ((Over.pullback τ).map (θMI.inv ≫ (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫
        θNI.hom)).left ≫
        pullback.fst (pullback.snd N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) τ =
        pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ (θMI.inv ≫
            (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom).left :=
      pullback.lift_fst _ _ _
    refine e1.trans (Eq.trans ?_ e2.symm)
    apply (cancel_mono (pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N))).1
    simp only [Category.assoc]
    rw [hm₁, hm₂]
    calc pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ θMU.inv.left ≫
        pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) (V'.1.ι ∣_ U) ≫ aU
        = (pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ θMU.inv.left ≫
            pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) (V'.1.ι ∣_ U)) ≫ aU
                := by
          simp only [Category.assoc]
      _ = (δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk
          s) ∣_ U)) ≫ aU := congrArg (fun k => k ≫ aU) hδM
      _ = δ ≫ pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) ((S.fromSpecStalk
          s) ∣_ U) ≫ aU := Category.assoc _ _ _
      _ = δ ≫ M.overlapIso.hom.hom.left ≫ pullback.fst (pullback.snd M.hom M.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ aLm :=
          congrArg (fun k => δ ≫ k) hstar
      _ = (δ ≫ M.overlapIso.hom.hom.left) ≫ pullback.fst (pullback.snd M.hom M.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ aLm :=
          (Category.assoc _ _ _).symm
      _ = δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ aLm
          := congrArg (fun k => k ≫ pullback.fst (pullback.snd M.hom M.localBase)
          (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ aLm) hov
      _ = δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' hV'M)) ≫ b :=
          congrArg (fun k => δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk
              s) ⁻¹ᵁ U).ι) ≫ k) hDESC.symm
      _ = (δ' ≫ pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          (restrictLift M.hom (S.homOfLE hV'M) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' hV'M))) ≫ b := by simp only [Category.assoc]
      _ = (pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) τ ≫ θMI.inv.left ≫
            pullback.fst (pullback.snd M.hom (S.homOfLE hV'M)) ((V'.1.ι ⁻¹ᵁ U).ι)) ≫ b :=
          congrArg (fun k => k ≫ b) hδ'M.symm
      _ = _ := by simp only [Category.assoc]
  obtain ⟨W, hWV', v, hv, heq⟩ := exists_eventually_eq_overlap_restriction S U s hU V'
    ((Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)).obj (Over.mk M.hom))
    ((Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)).obj (Over.mk N.hom))
    (finitePresentation_pullback _ _ M.finitePresentation)
    (finitePresentation_pullback _ _ N.finitePresentation) (θMU.inv ≫ (Over.pullback (V'.1.ι ∣_
        U)).map kU ≫ θNU.hom) (θMI.inv ≫ (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom) τ hτ
        hmain
  have hWM : W.1 ≤ M.neighborhood.V := hWV'.trans hV'M
  have hvρ : v ≫ ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) = ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hWM) := by
    rw [← Category.assoc, hv, Category.assoc, S.homOfLE_homOfLE]
  let χ := pullback.lift (restrictLift M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) v ((W.1.ι ⁻¹ᵁ
      U).ι ≫ S.homOfLE hWM) hvρ)
    (pullback.snd M.hom ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hWM)) (restrictLift_snd _ _ _ _ _)
  have hχfst : χ ≫ pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v =
      restrictLift M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M) v ((W.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hWM)
          hvρ := pullback.lift_fst _ _ _
  have e3 : ((Over.pullback v).map (θMU.inv ≫ (Over.pullback (V'.1.ι ∣_ U)).map kU ≫
      θNU.hom)).left ≫
      pullback.fst (pullback.snd N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) v =
      pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ (θMU.inv ≫
          (Over.pullback (V'.1.ι ∣_ U)).map kU ≫ θNU.hom).left := pullback.lift_fst _ _ _
  have e4 : ((Over.pullback v).map (θMI.inv ≫ (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫
      θNI.hom)).left ≫
      pullback.fst (pullback.snd N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) v =
      pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ (θMI.inv ≫
          (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom).left := pullback.lift_fst _ _ _
  have hagree : pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ (θMU.inv
      ≫ (Over.pullback (V'.1.ι ∣_ U)).map kU ≫ θNU.hom).left =
      pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ (θMI.inv ≫
          (Over.pullback ((V'.1.ι ⁻¹ᵁ U).ι)).map kb ≫ θNI.hom).left :=
    e3.symm.trans ((congrArg (fun k => k.left ≫
      pullback.fst (pullback.snd N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'N)) v) heq).trans e4)
  have hagree2 := congrArg (fun k => χ ≫ k ≫ pullback.fst N.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE
      hV'N)) hagree
  simp only [Category.assoc] at hagree2
  rw [hm₁, hm₂] at hagree2
  refine ⟨W, hWV',
    χ ≫ pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ θMU.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V)) (V'.1.ι ∣_ U),
    χ ≫ pullback.fst (pullback.snd M.hom ((V'.1.ι ⁻¹ᵁ U).ι ≫ S.homOfLE hV'M)) v ≫ θMI.inv.left ≫
      pullback.fst (pullback.snd M.hom (S.homOfLE hV'M)) ((V'.1.ι ⁻¹ᵁ U).ι), ?_, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hθMUinv, ← Category.assoc, hχfst, restrictLift_fst]
  · simp only [Category.assoc]
    rw [hθMIinv, ← Category.assoc, hχfst, restrictLift_fst]
  · simp only [Category.assoc]
    exact hagree2



/-- The two components of a morphism of gluing data agree on the punctured local scheme, after
the canonical comparison. -/
private lemma glueingData_map_overlap
    (S : Scheme.{u}) (U : S.Opens) (s : S)
    (M N : FinitePresentationNeighborhoodModel S U s)
    (f : (neighborhoodModelToGlueingData S U s).obj M ⟶
      (neighborhoodModelToGlueingData S U s).obj N) :
    pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        ((S.fromSpecStalk s) ∣_ U) ≫
        f.hom.left.hom.left ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) =
      M.overlapIso.hom.hom.left ≫
        pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
          f.hom.right.hom.left ≫ pullback.fst N.hom N.localBase := by
  have hNov := FinitePresentationNeighborhoodModel.overlapIso_hom_fst N
  have hmL : ((restrictOpenToPuncturedLocal S U s).map f.hom.left).hom.left ≫
      pullback.fst (pullback.snd N.hom (S.homOfLE N.neighborhood.le_V))
        ((S.fromSpecStalk s) ∣_ U) =
      pullback.fst (pullback.snd M.hom (S.homOfLE M.neighborhood.le_V))
        ((S.fromSpecStalk s) ∣_ U) ≫ f.hom.left.hom.left := pullback.lift_fst _ _ _
  have hmR : ((restrictLocalToPuncturedLocal S U s).map f.hom.right).hom.left ≫
      pullback.fst (pullback.snd N.hom N.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) =
      pullback.fst (pullback.snd M.hom M.localBase) (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫
        f.hom.right.hom.left := pullback.lift_fst _ _ _
  have hww : ((restrictOpenToPuncturedLocal S U s).map f.hom.left).hom.left ≫
      N.overlapIso.hom.hom.left =
      M.overlapIso.hom.hom.left ≫
        ((restrictLocalToPuncturedLocal S U s).map f.hom.right).hom.left :=
    congrArg (fun m => m.hom.left) f.hom.w
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans
    (congrArg (fun k => k ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V)) hmL.symm)
    (Eq.trans (Category.assoc _ _ _) (Eq.trans
      (congrArg (fun k => ((restrictOpenToPuncturedLocal S U s).map
        f.hom.left).hom.left ≫ k) hNov.symm)
      (Eq.trans (Category.assoc _ _ _).symm (Eq.trans
        (congrArg (fun k => k ≫
          (pullback.fst (pullback.snd N.hom N.localBase)
            (((S.fromSpecStalk s) ⁻¹ᵁ U).ι) ≫ pullback.fst N.hom N.localBase)) hww)
        (Eq.trans (Category.assoc _ _ _) (congrArg
          (fun k => M.overlapIso.hom.hom.left ≫ k)
          (Eq.trans (Category.assoc _ _ _).symm (Eq.trans
            (congrArg (fun k => k ≫ pullback.fst N.hom N.localBase) hmR)
            (Category.assoc _ _ _))))))))))

/-- Every morphism of gluing data between the images of two neighbourhood models is realized
by a right fraction. -/
private lemma exists_rightFraction_of_map
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S))
    (M N : FinitePresentationNeighborhoodModel S U s)
    (f : (neighborhoodModelToGlueingData S U s).obj M ⟶
      (neighborhoodModelToGlueingData S U s).obj N) :
    ∃ (P : FinitePresentationNeighborhoodModel S U s) (t : P ⟶ M)
      (_ : FinitePresentationNeighborhoodModel.restrictionMorphisms t) (g : P ⟶ N),
      (neighborhoodModelToGlueingData S U s).map g =
        (neighborhoodModelToGlueingData S U s).map t ≫ f := by
  classical
  have haU : (f.hom.left.hom.left ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V)) ≫ N.hom =
      pullback.snd M.hom (S.homOfLE M.neighborhood.le_V) ≫ (S.homOfLE N.neighborhood.le_V) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => f.hom.left.hom.left ≫ k) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (S.homOfLE N.neighborhood.le_V)) f.hom.left.hom.w)))
  have haL : (f.hom.right.hom.left ≫ pullback.fst N.hom N.localBase) ≫ N.hom = pullback.snd M.hom
      M.localBase ≫ N.localBase :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => f.hom.right.hom.left ≫ k) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ N.localBase) f.hom.right.hom.w)))
  obtain ⟨V, hVMN⟩ := exists_affineNeighborhood_le S s
    (M.neighborhood.V ⊓ N.neighborhood.V) ⟨M.neighborhood.mem_V, N.neighborhood.mem_V⟩
  have hVM : V.1 ≤ M.neighborhood.V := hVMN.trans inf_le_left
  have hVN : V.1 ≤ N.neighborhood.V := hVMN.trans inf_le_right
  obtain ⟨V', h, b, hbN, hDESC⟩ := exists_local_descent S U s M N (f.hom.right.hom.left ≫
      pullback.fst N.hom N.localBase) haL V hVM hVN
  obtain ⟨W, hWV', cU, cV, hcU, hcV, hagree⟩ := exists_overlap_agreement S U s hU M N
    (f.hom.left.hom.left ≫ pullback.fst N.hom (S.homOfLE N.neighborhood.le_V)) haU
        (f.hom.right.hom.left ≫ pullback.fst N.hom N.localBase) (glueingData_map_overlap S U s M N
        f) V' (h.trans hVM) (h.trans hVN)
    b hbN hDESC
  have hOm : U ⊔ W.1 ≤ M.neighborhood.V :=
    sup_le M.neighborhood.le_V (hWV'.trans (h.trans hVM))
  have hOn : U ⊔ W.1 ≤ N.neighborhood.V :=
    sup_le N.neighborhood.le_V (hWV'.trans (h.trans hVN))
  have hmem : s ∈ U ⊔ W.1 := Or.inr W.2.2
  have : IsOpenImmersion (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) :=
      inferInstance
  have hbaseW : ((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) = (W.1.ι ∣_ U) ≫
      (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1)) := by
    apply (cancel_mono (U ⊔ W.1 : S.Opens).ι).1
    rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      morphismRestrict_ι]
  have hcondw : pullback.fst M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) ≫
      M.hom =
      (pullback.snd M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) ≫ (((W.1.ι
          ⁻¹ᵁ U).ι) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)))) ≫ (S.homOfLE hOm) := by
    rw [Category.assoc, Category.assoc, S.homOfLE_homOfLE]
    exact pullback.condition
  let w := pullback.lift (pullback.fst M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans
      hVM)))))
    (pullback.snd M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) ≫ (((W.1.ι
        ⁻¹ᵁ U).ι) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)))) hcondw
  have hwfst : w ≫ pullback.fst M.hom (S.homOfLE hOm) = pullback.fst M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫
      (S.homOfLE (hWV'.trans (h.trans hVM)))) :=
    pullback.lift_fst _ _ _
  have hwsnd : w ≫ pullback.snd M.hom (S.homOfLE hOm) =
      pullback.snd M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) ≫ (((W.1.ι
          ⁻¹ᵁ U).ι) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) := pullback.lift_snd _ _ _
  have : IsOpenImmersion (w ≫ pullback.fst M.hom (S.homOfLE hOm)) := by
    rw [hwfst]; infer_instance
  have : IsOpenImmersion w := IsOpenImmersion.of_comp w (pullback.fst M.hom (S.homOfLE hOm))
  let u := pullback.lift w (pullback.snd M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans
      (h.trans hVM)))) ≫ (W.1.ι ∣_ U))
    (by rw [hwsnd, Category.assoc, hbaseW])
  let v₀ := pullback.lift w (pullback.snd M.hom (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans
      (h.trans hVM)))) ≫ ((W.1.ι ⁻¹ᵁ U).ι))
    (by rw [hwsnd, Category.assoc])
  have hu : u ≫ (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U
      ⊔ W.1))) = w := pullback.lift_fst _ _ _
  have hv₀ : v₀ ≫ (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right :
      W.1 ≤ U ⊔ W.1))) = w := pullback.lift_fst _ _ _
  have hcover : Set.range (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
      (le_sup_left : U ≤ U ⊔ W.1))) ∪ Set.range (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
      (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) = Set.univ := by
    rw [IsOpenImmersion.range_pullbackFst, IsOpenImmersion.range_pullbackFst,
      Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
    apply Set.eq_univ_of_forall
    intro x
    rcases (pullback.snd M.hom (S.homOfLE hOm) x).2 with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hrange : Set.range w = Set.range (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
      (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))) ∩ Set.range (pullback.fst (pullback.snd M.hom
      (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) := by
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨z, rfl⟩
      exact ⟨⟨u z, by rw [← Scheme.Hom.comp_apply, hu]⟩,
        ⟨v₀ z, by rw [← Scheme.Hom.comp_apply, hv₀]⟩⟩
    · rw [IsOpenImmersion.range_pullbackFst, IsOpenImmersion.range_pullbackFst,
        Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE]
      rintro x ⟨hx1, hx2⟩
      have hpt : M.hom (pullback.fst M.hom (S.homOfLE hOm) x) =
          (((W.1.ι ⁻¹ᵁ U).ι) ≫ (S.homOfLE (hWV'.trans (h.trans hVM)))) (⟨⟨(pullback.snd M.hom
              (S.homOfLE hOm) x).1, hx2⟩, hx1⟩ :
            (W.1.ι ⁻¹ᵁ U).toScheme) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        exact (Subtype.ext ((Scheme.homOfLE_apply hOm
            (pullback.snd M.hom (S.homOfLE hOm) x)).trans
          (Scheme.homOfLE_apply (hWV'.trans (h.trans hVM)) (((W.1.ι ⁻¹ᵁ U).ι)
            (⟨⟨(pullback.snd M.hom (S.homOfLE hOm) x).1, hx2⟩, hx1⟩ :
              (W.1.ι ⁻¹ᵁ U).toScheme))).symm)).trans
          (Scheme.Hom.comp_apply _ _ _).symm
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpt
      refine ⟨z, ?_⟩
      apply (pullback.fst M.hom (S.homOfLE hOm)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hwfst, hz1]
  have hmjM : Mono (pullback.fst M.hom (S.homOfLE M.neighborhood.le_V)) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hmrM : Mono (pullback.fst M.hom (S.homOfLE (h.trans hVM))) :=
    (IsPullback.of_hasPullback _ _).mono_fst_of_mono
  have hucA : u ≫ (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔
      W.1)) (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) = cU :=
    (cancel_mono (pullback.fst M.hom (S.homOfLE M.neighborhood.le_V))).1
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => u ≫ k) (doubleRestrictLift_fst _ _ _ _ _)).trans
          (((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ pullback.fst M.hom (S.homOfLE hOm)) hu)).trans
              (hwfst.trans hcU.symm))))
  have hvcB : v₀ ≫ (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔
      W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
      (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
      (S.homOfLE_homOfLE _ _)) = cV :=
    (cancel_mono (pullback.fst M.hom (S.homOfLE (h.trans hVM)))).1
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => v₀ ≫ k)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE
                (le_sup_right : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM)))
                (S.homOfLE_homOfLE _ _)) ≫ k) (restrictLift_fst _ _ _ _ _)).trans
              (doubleRestrictLift_fst _ _ _ _ _)))).trans
          (((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ pullback.fst M.hom (S.homOfLE hOm)) hv₀)).trans
              (hwfst.trans hcV.symm))))
  have hglue : u ≫ ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔
      W.1)) (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ (f.hom.left.hom.left ≫
      pullback.fst N.hom (S.homOfLE N.neighborhood.le_V))) = v₀ ≫ ((doubleRestrictLift M.hom
      (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans
      hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE
      hWV') (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ b) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (f.hom.left.hom.left ≫ pullback.fst N.hom (S.homOfLE
          N.neighborhood.le_V))) hucA).trans
        (hagree.trans
          ((congrArg (fun k => k ≫ b) hvcB.symm).trans
            (((Category.assoc _ _ _).trans
              (congrArg (fun k => v₀ ≫ k) (Category.assoc _ _ _)))))))
  obtain ⟨gmap, hpg, hqg⟩ := exists_glued_hom_of_range_union (pullback.fst (pullback.snd M.hom
      (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))) (pullback.fst (pullback.snd M.hom
      (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) hcover
    ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1)) (S.homOfLE
        M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ (f.hom.left.hom.left ≫ pullback.fst N.hom
        (S.homOfLE N.neighborhood.le_V))) ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE
        (le_sup_right : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE
        _ _)) ≫ (restrictLift M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE
        (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ b)
    (glue_cond_of_range_inter (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
        (le_sup_left : U ≤ U ⊔ W.1))) (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
        (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) w u v₀ hu hv₀ hrange _ _ hglue)
  have hgw : gmap ≫ N.hom = pullback.snd M.hom (S.homOfLE hOm) ≫ (S.homOfLE hOn) := by
    refine hom_ext_of_range_union (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
        (le_sup_left : U ≤ U ⊔ W.1))) (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
        (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) hcover ?_ ?_
    · calc (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
        W.1))) ≫ gmap ≫ N.hom
          = ((pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
              W.1))) ≫ gmap) ≫ N.hom := (Category.assoc _ _ _).symm
        _ = ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))
            (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ (f.hom.left.hom.left ≫
            pullback.fst N.hom (S.homOfLE N.neighborhood.le_V))) ≫ N.hom := congrArg (fun k => k ≫
            N.hom) hpg
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))
            (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ (f.hom.left.hom.left ≫
            pullback.fst N.hom (S.homOfLE N.neighborhood.le_V)) ≫ N.hom := Category.assoc _ _ _
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))
            (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ pullback.snd M.hom
            (S.homOfLE M.neighborhood.le_V) ≫ (S.homOfLE N.neighborhood.le_V) :=
            congrArg (fun k => (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left :
                U ≤ U ⊔ W.1)) (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ k) haU
        _ = ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))
            (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) ≫ pullback.snd M.hom
            (S.homOfLE M.neighborhood.le_V)) ≫ (S.homOfLE N.neighborhood.le_V) := (Category.assoc
            _ _ _).symm
        _ = (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
            W.1))) ≫ (S.homOfLE N.neighborhood.le_V) :=
            congrArg (fun k => k ≫ (S.homOfLE N.neighborhood.le_V)) (doubleRestrictLift_snd _ _ _
                _ _)
        _ = (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
            W.1))) ≫ (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1)) ≫ (S.homOfLE hOn) :=
            congrArg (fun k => (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
                (le_sup_left : U ≤ U ⊔ W.1))) ≫ k) (S.homOfLE_homOfLE _ _).symm
        _ = ((pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
            W.1))) ≫ (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))) ≫ (S.homOfLE hOn) := (Category.assoc
            _ _ _).symm
        _ = ((pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
            W.1))) ≫ pullback.snd M.hom (S.homOfLE hOm)) ≫ (S.homOfLE hOn) :=
            congrArg (fun k => k ≫ (S.homOfLE hOn)) pullback.condition.symm
        _ = (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔
            W.1))) ≫ pullback.snd M.hom (S.homOfLE hOm) ≫ (S.homOfLE hOn) := Category.assoc _ _ _
    · calc (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔
        W.1))) ≫ gmap ≫ N.hom
          = ((pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
              ⊔ W.1))) ≫ gmap) ≫ N.hom := (Category.assoc _ _ _).symm
        _ = ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
            (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
            (S.homOfLE_homOfLE _ _)) ≫ b) ≫ N.hom := congrArg (fun k => k ≫ N.hom) hqg
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
            (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
            (S.homOfLE_homOfLE _ _)) ≫ b ≫ N.hom := by simp only [Category.assoc]
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
            (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
            (S.homOfLE_homOfLE _ _)) ≫ pullback.snd M.hom (S.homOfLE (h.trans hVM)) ≫ (S.homOfLE
            (h.trans hVN)) :=
            congrArg (fun k => (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right
                : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _))
                ≫ (restrictLift M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE
                (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ k) hbN
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ ((restrictLift M.hom
            (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
            (S.homOfLE_homOfLE _ _)) ≫ pullback.snd M.hom (S.homOfLE (h.trans hVM))) ≫ (S.homOfLE
            (h.trans hVN)) := by
            simp only [Category.assoc]
        _ = (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (pullback.snd M.hom
            (S.homOfLE (hWV'.trans (h.trans hVM))) ≫ S.homOfLE hWV') ≫ (S.homOfLE (h.trans hVN))
            :=
            congrArg (fun k => (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right
                : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _))
                ≫ k ≫ (S.homOfLE (h.trans hVN))) (restrictLift_snd _ _ _ _ _)
        _ = ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ pullback.snd M.hom
            (S.homOfLE (hWV'.trans (h.trans hVM)))) ≫ S.homOfLE hWV' ≫ (S.homOfLE (h.trans hVN))
            := by
            simp only [Category.assoc]
        _ = (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ S.homOfLE hWV' ≫ (S.homOfLE (h.trans hVN)) :=
            congrArg (fun k => k ≫ S.homOfLE hWV' ≫ (S.homOfLE (h.trans hVN)))
              (doubleRestrictLift_snd _ _ _ _ _)
        _ = (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ (S.homOfLE (hWV'.trans (h.trans hVN))) := congrArg (fun k => (pullback.snd
            (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) ≫ k)
            (S.homOfLE_homOfLE _ _)
        _ = (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) ≫ (S.homOfLE hOn) :=
            congrArg (fun k => (pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
                (le_sup_right : W.1 ≤ U ⊔ W.1))) ≫ k) (S.homOfLE_homOfLE _ _).symm
        _ = ((pullback.snd (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) ≫ (S.homOfLE hOn) :=
            (Category.assoc _ _ _).symm
        _ = ((pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ pullback.snd M.hom (S.homOfLE hOm)) ≫ (S.homOfLE hOn) :=
            congrArg (fun k => k ≫ (S.homOfLE hOn)) pullback.condition.symm
        _ = (pullback.fst (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U
            ⊔ W.1))) ≫ pullback.snd M.hom (S.homOfLE hOm) ≫ (S.homOfLE hOn) := Category.assoc _ _
            _
  refine ⟨(M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm), (M.restrictNeighborhoodHom ⟨U
      ⊔ W.1, le_sup_left, hmem⟩ hOm), M.restrictNeighborhoodHom_mem _ hOm, (⟨hOn, gmap, hgw⟩ :
      (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) ⟶ N), ?_⟩
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · apply ObjectProperty.hom_ext
    refine overPullback_hom_ext_fst (S.homOfLE N.neighborhood.le_V) ?_
    have e1 : ((neighborhoodModelOpenRestrictionFunctor S U s).map (⟨hOn, gmap, hgw⟩ :
        (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) ⟶ N)).hom.left ≫
        pullback.fst N.hom (S.homOfLE N.neighborhood.le_V) = (pullback.fst (pullback.snd M.hom
            (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))) ≫ gmap := pullback.lift_fst
            _ _ _
    have e2 : ((neighborhoodModelOpenRestrictionFunctor S U s).map (M.restrictNeighborhoodHom ⟨U ⊔
        W.1, le_sup_left, hmem⟩ hOm)).hom.left ≫
        pullback.fst M.hom (S.homOfLE M.neighborhood.le_V) = (pullback.fst (pullback.snd M.hom
            (S.homOfLE hOm)) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))) ≫ pullback.fst M.hom
            (S.homOfLE hOm) :=
      pullback.lift_fst _ _ _
    have e3 : ((neighborhoodModelOpenRestrictionFunctor S U s).map (M.restrictNeighborhoodHom ⟨U ⊔
        W.1, le_sup_left, hmem⟩ hOm)).hom.left =
        (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_left : U ≤ U ⊔ W.1))
            (S.homOfLE M.neighborhood.le_V) (S.homOfLE_homOfLE _ _)) :=
      (cancel_mono (pullback.fst M.hom (S.homOfLE M.neighborhood.le_V))).1
        (e2.trans (doubleRestrictLift_fst _ _ _ _ _).symm)
    exact e1.trans (hpg.trans
      ((congrArg (fun k => k ≫ (f.hom.left.hom.left ≫ pullback.fst N.hom (S.homOfLE
          N.neighborhood.le_V))) e3).symm.trans (Category.assoc _ _ _).symm))
  · apply ObjectProperty.hom_ext
    refine overPullback_hom_ext_fst N.localBase ?_
    have hPloc : (restrictLift (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1
        ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩
        hOm).localBase (localBase_eq_stalkπ_comp S U s (M.restrictNeighborhood ⟨U ⊔ W.1,
        le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ (pullback.fst (pullback.snd M.hom (S.homOfLE
        hOm)) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))) = (pullback.fst (pullback.snd M.hom
        (S.homOfLE hOm)) (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm).localBase) :=
        restrictLift_fst _ _ _ _ _
    have e1 : ((neighborhoodModelLocalRestrictionFunctor S U s).map (⟨hOn, gmap, hgw⟩ :
        (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) ⟶ N)).hom.left ≫
        pullback.fst N.hom N.localBase = (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
            (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm).localBase) ≫ gmap :=
            pullback.lift_fst _ _ _
    have e2 : ((neighborhoodModelLocalRestrictionFunctor S U s).map (M.restrictNeighborhoodHom ⟨U
        ⊔ W.1, le_sup_left, hmem⟩ hOm)).hom.left ≫
        pullback.fst M.hom M.localBase = (pullback.fst (pullback.snd M.hom (S.homOfLE hOm))
            (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm).localBase) ≫ pullback.fst
            M.hom (S.homOfLE hOm) :=
      pullback.lift_fst _ _ _
    have e3 : (restrictLift (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE (le_sup_right : W.1 ≤
        U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩
        hOm).localBase (localBase_eq_stalkπ_comp S U s (M.restrictNeighborhood ⟨U ⊔ W.1,
        le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ (doubleRestrictLift M.hom (S.homOfLE hOm)
        (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM)))
        (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE hWV')
        (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) =
        ((neighborhoodModelLocalRestrictionFunctor S U s).map (M.restrictNeighborhoodHom ⟨U ⊔ W.1,
        le_sup_left, hmem⟩ hOm)).hom.left ≫ (restrictLift M.hom (S.homOfLE (h.trans hVM)) (stalkπ
        S s V') M.localBase (localBase_eq_stalkπ_comp S U s M V' (h.trans hVM))) := by
      apply (cancel_mono (pullback.fst M.hom (S.homOfLE (h.trans hVM)))).1
      refine Eq.trans ((Category.assoc (restrictLift (pullback.snd M.hom (S.homOfLE hOm))
          (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔
          W.1, le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
          (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right))
          ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
          (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
          (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
          (S.homOfLE_homOfLE _ _)))
        (pullback.fst M.hom (S.homOfLE (h.trans hVM)))).trans
          (congrArg (fun k => (restrictLift (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
              (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔ W.1,
              le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
              (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ k)
            (Category.assoc (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right :
                W.1 ≤ U ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _))
                (restrictLift M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE
                (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) (pullback.fst M.hom
                (S.homOfLE (h.trans hVM)))))) ?_
      refine Eq.trans (congrArg (fun k => (restrictLift (pullback.snd M.hom (S.homOfLE hOm))
          (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔
          W.1, le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
          (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫
          (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
          (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ k)
        (restrictLift_fst _ _ _ _ _)) ?_
      refine Eq.trans (congrArg (fun k => (restrictLift (pullback.snd M.hom (S.homOfLE hOm))
          (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔
          W.1, le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
          (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ k)
        (doubleRestrictLift_fst _ _ _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun k => k ≫ pullback.fst M.hom (S.homOfLE hOm)) hPloc) ?_
      refine Eq.trans e2.symm ?_
      refine Eq.trans (congrArg (fun k => ((neighborhoodModelLocalRestrictionFunctor S U s).map
          (M.restrictNeighborhoodHom ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm)).hom.left ≫ k)
        (restrictLift_fst M.hom (S.homOfLE (h.trans hVM)) (stalkπ S s V') M.localBase
          (localBase_eq_stalkπ_comp S U s M V' (h.trans hVM))).symm) ?_
      exact (Category.assoc _ _ _).symm
    refine Eq.trans e1 ?_
    refine Eq.trans (congrArg (fun k => k ≫ gmap) hPloc.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => (restrictLift (pullback.snd M.hom (S.homOfLE hOm))
        (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔
        W.1, le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
        (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ k) hqg) ?_
    refine Eq.trans ((congrArg (fun k => (restrictLift (pullback.snd M.hom (S.homOfLE hOm))
        (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔
        W.1, le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
        (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right)) ≫ k)
      (Category.assoc (doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U
          ⊔ W.1)) (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) (restrictLift
          M.hom (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
          (S.homOfLE_homOfLE _ _)) b).symm).trans
        (Category.assoc (restrictLift (pullback.snd M.hom (S.homOfLE hOm)) (S.homOfLE
            (le_sup_right : W.1 ≤ U ⊔ W.1)) (stalkπ S s W) (M.restrictNeighborhood ⟨U ⊔ W.1,
            le_sup_left, hmem⟩ hOm).localBase (localBase_eq_stalkπ_comp S U s
            (M.restrictNeighborhood ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm) W le_sup_right))
            ((doubleRestrictLift M.hom (S.homOfLE hOm) (S.homOfLE (le_sup_right : W.1 ≤ U ⊔ W.1))
            (S.homOfLE (hWV'.trans (h.trans hVM))) (S.homOfLE_homOfLE _ _)) ≫ (restrictLift M.hom
            (S.homOfLE (h.trans hVM)) (S.homOfLE hWV') (S.homOfLE (hWV'.trans (h.trans hVM)))
            (S.homOfLE_homOfLE _ _))) b).symm) ?_
    refine Eq.trans (congrArg (fun k => k ≫ b) e3) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => ((neighborhoodModelLocalRestrictionFunctor S U s).map
        (M.restrictNeighborhoodHom ⟨U ⊔ W.1, le_sup_left, hmem⟩ hOm)).hom.left ≫ k) hDESC) ?_
    exact (Category.assoc _ _ _).symm

private lemma neighborhoodModelToGlueingData_essSurj
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S)) :
    (neighborhoodModelToGlueingData S U s).EssSurj := by
  refine ⟨fun Z => ?_⟩
  have : IsIso Z.obj.hom := Z.property
  obtain ⟨M, jU, jL, hcU, hcL, hc⟩ := exists_neighborhoodModel_of_glueingData S U s hU
    Z.obj.left.obj Z.obj.left.property Z.obj.right.obj Z.obj.right.property
    ((show ObjectProperty (Over (puncturedLocalScheme S U s)) from
      fun Y ↦ FinitePresentation Y.hom).ι.mapIso (asIso Z.obj.hom))
  exact ⟨M, nonempty_iso_neighborhoodModel_of_pullbacks S U s Z M jU jL hcU hcL hc⟩

private lemma finitePresentationGermToGlueingData_isEquivalence
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hU : IsRetrocompact (U : Set S)) :
    (finitePresentationGermToGlueingData S U s).IsEquivalence := by
  have := FinitePresentationNeighborhoodModel.restrictionMorphisms_multiplicative S U s
  have := FinitePresentationNeighborhoodModel.restrictionMorphisms_rightCalculus S U s
  have hF : (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := U) (s := s)).IsInvertedBy
      (neighborhoodModelToGlueingData S U s) := by
    intro X Y f hf
    exact neighborhoodModelToGlueingData_inverts_restriction S U s f hf
  refine localizationLift_isEquivalence_of_rightFractions _
    (neighborhoodModelToGlueingData S U s) hF
    (neighborhoodModelToGlueingData_essSurj S U s hU) ?_ ?_
  · intro X Y f
    obtain ⟨P, t, ht, g, heq⟩ := exists_rightFraction_of_map S U s hU X Y f
    refine ⟨⟨t, ht, g⟩, ?_⟩
    have : IsIso ((neighborhoodModelToGlueingData S U s).map t) := hF _ ht
    apply (cancel_epi ((neighborhoodModelToGlueingData S U s).map t)).1
    exact (MorphismProperty.RightFraction.map_s_comp_map ⟨t, ht, g⟩
      (neighborhoodModelToGlueingData S U s) hF).trans heq
  · intro X Y φ ψ hφψ
    exact restrictionMorphisms_rightFractionRel S U s hF X Y φ ψ hφψ

/-- **Stacks Project, Tag 0BQ5.** Finite-presentation schemes on open neighbourhoods of a
retrocompact open together with a point are equivalent, as a germ, to compatible
finite-presentation schemes on the open and on the local scheme at the point. The natural
identifications with base change intertwine the gluing comparison with the canonical
iterated-pullback comparison on the overlap. -/
@[stacks 0BQ5, no_expose]
public noncomputable def glueingEquivalenceNearPoint
    (S : Scheme.{u}) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hU : IsRetrocompact (U : Set S)) :
    { e : FinitePresentationGerm S U s ≌ glueingDataNearPoint S U s //
      ∃ a : (((FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ openComponent S U s) ≅
        (neighborhoodModelToAmbient S U s ⋙ Over.pullback U.ι)),
      ∃ b : (((FinitePresentationNeighborhoodModel.restrictionMorphisms
        (S := S) (U := U) (s := s)).Q ⋙ e.functor ⋙ localComponent S U s) ≅
        (neighborhoodModelToAmbient S U s ⋙ Over.pullback (S.fromSpecStalk s))),
      overlapComparisonCompatible S U s e a b } :=
  glueingEquivalenceNearPoint_of_isEquivalence S U s
    (finitePresentationGermToGlueingData_isEquivalence S U s hU)


/-! ### Glueing at a closed point

Stacks 0BPA is the case `U = S \ {s}` for a *closed* point `s` whose open complement has
quasi-compact inclusion.  Every open neighbourhood of `U ∪ {s}` is then `S` itself, so a
neighbourhood model is the same data as a scheme of finite presentation over `S`, every
restriction morphism is an isomorphism, and no localization is needed: the comparison functor
`neighborhoodModelToGlueingData` is itself an equivalence. -/

/-- The canonical comparison between the two restrictions of a scheme of finite presentation
over `S` to the punctured local scheme: the base-change associativity isomorphism of the square
whose bottom row is `U ⟶ S` and whose right column is `Spec 𝒪_{S, s} ⟶ S`. -/
public noncomputable def restrictionComparisonAtPoint (S : Scheme.{u}) (U : S.Opens) (s : S) :
    finitePresentationBaseChange U.ι ⋙ restrictOpenToPuncturedLocal S U s ≅
      finitePresentationBaseChange (S.fromSpecStalk s) ⋙ restrictLocalToPuncturedLocal S U s :=
  finitePresentationPullbackSquareIso (morphismRestrict_ι (S.fromSpecStalk s) U)

/-- The canonical restriction functor: a scheme of finite presentation over `S` goes to its
restriction to `U`, its restriction to `Spec 𝒪_{S, s}`, and the canonical comparison of the two
induced restrictions to the punctured local scheme. -/
public noncomputable def restrictionFunctorAtPoint (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationOver S ⥤ glueingDataNearPoint S U s :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocal S U s)
      (restrictLocalToPuncturedLocal S U s)) from fun X ↦ IsIso X.hom).lift
    { obj := fun X ↦ ⟨(finitePresentationBaseChange U.ι).obj X,
        (finitePresentationBaseChange (S.fromSpecStalk s)).obj X,
        (restrictionComparisonAtPoint S U s).hom.app X⟩
      map := fun f ↦ ⟨(finitePresentationBaseChange U.ι).map f,
        (finitePresentationBaseChange (S.fromSpecStalk s)).map f,
        (restrictionComparisonAtPoint S U s).hom.naturality f⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp } (fun X ↦ inferInstance)

/-- The overlap comparison of a neighbourhood model's glueing datum is the base-change
associativity isomorphism used by `restrictionFunctorAtPoint`. -/
private lemma canonicalOverlapIso_hom_eq (S : Scheme.{u}) (U : S.Opens) (s : S) (X : Over S) :
    (canonicalOverlapIso S U s X).hom =
      (Over.pullbackSquareObjIso (morphismRestrict_ι (S.fromSpecStalk s) U) X).hom := by
  apply CategoryTheory.Over.OverMorphism.ext
  apply (Over.isPullback_pullback_snd_pullback'
    (morphismRestrict_ι (S.fromSpecStalk s) U) X).hom_ext
  · exact (canonicalOverlapIso_hom_fst S U s X).trans
      (Over.pullbackSquareObjIso_hom_left_fst
        (morphismRestrict_ι (S.fromSpecStalk s) U) X).symm
  · exact ((canonicalOverlapIso S U s X).hom.w).trans
      ((Over.pullbackSquareObjIso (morphismRestrict_ι (S.fromSpecStalk s) U) X).hom.w).symm

section ClosedPoint

variable {S : Scheme.{u}} {s : S}

/-- The open complement of a closed point. -/
public def puncturedOpen (hs : IsClosed ({s} : Set S)) : S.Opens :=
  ⟨({s} : Set S)ᶜ, hs.isOpen_compl⟩

/-- A closed point does not lie in its own open complement. -/
public lemma notMem_puncturedOpen (hs : IsClosed ({s} : Set S)) : s ∉ puncturedOpen hs := by
  simp [puncturedOpen]

/-- An open subscheme whose inclusion is quasi-compact is retrocompact. -/
public lemma isRetrocompact_of_quasiCompact_ι (V : S.Opens) (hqc : QuasiCompact V.ι) :
    IsRetrocompact (V : Set S) := by
  apply IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
  show IsSpectralMap V.ι.base
  exact quasiCompact_iff_isSpectralMap.mp hqc

/-- An open subscheme containing a closed point together with its complement is everything. -/
public lemma eq_top_of_puncturedOpen_le (hs : IsClosed ({s} : Set S)) {V : S.Opens}
    (hUV : puncturedOpen hs ≤ V) (hsV : s ∈ V) : V = ⊤ := by
  apply top_unique
  intro z _
  by_cases hz : z = s
  · subst hz; exact hsV
  · exact hUV (by simpa [puncturedOpen] using hz)

/-- An open neighbourhood of a closed point which contains the complement of that point is the
whole scheme. -/
private lemma openNeighborhood_eq_top (hs : IsClosed ({s} : Set S))
    (N : OpenNeighborhood S (puncturedOpen hs) s) : N.V = ⊤ :=
  eq_top_of_puncturedOpen_le hs N.le_V N.mem_V

/-- Restriction between two opens each contained in the other is an isomorphism. -/
private lemma isIso_homOfLE {V W : S.Opens} (h : V ≤ W) (h' : W ≤ V) : IsIso (S.homOfLE h) :=
  ⟨⟨S.homOfLE h',
    by rw [Scheme.homOfLE_homOfLE]; exact S.homOfLE_rfl _,
    by rw [Scheme.homOfLE_homOfLE]; exact S.homOfLE_rfl _⟩⟩

/-- In the closed-point situation every restriction morphism of neighbourhood models is an
isomorphism, because every neighbourhood is the whole scheme. -/
private lemma isIso_of_restrictionMorphisms (hs : IsClosed ({s} : Set S))
    {X Y : FinitePresentationNeighborhoodModel S (puncturedOpen hs) s} (f : X ⟶ Y)
    (hf : FinitePresentationNeighborhoodModel.restrictionMorphisms f) : IsIso f := by
  have hrev : Y.neighborhood.V ≤ X.neighborhood.V := by
    rw [openNeighborhood_eq_top hs X.neighborhood, openNeighborhood_eq_top hs Y.neighborhood]
  have hiso : IsIso (S.homOfLE f.base_le) := isIso_homOfLE f.base_le hrev
  have hcomp : S.homOfLE f.base_le ≫ S.homOfLE hrev = 𝟙 _ := by
    rw [Scheme.homOfLE_homOfLE]; exact S.homOfLE_rfl _
  have hleft : IsIso f.left :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) hf.flip hiso
  refine ⟨⟨⟨hrev, inv f.left, ?_⟩, ?_, ?_⟩⟩
  · calc inv f.left ≫ X.hom
        = inv f.left ≫ X.hom ≫ S.homOfLE f.base_le ≫ S.homOfLE hrev := by
          rw [hcomp, Category.comp_id]
      _ = inv f.left ≫ (f.left ≫ Y.hom) ≫ S.homOfLE hrev := by
          refine congrArg (fun k ↦ inv f.left ≫ k) ?_
          rw [← Category.assoc, ← f.w]
      _ = Y.hom ≫ S.homOfLE hrev := by
          simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · refine FinitePresentationNeighborhoodModel.Hom.ext _ _ ?_
    rw [FinitePresentationNeighborhoodModel.comp_left,
      FinitePresentationNeighborhoodModel.id_left]
    exact IsIso.hom_inv_id f.left
  · refine FinitePresentationNeighborhoodModel.Hom.ext _ _ ?_
    rw [FinitePresentationNeighborhoodModel.comp_left,
      FinitePresentationNeighborhoodModel.id_left]
    exact IsIso.inv_hom_id f.left

private lemma neighborhoodModelToGlueingData_invertedBy (hs : IsClosed ({s} : Set S)) :
    (FinitePresentationNeighborhoodModel.restrictionMorphisms
      (S := S) (U := puncturedOpen hs) (s := s)).IsInvertedBy
      (neighborhoodModelToGlueingData S (puncturedOpen hs) s) := fun _ _ f hf =>
  neighborhoodModelToGlueingData_inverts_restriction S (puncturedOpen hs) s f hf

private lemma neighborhoodModelToGlueingData_full (hs : IsClosed ({s} : Set S))
    (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (neighborhoodModelToGlueingData S (puncturedOpen hs) s).Full := by
  refine ⟨?_⟩
  intro M N f
  obtain ⟨P, t, ht, g, heq⟩ := exists_rightFraction_of_map S (puncturedOpen hs) s
    (isRetrocompact_of_quasiCompact_ι _ hqc) M N f
  have : IsIso t := isIso_of_restrictionMorphisms hs t ht
  refine ⟨inv t ≫ g, ?_⟩
  rw [CategoryTheory.Functor.map_comp, heq, CategoryTheory.Functor.map_inv,
    IsIso.inv_hom_id_assoc]

private lemma neighborhoodModelToGlueingData_faithful (hs : IsClosed ({s} : Set S)) :
    (neighborhoodModelToGlueingData S (puncturedOpen hs) s).Faithful := by
  have hmult := FinitePresentationNeighborhoodModel.restrictionMorphisms_multiplicative
    S (puncturedOpen hs) s
  have hF := neighborhoodModelToGlueingData_invertedBy hs
  refine ⟨?_⟩
  intro M N a b hab
  have hrel := restrictionMorphisms_rightFractionRel S (puncturedOpen hs) s hF M N
    (MorphismProperty.RightFraction.mk (𝟙 M) (hmult.id_mem M) a)
    (MorphismProperty.RightFraction.mk (𝟙 M) (hmult.id_mem M) b)
    (by simp [MorphismProperty.RightFraction.map, hab])
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := hrel
  have ht12 : t₁ = t₂ := by simpa using hst
  have : IsIso t₁ := isIso_of_restrictionMorphisms hs t₁ (by simpa using ht)
  refine (cancel_epi t₁).1 ?_
  refine Eq.trans (by simpa using hft) ?_
  rw [ht12]

private lemma neighborhoodModelToGlueingData_isEquivalence (hs : IsClosed ({s} : Set S))
    (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (neighborhoodModelToGlueingData S (puncturedOpen hs) s).IsEquivalence := by
  have := neighborhoodModelToGlueingData_faithful hs
  have := neighborhoodModelToGlueingData_full hs hqc
  have := neighborhoodModelToGlueingData_essSurj S (puncturedOpen hs) s
    (isRetrocompact_of_quasiCompact_ι _ hqc)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Forgetting the neighbourhood of a model.  In the closed-point situation the neighbourhood is
all of `S`, so the composite structure morphism to `S` is again of finite presentation. -/
private noncomputable def modelToAmbientFP (hs : IsClosed ({s} : Set S)) :
    FinitePresentationNeighborhoodModel S (puncturedOpen hs) s ⥤ FinitePresentationOver S :=
  (show ObjectProperty (Over S) from fun X ↦ FinitePresentation X.hom).lift
    (neighborhoodModelToAmbient S (puncturedOpen hs) s) (fun M ↦ by
      have hV : IsIso M.neighborhood.V.ι := by
        rw [openNeighborhood_eq_top hs M.neighborhood]
        exact (Scheme.topIso S).isIso_hom
      have : LocallyOfFinitePresentation M.hom := M.finitePresentation.1
      have : QuasiCompact M.hom := M.finitePresentation.2.1
      have : QuasiSeparated M.hom := M.finitePresentation.2.2
      change FinitePresentation (M.hom ≫ M.neighborhood.V.ι)
      exact ⟨inferInstance, inferInstance, inferInstance⟩)

private lemma modelToAmbientFP_faithful (hs : IsClosed ({s} : Set S)) :
    (modelToAmbientFP hs).Faithful := by
  refine ⟨?_⟩
  intro M N a b hab
  refine FinitePresentationNeighborhoodModel.Hom.ext _ _ ?_
  exact congrArg (fun k ↦ k.hom.left) hab

private lemma modelToAmbientFP_full (hs : IsClosed ({s} : Set S)) :
    (modelToAmbientFP hs).Full := by
  refine ⟨?_⟩
  intro M N g
  have hle : M.neighborhood.V ≤ N.neighborhood.V := by
    rw [openNeighborhood_eq_top hs M.neighborhood, openNeighborhood_eq_top hs N.neighborhood]
  refine ⟨⟨hle, g.hom.left, ?_⟩, ?_⟩
  · apply (cancel_mono N.neighborhood.V.ι).1
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact g.hom.w
  · exact ObjectProperty.hom_ext _ (CategoryTheory.Over.OverMorphism.ext rfl)

private lemma modelToAmbientFP_essSurj (hs : IsClosed ({s} : Set S)) :
    (modelToAmbientFP hs).EssSurj := by
  refine ⟨?_⟩
  intro X
  have : LocallyOfFinitePresentation X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2.1
  have : QuasiSeparated X.obj.hom := X.property.2.2
  have hfp : FinitePresentation (X.obj.hom ≫ S.topIso.inv) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨⟨⟨⊤, le_top, by trivial⟩, X.obj.left, X.obj.hom ≫ S.topIso.inv, hfp⟩, ⟨?_⟩⟩
  refine ObjectProperty.isoMk _ (CategoryTheory.Over.isoMk (Iso.refl _) ?_)
  show 𝟙 X.obj.left ≫ X.obj.hom = (X.obj.hom ≫ S.topIso.inv) ≫ Scheme.Opens.ι ⊤
  rw [Category.id_comp, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]

private lemma modelToAmbientFP_isEquivalence (hs : IsClosed ({s} : Set S)) :
    (modelToAmbientFP hs).IsEquivalence := by
  have := modelToAmbientFP_faithful hs
  have := modelToAmbientFP_full hs
  have := modelToAmbientFP_essSurj hs
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The glueing datum attached to a neighbourhood model agrees with the canonical restriction of
its underlying scheme over `S`. -/
private noncomputable def glueingDataComparison (hs : IsClosed ({s} : Set S)) :
    neighborhoodModelToGlueingData S (puncturedOpen hs) s ≅
      modelToAmbientFP hs ⋙ restrictionFunctorAtPoint S (puncturedOpen hs) s :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (Comma.isoMk
      (ObjectProperty.isoMk _ M.openAmbientIso)
      (ObjectProperty.isoMk _ M.localAmbientIso) (by
        refine ObjectProperty.hom_ext _ ?_
        change (Over.pullback ((S.fromSpecStalk s) ∣_ (puncturedOpen hs))).map
            M.openAmbientIso.hom ≫
            (Over.pullbackSquareObjIso
              (morphismRestrict_ι (S.fromSpecStalk s) (puncturedOpen hs))
              (Over.mk (M.hom ≫ M.neighborhood.V.ι))).hom =
          M.overlapIso.hom.hom ≫
            (Over.pullback (((S.fromSpecStalk s) ⁻¹ᵁ (puncturedOpen hs)).ι)).map
              M.localAmbientIso.hom
        rw [← canonicalOverlapIso_hom_eq]
        exact neighborhoodModel_overlapComparison S (puncturedOpen hs) s M)))
    (by
      intro M N f
      refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)
      · exact ObjectProperty.hom_ext _
          ((neighborhoodModelOpenAmbientIso S (puncturedOpen hs) s).hom.naturality f)
      · exact ObjectProperty.hom_ext _
          ((neighborhoodModelLocalAmbientIso S (puncturedOpen hs) s).hom.naturality f))

/-- **Stacks Project, Tag 0BPA.** Let `s` be a closed point of a scheme `S` whose open
complement `U = S \ {s}` has quasi-compact inclusion.  Restricting a scheme of finite
presentation over `S` to `U` and to `Spec 𝒪_{S, s}`, together with the canonical comparison of
the two induced restrictions to `V = Spec 𝒪_{S, s} ∩ U`, is an equivalence onto the category of
such glueing data. -/
@[stacks 0BPA]
public theorem restrictionFunctorAtPoint_isEquivalence (S : Scheme.{u}) (s : S)
    (hs : IsClosed ({s} : Set S)) (hqc : QuasiCompact (puncturedOpen hs).ι) :
    (restrictionFunctorAtPoint S (puncturedOpen hs) s).IsEquivalence := by
  have hE := modelToAmbientFP_isEquivalence hs
  have hG := neighborhoodModelToGlueingData_isEquivalence hs hqc
  have hER : Functor.IsEquivalence
      (modelToAmbientFP hs ⋙ restrictionFunctorAtPoint S (puncturedOpen hs) s) :=
    Functor.isEquivalence_of_iso (glueingDataComparison hs)
  exact Functor.isEquivalence_of_comp_left (modelToAmbientFP hs)
    (restrictionFunctorAtPoint S (puncturedOpen hs) s)

end ClosedPoint

end AlgebraicGeometry.GlueingNearPoint

