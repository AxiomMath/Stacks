module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesFiniteProperMono
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Gluing flat proper algebraic spaces across an affine thickening pushout (Stacks 0D1J)

Let
```
T  ⟶ T'
↓     ↓
S  ⟶ S'
```
be a pushout of schemes in which `T ⟶ T'` is a thickening and `T ⟶ S` is affine (Stacks 07RT).
Stacks 0D1J asserts that restriction
```
Spaces'_{fp, flat, proper, S'} ⟶
  Spaces'_{fp, flat, proper, S} ×_{Spaces'_{fp, flat, proper, T}} Spaces'_{fp, flat, proper, T'}
```
is an equivalence of fibre categories.

## Main definitions

* `AlgebraicGeometry.Space.fibreBaseChange`: base change between the fibre categories cut out
  of the slices of algebraic spaces by a family of properties, one property for each base
  scheme of the big fppf site.
* `AlgebraicGeometry.Space.fibrePushoutRestriction`: the canonical restriction functor from the
  fibre over the pushout `S'` to the categorical pullback of the fibres over `S` and `T'`.
* `AlgebraicGeometry.Space.FlatLfpOver`: the fibre category of flat algebraic spaces locally of
  finite presentation over a scheme of the big fppf site, the fibre of `Spaces'_{flat, lfp}`.
* `AlgebraicGeometry.Space.FlatLfpPushoutRS`: the statement of Stacks 07W3, that restriction is an
  equivalence for `Spaces'_{flat, lfp}`.

## Main results

* `AlgebraicGeometry.Space.properPushoutRS_of_flatLfpPushoutRS`: Stacks 0D1J, assuming the
  statement `h07W3` of Stacks 07W3.
* `AlgebraicGeometry.Space.fibreRestriction_isEquivalence_of_le`: if restriction is an
  equivalence for a family of properties `R`, and a smaller family `R'` is preserved by base
  change and reflected by the restriction to `S`, then restriction is an equivalence for `R'`.
* `AlgebraicGeometry.Space.isProper_iff_of_basechange_isThickeningHom`: for a morphism locally of
  finite presentation, properness over the target is equivalent to properness of its base change
  along a thickening of the target.

## References

* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ u

namespace AlgebraicGeometry.Space

/-! ### Two outer rectangles of a pushout square -/

section Square

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
variable {T T' S S' : C} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')

/-- Pulling an object over `S'` back to `S` and then to `T` computes the pullback along
`f ≫ h`. -/
theorem isPullback_pullbackSndPullbackSnd_left (Z : Over S') :
    IsPullback (pullback.fst (pullback.snd Z.hom h) f ≫ pullback.fst Z.hom h)
      (pullback.snd (pullback.snd Z.hom h) f) Z.hom (f ≫ h) :=
  (IsPullback.of_hasPullback (pullback.snd Z.hom h) f).paste_horiz
    (IsPullback.of_hasPullback Z.hom h)

/-- Pulling an object over `S'` back to `T'` and then to `T` computes the pullback along
`f ≫ h`, once the square commutes. -/
theorem isPullback_pullbackSndPullbackSnd_right (hc : f ≫ h = i ≫ g) (Z : Over S') :
    IsPullback (pullback.fst (pullback.snd Z.hom g) i ≫ pullback.fst Z.hom g)
      (pullback.snd (pullback.snd Z.hom g) i) Z.hom (f ≫ h) := by
  rw [hc]
  exact (IsPullback.of_hasPullback (pullback.snd Z.hom g) i).paste_horiz
    (IsPullback.of_hasPullback Z.hom g)

variable (hc : f ≫ h = i ≫ g)

/-- The two routes from the slice over `S'` to the slice over `T` agree on an object. -/
def sliceOverlapIso (Z : Over S') :
    (Over.pullback h ⋙ Over.pullback f).obj Z ≅ (Over.pullback g ⋙ Over.pullback i).obj Z :=
  Over.isoMk ((isPullback_pullbackSndPullbackSnd_left f h Z).isoIsPullback _ _
      (isPullback_pullbackSndPullbackSnd_right i f g h hc Z))
    ((isPullback_pullbackSndPullbackSnd_left f h Z).isoIsPullback_hom_snd _ _
      (isPullback_pullbackSndPullbackSnd_right i f g h hc Z))

/-- `AlgebraicGeometry.Space.sliceOverlapIso` is compatible with the two comparison maps down to
the original object over `S'`. -/
theorem sliceOverlapIso_hom_left_comp_fst (Z : Over S') :
    ((sliceOverlapIso i f g h hc Z).hom).left ≫
      (pullback.fst (pullback.snd Z.hom g) i ≫ pullback.fst Z.hom g) =
    pullback.fst (pullback.snd Z.hom h) f ≫ pullback.fst Z.hom h :=
  (isPullback_pullbackSndPullbackSnd_left f h Z).isoIsPullback_hom_fst _ _
    (isPullback_pullbackSndPullbackSnd_right i f g h hc Z)

/-- `AlgebraicGeometry.Space.sliceOverlapIso` is a morphism over `T`. -/
theorem sliceOverlapIso_hom_left_comp_snd (Z : Over S') :
    ((sliceOverlapIso i f g h hc Z).hom).left ≫ pullback.snd (pullback.snd Z.hom g) i =
    pullback.snd (pullback.snd Z.hom h) f :=
  (isPullback_pullbackSndPullbackSnd_left f h Z).isoIsPullback_hom_snd _ _
    (isPullback_pullbackSndPullbackSnd_right i f g h hc Z)

/-- The two routes from the slice over `S'` to the slice over `T` agree naturally. -/
def sliceOverlapNatIso :
    Over.pullback h ⋙ Over.pullback f ≅ Over.pullback g ⋙ Over.pullback i :=
  NatIso.ofComponents (sliceOverlapIso i f g h hc) (by
    intro Z W k
    apply Over.OverMorphism.ext
    apply (isPullback_pullbackSndPullbackSnd_right i f g h hc W).hom_ext
    · simp only [Functor.comp_map, Over.comp_left, Category.assoc,
        sliceOverlapIso_hom_left_comp_fst]
      simp [Over.pullback, pullback.lift_fst_assoc, Category.assoc]
      simpa only [Category.assoc] using
        (congrArg (fun q => q ≫ k.left) (sliceOverlapIso_hom_left_comp_fst i f g h hc Z)).symm
    · simp only [Functor.comp_map, Over.comp_left, Category.assoc,
        sliceOverlapIso_hom_left_comp_snd]
      simp [Over.pullback]
      simp only [pullback.lift_snd, sliceOverlapIso_hom_left_comp_snd])

end Square

/-! ### Fibre categories cut out by a family of properties -/

section Fibres

variable {B : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}

/-- A family of properties of the slices of algebraic spaces over `S₀`, one for each base scheme
of the big fppf site, is *stable* when each of its members is preserved by base change. -/
abbrev FibreStable (R : ∀ U : BigFppfOver B S₀ hS₀, ObjectProperty (Over (schemeSpace U))) :
    Prop :=
  ∀ {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V) (Z : Over (schemeSpace V)),
    R V Z → R U ((Over.pullback (schemeSpaceMap a)).obj Z)

variable (R : ∀ U : BigFppfOver B S₀ hS₀, ObjectProperty (Over (schemeSpace U)))
  (hR : FibreStable R)

/-- Base change along `a : U ⟶ V` between the fibre categories cut out by `R`. -/
def fibreBaseChange {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V) :
    (R V).FullSubcategory ⥤ (R U).FullSubcategory :=
  (R U).lift ((R V).ι ⋙ Over.pullback (schemeSpaceMap a)) fun Z => hR a Z.obj Z.property

/-- The comparison from a base-changed family to the family it came from.

The target fibre is cut out of the slice over `U` by `R U`, so this is the pullback projection
of the slice, read in the fibre. -/
def fibreBaseChangeComparison {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V) :
    fibreBaseChange R hR a ⋙ (R U).ι ⋙ Over.forget (schemeSpace U) ⟶
      (R V).ι ⋙ Over.forget (schemeSpace V) where
  app Z := pullback.fst Z.obj.hom (schemeSpaceMap a)
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- Each component of `AlgebraicGeometry.Space.fibreBaseChangeComparison` is cartesian. -/
theorem fibreBaseChange_isPullback {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V)
    (Z : (R V).FullSubcategory) :
    IsPullback ((fibreBaseChangeComparison R hR a).app Z)
      ((fibreBaseChange R hR a).obj Z).obj.hom Z.obj.hom (schemeSpaceMap a) :=
  IsPullback.of_hasPullback _ _

variable {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
  (hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g)

/-- The two routes from the fibre over `S'` to the fibre over `T` agree. -/
def fibreOverlapComparison :
    fibreBaseChange R hR h ⋙ fibreBaseChange R hR f ≅
      fibreBaseChange R hR g ⋙ fibreBaseChange R hR i :=
  NatIso.ofComponents
    (fun Z =>
      { hom := (R T).homMk ((sliceOverlapNatIso (schemeSpaceMap i) (schemeSpaceMap f)
          (schemeSpaceMap g) (schemeSpaceMap h) hc).hom.app Z.obj)
        inv := (R T).homMk ((sliceOverlapNatIso (schemeSpaceMap i) (schemeSpaceMap f)
          (schemeSpaceMap g) (schemeSpaceMap h) hc).inv.app Z.obj)
        hom_inv_id := (R T).ι.map_injective <|
          (sliceOverlapNatIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
            (schemeSpaceMap h) hc).hom_inv_id_app Z.obj
        inv_hom_id := (R T).ι.map_injective <|
          (sliceOverlapNatIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
            (schemeSpaceMap h) hc).inv_hom_id_app Z.obj })
    (fun k => (R T).ι.map_injective <|
      (sliceOverlapNatIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
        (schemeSpaceMap h) hc).hom.naturality ((R S').ι.map k))

/-- The canonical restriction functor from the fibre over the pushout `S'` to compatible pairs
over `S` and `T'`. -/
def fibrePushoutRestriction :
    (R S').FullSubcategory ⥤
      CategoricalPullback (fibreBaseChange R hR f) (fibreBaseChange R hR i) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (fibreBaseChange R hR f) (fibreBaseChange R hR i) (R S').FullSubcategory).obj
      { fst := fibreBaseChange R hR h
        snd := fibreBaseChange R hR g
        iso := fibreOverlapComparison R hR i f g h hc }

/-- The first projection of `AlgebraicGeometry.Space.fibrePushoutRestriction` is restriction to
`S`. -/
def fibreRestrictionFst :
    fibrePushoutRestriction R hR i f g h hc ⋙
        CategoricalPullback.π₁ (fibreBaseChange R hR f) (fibreBaseChange R hR i) ≅
      fibreBaseChange R hR h :=
  Iso.refl _

/-- The second projection of `AlgebraicGeometry.Space.fibrePushoutRestriction` is restriction to
`T'`. -/
def fibreRestrictionSnd :
    fibrePushoutRestriction R hR i f g h hc ⋙
        CategoricalPullback.π₂ (fibreBaseChange R hR f) (fibreBaseChange R hR i) ≅
      fibreBaseChange R hR g :=
  Iso.refl _

/-- The two projections of `AlgebraicGeometry.Space.fibrePushoutRestriction` are compatible with
the comparison over the overlap. -/
theorem fibreRestriction_overlap (Z : (R S').FullSubcategory) :
    (fibreBaseChange R hR f).map ((fibreRestrictionFst R hR i f g h hc).hom.app Z) ≫
        (fibreOverlapComparison R hR i f g h hc).hom.app Z =
      ((fibrePushoutRestriction R hR i f g h hc).obj Z).iso.hom ≫
        (fibreBaseChange R hR i).map ((fibreRestrictionSnd R hR i f g h hc).hom.app Z) := by
  change (fibreBaseChange R hR f).map (𝟙 _) ≫
      (fibreOverlapComparison R hR i f g h hc).hom.app Z =
    (fibreOverlapComparison R hR i f g h hc).hom.app Z ≫ (fibreBaseChange R hR i).map (𝟙 _)
  simp

end Fibres

/-! ### Transferring the equivalence to a smaller family of properties -/

section Transfer

variable {B : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}
variable (R R' : ∀ U : BigFppfOver B S₀ hS₀, ObjectProperty (Over (schemeSpace U)))
  (hR : FibreStable R) (hR' : FibreStable R')
variable {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
  (hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g)

/-- The inclusion of the fibre cut out by the smaller family into the fibre cut out by the
larger one. -/
def fibreInclusionOfLe
    (hle : ∀ (U : BigFppfOver B S₀ hS₀) (Z : Over (schemeSpace U)), R' U Z → R U Z)
    (U : BigFppfOver B S₀ hS₀) :
    (R' U).FullSubcategory ⥤ (R U).FullSubcategory :=
  (R U).lift (R' U).ι fun Z => hle U Z.obj Z.property

/-- Restriction for the smaller family is faithful as soon as restriction for the larger one
is. -/
theorem fibreRestriction_faithful_of_le
    (hle : ∀ (U : BigFppfOver B S₀ hS₀) (Z : Over (schemeSpace U)), R' U Z → R U Z)
    [(fibrePushoutRestriction R hR i f g h hc).Faithful] :
    (fibrePushoutRestriction R' hR' i f g h hc).Faithful := by
  constructor
  intro Z W m m' hmm
  apply (R' S').ι.map_injective
  have key : (fibrePushoutRestriction R hR i f g h hc).map
        ((fibreInclusionOfLe R R' hle S').map m) =
      (fibrePushoutRestriction R hR i f g h hc).map ((fibreInclusionOfLe R R' hle S').map m') := by
    apply CategoricalPullback.hom_ext
    · exact (R S).ι.map_injective
        (congrArg (R' S).ι.map (congrArg CategoricalPullback.Hom.fst hmm))
    · exact (R T').ι.map_injective
        (congrArg (R' T').ι.map (congrArg CategoricalPullback.Hom.snd hmm))
  exact congrArg (R S').ι.map ((fibrePushoutRestriction R hR i f g h hc).map_injective key)

/-- Restriction for the smaller family is full as soon as restriction for the larger one is. -/
theorem fibreRestriction_full_of_le
    (hle : ∀ (U : BigFppfOver B S₀ hS₀) (Z : Over (schemeSpace U)), R' U Z → R U Z)
    [(fibrePushoutRestriction R hR i f g h hc).Full] :
    (fibrePushoutRestriction R' hR' i f g h hc).Full := by
  constructor
  intro Z W k
  obtain ⟨m, hm⟩ := (fibrePushoutRestriction R hR i f g h hc).map_surjective
    (show (fibrePushoutRestriction R hR i f g h hc).obj ((fibreInclusionOfLe R R' hle S').obj Z) ⟶
        (fibrePushoutRestriction R hR i f g h hc).obj ((fibreInclusionOfLe R R' hle S').obj W) from
      { fst := (R S).homMk ((R' S).ι.map k.fst)
        snd := (R T').homMk ((R' T').ι.map k.snd)
        w := (R T).ι.map_injective (congrArg (R' T).ι.map k.w) })
  refine ⟨(R' S').homMk ((R S').ι.map m), ?_⟩
  apply CategoricalPullback.hom_ext
  · exact (R' S).ι.map_injective
      (congrArg (R S).ι.map (congrArg CategoricalPullback.Hom.fst hm))
  · exact (R' T').ι.map_injective
      (congrArg (R T').ι.map (congrArg CategoricalPullback.Hom.snd hm))

/-- Restriction for the smaller family is essentially surjective as soon as restriction for the
larger one is, provided the smaller family is closed under isomorphisms and is reflected by the
restriction to `S`. -/
theorem fibreRestriction_essSurj_of_le
    (hle : ∀ (U : BigFppfOver B S₀ hS₀) (Z : Over (schemeSpace U)), R' U Z → R U Z)
    (hiso : ∀ (U : BigFppfOver B S₀ hS₀) {Z W : Over (schemeSpace U)}, (Z ≅ W) →
      R' U Z → R' U W)
    (hreflect : ∀ Z : Over (schemeSpace S'), R S' Z →
      (R' S' Z ↔ R' S ((Over.pullback (schemeSpaceMap h)).obj Z)))
    [(fibrePushoutRestriction R hR i f g h hc).EssSurj] :
    (fibrePushoutRestriction R' hR' i f g h hc).EssSurj := by
  constructor
  intro X
  let X' : CategoricalPullback (fibreBaseChange R hR f) (fibreBaseChange R hR i) :=
    { fst := (fibreInclusionOfLe R R' hle S).obj X.fst
      snd := (fibreInclusionOfLe R R' hle T').obj X.snd
      iso := (R T).isoMk ((R' T).ι.mapIso X.iso) }
  let Z := (fibrePushoutRestriction R hR i f g h hc).objPreimage X'
  let e : (fibrePushoutRestriction R hR i f g h hc).obj Z ≅ X' :=
    (fibrePushoutRestriction R hR i f g h hc).objObjPreimageIso X'
  let eS := (CategoricalPullback.π₁ (fibreBaseChange R hR f)
    (fibreBaseChange R hR i)).mapIso e
  let eT := (CategoricalPullback.π₂ (fibreBaseChange R hR f)
    (fibreBaseChange R hR i)).mapIso e
  exact ⟨⟨Z.obj, (hreflect Z.obj Z.property).mpr
      (hiso S ((R S).ι.mapIso eS).symm X.fst.property)⟩,
    ⟨CategoricalPullback.mkIso ((R' S).isoMk ((R S).ι.mapIso eS))
      ((R' T').isoMk ((R T').ι.mapIso eT))
      ((R' T).ι.map_injective (congrArg (R T).ι.map e.hom.w))⟩⟩

/-- If restriction is an equivalence for the family `R`, and a smaller family `R'` is stable
under base change, closed under isomorphisms and reflected by the restriction to `S`, then
restriction is an equivalence for `R'` too. -/
theorem fibreRestriction_isEquivalence_of_le
    (hle : ∀ (U : BigFppfOver B S₀ hS₀) (Z : Over (schemeSpace U)), R' U Z → R U Z)
    (hiso : ∀ (U : BigFppfOver B S₀ hS₀) {Z W : Over (schemeSpace U)}, (Z ≅ W) →
      R' U Z → R' U W)
    (hreflect : ∀ Z : Over (schemeSpace S'), R S' Z →
      (R' S' Z ↔ R' S ((Over.pullback (schemeSpaceMap h)).obj Z)))
    (hequiv : (fibrePushoutRestriction R hR i f g h hc).IsEquivalence) :
    (fibrePushoutRestriction R' hR' i f g h hc).IsEquivalence := by
  let := hequiv
  have := fibreRestriction_faithful_of_le R R' hR hR' i f g h hc hle
  have := fibreRestriction_full_of_le R R' hR hR' i f g h hc hle
  have := fibreRestriction_essSurj_of_le R R' hR hR' i f g h hc hle hiso hreflect
  exact { }

end Transfer

/-! ### Properness across a thickening -/

section Properness

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Properness is invariant under pullback along a thickening subspace of the target, for a map
locally of finite type on both sides. -/
theorem isProper_iff_of_preimage_isThickening
    {Y' X' : AlgebraicSpaces B S hS} (Y : Subfunctor Y'.1) (q : X' ⟶ Y')
    (hY : IsThickening B S hS Y' Y)
    (hleft : IsLocallyOfFiniteType B S hS (Y.fromPreimage q.hom))
    (hright : IsLocallyOfFiniteType B S hS q.hom) :
    IsProper B S hS (Y.fromPreimage q.hom) ↔ IsProper B S hS q.hom :=
  CartesianLocallyFiniteTypeMorphismOfThickenings.isProper_iff
    { X' := X'
      Y' := Y'
      X := Y.preimage q.hom
      Y := Y
      sourceThickening := isThickening_preimage B S hS Y q hY
      targetThickening := hY
      morphism := thickeningBaseChangeHom B S hS Y q
      locallyOfFiniteType_left := hleft
      locallyOfFiniteType_right := hright
      cartesian := Subfunctor.isPullback_preimage q.hom Y }

variable {B S hS}

/-- The morphism property of being proper, for morphisms of algebraic spaces. -/
private abbrev properMorphisms : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ b => IsProper B S hS b.hom

private instance : (properMorphisms (B := B) (S := S) (hS := hS)).RespectsIso :=
  have : (properMorphisms (B := B) (S := S) (hS := hS)).IsStableUnderBaseChange :=
    isProper_isStableUnderBaseChange B S hS
  inferInstance

/-- Properness of a morphism is unchanged by postcomposing with an isomorphism. -/
private theorem isProper_comp_iff {X Y Z : AlgebraicSpaces B S hS} (q : X ⟶ Y) (e : Y ⟶ Z)
    [IsIso e] : IsProper B S hS (q ≫ e).hom ↔ IsProper B S hS q.hom :=
  (properMorphisms (B := B) (S := S) (hS := hS)).cancel_right_of_respectsIso q e

/-- Properness of a morphism is unchanged by precomposing with an isomorphism. -/
private theorem isProper_iso_comp_iff {X Y Z : AlgebraicSpaces B S hS} (e : X ⟶ Y) (q : Y ⟶ Z)
    [IsIso e] : IsProper B S hS (e ≫ q).hom ↔ IsProper B S hS q.hom :=
  (properMorphisms (B := B) (S := S) (hS := hS)).cancel_left_of_respectsIso e q

/-- Properness of a chosen pullback is unchanged when the morphism pulled back along is
precomposed with an isomorphism. -/
private theorem isProper_pullbackSnd_iso_comp_iff {X Y Y₀ Z : AlgebraicSpaces B S hS}
    (q : X ⟶ Z) (r : Y₀ ⟶ Z) (a : Y ≅ Y₀) :
    IsProper B S hS (pullback.snd q (a.hom ≫ r)).hom ↔
      IsProper B S hS (pullback.snd q r).hom := by
  let k : pullback q (a.hom ≫ r) ⟶ pullback q r :=
    pullback.lift (pullback.fst q (a.hom ≫ r)) (pullback.snd q (a.hom ≫ r) ≫ a.hom) (by
      simpa only [Category.assoc] using (pullback.condition (f := q) (g := a.hom ≫ r)))
  have houter : IsPullback (k ≫ pullback.fst q r) (pullback.snd q (a.hom ≫ r)) q
      (a.hom ≫ r) := by
    simpa only [k, pullback.lift_fst] using (IsPullback.of_hasPullback q (a.hom ≫ r))
  have hleft : IsPullback k (pullback.snd q (a.hom ≫ r)) (pullback.snd q r) a.hom :=
    houter.of_right (by simp only [k, pullback.lift_snd]) (IsPullback.of_hasPullback q r)
  have : IsIso k := hleft.isIso_fst_of_isIso
  rw [← isProper_comp_iff (pullback.snd q (a.hom ≫ r)) a.hom, ← hleft.w]
  exact isProper_iso_comp_iff k _

/-- Properness of a chosen pullback is properness of any cartesian square over the same
cospan. -/
private theorem isProper_pullbackSnd_iff_of_isPullback {W X Y Z : AlgebraicSpaces B S hS}
    (q : X ⟶ Z) (r : Y ⟶ Z) (p : W ⟶ X) (s : W ⟶ Y) (H : IsPullback p s q r) :
    IsProper B S hS s.hom ↔ IsProper B S hS (pullback.snd q r).hom := by
  rw [← H.isoPullback_hom_snd, isProper_iso_comp_iff]

/-- For a morphism of algebraic spaces locally of finite presentation, properness is equivalent
to properness of its base change along a thickening of the target. -/
theorem isProper_iff_of_basechange_isThickeningHom {Y Y' X' : AlgebraicSpaces B S hS}
    (a : Y ⟶ Y') (q : X' ⟶ Y') (ha : IsThickeningHom B S hS a)
    (hlfp : IsLocallyOfFinitePresentation B S hS q.hom) :
    IsProper B S hS (pullback.snd q a).hom ↔ IsProper B S hS q.hom := by
  refine ⟨fun hleft => ?_, fun hright =>
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback q a) hright⟩
  let V := Subfunctor.range a.hom
  let Y₀ : AlgebraicSpaces B S hS := ⟨V.toFunctor, ha.2.1.1⟩
  let j : Y₀ ⟶ Y' := ObjectProperty.homMk V.ι
  have : IsIso (Subfunctor.toRange a.hom) := ha.1
  let e : Y ≅ Y₀ :=
    (show ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) from
      fun F => IsAlgebraicSpace B S hS F).isoMk (asIso (Subfunctor.toRange a.hom))
  have hae : a = e.hom ≫ j :=
    (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).map_injective
      (Subfunctor.toRange_ι a.hom).symm
  let X₀ : AlgebraicSpaces B S hS :=
    ⟨(V.preimage q.hom).toFunctor, (isThickening_preimage B S hS V q ha.2).1.1⟩
  let p : X₀ ⟶ X' := ObjectProperty.homMk (V.preimage q.hom).ι
  let s : X₀ ⟶ Y₀ := ObjectProperty.homMk (V.fromPreimage q.hom)
  have hpb : IsPullback p s q j :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (Subfunctor.isPullback_preimage q.hom V).flip
  have hchosen : IsProper B S hS (pullback.snd q (e.hom ≫ j)).hom := by
    refine (isProper_pullbackSnd_iff_of_isPullback q (e.hom ≫ j) (pullback.fst q a)
      (pullback.snd q a) ?_).mp hleft
    simpa only [← hae] using (IsPullback.of_hasPullback q a)
  have hpre : IsProper B S hS s.hom :=
    (isProper_pullbackSnd_iff_of_isPullback q j p s hpb).mpr
      ((isProper_pullbackSnd_iso_comp_iff q j e).mp hchosen)
  exact (isProper_iff_of_preimage_isThickening B S hS V q ha.2 hpre.2.1.1
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp)).mp hpre

/-- A morphism of algebraic spaces which is proper and locally of finite presentation is of
finite presentation. -/
theorem isFinitePresentation_of_isLocallyOfFinitePresentation_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (q : X ⟶ Y)
    (hlfp : IsLocallyOfFinitePresentation B S hS q) (hproper : IsProper B S hS q) :
    IsFinitePresentation B S hS q :=
  ⟨hlfp, hproper.2.1.2,
    isQuasiCompact_of_isClosedImmersion B S hS (pullback.diagonal q) hX
      (isAlgebraicSpace_pullback B S hS q q hX hX hY) hproper.1⟩

end Properness

/-! ### Stacks 0D1J -/

section Main

variable (B : BigFppfSite.{u}) (S₀ : Scheme.{u}) (hS₀ : B.Contains S₀)

/-- The family of properties cutting `AlgebraicGeometry.Space.FpFlatProperOver` out of the
slices of algebraic spaces: being finitely presented, flat and proper over the base. -/
abbrev fpFlatProperProperty (U : BigFppfOver B S₀ hS₀) : ObjectProperty (Over (schemeSpace U)) :=
  fun Z ↦ IsFinitePresentation B S₀ hS₀ Z.hom.hom ∧
    IsFlat B S₀ hS₀ Z.hom.hom ∧ IsProper B S₀ hS₀ Z.hom.hom

/-- The family of properties cutting the fibres of the stack `Spaces'_{flat, lfp}` out of
the slices of algebraic spaces: being flat and locally of finite presentation over the base. -/
abbrev flatLfpProperty (U : BigFppfOver B S₀ hS₀) : ObjectProperty (Over (schemeSpace U)) :=
  fun Z ↦ IsFlat B S₀ hS₀ Z.hom.hom ∧ IsLocallyOfFinitePresentation B S₀ hS₀ Z.hom.hom

/-- The fibre category of flat algebraic spaces locally of finite presentation over a scheme `U`
of the big fppf site: the fibre of the stack `Spaces'_{flat, lfp}` over `U`. -/
abbrev FlatLfpOver (U : BigFppfOver B S₀ hS₀) := (flatLfpProperty B S₀ hS₀ U).FullSubcategory

/-- Being finitely presented, flat and proper is stable under base change: Stacks 03XR, 03MO and
04WP. -/
theorem fpFlatProperProperty_fibreStable : FibreStable (fpFlatProperProperty B S₀ hS₀) := by
  intro U V a Z hZ
  have sq : IsPullback (pullback.fst Z.hom (schemeSpaceMap a))
      (pullback.snd Z.hom (schemeSpaceMap a)) Z.hom (schemeSpaceMap a) :=
    IsPullback.of_hasPullback _ _
  exact ⟨(isFinitePresentation_isStableUnderBaseChange B S₀ hS₀).of_isPullback sq hZ.1,
    (isFlat_isStableUnderBaseChange B S₀ hS₀).of_isPullback sq hZ.2.1,
    (isProper_isStableUnderBaseChange B S₀ hS₀).of_isPullback sq hZ.2.2⟩

/-- Being flat and locally of finite presentation is stable under base change: Stacks 03MO and
03XR. -/
theorem flatLfpProperty_fibreStable : FibreStable (flatLfpProperty B S₀ hS₀) := by
  intro U V a Z hZ
  have sq : IsPullback (pullback.fst Z.hom (schemeSpaceMap a))
      (pullback.snd Z.hom (schemeSpaceMap a)) Z.hom (schemeSpaceMap a) :=
    IsPullback.of_hasPullback _ _
  exact ⟨(isFlat_isStableUnderBaseChange B S₀ hS₀).of_isPullback sq hZ.1,
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S₀ hS₀).of_isPullback sq hZ.2⟩

/-- The statement of Stacks 07W3: for a pushout of schemes along an affine
morphism and a thickening, restriction is an equivalence from the fibre of
`Spaces'_{flat, lfp}` over the pushout to the compatible pairs over the two pieces. -/
abbrev FlatLfpPushoutRS :=
  ∀ {T T' S S' : BigFppfOver B S₀ hS₀} (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S'),
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map i) →
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S₀ hS₀).map f) →
    IsPushout ((BigFppfOver.toScheme B S₀ hS₀).map i) ((BigFppfOver.toScheme B S₀ hS₀).map f)
      ((BigFppfOver.toScheme B S₀ hS₀).map g) ((BigFppfOver.toScheme B S₀ hS₀).map h) →
    ∀ hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g,
      (fibrePushoutRestriction (flatLfpProperty B S₀ hS₀) (flatLfpProperty_fibreStable B S₀ hS₀)
        i f g h hc).IsEquivalence

variable {B S₀ hS₀}

/-- The algebraic space of a thickening of schemes of the big fppf site is a thickening of
algebraic spaces. -/
theorem isThickeningHom_schemeSpaceMap {U V : BigFppfOver B S₀ hS₀} (a : U ⟶ V)
    (ha : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map a)) :
    IsThickeningHom B S₀ hS₀ (schemeSpaceMap a) :=
  (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S₀ hS₀ (schemeSpaceMap a)).mpr
    ⟨(BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S₀ hS₀
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) a).2 ha.1,
      isSurjective_yoneda_map B S₀ hS₀ a ⟨ha.2⟩⟩

/-- Being finitely presented, flat and proper over the base is invariant under isomorphism in
the slice. -/
theorem fpFlatProperProperty_of_iso (U : BigFppfOver B S₀ hS₀)
    {Z W : Over (schemeSpace U)} (eZW : Z ≅ W) (hZ : fpFlatProperProperty B S₀ hS₀ U Z) :
    fpFlatProperProperty B S₀ hS₀ U W := by
  have : IsIso eZW.hom.left := by
    change IsIso ((Over.forget (schemeSpace U)).map eZW.hom)
    infer_instance
  have : IsIso eZW.inv.left := by
    change IsIso ((Over.forget (schemeSpace U)).map eZW.inv)
    infer_instance
  have hcomp : ∀ (P : MorphismProperty (AlgebraicSpaces B S₀ hS₀)) [P.RespectsIso],
      P Z.hom → P W.hom := by
    intro P _ hP
    simpa only [eZW.inv.w] using MorphismProperty.RespectsIso.precomp P eZW.inv.left Z.hom hP
  let P₁ : MorphismProperty (AlgebraicSpaces B S₀ hS₀) :=
    fun _ _ b => IsFinitePresentation B S₀ hS₀ b.hom
  let P₂ : MorphismProperty (AlgebraicSpaces B S₀ hS₀) :=
    fun _ _ b => IsFlat B S₀ hS₀ b.hom
  let P₃ : MorphismProperty (AlgebraicSpaces B S₀ hS₀) :=
    fun _ _ b => IsProper B S₀ hS₀ b.hom
  let : P₁.IsStableUnderBaseChange := isFinitePresentation_isStableUnderBaseChange B S₀ hS₀
  let : P₂.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange B S₀ hS₀
  let : P₃.IsStableUnderBaseChange := isProper_isStableUnderBaseChange B S₀ hS₀
  exact ⟨@hcomp P₁ MorphismProperty.IsStableUnderBaseChange.respectsIso hZ.1,
    @hcomp P₂ MorphismProperty.IsStableUnderBaseChange.respectsIso hZ.2.1,
    @hcomp P₃ MorphismProperty.IsStableUnderBaseChange.respectsIso hZ.2.2⟩

/-- Assume `h07W3`, the statement of Stacks 07W3 for the flat algebraic spaces locally of finite
presentation. For a pushout of schemes in which `T ⟶ T'` is a thickening and `T ⟶ S` is affine,
restriction identifies the finitely presented, flat and proper algebraic spaces over `S'` with
compatible pairs over `S` and `T'`, with the canonical restriction functor as the
equivalence. -/
def properPushoutRS_of_flatLfpPushoutRS (h07W3 : FlatLfpPushoutRS B S₀ hS₀) :
    ProperPushoutRS B S₀ hS₀ := by
  intro T T' S S' i f g h hi hf hsq
  haveI := hf
  have hthick : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S₀ hS₀).map h) :=
    Stacks.Pushout.isThickening_of_isPushout_of_isThickening hsq hi
  have hc : schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap i ≫ schemeSpaceMap g := by
    have hsite : f ≫ h = i ≫ g :=
      (BigFppfOver.toScheme B S₀ hS₀).map_injective
        (by simpa only [Functor.map_comp] using hsq.w.symm)
    calc schemeSpaceMap f ≫ schemeSpaceMap h = schemeSpaceMap (f ≫ h) := by ext; rfl
      _ = schemeSpaceMap (i ≫ g) := by rw [hsite]
      _ = _ := by ext; rfl
  have hah : IsThickeningHom B S₀ hS₀ (schemeSpaceMap h) := isThickeningHom_schemeSpaceMap h hthick
  have hreflect : ∀ Z : Over (schemeSpace S'), flatLfpProperty B S₀ hS₀ S' Z →
      (fpFlatProperProperty B S₀ hS₀ S' Z ↔
        fpFlatProperProperty B S₀ hS₀ S
          ((Over.pullback (schemeSpaceMap h)).obj Z)) := by
    intro Z hZ
    refine ⟨fun hfp => fpFlatProperProperty_fibreStable B S₀ hS₀ h Z hfp, fun hfp => ?_⟩
    have hproper : IsProper B S₀ hS₀ Z.hom.hom :=
      (isProper_iff_of_basechange_isThickeningHom (schemeSpaceMap h) Z.hom hah hZ.2).mp hfp.2.2
    exact ⟨isFinitePresentation_of_isLocallyOfFinitePresentation_of_isProper
        Z.left.property (schemeSpace S').property Z.hom.hom hZ.2 hproper,
      hZ.1, hproper⟩
  have hequiv := fibreRestriction_isEquivalence_of_le (flatLfpProperty B S₀ hS₀)
    (fpFlatProperProperty B S₀ hS₀) (flatLfpProperty_fibreStable B S₀ hS₀)
    (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc
    (fun U Z hZ => ⟨hZ.2.1, hZ.1.1⟩) fpFlatProperProperty_of_iso hreflect
    (h07W3 i f g h hi hf hsq hc)
  exact
    { toOverlapFromS :=
        { functor := fibreBaseChange (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) f
          comparison := fibreBaseChangeComparison (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) f
          cartesian := fibreBaseChange_isPullback (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) f }
      toOverlapFromT' :=
        { functor := fibreBaseChange (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) i
          comparison := fibreBaseChangeComparison (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) i
          cartesian := fibreBaseChange_isPullback (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) i }
      fromPushoutToS :=
        { functor := fibreBaseChange (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) h
          comparison := fibreBaseChangeComparison (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) h
          cartesian := fibreBaseChange_isPullback (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) h }
      fromPushoutToT' :=
        { functor := fibreBaseChange (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) g
          comparison := fibreBaseChangeComparison (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) g
          cartesian := fibreBaseChange_isPullback (fpFlatProperProperty B S₀ hS₀)
            (fpFlatProperProperty_fibreStable B S₀ hS₀) g }
      overlapComparison := fibreOverlapComparison (fpFlatProperProperty B S₀ hS₀)
        (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc
      overlapComparison_canonical := by
        intro Z
        change ((sliceOverlapIso (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap g)
            (schemeSpaceMap h) hc Z.obj).hom).left ≫
          (pullback.fst (pullback.snd Z.obj.hom (schemeSpaceMap g)) (schemeSpaceMap i) ≫
            pullback.fst Z.obj.hom (schemeSpaceMap g)) =
          pullback.fst (pullback.snd Z.obj.hom (schemeSpaceMap h)) (schemeSpaceMap f) ≫
            pullback.fst Z.obj.hom (schemeSpaceMap h)
        exact sliceOverlapIso_hom_left_comp_fst (schemeSpaceMap i) (schemeSpaceMap f)
          (schemeSpaceMap g) (schemeSpaceMap h) hc Z.obj
      restrictionFunctor := fibrePushoutRestriction (fpFlatProperProperty B S₀ hS₀)
        (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc
      equivalence := hequiv
      restriction_toS := fibreRestrictionFst (fpFlatProperProperty B S₀ hS₀)
        (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc
      restriction_toT' := fibreRestrictionSnd (fpFlatProperProperty B S₀ hS₀)
        (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc
      restriction_overlap := fibreRestriction_overlap (fpFlatProperProperty B S₀ hS₀)
        (fpFlatProperProperty_fibreStable B S₀ hS₀) i f g h hc }

end Main

end AlgebraicGeometry.Space

end
