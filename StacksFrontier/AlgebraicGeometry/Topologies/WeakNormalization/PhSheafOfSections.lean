module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationInitial.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSheafCriterion

/-!
# Global functions on absolute weak normalizations form a ph sheaf

On a big ph site over a scheme `S`, the rule sending an object `X` to the ring of global
functions on its absolute weak normalization is a sheaf.

## Main definitions

* `AlgebraicGeometry.absoluteWeakNormalizationMap` is the unique lift of a morphism of schemes
  to the absolute weak normalizations, and
  `AlgebraicGeometry.absoluteWeakNormalizationFunctor` the functor it assembles into.
* `AlgebraicGeometry.absoluteWeakNormalizationSections` is the presheaf of rings of global
  functions on the absolute weak normalizations.

## Main results

* `AlgebraicGeometry.isReduced_absoluteWeakNormalization`: the absolute weak normalization of a
  scheme is reduced.
* `AlgebraicGeometry.isSheafFor_absoluteWeakNormalizationSections_of_zariskiCover` and
  `AlgebraicGeometry.isSheafFor_absoluteWeakNormalizationSections_of_properSurjective`: the two
  descent conditions of Stacks Tag 0DBQ.
* `AlgebraicGeometry.isSheaf_absoluteWeakNormalizationSections`: the sheaf property for the ph
  topology.

## Implementation notes

The lifts are functorial because they are unique, so the functor is built directly from
`AlgebraicGeometry.existsUnique_absoluteWeakNormalization_lift`.

Zariski descent uses that absolute weak normalization commutes with restriction to an open
subscheme: over an open immersion the initial universal homeomorphism is the base change of the
one over the ambient scheme, so the lift is itself an open immersion with the expected image,
and the covering of the ambient absolute weak normalization by those of the members of a
Zariski covering is again a Zariski covering. Sections are then glued by presenting a section
as a morphism to the affine line and using that the Zariski topology is subcanonical.

For descent along a proper surjection `f : Y ⟶ X` with affine target, a compatible section of
`Yᵃʷⁿ` is a morphism `e : Yᵃʷⁿ ⟶ 𝔸¹_X`; its scheme-theoretic image is finite and surjective over
`X`, and its diagonal is surjective because the two pullback projections already agree, so the
image is a universal homeomorphism over `X` and the absolute weak normalization of `X` maps to
it. Uniqueness is separatedness of the affine line together with dominance of the map on absolute
weak normalizations, for which the reducedness of `Xᵃʷⁿ` is needed.

Reducedness of `Xᵃʷⁿ` is obtained from initiality: the reduction of `Xᵃʷⁿ` is again a universal
homeomorphism over `X`, so initiality splits the closed immersion of the reduction, and a split
epimorphism which is a monomorphism is an isomorphism.

The initial universal homeomorphism over an arbitrary scheme exists by the instance
`AlgebraicGeometry.hasInitialUniversalHomeomorphismOver` (Stacks Tag 0EUS).

## References

* [Stacks Project, Tag 0EVT](https://stacks.math.columbia.edu/tag/0EVT)
* [Stacks Project, Tag 0DBQ](https://stacks.math.columbia.edu/tag/0DBQ)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Scheme-theoretic images over the affine line -/

/-- The scheme-theoretic image of a morphism to the affine line over `Y` is finite over `Y`
when the composition to `Y` is universally closed. -/
theorem isFinite_imageι_comp_of_universallyClosed {X Y : Scheme.{u}}
    (f : X ⟶ AffineSpace.{u} (ULift.{u} (Fin 1)) Y)
    [UniversallyClosed (f ≫ (AffineSpace.{u} (ULift.{u} (Fin 1)) Y ↘ Y))] :
    IsFinite (f.imageι ≫ (AffineSpace.{u} (ULift.{u} (Fin 1)) Y ↘ Y)) :=
  IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨isProper_imageι_comp f (AffineSpace.{u} (ULift.{u} (Fin 1)) Y ↘ Y), inferInstance⟩

/-- A morphism whose composition with a separated morphism is universally closed and
surjective has surjective scheme-theoretic image over the target. -/
theorem surjective_imageι_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective (f ≫ g)] [UniversallyClosed (f ≫ g)] [IsSeparated g] :
    Surjective (f.imageι ≫ g) := by
  have _ : Surjective f.toImage := surjective_toImage f g
  refine ⟨fun z => ?_⟩
  obtain ⟨x, hx⟩ := (f ≫ g).surjective z
  refine ⟨f.toImage x, ?_⟩
  calc
    (f.imageι ≫ g) (f.toImage x) = (f.toImage ≫ f.imageι ≫ g) x := rfl
    _ = (f ≫ g) x := by rw [Scheme.Hom.toImage_imageι_assoc]
    _ = z := hx

/-! ### The absolute weak normalization functor -/

/-- The unique lift of a morphism of schemes to the absolute weak normalizations. -/
def absoluteWeakNormalizationMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.absoluteWeakNormalization ⟶ Y.absoluteWeakNormalization :=
  Classical.choose (existsUnique_absoluteWeakNormalization_lift f).exists

/-- The lift of a morphism to the absolute weak normalizations commutes with the two structure
morphisms. -/
theorem absoluteWeakNormalizationMap_spec {X Y : Scheme.{u}} (f : X ⟶ Y) :
    absoluteWeakNormalizationMap f ≫ Y.absoluteWeakNormalizationHom =
      X.absoluteWeakNormalizationHom ≫ f :=
  Classical.choose_spec (existsUnique_absoluteWeakNormalization_lift f).exists

/-- Absolute weak normalization, functorially in the scheme. -/
def absoluteWeakNormalizationFunctor : Scheme.{u} ⥤ Scheme.{u} where
  obj X := X.absoluteWeakNormalization
  map f := absoluteWeakNormalizationMap f
  map_id X := by
    apply (existsUnique_absoluteWeakNormalization_lift (𝟙 X)).unique
    · exact absoluteWeakNormalizationMap_spec (𝟙 X)
    · simp
  map_comp f g := by
    apply (existsUnique_absoluteWeakNormalization_lift (f ≫ g)).unique
    · exact absoluteWeakNormalizationMap_spec (f ≫ g)
    · rw [Category.assoc, absoluteWeakNormalizationMap_spec g, ← Category.assoc,
        absoluteWeakNormalizationMap_spec f, Category.assoc]

/-- The lifts to absolute weak normalizations are compatible with composition. -/
theorem absoluteWeakNormalizationMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    absoluteWeakNormalizationMap f ≫ absoluteWeakNormalizationMap g =
      absoluteWeakNormalizationMap (f ≫ g) :=
  (absoluteWeakNormalizationFunctor.map_comp f g).symm

/-- The structure morphism of the absolute weak normalization is a universal homeomorphism. -/
theorem universalHomeomorphism_absoluteWeakNormalizationHom (X : Scheme.{u}) :
    UniversalHomeomorphism X.absoluteWeakNormalizationHom :=
  (initial (UniversalHomeomorphismOver X)).property

/-- The presheaf of rings assigning to an object of a big ph site the global functions on its
absolute weak normalization. -/
abbrev absoluteWeakNormalizationSections (B : BigPHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (BigPHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (BigPHOver.toScheme B S hS ⋙ absoluteWeakNormalizationFunctor).op ⋙ Scheme.Γ

/-! ### Reducedness of the absolute weak normalization -/

/-- The absolute weak normalization of a scheme is reduced. -/
theorem isReduced_absoluteWeakNormalization (X : Scheme.{u}) :
    IsReduced X.absoluteWeakNormalization := by
  let Y := X.absoluteWeakNormalization
  let π := X.absoluteWeakNormalizationHom
  let ι := Y.nilradical.subschemeι
  have hπ : UniversalHomeomorphism π := universalHomeomorphism_absoluteWeakNormalizationHom X
  have hcomp : UniversalHomeomorphism (ι ≫ π) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem ι π
      (universalHomeomorphism_nilradical_subschemeι Y) hπ
  let Z : UniversalHomeomorphismOver X := ⟨Over.mk (ι ≫ π), hcomp⟩
  let m : initial (UniversalHomeomorphismOver X) ⟶ Z := initial.to Z
  have hw : m.hom.left ≫ (ι ≫ π) = π := m.hom.w
  let n : initial (UniversalHomeomorphismOver X) ⟶ initial (UniversalHomeomorphismOver X) :=
    ObjectProperty.homMk (Over.homMk (m.hom.left ≫ ι) (by
      change (m.hom.left ≫ ι) ≫ π = π
      rw [Category.assoc]
      exact hw))
  have hsplit : m.hom.left ≫ ι = 𝟙 Y :=
    congrArg (fun k : initial (UniversalHomeomorphismOver X) ⟶
      initial (UniversalHomeomorphismOver X) => k.hom.left) (initial.hom_ext n (𝟙 _))
  have _ : IsSplitEpi ι := ⟨⟨m.hom.left, hsplit⟩⟩
  have _ : IsIso ι := isIso_of_mono_of_isSplitEpi ι
  have _ : IsReduced Y.nilradical.subscheme := isReduced_nilradical_subscheme Y
  exact isReduced_of_isOpenImmersion (inv ι)

/-! ### Absolute weak normalization over an open subscheme -/

/-- Over an open subscheme the absolute weak normalization is the base change of the absolute
weak normalization of the ambient scheme. -/
def absoluteWeakNormalizationOpenIso {X U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] :
    U.absoluteWeakNormalization ≅ pullback i X.absoluteWeakNormalizationHom :=
  (Over.forget U).mapIso ((ObjectProperty.ι _).mapIso
    (CategoryTheory.Limits.initialIsInitial.uniqueUpToIso (isInitial_pullback_initial i)))

/-- The isomorphism `absoluteWeakNormalizationOpenIso` lies over the open subscheme. -/
theorem absoluteWeakNormalizationOpenIso_fst {X U : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] :
    (absoluteWeakNormalizationOpenIso i).hom ≫ pullback.fst i X.absoluteWeakNormalizationHom =
      U.absoluteWeakNormalizationHom :=
  (CategoryTheory.Limits.initialIsInitial.uniqueUpToIso
    (isInitial_pullback_initial i)).hom.hom.w

/-- The lift of an open immersion is the base change of the structure morphism of the ambient
absolute weak normalization, composed with `absoluteWeakNormalizationOpenIso`. -/
theorem absoluteWeakNormalizationMap_open {X U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] :
    absoluteWeakNormalizationMap i = (absoluteWeakNormalizationOpenIso i).hom ≫
      pullback.snd i X.absoluteWeakNormalizationHom := by
  refine (existsUnique_absoluteWeakNormalization_lift i).unique
    (absoluteWeakNormalizationMap_spec i) ?_
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    absoluteWeakNormalizationOpenIso_fst]

/-- The lift of an open immersion to the absolute weak normalizations is an open immersion. -/
theorem isOpenImmersion_absoluteWeakNormalizationMap {X U : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] : IsOpenImmersion (absoluteWeakNormalizationMap i) := by
  rw [absoluteWeakNormalizationMap_open]
  infer_instance

/-- The canonical morphism from the absolute weak normalization of `X` to any universal
homeomorphism over `X`. -/
def absoluteWeakNormalizationLift {X Z : Scheme.{u}} (q : Z ⟶ X)
    (hq : UniversalHomeomorphism q) : X.absoluteWeakNormalization ⟶ Z :=
  (CategoryTheory.Limits.initial.to
    (⟨Over.mk q, hq⟩ : UniversalHomeomorphismOver X)).hom.left

/-- The morphism `absoluteWeakNormalizationLift q hq` lies over `X`. -/
theorem absoluteWeakNormalizationLift_spec {X Z : Scheme.{u}} (q : Z ⟶ X)
    (hq : UniversalHomeomorphism q) :
    absoluteWeakNormalizationLift q hq ≫ q = X.absoluteWeakNormalizationHom :=
  (CategoryTheory.Limits.initial.to
    (⟨Over.mk q, hq⟩ : UniversalHomeomorphismOver X)).hom.w

/-- A morphism `g` from `Yᵃʷⁿ` to a universal homeomorphism `q : Z ⟶ X`, lying over
`f : Y ⟶ X`, is the composition of the lift of `f` with `absoluteWeakNormalizationLift q hq`. -/
theorem absoluteWeakNormalizationMap_comp_lift {X Y Z : Scheme.{u}} (f : Y ⟶ X) (q : Z ⟶ X)
    (hq : UniversalHomeomorphism q) (g : Y.absoluteWeakNormalization ⟶ Z)
    (hg : g ≫ q = Y.absoluteWeakNormalizationHom ≫ f) :
    absoluteWeakNormalizationMap f ≫ absoluteWeakNormalizationLift q hq = g := by
  let target : UniversalHomeomorphismOver Y :=
    ⟨Over.mk (pullback.fst f q), ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f q |>.flip) hq.universally_isHomeomorph⟩⟩
  let lhs := pullback.lift Y.absoluteWeakNormalizationHom
    (absoluteWeakNormalizationMap f ≫ absoluteWeakNormalizationLift q hq) (by
      rw [Category.assoc, absoluteWeakNormalizationLift_spec, absoluteWeakNormalizationMap_spec])
  let rhs := pullback.lift Y.absoluteWeakNormalizationHom g hg.symm
  let hmaps : initial (UniversalHomeomorphismOver Y) ⟶ target :=
    ObjectProperty.homMk (Over.homMk lhs (by
      change lhs ≫ pullback.fst f q = Y.absoluteWeakNormalizationHom
      rw [pullback.lift_fst]))
  let hmaps' : initial (UniversalHomeomorphismOver Y) ⟶ target :=
    ObjectProperty.homMk (Over.homMk rhs (by
      change rhs ≫ pullback.fst f q = Y.absoluteWeakNormalizationHom
      rw [pullback.lift_fst]))
  have h := congrArg (fun k : initial (UniversalHomeomorphismOver Y) ⟶ target =>
    k.hom.left ≫ pullback.snd f q) (initial.hom_ext hmaps hmaps')
  have hleft : hmaps.hom.left = lhs := by simp [hmaps]
  have hleft' : hmaps'.hom.left = rhs := by simp [hmaps']
  have h' : lhs ≫ pullback.snd f q = rhs ≫ pullback.snd f q := by
    simpa only [hleft, hleft'] using h
  simpa [lhs, rhs, pullback.lift_snd] using h'

/-! ### Topological properties of the structure morphisms -/

/-- The structure morphism of the absolute weak normalization is universally closed. -/
theorem universallyClosed_absoluteWeakNormalizationHom (X : Scheme.{u}) :
    UniversallyClosed X.absoluteWeakNormalizationHom := by
  have _ : IsIntegralHom X.absoluteWeakNormalizationHom :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
      (universalHomeomorphism_absoluteWeakNormalizationHom X) |>.1
  infer_instance

/-- The structure morphism of the absolute weak normalization is surjective. -/
theorem surjective_absoluteWeakNormalizationHom (X : Scheme.{u}) :
    Surjective X.absoluteWeakNormalizationHom :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (universalHomeomorphism_absoluteWeakNormalizationHom X) |>.2.2

/-- For a proper morphism `f : Y ⟶ X`, the composition `Yᵃʷⁿ ⟶ Y ⟶ X` is universally closed. -/
theorem universallyClosed_absoluteWeakNormalizationHom_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsProper f] : UniversallyClosed (Y.absoluteWeakNormalizationHom ≫ f) := by
  have _ : UniversallyClosed Y.absoluteWeakNormalizationHom :=
    universallyClosed_absoluteWeakNormalizationHom Y
  infer_instance

/-- For a surjective morphism `f : Y ⟶ X`, the composition `Yᵃʷⁿ ⟶ Y ⟶ X` is surjective. -/
theorem surjective_absoluteWeakNormalizationHom_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Surjective f] : Surjective (Y.absoluteWeakNormalizationHom ≫ f) := by
  have _ : Surjective Y.absoluteWeakNormalizationHom :=
    surjective_absoluteWeakNormalizationHom Y
  infer_instance

/-- The structure morphism of the absolute weak normalization is a homeomorphism. -/
private theorem isHomeomorph_absoluteWeakNormalizationHom (X : Scheme.{u}) :
    IsHomeomorph X.absoluteWeakNormalizationHom :=
  (universalHomeomorphism_absoluteWeakNormalizationHom X).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd

/-- The lift of a morphism to the absolute weak normalizations commutes with the structure
morphisms pointwise. -/
private theorem absoluteWeakNormalizationHom_map_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    (y : Y.absoluteWeakNormalization) :
    X.absoluteWeakNormalizationHom (absoluteWeakNormalizationMap f y) =
      f (Y.absoluteWeakNormalizationHom y) :=
  congrArg (fun k => k y) (absoluteWeakNormalizationMap_spec f)

/-- The lift of a surjective morphism to the absolute weak normalizations is surjective. -/
theorem surjective_absoluteWeakNormalizationMap {X Y : Scheme.{u}} (f : Y ⟶ X) [Surjective f] :
    Surjective (absoluteWeakNormalizationMap f) := by
  have _ : Surjective (Y.absoluteWeakNormalizationHom ≫ f) :=
    surjective_absoluteWeakNormalizationHom_comp f
  refine ⟨fun x => ?_⟩
  obtain ⟨y, hy⟩ := (Y.absoluteWeakNormalizationHom ≫ f).surjective
    (X.absoluteWeakNormalizationHom x)
  exact ⟨y, (isHomeomorph_absoluteWeakNormalizationHom X).injective
    ((absoluteWeakNormalizationHom_map_apply f y).trans hy)⟩

/-- The lifts of a jointly surjective family of morphisms to the absolute weak normalizations
are jointly surjective. -/
theorem jointlySurjective_absoluteWeakNormalizationMap {X : Scheme.{u}} {I : Type*}
    {Y : I → Scheme.{u}} (f : (i : I) → Y i ⟶ X) (hcover : ∀ x : X, ∃ i y, f i y = x) :
    ∀ x : X.absoluteWeakNormalization, ∃ i : I, ∃ y : (Y i).absoluteWeakNormalization,
      absoluteWeakNormalizationMap (f i) y = x := by
  intro x
  obtain ⟨i, y, hy⟩ := hcover (X.absoluteWeakNormalizationHom x)
  have _ : Surjective (Y i).absoluteWeakNormalizationHom :=
    surjective_absoluteWeakNormalizationHom (Y i)
  obtain ⟨z, hz⟩ := (Y i).absoluteWeakNormalizationHom.surjective y
  exact ⟨i, z, (isHomeomorph_absoluteWeakNormalizationHom X).injective
    ((absoluteWeakNormalizationHom_map_apply (f i) z).trans (by rw [hz, hy]))⟩

/-- The image of the lift of an open immersion `i : U ⟶ X` is the preimage of the image of `i`
under the structure morphism of `Xᵃʷⁿ`. -/
theorem range_absoluteWeakNormalizationMap {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] :
    Set.range (absoluteWeakNormalizationMap i) =
      X.absoluteWeakNormalizationHom ⁻¹' Set.range i := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨U.absoluteWeakNormalizationHom y,
      (absoluteWeakNormalizationHom_map_apply i y).symm.trans (congrArg _ hy)⟩
  · rintro ⟨z, hz⟩
    have _ : Surjective U.absoluteWeakNormalizationHom :=
      surjective_absoluteWeakNormalizationHom U
    obtain ⟨w, hw⟩ := U.absoluteWeakNormalizationHom.surjective z
    exact ⟨w, (isHomeomorph_absoluteWeakNormalizationHom X).injective
      ((absoluteWeakNormalizationHom_map_apply i w).trans ((congrArg i hw).trans hz))⟩

/-- The square of absolute weak normalizations of two open subschemes and their intersection
commutes. -/
theorem absoluteWeakNormalizationMap_pullback_comm {X U V : Scheme.{u}} (i : U ⟶ X)
    (j : V ⟶ X) :
    absoluteWeakNormalizationMap (pullback.fst i j) ≫ absoluteWeakNormalizationMap i =
      absoluteWeakNormalizationMap (pullback.snd i j) ≫ absoluteWeakNormalizationMap j := by
  calc
    absoluteWeakNormalizationMap (pullback.fst i j) ≫ absoluteWeakNormalizationMap i =
        absoluteWeakNormalizationMap (pullback.fst i j ≫ i) :=
      absoluteWeakNormalizationMap_comp _ _
    _ = absoluteWeakNormalizationMap (pullback.snd i j ≫ j) :=
      congrArg absoluteWeakNormalizationMap pullback.condition
    _ = absoluteWeakNormalizationMap (pullback.snd i j) ≫ absoluteWeakNormalizationMap j :=
      (absoluteWeakNormalizationMap_comp _ _).symm

/-- Absolute weak normalization turns the intersection of two open subschemes into the
intersection of their absolute weak normalizations. -/
theorem isIso_absoluteWeakNormalizationMap_pullback_open {X U V : Scheme.{u}} (i : U ⟶ X)
    (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    IsIso (pullback.lift (absoluteWeakNormalizationMap (pullback.fst i j))
      (absoluteWeakNormalizationMap (pullback.snd i j))
      (absoluteWeakNormalizationMap_pullback_comm i j)) := by
  let p₁ := pullback.fst i j
  let p₂ := pullback.snd i j
  let π₁ := absoluteWeakNormalizationMap i
  let π₂ := absoluteWeakNormalizationMap j
  have _ : IsOpenImmersion π₁ := isOpenImmersion_absoluteWeakNormalizationMap i
  have _ : IsOpenImmersion π₂ := isOpenImmersion_absoluteWeakNormalizationMap j
  let q₁ := pullback.fst π₁ π₂
  let t := p₁ ≫ i
  let r := q₁ ≫ π₁
  let e := pullback.lift (absoluteWeakNormalizationMap p₁)
    (absoluteWeakNormalizationMap p₂) (absoluteWeakNormalizationMap_pullback_comm i j)
  have hefst : e ≫ q₁ = absoluteWeakNormalizationMap p₁ := by
    dsimp [e, q₁]
    rw [pullback.lift_fst]
  have hcomp : e ≫ r = absoluteWeakNormalizationMap t := by
    calc
      e ≫ r = (e ≫ q₁) ≫ π₁ := (Category.assoc _ _ _).symm
      _ = absoluteWeakNormalizationMap p₁ ≫ absoluteWeakNormalizationMap i := by rw [hefst]
      _ = absoluteWeakNormalizationMap (p₁ ≫ i) := absoluteWeakNormalizationMap_comp p₁ i
      _ = absoluteWeakNormalizationMap t := rfl
  have hrange : Set.range r = Set.range (absoluteWeakNormalizationMap t) := by
    rw [show r = pullback.fst π₁ π₂ ≫ π₁ from rfl,
      IsOpenImmersion.range_pullback_to_base_of_left,
      range_absoluteWeakNormalizationMap i, range_absoluteWeakNormalizationMap j,
      range_absoluteWeakNormalizationMap, show t = pullback.fst i j ≫ i from rfl,
      IsOpenImmersion.range_pullback_to_base_of_left]
    simp only [Set.preimage_inter]
  have _ : IsOpenImmersion (e ≫ q₁) := by
    rw [hefst]
    exact isOpenImmersion_absoluteWeakNormalizationMap p₁
  have heOpen : IsOpenImmersion e := IsOpenImmersion.of_comp e q₁
  have hrOpen : IsOpenImmersion r := by
    dsimp [r]
    infer_instance
  have heSurj : Function.Surjective e := by
    intro z
    obtain ⟨w, hw⟩ : r z ∈ Set.range (absoluteWeakNormalizationMap t) := by
      rw [← hrange]
      exact ⟨z, rfl⟩
    refine ⟨w, r.isOpenEmbedding.injective ?_⟩
    calc
      r (e w) = (e ≫ r) w := rfl
      _ = absoluteWeakNormalizationMap t w := by rw [hcomp]
      _ = r z := hw
  have heRange : e.opensRange = ⊤ := by
    apply SetLike.coe_injective
    change Set.range e = Set.univ
    exact Set.range_eq_univ.mpr heSurj
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top e heRange

/-- For open subschemes `U` and `V` of `X`, global functions on `Uᵃʷⁿ` and `Vᵃʷⁿ` which agree
on the absolute weak normalization of `U ×_X V` agree on `Uᵃʷⁿ ×_{Xᵃʷⁿ} Vᵃʷⁿ`. -/
theorem absoluteWeakNormalizationMap_pullback_open_appTop {X U V : Scheme.{u}} (i : U ⟶ X)
    (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (s : Γ(U.absoluteWeakNormalization, ⊤)) (t : Γ(V.absoluteWeakNormalization, ⊤))
    (h : (absoluteWeakNormalizationMap (pullback.fst i j)).appTop s =
      (absoluteWeakNormalizationMap (pullback.snd i j)).appTop t) :
    (pullback.fst (absoluteWeakNormalizationMap i)
      (absoluteWeakNormalizationMap j)).appTop s =
    (pullback.snd (absoluteWeakNormalizationMap i)
      (absoluteWeakNormalizationMap j)).appTop t := by
  let p₁ := pullback.fst i j
  let p₂ := pullback.snd i j
  let π₁ := absoluteWeakNormalizationMap i
  let π₂ := absoluteWeakNormalizationMap j
  let e := pullback.lift (absoluteWeakNormalizationMap p₁)
    (absoluteWeakNormalizationMap p₂) (absoluteWeakNormalizationMap_pullback_comm i j)
  have _ : IsIso e := isIso_absoluteWeakNormalizationMap_pullback_open i j
  have _ : IsIso e.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso (asIso e).op).isIso_hom
  have he₁ : (pullback.fst π₁ π₂).appTop ≫ e.appTop =
      (absoluteWeakNormalizationMap p₁).appTop := by
    rw [← Scheme.Hom.comp_appTop]
    congr 1
    exact pullback.lift_fst _ _ _
  have he₂ : (pullback.snd π₁ π₂).appTop ≫ e.appTop =
      (absoluteWeakNormalizationMap p₂).appTop := by
    rw [← Scheme.Hom.comp_appTop]
    congr 1
    exact pullback.lift_snd _ _ _
  refine ((forget CommRingCat).mapIso (asIso e.appTop)).toEquiv.injective ?_
  change ((pullback.fst π₁ π₂).appTop ≫ e.appTop) s = ((pullback.snd π₁ π₂).appTop ≫ e.appTop) t
  rw [he₁, he₂]
  exact h

/-! ### Sections as morphisms to the affine line -/

/-- A global function on the absolute weak normalization of `Y`, read as a morphism to the
affine line over `X` along `Y ⟶ X`. -/
def sectionToAffineLine {X Y : Scheme.{u}} (f : Y ⟶ X)
    (s : Γ(Y.absoluteWeakNormalization, ⊤)) :
    Y.absoluteWeakNormalization ⟶ AffineSpace.{u} (ULift.{u} (Fin 1)) X :=
  AffineSpace.homOfVector (Y.absoluteWeakNormalizationHom ≫ f) fun _ => s

/-- The coordinate function pulls back along `sectionToAffineLine f s` to `s`. -/
theorem sectionToAffineLine_appTop_coord {X Y : Scheme.{u}} (f : Y ⟶ X)
    (s : Γ(Y.absoluteWeakNormalization, ⊤)) (i : ULift.{u} (Fin 1)) :
    (sectionToAffineLine f s).appTop (AffineSpace.coord X i) = s :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Precomposing `sectionToAffineLine f s` with `g` gives the morphism to the affine line
defined by the pullback of `s` along `g`. -/
theorem sectionToAffineLine_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (s : Γ(Y.absoluteWeakNormalization, ⊤)) (g : Z ⟶ Y.absoluteWeakNormalization) :
    g ≫ sectionToAffineLine f s =
      AffineSpace.homOfVector (g ≫ Y.absoluteWeakNormalizationHom ≫ f)
        fun _ => g.appTop s := by
  simpa [sectionToAffineLine, Function.comp_def] using
    AffineSpace.comp_homOfVector (fun _ : ULift.{u} (Fin 1) => s) g
      (Y.absoluteWeakNormalizationHom ≫ f)

/-! ### Zariski descent -/

/-- A family of morphisms out of the absolute weak normalizations of the members of a Zariski
covering, agreeing on overlaps, glues uniquely. -/
theorem existsUnique_zariski_glue_morphism {X : Scheme.{u}} {I : Type*} {Y : I → Scheme.{u}}
    (f : (i : I) → Y i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i))
    (hcover : ∀ x : X, ∃ i y, f i y = x) {Z : Scheme.{u}}
    (g : (i : I) → (Y i).absoluteWeakNormalization ⟶ Z)
    (hcompat : ∀ i j, pullback.fst (absoluteWeakNormalizationMap (f i))
        (absoluteWeakNormalizationMap (f j)) ≫ g i =
      pullback.snd (absoluteWeakNormalizationMap (f i))
        (absoluteWeakNormalizationMap (f j)) ≫ g j) :
    ∃! g₀ : X.absoluteWeakNormalization ⟶ Z, ∀ i, absoluteWeakNormalizationMap (f i) ≫ g₀ = g i
    := by
  let π : (i : I) → (Y i).absoluteWeakNormalization ⟶ X.absoluteWeakNormalization :=
    fun i => absoluteWeakNormalizationMap (f i)
  let P := yoneda.obj Z
  have hcov : Presieve.ofArrows (fun i => (Y i).absoluteWeakNormalization) π ∈
      Scheme.zariskiPrecoverage X.absoluteWeakNormalization := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨jointlySurjective_absoluteWeakNormalizationMap f hcover, fun i => ?_⟩
    have _ : IsOpenImmersion (f i) := hf i
    exact isOpenImmersion_absoluteWeakNormalizationMap (f i)
  have hP : Presieve.IsSheaf Scheme.zariskiTopology P :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P
  have hsf := hP.isSheafFor (Presieve.ofArrows (fun i => (Y i).absoluteWeakNormalization) π)
    (Precoverage.generate_mem_toGrothendieck hcov)
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible] at hsf
  have hcompat' : (i : I) → (j : I) → ∀ {W : Scheme.{u}}
      (a : W ⟶ (Y i).absoluteWeakNormalization) (b : W ⟶ (Y j).absoluteWeakNormalization),
      a ≫ π i = b ≫ π j → a ≫ g i = b ≫ g j := by
    intro i j W a b hab
    let l := pullback.lift a b hab
    calc
      a ≫ g i = l ≫ pullback.fst (π i) (π j) ≫ g i := by
        simp only [← Category.assoc, l, pullback.lift_fst]
      _ = l ≫ pullback.snd (π i) (π j) ≫ g j := by
        simpa only [Category.assoc] using congrArg (fun k => l ≫ k) (hcompat i j)
      _ = b ≫ g j := by simp only [← Category.assoc, l, pullback.lift_snd]
  obtain ⟨g₀, hg₀⟩ := hsf.2 ⟨g, fun i j _ a b hab => hcompat' i j a b hab⟩
  have h₀ (i : I) : π i ≫ g₀ = g i := by
    simpa [P, π] using congrFun (congrArg Subtype.val hg₀) i
  refine ⟨g₀, h₀, fun g₁ hg₁ => hsf.1 ?_⟩
  ext i
  simpa [P, π] using (hg₁ i).trans (h₀ i).symm

/-- A family of global functions on the absolute weak normalizations of the members of a Zariski
covering, agreeing on overlaps, glues uniquely. -/
theorem existsUnique_zariski_glue_section {X : Scheme.{u}} {I : Type*} {Y : I → Scheme.{u}}
    (f : (i : I) → Y i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i))
    (hcover : ∀ x : X, ∃ i y, f i y = x)
    (s : (i : I) → Γ((Y i).absoluteWeakNormalization, ⊤))
    (hcompat : ∀ i j, (pullback.fst (absoluteWeakNormalizationMap (f i))
        (absoluteWeakNormalizationMap (f j))).appTop (s i) =
      (pullback.snd (absoluteWeakNormalizationMap (f i))
        (absoluteWeakNormalizationMap (f j))).appTop (s j)) :
    ∃! s₀ : Γ(X.absoluteWeakNormalization, ⊤),
      ∀ i, (absoluteWeakNormalizationMap (f i)).appTop s₀ = s i := by
  let π : (i : I) → (Y i).absoluteWeakNormalization ⟶ X.absoluteWeakNormalization :=
    fun i => absoluteWeakNormalizationMap (f i)
  let g : (i : I) → (Y i).absoluteWeakNormalization ⟶ AffineSpace.{u} (ULift.{u} (Fin 1)) X :=
    fun i => sectionToAffineLine (f i) (s i)
  have hgcompat : ∀ i j, pullback.fst (π i) (π j) ≫ g i = pullback.snd (π i) (π j) ≫ g j := by
    intro i j
    refine AffineSpace.hom_ext ?_ ?_
    · change (pullback.fst (π i) (π j) ≫ sectionToAffineLine (f i) (s i)) ≫
        (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X) =
        (pullback.snd (π i) (π j) ≫ sectionToAffineLine (f j) (s j)) ≫
        (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X)
      rw [Category.assoc, sectionToAffineLine, AffineSpace.homOfVector_over,
        Category.assoc, sectionToAffineLine, AffineSpace.homOfVector_over]
      calc
        pullback.fst (π i) (π j) ≫ ((Y i).absoluteWeakNormalizationHom ≫ f i) =
            pullback.fst (π i) (π j) ≫ (π i ≫ X.absoluteWeakNormalizationHom) := by
          rw [← absoluteWeakNormalizationMap_spec]
        _ = pullback.snd (π i) (π j) ≫ (π j ≫ X.absoluteWeakNormalizationHom) :=
          congrArg (fun q => q ≫ X.absoluteWeakNormalizationHom)
            (pullback.condition : pullback.fst (π i) (π j) ≫ π i =
              pullback.snd (π i) (π j) ≫ π j)
        _ = pullback.snd (π i) (π j) ≫ ((Y j).absoluteWeakNormalizationHom ≫ f j) := by
          rw [absoluteWeakNormalizationMap_spec]
    · intro k
      rw [sectionToAffineLine_comp, AffineSpace.homOfVector_appTop_coord,
        sectionToAffineLine_comp, AffineSpace.homOfVector_appTop_coord]
      exact hcompat i j
  obtain ⟨g₀, hg₀, huniq⟩ := existsUnique_zariski_glue_morphism f hf hcover g hgcompat
  let k : ULift.{u} (Fin 1) := ULift.up 0
  refine ⟨g₀.appTop (AffineSpace.coord X k), fun i => ?_, fun s₁ hs₁ => ?_⟩
  · have h := congrArg (fun m => m.appTop (AffineSpace.coord X k)) (hg₀ i)
    change (π i).appTop (g₀.appTop (AffineSpace.coord X k)) = s i
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, g, sectionToAffineLine_appTop_coord] using h
  · let g₁ := sectionToAffineLine (𝟙 X) s₁
    have hg₁ (i : I) : π i ≫ g₁ = g i := by
      refine AffineSpace.hom_ext ?_ ?_
      · change (π i ≫ sectionToAffineLine (𝟙 X) s₁) ≫
          (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X) =
          sectionToAffineLine (f i) (s i) ≫ (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X)
        rw [Category.assoc, sectionToAffineLine, AffineSpace.homOfVector_over,
          sectionToAffineLine, AffineSpace.homOfVector_over]
        simpa using absoluteWeakNormalizationMap_spec (f i)
      · intro j
        change (π i ≫ sectionToAffineLine (𝟙 X) s₁).appTop (AffineSpace.coord X j) =
          (sectionToAffineLine (f i) (s i)).appTop (AffineSpace.coord X j)
        rw [sectionToAffineLine_comp, AffineSpace.homOfVector_appTop_coord,
          sectionToAffineLine_appTop_coord]
        exact hs₁ i
    calc
      s₁ = g₁.appTop (AffineSpace.coord X k) :=
        (sectionToAffineLine_appTop_coord (𝟙 X) s₁ k).symm
      _ = g₀.appTop (AffineSpace.coord X k) := by
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply] using
          congrArg (fun m => m.appTop (AffineSpace.coord X k)) (huniq g₁ hg₁)

/-- The underlying type-valued presheaf of global functions on absolute weak normalizations. -/
abbrev absoluteWeakNormalizationSectionTypes : Scheme.{u}ᵒᵖ ⥤ Type u :=
  (absoluteWeakNormalizationFunctor.op ⋙ Scheme.Γ) ⋙ forget CommRingCat

/-- For open immersions `f` and `g` into `X`, the restrictions of a global function on `Xᵃʷⁿ`
to `Yᵃʷⁿ` and `Zᵃʷⁿ` agree on `Yᵃʷⁿ ×_{Xᵃʷⁿ} Zᵃʷⁿ`. -/
theorem absoluteWeakNormalizationMap_section_compatible {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (g : Z ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (s : Γ(X.absoluteWeakNormalization, ⊤)) :
    (pullback.fst (absoluteWeakNormalizationMap f)
      (absoluteWeakNormalizationMap g)).appTop ((absoluteWeakNormalizationMap f).appTop s) =
    (pullback.snd (absoluteWeakNormalizationMap f)
      (absoluteWeakNormalizationMap g)).appTop ((absoluteWeakNormalizationMap g).appTop s) := by
  refine absoluteWeakNormalizationMap_pullback_open_appTop f g _ _ ?_
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] using
    congrArg (fun k => k.appTop s) (absoluteWeakNormalizationMap_pullback_comm f g)

/-- **Zariski descent.** Global functions on absolute weak normalizations satisfy descent for a
Zariski covering. -/
theorem isSheafFor_absoluteWeakNormalizationSections_of_zariskiCover {X : Scheme.{u}}
    {I : Type*} {Y : I → Scheme.{u}} (f : (i : I) → Y i ⟶ X)
    (hcover : Presieve.ofArrows Y f ∈ Scheme.zariskiPrecoverage X) :
    Presieve.IsSheafFor absoluteWeakNormalizationSectionTypes (Presieve.ofArrows Y f) := by
  classical
  rw [Scheme.ofArrows_mem_precoverage_iff] at hcover
  obtain ⟨hcover, hf⟩ := hcover
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible]
  constructor
  · intro s t hst
    have hlocal (i : I) : (absoluteWeakNormalizationMap (f i)).appTop s =
        (absoluteWeakNormalizationMap (f i)).appTop t := congrFun (congrArg Subtype.val hst) i
    have hcompat (i j : I) :
        (pullback.fst (absoluteWeakNormalizationMap (f i))
          (absoluteWeakNormalizationMap (f j))).appTop
            ((absoluteWeakNormalizationMap (f i)).appTop s) =
        (pullback.snd (absoluteWeakNormalizationMap (f i))
          (absoluteWeakNormalizationMap (f j))).appTop
            ((absoluteWeakNormalizationMap (f j)).appTop s) := by
      have _ : IsOpenImmersion (f i) := hf i
      have _ : IsOpenImmersion (f j) := hf j
      exact absoluteWeakNormalizationMap_section_compatible (f i) (f j) s
    obtain ⟨s₀, hs₀, hsuniq⟩ := existsUnique_zariski_glue_section f hf hcover
      (fun i => (absoluteWeakNormalizationMap (f i)).appTop s) hcompat
    exact (hsuniq s fun _ => rfl).trans (hsuniq t fun i => (hlocal i).symm).symm
  · intro x
    have hcompat (i j : I) :
        (pullback.fst (absoluteWeakNormalizationMap (f i))
          (absoluteWeakNormalizationMap (f j))).appTop (x.val i) =
        (pullback.snd (absoluteWeakNormalizationMap (f i))
          (absoluteWeakNormalizationMap (f j))).appTop (x.val j) := by
      have _ : IsOpenImmersion (f i) := hf i
      have _ : IsOpenImmersion (f j) := hf j
      refine absoluteWeakNormalizationMap_pullback_open_appTop (f i) (f j) _ _ ?_
      exact x.property i j (pullback (f i) (f j)) (pullback.fst (f i) (f j))
        (pullback.snd (f i) (f j)) pullback.condition
    obtain ⟨s₀, hs₀, _⟩ := existsUnique_zariski_glue_section f hf hcover x.val hcompat
    exact ⟨s₀, Subtype.ext (funext hs₀)⟩

/-! ### Descent along a proper surjection -/

/-- The comparison map from the absolute weak normalization of a fibre product to the fibre
product of the absolute weak normalizations over the base is surjective. -/
theorem surjective_absoluteWeakNormalization_pullback_lift {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) :
    Surjective (pullback.lift (f := X.absoluteWeakNormalizationHom ≫ f)
      (g := Y.absoluteWeakNormalizationHom ≫ g)
      (absoluteWeakNormalizationMap (pullback.fst f g))
      (absoluteWeakNormalizationMap (pullback.snd f g)) (by
        rw [← Category.assoc, absoluteWeakNormalizationMap_spec, ← Category.assoc,
          absoluteWeakNormalizationMap_spec, Category.assoc, Category.assoc,
          pullback.condition])) := by
  let η := fun W : Scheme.{u} => W.absoluteWeakNormalizationHom
  let first := absoluteWeakNormalizationMap (pullback.fst f g)
  let second := absoluteWeakNormalizationMap (pullback.snd f g)
  let k := pullback.lift (f := η X ≫ f) (g := η Y ≫ g) first second (by
    dsimp [first, second, η]
    rw [← Category.assoc, absoluteWeakNormalizationMap_spec, ← Category.assoc,
      absoluteWeakNormalizationMap_spec, Category.assoc, Category.assoc, pullback.condition])
  let m := pullback.map (η X ≫ f) (η Y ≫ g) f g (η X) (η Y) (𝟙 Z) rfl rfl
  have hm : UniversalHomeomorphism m := by
    have _ : MorphismProperty.IsStableUnderComposition (@UniversalHomeomorphism) :=
      universalHomeomorphism_hasTwoOutOfThreeProperty.toIsStableUnderComposition
    have _ : MorphismProperty.IsStableUnderBaseChange (@UniversalHomeomorphism) := ⟨by
      intro A B C D f' g' f'' g'' sq hg
      rw [universalHomeomorphism_iff] at hg ⊢
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hg⟩
    exact MorphismProperty.pullbackMap
      (universalHomeomorphism_absoluteWeakNormalizationHom X)
      (universalHomeomorphism_absoluteWeakNormalizationHom Y) rfl rfl
  have hkm : k ≫ m = η (pullback f g) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      dsimp [m, pullback.map]
      rw [pullback.lift_fst, ← Category.assoc]
      dsimp [k]
      rw [pullback.lift_fst]
      exact absoluteWeakNormalizationMap_spec _
    · rw [Category.assoc]
      dsimp [m, pullback.map]
      rw [pullback.lift_snd, ← Category.assoc]
      dsimp [k]
      rw [pullback.lift_snd]
      exact absoluteWeakNormalizationMap_spec _
  have hk := (universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty).of_postcomp
    k m hm (by
      rw [hkm]
      exact universalHomeomorphism_absoluteWeakNormalizationHom _)
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective k).mp hk |>.2.2

/-- The scheme-theoretic image of a compatible section, read as a morphism to the affine line,
is a universal homeomorphism over the affine base. -/
theorem universalHomeomorphism_sectionImage_of_compatible {X Y : Scheme.{u}} [IsAffine X]
    (f : Y ⟶ X) [IsProper f] [Surjective f] (s : Γ(Y.absoluteWeakNormalization, ⊤))
    (hs : (absoluteWeakNormalizationMap (pullback.fst f f)).appTop s =
      (absoluteWeakNormalizationMap (pullback.snd f f)).appTop s) :
    UniversalHomeomorphism ((sectionToAffineLine f s).imageι ≫
      (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X)) := by
  let e := sectionToAffineLine f s
  let projection := AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X
  let q := e.imageι ≫ projection
  let η := Y.absoluteWeakNormalizationHom ≫ f
  have he : e ≫ projection = η := AffineSpace.homOfVector_over _ _
  have _ : UniversallyClosed (e ≫ projection) := by
    rw [he]
    exact universallyClosed_absoluteWeakNormalizationHom_comp f
  have _ : Surjective (e ≫ projection) := by
    rw [he]
    exact surjective_absoluteWeakNormalizationHom_comp f
  have _ : IsFinite q := isFinite_imageι_comp_of_universallyClosed e
  have _ : Surjective q := surjective_imageι_comp e projection
  have _ : Surjective e.toImage := surjective_toImage e projection
  have hfactor : η = e.toImage ≫ q := by
    simp only [q, ← Category.assoc, Scheme.Hom.toImage_imageι, he]
  let m := pullback.map η η q q e.toImage e.toImage (𝟙 X)
    ((Category.comp_id _).trans hfactor) ((Category.comp_id _).trans hfactor)
  have _ : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) := ⟨by
    intro A B C a b ha hb
    have _ := ha
    have _ := hb
    infer_instance⟩
  have _ : Surjective m := MorphismProperty.pullbackMap (P := @Surjective)
    (inferInstance : Surjective e.toImage) (inferInstance : Surjective e.toImage)
    hfactor hfactor
  let first := absoluteWeakNormalizationMap (pullback.fst f f)
  let second := absoluteWeakNormalizationMap (pullback.snd f f)
  have hbase : first ≫ η = second ≫ η := by
    dsimp [first, second, η]
    rw [← Category.assoc, absoluteWeakNormalizationMap_spec, ← Category.assoc,
      absoluteWeakNormalizationMap_spec, Category.assoc, Category.assoc, pullback.condition]
  let k := pullback.lift first second hbase
  have _ : Surjective k := surjective_absoluteWeakNormalization_pullback_lift f f
  have hequal : first ≫ e = second ≫ e := by
    dsimp [e]
    rw [sectionToAffineLine_comp, sectionToAffineLine_comp,
      show first ≫ Y.absoluteWeakNormalizationHom ≫ f =
        second ≫ Y.absoluteWeakNormalizationHom ≫ f from hbase]
    exact congrArg (AffineSpace.homOfVector (second ≫ Y.absoluteWeakNormalizationHom ≫ f))
      (congrArg (fun t => fun _ : ULift.{u} (Fin 1) => t) hs)
  have hpair : (k ≫ m) ≫ pullback.fst q q = (k ≫ m) ≫ pullback.snd q q := by
    refine (cancel_mono e.imageι).mp ?_
    simp only [Category.assoc]
    dsimp [m, pullback.map]
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    simp only [Category.assoc, Scheme.Hom.toImage_imageι]
    rw [← Category.assoc, ← Category.assoc]
    dsimp [k]
    rw [pullback.lift_fst, pullback.lift_snd]
    exact hequal
  have hdiag : ((k ≫ m) ≫ pullback.fst q q) ≫ pullback.diagonal q = k ≫ m := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hpair
  have _ : Surjective (((k ≫ m) ≫ pullback.fst q q) ≫ pullback.diagonal q) := by
    rw [hdiag]
    infer_instance
  have _ : UniversallyInjective q := (UniversallyInjective.iff_diagonal q).mpr
    (Surjective.of_comp ((k ≫ m) ≫ pullback.fst q q) (pullback.diagonal q))
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective q).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- A global function on the absolute weak normalization of `Y` which is compatible on the
fibre square of a proper surjection `Y ⟶ X` with affine `X` descends uniquely. -/
theorem existsUnique_properSurjective_glue_section {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X)
    [IsProper f] [Surjective f] (s : Γ(Y.absoluteWeakNormalization, ⊤))
    (hs : (absoluteWeakNormalizationMap (pullback.fst f f)).appTop s =
      (absoluteWeakNormalizationMap (pullback.snd f f)).appTop s) :
    ∃! t : Γ(X.absoluteWeakNormalization, ⊤),
      (absoluteWeakNormalizationMap f).appTop t = s := by
  let e := sectionToAffineLine f s
  let q := e.imageι ≫ (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X)
  have hq := universalHomeomorphism_sectionImage_of_compatible f s hs
  let g := absoluteWeakNormalizationLift q hq
  let t := (g ≫ e.imageι).appTop (AffineSpace.coord X (ULift.up 0))
  have hge : absoluteWeakNormalizationMap f ≫ g = e.toImage := by
    refine absoluteWeakNormalizationMap_comp_lift _ _ _ _ ?_
    simpa only [q, e, sectionToAffineLine, Category.assoc, Scheme.Hom.toImage_imageι_assoc] using
      AffineSpace.homOfVector_over (Y.absoluteWeakNormalizationHom ≫ f) (fun _ => s)
  have ht : (absoluteWeakNormalizationMap f).appTop t = s := by
    change (absoluteWeakNormalizationMap f ≫ g ≫ e.imageι).appTop
      (AffineSpace.coord X (ULift.up 0)) = s
    rw [← Category.assoc, hge, Scheme.Hom.toImage_imageι]
    exact sectionToAffineLine_appTop_coord f s _
  refine ⟨t, ht, fun t' ht' => ?_⟩
  have _ : IsReduced X.absoluteWeakNormalization := isReduced_absoluteWeakNormalization X
  have _ : Surjective (absoluteWeakNormalizationMap f) :=
    surjective_absoluteWeakNormalizationMap f
  let a := AffineSpace.homOfVector X.absoluteWeakNormalizationHom
    (fun _ : ULift.{u} (Fin 1) => t')
  let b := AffineSpace.homOfVector X.absoluteWeakNormalizationHom
    (fun _ : ULift.{u} (Fin 1) => t)
  have hab : a = b := ext_of_isDominant_of_isSeparated
    (AffineSpace.{u} (ULift.{u} (Fin 1)) X ↘ X)
    (by simp [a, b, AffineSpace.homOfVector_over]) (absoluteWeakNormalizationMap f) (by
      rw [AffineSpace.comp_homOfVector, AffineSpace.comp_homOfVector]
      dsimp [Function.comp_def]
      rw [ht', ht])
  simpa only [a, b, AffineSpace.homOfVector_appTop_coord] using
    congrArg (fun h => h.appTop (AffineSpace.coord X (ULift.up 0))) hab

/-- **Descent along a proper surjection.** Global functions on absolute weak normalizations
satisfy descent for a proper surjection onto an affine scheme. -/
theorem isSheafFor_absoluteWeakNormalizationSections_of_properSurjective {X Y : Scheme.{u}}
    [IsAffine X] (f : Y ⟶ X) [IsProper f] [Surjective f] :
    Presieve.IsSheafFor absoluteWeakNormalizationSectionTypes
      (Presieve.ofArrows (fun _ : Unit => Y) fun _ => f) := by
  rw [Presieve.isSheafFor_arrows_iff_pullbacks]
  intro s hs
  obtain ⟨t, ht, huniq⟩ := existsUnique_properSurjective_glue_section f (s ()) (hs () ())
  exact ⟨t, fun i => by cases i; exact ht, fun t' ht' => huniq t' (ht' ())⟩

/-! ### The ph sheaf property -/

/-- The inclusion of a big ph site into all schemes creates fibre products. -/
@[instance_reducible]
def createsLimitsOfShape_walkingCospan_bigPHSite_inclusion (B : BigPHSite.{u}) :
    CreatesLimitsOfShape WalkingCospan B.inclusion := by
  refine { CreatesLimit := fun {D} => ?_ }
  let D' := D ⋙ B.inclusion
  let t := pullback.cone (D'.map WalkingCospan.Hom.inl) (D'.map WalkingCospan.Hom.inr)
  exact createsLimitFullSubcategoryInclusion' D
    ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D') t).symm (limit.isLimit _))
    (Scheme.size_pullback_lt _ _ (D.obj .left).property (D.obj .right).property)

/-- A cone of commutative rings whose underlying cone of types is limiting is itself
limiting. -/
def isLimit_of_isLimit_forget {J : Type*} [Category* J] {D : J ⥤ CommRingCat.{u}} (c : Cone D)
    (hc : IsLimit ((forget CommRingCat).mapCone c)) : IsLimit c := by
  let e := Types.isLimitEquivSections hc
  let liftFun (s : Cone D) (x : s.pt) : c.pt :=
    e.symm (Types.sectionOfCone ((forget CommRingCat).mapCone s) x)
  have hfac (s : Cone D) (j : J) (x : s.pt) : c.π.app j (liftFun s x) = s.π.app j x :=
    Types.isLimitEquivSections_symm_apply hc _ j
  have hext (x y : c.pt) (h : ∀ j, c.π.app j x = c.π.app j y) : x = y := by
    refine e.injective ?_
    ext j
    exact h j
  let liftRing (s : Cone D) : s.pt →+* c.pt :=
    { toFun := liftFun s
      map_one' := hext _ _ fun j => by simp [hfac]
      map_mul' x y := hext _ _ fun j => by simp only [hfac, map_mul]
      map_zero' := hext _ _ fun j => by simp [hfac]
      map_add' x y := hext _ _ fun j => by simp only [hfac, map_add] }
  refine ⟨fun s => CommRingCat.ofHom (liftRing s), fun s j => ?_, fun s m hm => ?_⟩
  · ext x
    exact hfac s j x
  · ext x
    exact hext _ _ fun j =>
      (congrArg (fun k : s.pt ⟶ D.obj j => k x) (hm j)).trans (hfac s j x).symm

/-- On a big ph site, global functions on absolute weak normalizations form a sheaf.

Together with `AlgebraicGeometry.existsUnique_hom_absoluteWeakNormalizationSections`, this shows
that the canonical map from the structure sheaf exhibits this sheaf as its ph sheafification. -/
@[stacks 0EVT, stacks 0EVU "ph topology, the sheaf property"]
theorem isSheaf_absoluteWeakNormalizationSections (B : BigPHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Presheaf.IsSheaf (BigPHOver.topology B S hS) (absoluteWeakNormalizationSections B S hS) := by
  let inc := B.inclusion
  have _ : CreatesLimitsOfShape WalkingCospan inc :=
    createsLimitsOfShape_walkingCospan_bigPHSite_inclusion B
  have _ : HasPullbacks B.Schemes :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape inc
  have _ : PreservesLimitsOfShape WalkingCospan inc := inferInstance
  let F := BigPHOver.toScheme B S hS
  have _ : PreservesLimitsOfShape WalkingCospan F := inferInstance
  let P := F.op ⋙ absoluteWeakNormalizationSectionTypes
  have _ : ReflectsLimitsOfSize.{u, u + 1} (forget CommRingCat.{u}) :=
    { reflectsLimitsOfShape := fun {J} _ =>
      { reflectsLimit := fun {D} =>
        { reflects := fun {c} hc => ⟨isLimit_of_isLimit_forget c hc⟩ } } }
  refine Presheaf.isSheaf_of_isSheaf_comp (BigPHOver.topology B S hS)
    (absoluteWeakNormalizationSections B S hS) (forget CommRingCat.{u}) ?_
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ?_
  change Presieve.IsSheaf (BigPHOver.topology B S hS) P
  refine (isSheaf_iff_zariski_and_properSurjective B S hS P).mpr ?_
  have hz : IsZariskiSheaf B S hS P := by
    intro X E hE
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks F
      absoluteWeakNormalizationSectionTypes E.presieve₀, ← PreZeroHypercover.presieve₀_map]
    exact isSheafFor_absoluteWeakNormalizationSections_of_zariskiCover (E.map F).f hE
  refine ⟨hz, (properSurjective_iff_affine B S hS P hz).mpr ?_⟩
  intro X Y f hX hf hsurj
  have _ : IsAffine (F.obj X) := hX
  have _ : IsProper (F.map f) := hf
  have _ : Surjective (F.map f) := hsurj
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks F
    absoluteWeakNormalizationSectionTypes, Presieve.map_ofArrows]
  exact isSheafFor_absoluteWeakNormalizationSections_of_properSurjective (F.map f)

end AlgebraicGeometry

end
