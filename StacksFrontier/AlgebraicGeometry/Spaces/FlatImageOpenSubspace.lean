module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open image of a flat morphism of algebraic spaces locally of finite presentation

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally of
finite presentation. Its image `|g|(|X|)` is open in `|Y|` (the open half of Stacks 042S), so it
is the point set of an open subspace `V ⊆ Y` (Stacks 03BZ). This file packages `V` as an object
of `AlgebraicGeometry.AlgebraicSpaces`, together with the factorisation `X ⟶ V ⟶ Y` of `g`, and
records the properties of the two factors:

* the inclusion `V ⟶ Y` is an étale monomorphism whose image is the image of `g`;
* the corestriction `X ⟶ V` is surjective, flat and locally of finite presentation.

For an fppf covering `{g i : X i ⟶ Y}` the images of the members therefore form an étale
covering of `Y` by open subspaces, over each of which the corresponding member becomes a single
surjective, flat morphism locally of finite presentation. This is how descent along an fppf
covering family is reduced to descent along single fppf morphisms (Stacks 0GFX from
Stacks 0GFW).

## Main definitions

* `AlgebraicGeometry.Space.flatImage`: the open subspace of `Y` cut out by the image of `g`.
* `AlgebraicGeometry.Space.flatImageι`: its inclusion into `Y`.
* `AlgebraicGeometry.Space.flatImageLift`: the corestriction of `g`.

## Main results

* `AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isFlat`: the image of `g` is open.
* `AlgebraicGeometry.Space.isPullback_flatImageLift`: the corestriction is the base change of
  `g` along the inclusion, the inclusion being a monomorphism.
* `AlgebraicGeometry.Space.isSurjective_flatImageLift`, `isFlat_flatImageLift`,
  `isLocallyOfFinitePresentation_flatImageLift`: the properties of the corestriction.
* `AlgebraicGeometry.Space.isEtaleCovering_flatImageι`: the images of the members of an fppf
  covering form an étale covering.
* `AlgebraicGeometry.Space.surjectiveFlatLfp_pullback_snd_of_fac`: the base change of `g` along a
  morphism factoring through its image is surjective, flat and locally of finite presentation.

## References

* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0GFX](https://stacks.math.columbia.edu/tag/0GFX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/-- The base change of `g = l ≫ i` along `t = a ≫ i`, for a monomorphism `i`, is the base change
of `l` along `a`, so it has every property of `l` stable under base change. -/
@[sga "3 V 10.1.1" "(i) ⇒ (ii), partial"]
theorem CategoryTheory.MorphismProperty.pullback_snd_comp_of_mono {C : Type*} [Category C]
    [HasPullbacks C] (P : MorphismProperty C) [P.IsStableUnderBaseChange] {X V Y T : C}
    {g : X ⟶ Y} {t : T ⟶ Y} (l : X ⟶ V) (i : V ⟶ Y) [Mono i] (a : T ⟶ V) (hg : l ≫ i = g)
    (ht : a ≫ i = t) (hl : P l) : P (pullback.snd g t) := by
  subst hg ht
  have h := IsPullback.of_isLimit (pullbackIsPullbackOfCompMono l a i)
  rw [← (IsPullback.of_hasPullback (l ≫ i) (a ≫ i)).isoIsPullback_hom_snd _ _ h,
    P.cancel_left_of_respectsIso]
  exact P.pullback_snd l a hl

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section FlatImage

variable {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)

/-- The image of a flat morphism of algebraic spaces locally of finite presentation is open in
the point space of the target. -/
theorem isOpen_range_pointsMap_of_isFlat (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) :
    IsOpen (Set.range (pointsMap B S hS X.1 g.hom)) :=
  (isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS X.property
    Y.property g.hom hflat hlfp).isOpen_range

/-- The subfunctor of the target cut out by the image of a flat morphism locally of finite
presentation is an open subspace. -/
theorem isOpenSubspace_flatImage (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) :
    IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS Y.1 (Set.range (pointsMap B S hS X.1 g.hom))) :=
  isOpenSubspace_openSubspaceOfPoints B S hS Y.property _
    (isOpen_range_pointsMap_of_isFlat B S hS g hflat hlfp)

/-- The open subspace of `Y` cut out by the image of a flat morphism `g : X ⟶ Y` locally of
finite presentation, as an algebraic space over `S`. -/
noncomputable def flatImage (hflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS g.hom) : AlgebraicSpaces B S hS :=
  ⟨(openSubspaceOfPoints B S hS Y.1 (Set.range (pointsMap B S hS X.1 g.hom))).toFunctor,
    (isOpenSubspace_flatImage B S hS g hflat hlfp).1⟩

variable (hflat : IsFlat B S hS g.hom) (hlfp : IsLocallyOfFinitePresentation B S hS g.hom)

/-- The inclusion of the image of `g` into the target. -/
noncomputable def flatImageι : flatImage B S hS g hflat hlfp ⟶ Y :=
  ObjectProperty.homMk
    (openSubspaceOfPoints B S hS Y.1 (Set.range (pointsMap B S hS X.1 g.hom))).ι

/-- The corestriction of `g` to its image. -/
noncomputable def flatImageLift : X ⟶ flatImage B S hS g hflat hlfp :=
  ObjectProperty.homMk
    (Subfunctor.lift g.hom (range_le_openSubspaceOfPoints_range_pointsMap g.hom))

/-- The corestriction followed by the inclusion is `g`. -/
@[reassoc (attr := simp)]
theorem flatImageLift_ι :
    flatImageLift B S hS g hflat hlfp ≫ flatImageι B S hS g hflat hlfp = g :=
  ObjectProperty.hom_ext _ <|
    Subfunctor.lift_ι g.hom (range_le_openSubspaceOfPoints_range_pointsMap g.hom)

/-- The inclusion of the image is a monomorphism. -/
instance mono_flatImageι : Mono (flatImageι B S hS g hflat hlfp) :=
  (ObjectProperty.ι _).mono_of_mono_map
    (inferInstanceAs (Mono (openSubspaceOfPoints B S hS Y.1
      (Set.range (pointsMap B S hS X.1 g.hom))).ι))

/-- The inclusion of the image is étale. -/
theorem isEtale_flatImageι : IsEtale B S hS (flatImageι B S hS g hflat hlfp).hom :=
  isEtale_ι_of_isOpenSubspace (isOpenSubspace_flatImage B S hS g hflat hlfp)

/-- The inclusion of the image is an open immersion. -/
theorem isOpenImmersion_flatImageι :
    IsOpenImmersion B S hS (flatImageι B S hS g hflat hlfp).hom :=
  (isOpenSubspace_flatImage B S hS g hflat hlfp).2

/-- The image of the inclusion is the image of `g`. -/
theorem range_pointsMap_flatImageι :
    Set.range (pointsMap B S hS (flatImage B S hS g hflat hlfp).1
      (flatImageι B S hS g hflat hlfp).hom) = Set.range (pointsMap B S hS X.1 g.hom) :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The corestriction of `g` is the base change of `g` along the inclusion of its image. -/
theorem isPullback_flatImageLift :
    IsPullback (flatImageLift B S hS g hflat hlfp) (𝟙 X) (flatImageι B S hS g hflat hlfp) g :=
  IsPullback.of_vert_isIso_mono ⟨by simp⟩

/-- The corestriction of `g` to its image is surjective. -/
theorem isSurjective_flatImageLift :
    IsSurjective B S hS (flatImageLift B S hS g hflat hlfp).hom :=
  isSurjective_lift_openSubspaceOfPoints_range B S hS g.hom

/-- The corestriction of `g` to its image is flat, as a base change of `g` (Stacks 03MO). -/
theorem isFlat_flatImageLift : IsFlat B S hS (flatImageLift B S hS g hflat hlfp).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_flatImageLift B S hS g hflat hlfp).flip hflat

/-- The corestriction of `g` to its image is locally of finite presentation, as a base change
of `g` (Stacks 03XR). -/
theorem isLocallyOfFinitePresentation_flatImageLift :
    IsLocallyOfFinitePresentation B S hS (flatImageLift B S hS g hflat hlfp).hom :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_flatImageLift B S hS g hflat hlfp).flip hlfp

end FlatImage

/-! ### Surjective flat morphisms locally of finite presentation -/

/-- The morphisms of algebraic spaces over `S` which are surjective, flat and locally of finite
presentation. -/
def surjectiveFlatLfp : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ g => IsSurjective B S hS g.hom ∧ IsFlat B S hS g.hom ∧
    IsLocallyOfFinitePresentation B S hS g.hom

/-- Surjective flat morphisms locally of finite presentation are stable under base change
(Stacks 03MO, 03XR and 03MF). -/
instance : (surjectiveFlatLfp B S hS).IsStableUnderBaseChange :=
  ⟨fun sq hg => ⟨isSurjective_of_isPullback B S hS sq hg.1,
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hg.2.1,
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hg.2.2⟩⟩

/-- The base change of a flat morphism `g` locally of finite presentation along a morphism which
factors through the open image of `g` is surjective, flat and locally of finite presentation. -/
theorem surjectiveFlatLfp_pullback_snd_of_fac {X Y T : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (hflat : IsFlat B S hS g.hom) (hlfp : IsLocallyOfFinitePresentation B S hS g.hom)
    (t : T ⟶ Y) (a : T ⟶ flatImage B S hS g hflat hlfp)
    (ha : a ≫ flatImageι B S hS g hflat hlfp = t) :
    surjectiveFlatLfp B S hS (pullback.snd g t) :=
  MorphismProperty.pullback_snd_comp_of_mono (surjectiveFlatLfp B S hS)
    (flatImageLift B S hS g hflat hlfp) (flatImageι B S hS g hflat hlfp) a
    (flatImageLift_ι B S hS g hflat hlfp) ha
    ⟨isSurjective_flatImageLift B S hS g hflat hlfp, isFlat_flatImageLift B S hS g hflat hlfp,
      isLocallyOfFinitePresentation_flatImageLift B S hS g hflat hlfp⟩

/-! ### The images of an fppf covering -/

/-- The images of the members of an fppf covering of an algebraic space form an étale covering
of it, by open subspaces. -/
theorem isEtaleCovering_flatImageι {I : Type v} {Y : I → AlgebraicSpaces B S hS}
    {X : AlgebraicSpaces B S hS} (g : ∀ i, Y i ⟶ X)
    (hg : IsFppfCovering B S hS (fun i => (Y i).1) (fun i => (g i).hom)) :
    IsEtaleCovering B S hS
      (fun i => (flatImage B S hS (g i) (hg.flat i) (hg.locallyOfFinitePresentation i)).1)
      (fun i => (flatImageι B S hS (g i) (hg.flat i) (hg.locallyOfFinitePresentation i)).hom) where
  target_isAlgebraicSpace := X.property
  source_isAlgebraicSpace i :=
    (flatImage B S hS (g i) (hg.flat i) (hg.locallyOfFinitePresentation i)).property
  etale i := isEtale_flatImageι B S hS (g i) (hg.flat i) (hg.locallyOfFinitePresentation i)
  jointly_surjective := by
    simp_rw [range_pointsMap_flatImageι]
    exact hg.jointly_surjective

end AlgebraicGeometry.Space

end
