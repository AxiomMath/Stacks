module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChangeGeneric
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothStratification
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Smooth stratification of a morphism near a generic point of a reduced base

Let `f : X ⟶ S` be a morphism of finite presentation with `S` reduced and let `η ∈ S` be a
generic point of an irreducible component. Near `η` the morphism admits, after a finite locally
free universally injective surjective cover of an open neighbourhood, a finite filtration of the
base change of `X` by closed subschemes cut out by finite type ideal sheaves whose successive
differences are smooth over the cover.

## Main results

* `AlgebraicGeometry.exists_smooth_stratification_at_generic_point`: the open neighbourhood, the
  finite locally free universally injective cover, and the filtration with smooth strata.

## Implementation notes

The local ring of a reduced scheme at the generic point of an irreducible component is a field,
so the fibre of `f` over `η` is a scheme of finite type over a field; the stratification over a
field, after a finite purely inseparable extension, is Stacks 0H3W. Both the extension and the
stratification are then descended to a principal open neighbourhood of `η`, the local ring at
`η` being the filtered colimit of the principal localizations of an affine chart.

Closed subschemes are represented by their closed immersions into the base change, and each
successive stratum by an open subscheme of the preceding closed subscheme whose underlying set
is the difference of the successive closed images. Finite type of the defining ideal sheaves is
expressed through the ideal sheaf of a closed immersion of ringed spaces.

Descending the cover does not use the descent of finite local freeness along the limit: the
cover is affine, flat, locally of finite presentation, surjective and universally injective
over the limit, each of these five properties descends separately, and together they force
finite local freeness.

## References

* [Stacks Project, Tag 0H43](https://stacks.math.columbia.edu/tag/0H43)
* [Stacks Project, Tag 0H3W](https://stacks.math.columbia.edu/tag/0H3W)
* [Stacks Project, Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZN](https://stacks.math.columbia.edu/tag/01ZN)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.GenericFlatness (finitePresentation_pullback)

universe u

private local instance finiteLocallyFree_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) where
  of_isPullback sq hf := by
    rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation] at hf ⊢
    exact ⟨MorphismProperty.of_isPullback sq hf.1,
      MorphismProperty.of_isPullback sq hf.2.1,
      MorphismProperty.of_isPullback sq hf.2.2⟩
private local instance finiteLocallyFree_respectsIso :
    MorphismProperty.RespectsIso (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
private local instance universallyInjective_respectsIso :
    MorphismProperty.RespectsIso (@UniversallyInjective.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
private local instance flat_respectsIso :
    MorphismProperty.RespectsIso (@Flat.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
private local instance isAffineHom_respectsIso :
    MorphismProperty.RespectsIso (@IsAffineHom.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
private instance smooth_respectsIso :
    MorphismProperty.RespectsIso (@Smooth.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

namespace Stacks.SmoothStrata

open StageFactor

/-- A property respecting isomorphisms holds for the base change of the structure morphism of an
over object, viewed as a morphism to the terminal over object, exactly when it holds for the
structure morphism of the base change. -/
theorem property_overPullback_terminal_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (X : Over S) (f : T ⟶ S) :
    P ((Over.pullback f).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ↔
      P ((Over.pullback f).obj X).hom := by
  have h : ((Over.pullback f).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ≫
      pullback.snd (𝟙 S) f = ((Over.pullback f).obj X).hom :=
    Over.w _
  rw [← h, P.cancel_right_of_respectsIso]
private lemma property_hom_of_iso
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (h : P X.hom) : P Y.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← P.cancel_left_of_respectsIso e.hom.left Y.hom, Over.w]
  exact h
private noncomputable def pullbackConeCompIso
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (h : j ⟶ i) (X : Over (D.obj i)) :
    (Over.pullback (c.π.app i)).obj X ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map h)).obj X) :=
  (eqToIso (congrArg (fun f => (Over.pullback f).obj X) (c.w h).symm)) ≪≫
    (Over.pullbackComp (c.π.app j) (D.map h)).app X
private lemma universallyInjective_pullback_iff_surjective_diagonal
    {S T : Scheme.{u}} (X : Over S) (f : T ⟶ S) :
    UniversallyInjective ((Over.pullback f).obj X).hom ↔
      Surjective ((Over.pullback f).map
        (Over.homMk (pullback.diagonal X.hom) :
          X ⟶ Over.mk (pullback.snd X.hom X.hom ≫ X.hom))).left := by
  show UniversallyInjective (pullback.snd X.hom f) ↔ _
  have h : (pullbackSymmetry f X.hom).hom ≫ pullback.snd X.hom f =
      pullback.fst f X.hom := by simp
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (@UniversallyInjective) (pullbackSymmetry f X.hom).hom, h,
    UniversallyInjective.iff_diagonal, diagonal_pullback_fst]
  rw [MorphismProperty.cancel_left_of_respectsIso (@Surjective),
    MorphismProperty.cancel_right_of_respectsIso (@Surjective)]
private lemma exists_universallyInjective_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [UniversallyInjective ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i),
      UniversallyInjective ((Over.pullback (D.map h)).obj X).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let Y : Over (D.obj i) := Over.mk (pullback.snd X.hom X.hom ≫ X.hom)
  let a : X ⟶ Y := Over.homMk (pullback.diagonal X.hom)
  have : CompactSpace Y.left := inferInstanceAs (CompactSpace (pullback X.hom X.hom : Scheme))
  have : QuasiSeparatedSpace Y.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd X.hom X.hom)
  have : LocallyOfFinitePresentation a.left :=
    AlgebraicGeometry.locallyOfFinitePresentation_diagonal X.hom
  have : Surjective ((Over.pullback (c.π.app i)).map a).left :=
    (universallyInjective_pullback_iff_surjective_diagonal X _).mp inferInstance
  obtain ⟨j, h, hh⟩ :=
    AlgebraicGeometry.exists_surjective_baseChange_of_surjective_limitBaseChange D c hc i X Y a
  exact ⟨j, h, (universallyInjective_pullback_iff_surjective_diagonal X _).mpr hh⟩
/-- A property of the structure morphism of a finitely presented over object descends to a stage
once it descends for the morphism from the object to the terminal over object. -/
private lemma exists_baseChange_of_terminal
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : P ((Over.pullback (c.π.app i)).obj X).hom)
    (H : ∀ [CompactSpace X.left] [QuasiSeparatedSpace X.left]
      [CompactSpace (Over.mk (𝟙 (D.obj i))).left]
      [QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left]
      [LocallyOfFinitePresentation (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (D.obj i))).left],
      P ((Over.pullback (c.π.app i)).map
        (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (D.obj i)))).left →
      ∃ (j : I) (h : j ⟶ i), P ((Over.pullback (D.map h)).map
        (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (D.obj i)))).left) :
    ∃ (j : I) (h : j ⟶ i), P ((Over.pullback (D.map h)).obj X).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation (Over.homMk X.hom : X ⟶ Over.mk (𝟙 (D.obj i))).left := hX.1
  obtain ⟨j, h, hh⟩ := H ((property_overPullback_terminal_iff _ X _).mpr hP)
  exact ⟨j, h, (property_overPullback_terminal_iff _ X _).mp hh⟩
private lemma exists_surjective_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Surjective ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i), Surjective ((Over.pullback (D.map h)).obj X).hom :=
  exists_baseChange_of_terminal D c i X hX (@Surjective.{u}) inferInstance fun _ =>
    AlgebraicGeometry.exists_surjective_baseChange_of_surjective_limitBaseChange D c hc i X
      (Over.mk (𝟙 (D.obj i))) _
/-- A property stable under base change holds for the base change of an over object. -/
private lemma property_hom_baseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) (h : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  MorphismProperty.baseChange_obj f X h
private lemma property_hom_baseChange_comp
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {i j k : I} (g : j ⟶ i) (z : k ⟶ j)
    (X : Over (D.obj i)) (h : P ((Over.pullback (D.map g)).obj X).hom) :
    P ((Over.pullback (D.map (z ≫ g))).obj X).hom := by
  rw [D.map_comp]
  exact property_hom_of_iso P ((Over.pullbackComp (D.map z) (D.map g)).app X).symm
    (property_hom_baseChange P _ _ h)
private lemma exists_surjective_universallyInjective_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Surjective ((Over.pullback (c.π.app i)).obj X).hom]
    [UniversallyInjective ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i), Surjective ((Over.pullback (D.map h)).obj X).hom ∧
      UniversallyInjective ((Over.pullback (D.map h)).obj X).hom := by
  obtain ⟨j₁, h₁, hsurj⟩ := exists_surjective_baseChange D c hc i X hX
  obtain ⟨j₂, h₂, hinj⟩ := exists_universallyInjective_baseChange D c hc i X hX
  obtain ⟨j, a, b, hab⟩ := IsCofiltered.cospan h₁ h₂
  refine ⟨j, a ≫ h₁, ?_, ?_⟩
  · exact property_hom_baseChange_comp _ D h₁ a X hsurj
  · rw [hab]
    exact property_hom_baseChange_comp _ D h₂ b X hinj

/-- Flatness of a finitely presented morphism to the limit descends to a stage. -/
private lemma exists_flat_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Flat ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i), Flat ((Over.pullback (D.map h)).obj X).hom :=
  exists_baseChange_of_terminal D c i X hX (@Flat.{u}) inferInstance fun _ =>
    AlgebraicGeometry.exists_flat_baseChange_of_limitBaseChange D c i X
      (Over.mk (𝟙 (D.obj i))) _ hc

/-- Affineness of a finitely presented morphism to the limit descends to a stage. -/
private lemma exists_isAffineHom_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [IsAffineHom ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i), IsAffineHom ((Over.pullback (D.map h)).obj X).hom :=
  exists_baseChange_of_terminal D c i X hX (@IsAffineHom.{u}) inferInstance fun _ =>
    AlgebraicGeometry.exists_isAffineHom_of_isLimit D c hc i X
      (Over.mk (𝟙 (D.obj i))) _

/-- A finitely presented morphism whose base change to the limit is a finite locally free
universally injective surjection already is one at some stage. Finite local freeness is read
off from affineness, flatness, surjectivity and universal injectivity, each of which descends
separately. -/
private lemma exists_finiteLocallyFree_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (c.π.app i)).obj X).hom]
    [Surjective ((Over.pullback (c.π.app i)).obj X).hom]
    [UniversallyInjective ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i),
      Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (D.map h)).obj X).hom ∧
        Surjective ((Over.pullback (D.map h)).obj X).hom ∧
        UniversallyInjective ((Over.pullback (D.map h)).obj X).hom := by
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((Over.pullback (c.π.app i)).obj X).hom).mp inferInstance
  have : IsFinite ((Over.pullback (c.π.app i)).obj X).hom := hfin
  have : Flat ((Over.pullback (c.π.app i)).obj X).hom := hflat
  have : IsAffineHom ((Over.pullback (c.π.app i)).obj X).hom := inferInstance
  obtain ⟨j₁, h₁, hsurj, hinj⟩ :=
    exists_surjective_universallyInjective_baseChange D c hc i X hX
  obtain ⟨j₂, h₂, hflat₂⟩ := exists_flat_baseChange D c hc i X hX
  obtain ⟨j₃, h₃, haff₃⟩ := exists_isAffineHom_baseChange D c hc i X hX
  obtain ⟨j₄, a, b, hab⟩ := IsCofiltered.cospan h₁ h₂
  obtain ⟨j, v, w, hvw⟩ := IsCofiltered.cospan (a ≫ h₁) h₃
  have hs : Surjective ((Over.pullback (D.map ((v ≫ a) ≫ h₁))).obj X).hom :=
    property_hom_baseChange_comp _ D h₁ (v ≫ a) X hsurj
  have hi : UniversallyInjective ((Over.pullback (D.map ((v ≫ a) ≫ h₁))).obj X).hom :=
    property_hom_baseChange_comp _ D h₁ (v ≫ a) X hinj
  have he₂ : (v ≫ a) ≫ h₁ = (v ≫ b) ≫ h₂ := by
    rw [Category.assoc, hab, Category.assoc]
  have he₃ : (v ≫ a) ≫ h₁ = w ≫ h₃ := by
    rw [Category.assoc]; exact hvw
  have hf : Flat ((Over.pullback (D.map ((v ≫ a) ≫ h₁))).obj X).hom := by
    rw [he₂]; exact property_hom_baseChange_comp _ D h₂ (v ≫ b) X hflat₂
  have ha : IsAffineHom ((Over.pullback (D.map ((v ≫ a) ≫ h₁))).obj X).hom := by
    rw [he₃]; exact property_hom_baseChange_comp _ D h₃ w X haff₃
  refine ⟨j, (v ≫ a) ≫ h₁, ?_, hs, hi⟩
  have : LocallyOfFinitePresentation ((Over.pullback (D.map ((v ≫ a) ≫ h₁))).obj X).hom :=
    (finitePresentation_pullback (D.map ((v ≫ a) ≫ h₁)) X hX).1
  exact Stacks.Morphisms.isFiniteLocallyFree_of_flat_of_universallyInjective _

private lemma exists_finiteLocallyFree_surjective_universallyInjective_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (X : Over c.pt) (hX : FinitePresentation X.hom)
    [Stacks.Morphisms.IsFiniteLocallyFree X.hom] [Surjective X.hom]
    [UniversallyInjective X.hom] :
    ∃ (i : I) (Y : Over (D.obj i)),
      FinitePresentation Y.hom ∧ Stacks.Morphisms.IsFiniteLocallyFree Y.hom ∧
        Surjective Y.hom ∧ UniversallyInjective Y.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Y) := by
  obtain ⟨i, Y, hY, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  have : Stacks.Morphisms.IsFiniteLocallyFree ((Over.pullback (c.π.app i)).obj Y).hom :=
    property_hom_of_iso _ e inferInstance
  have : Surjective ((Over.pullback (c.π.app i)).obj Y).hom :=
    property_hom_of_iso _ e inferInstance
  have : UniversallyInjective ((Over.pullback (c.π.app i)).obj Y).hom :=
    property_hom_of_iso _ e inferInstance
  obtain ⟨j, h, hfree, hsurj, hinj⟩ := exists_finiteLocallyFree_baseChange D c hc i Y hY
  exact ⟨j, (Over.pullback (D.map h)).obj Y, finitePresentation_pullback _ Y hY,
    hfree, hsurj, hinj, ⟨e ≪≫ pullbackConeCompIso D c h Y⟩⟩

/-- If an affine inverse limit of quasi-compact schemes is empty, one stage is empty. -/
@[ega "IV 8.3.6" "Nontrivial direction"]
private lemma exists_isEmpty_obj_of_isEmpty_limit
    {I : Type u} [Category.{u} I] [IsCofilteredOrEmpty I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)] [IsEmpty c.pt] :
    ∃ i : I, IsEmpty (D.obj i) := by
  classical
  by_contra h
  have : ∀ i : I, Nonempty (D.obj i) := fun i => by
    by_contra hi
    have : IsEmpty (D.obj i) := not_nonempty_iff.mp hi
    exact h ⟨i, this⟩
  obtain ⟨x⟩ := Scheme.nonempty_of_isLimit D c hc
  exact isEmptyElim x

/-- Finitely many conditions preserved by refinement hold at one common stage. -/
private lemma exists_common_refinement
    {I : Type u} [Category.{u} I] [IsCofiltered I] (i : I)
    {A : Type*} [Finite A] (P : ∀ j : I, (j ⟶ i) → A → Prop)
    (hP : ∀ (a : A) {j k : I} (f : j ⟶ i) (g : k ⟶ j),
      P j f a → P k (g ≫ f) a)
    (hex : ∀ a : A, ∃ (j : I) (f : j ⟶ i), P j f a) :
    ∃ (j : I) (f : j ⟶ i), ∀ a : A, P j f a := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hfin (s : Finset A) : ∃ (j : I) (f : j ⟶ i), ∀ a ∈ s, P j f a := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨j, f, hf⟩ := ih
      obtain ⟨k, g, hg⟩ := hex a
      obtain ⟨l, b, c, hbc⟩ := IsCofiltered.cospan f g
      refine ⟨l, b ≫ f, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hbc]
        exact hP x g c hg
      · exact hP x f b (hf x hx)
  obtain ⟨j, f, hf⟩ := hfin Finset.univ
  exact ⟨j, f, fun a => hf a (Finset.mem_univ a)⟩

/-- Smoothness of a finitely presented morphism to the limit descends to a stage. -/
private lemma exists_smooth_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) (hX : FinitePresentation X.hom)
    [Smooth ((Over.pullback (c.π.app i)).obj X).hom] :
    ∃ (j : I) (h : j ⟶ i), Smooth ((Over.pullback (D.map h)).obj X).hom :=
  exists_baseChange_of_terminal D c i X hX (@Smooth.{u}) inferInstance fun _ =>
    AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange D c i X
      (Over.mk (𝟙 (D.obj i))) _ hc

/-- Finitely many smooth strata become smooth at one common stage. -/
private lemma exists_smooth_baseChange_finite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) {A : Type*} [Finite A] (X : A → Over (D.obj i))
    (hX : ∀ a, FinitePresentation (X a).hom)
    [∀ a, Smooth ((Over.pullback (c.π.app i)).obj (X a)).hom] :
    ∃ (j : I) (h : j ⟶ i), ∀ a, Smooth ((Over.pullback (D.map h)).obj (X a)).hom := by
  apply exists_common_refinement i
    (fun j h a => Smooth ((Over.pullback (D.map h)).obj (X a)).hom)
  · intro a j k f g hf
    exact property_hom_baseChange_comp _ D f g (X a) hf
  · exact fun a => exists_smooth_baseChange D c hc i (X a) (hX a)

/-- A finitely presented closed subscheme of the limit descends as a closed subscheme. -/
private lemma exists_isClosedImmersion_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (X : Over c.pt) (hX : FinitePresentation X.hom)
    [IsClosedImmersion X.hom] :
    ∃ (i : I) (Y : Over (D.obj i)),
      FinitePresentation Y.hom ∧ IsClosedImmersion Y.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Y) := by
  obtain ⟨i, Y, hY, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc X hX
  have : MorphismProperty.RespectsIso (@IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨j, h, hh⟩ := exists_baseChange_of_terminal D c i Y hY (@IsClosedImmersion.{u})
    (property_hom_of_iso _ e inferInstance) fun _ =>
    AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit D c hc i Y
      (Over.mk (𝟙 (D.obj i))) _
  exact ⟨j, (Over.pullback (D.map h)).obj Y, finitePresentation_pullback _ Y hY, hh,
    ⟨e ≪≫ pullbackConeCompIso D c h Y⟩⟩

/-- A finite family of closed subschemes has models at a common stage. -/
private lemma exists_closedSubscheme_family_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {A : Type*} [Finite A] (Z : A → Over c.pt)
    (hZ : ∀ a, FinitePresentation (Z a).hom)
    [∀ a, IsClosedImmersion (Z a).hom] :
    ∃ (i : I) (Y : A → Over (D.obj i)),
      (∀ a, FinitePresentation (Y a).hom) ∧
      (∀ a, IsClosedImmersion (Y a).hom) ∧
      (∀ a, Nonempty (Z a ≅ (Over.pullback (c.π.app i)).obj (Y a))) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  choose i Y hfp hcl e using fun a => exists_isClosedImmersion_model D c hc (Z a) (hZ a)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let h (a : A) : j ⟶ i a := (hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨j, fun a => (Over.pullback (D.map (h a))).obj (Y a),
    fun a => finitePresentation_pullback _ (Y a) (hfp a), ?_, ?_⟩
  · intro a
    exact property_hom_baseChange _ _ _ (hcl a)
  · intro a
    exact ⟨(e a).some ≪≫ pullbackConeCompIso D c (h a) (Y a)⟩

/-- A morphism between finitely presented models exists at a later stage whenever it
exists after passage to the limit. -/
private lemma exists_hom_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom)
    (f : (Over.pullback (c.π.app i)).obj X ⟶ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (h : j ⟶ i),
      Nonempty ((Over.pullback (D.map h)).obj X ⟶ (Over.pullback (D.map h)).obj Y) := by
  obtain ⟨j, h, g, _⟩ := AlgebraicGeometry.exists_morphism_after_baseChange D c hc i X Y hX hY f
  exact ⟨j, h, ⟨g⟩⟩

/-- A finite family of arrows between fixed models exists at a common later stage. -/
private lemma exists_hom_baseChange_finite
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) {A : Type*} [Finite A] (X Y : A → Over (D.obj i))
    (hX : ∀ a, FinitePresentation (X a).hom)
    (hY : ∀ a, FinitePresentation (Y a).hom)
    (f : ∀ a, (Over.pullback (c.π.app i)).obj (X a) ⟶
      (Over.pullback (c.π.app i)).obj (Y a)) :
    ∃ (j : I) (h : j ⟶ i), ∀ a,
      Nonempty ((Over.pullback (D.map h)).obj (X a) ⟶
        (Over.pullback (D.map h)).obj (Y a)) := by
  apply exists_common_refinement i
    (fun j h a => Nonempty ((Over.pullback (D.map h)).obj (X a) ⟶
      (Over.pullback (D.map h)).obj (Y a)))
  · rintro a j k h g ⟨v⟩
    rw [D.map_comp]
    exact ⟨((Over.pullbackComp (D.map g) (D.map h)).app (X a)).hom ≫
      (Over.pullback (D.map g)).map v ≫
      ((Over.pullbackComp (D.map g) (D.map h)).app (Y a)).inv⟩
  · exact fun a => exists_hom_baseChange D c hc i (X a) (Y a) (hX a) (hY a) (f a)

/-- A finite chain of finitely presented closed subschemes descends as a chain. -/
private lemma exists_closedSubscheme_chain_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (t : ℕ) (Z : Fin (t + 1) → Over c.pt)
    (hZ : ∀ a, FinitePresentation (Z a).hom)
    [∀ a, IsClosedImmersion (Z a).hom]
    (k : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc) :
    ∃ (i : I) (Y : Fin (t + 1) → Over (D.obj i))
      (l : ∀ a : Fin t, Y a.succ ⟶ Y a.castSucc),
      (∀ a, FinitePresentation (Y a).hom) ∧
      (∀ a, IsClosedImmersion (Y a).hom) ∧
      (∀ a, IsClosedImmersion (l a).left) ∧
      (∀ a, Nonempty (Z a ≅ (Over.pullback (c.π.app i)).obj (Y a))) := by
  classical
  obtain ⟨i, Y, hY, hcl, e⟩ := exists_closedSubscheme_family_model D c hc Z hZ
  let v (a : Fin t) := (e a.succ).some.inv ≫ k a ≫ (e a.castSucc).some.hom
  obtain ⟨j, h, l⟩ := exists_hom_baseChange_finite D c hc i
    (fun a : Fin t => Y a.succ) (fun a => Y a.castSucc)
    (fun a => hY a.succ) (fun a => hY a.castSucc) v
  let Y' (a : Fin (t + 1)) := (Over.pullback (D.map h)).obj (Y a)
  have hcl' (a : Fin (t + 1)) : IsClosedImmersion (Y' a).hom :=
    property_hom_baseChange _ _ _ (hcl a)
  refine ⟨j, Y', fun a => (l a).some,
    fun a => finitePresentation_pullback _ (Y a) (hY a), hcl', ?_, ?_⟩
  · intro a
    have : IsClosedImmersion (Y' a.castSucc).hom := hcl' _
    have : IsClosedImmersion ((l a).some.left ≫ (Y' a.castSucc).hom) := by
      rw [Over.w]
      exact hcl' _
    exact IsClosedImmersion.of_comp_isClosedImmersion (l a).some.left (Y' a.castSucc).hom
  · intro a
    exact ⟨(e a).some ≪≫ pullbackConeCompIso D c h (Y a)⟩

private noncomputable def stageBaseChangeDiagram
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (i : I) (X : Over (D.obj i)) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget X.left

private noncomputable def stageBaseChangeCone
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (X : Over (D.obj i)) : Cone (stageBaseChangeDiagram D i X) :=
  (Over.pullback X.hom ⋙ Over.forget X.left).mapCone ((Over.conePost D i).obj c)

private noncomputable def stageBaseChangeConeIsLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i : I) (X : Over (D.obj i)) : IsLimit (stageBaseChangeCone D c i X) := by
  have : IsConnected (Over i) := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget X.left)
    (Over.isLimitConePost i hc)

private lemma stageBaseChangeDiagram_map_isAffineHom
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (X : Over (D.obj i)) {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((stageBaseChangeDiagram D i X).map f) :=
  MorphismProperty.overPullbackMap X.hom ((Over.post D).map f)
    (inferInstanceAs (IsAffineHom (D.map f.left)))

private lemma stageBaseChangeDiagram_obj_compact
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) [QuasiCompact X.hom] (j : Over i) :
    CompactSpace ((stageBaseChangeDiagram D i X).obj j) := by
  show CompactSpace (pullback (D.map j.hom) X.hom : Scheme)
  infer_instance

private lemma stageBaseChangeDiagram_obj_quasiSeparated
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) [QuasiSeparated X.hom] (j : Over i) :
    QuasiSeparatedSpace ((stageBaseChangeDiagram D i X).obj j) := by
  show QuasiSeparatedSpace (pullback (D.map j.hom) X.hom : Scheme)
  have : QuasiSeparated (pullback.fst (D.map j.hom) X.hom) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D.map j.hom) X.hom).flip
      (inferInstanceAs (QuasiSeparated X.hom))
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) X.hom)

/-- Emptiness of the base change of a quasi-compact scheme descends to a later stage. -/
private lemma exists_isEmpty_baseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (X : Over (D.obj i)) [QuasiCompact X.hom]
    [IsEmpty ((Over.pullback (c.π.app i)).obj X).left] :
    ∃ (j : I) (h : j ⟶ i), IsEmpty ((Over.pullback (D.map h)).obj X).left := by
  have : ∀ {j k : Over i} (f : j ⟶ k),
      IsAffineHom ((stageBaseChangeDiagram D i X).map f) :=
    fun _ => stageBaseChangeDiagram_map_isAffineHom D i X _
  have : ∀ j : Over i, CompactSpace ((stageBaseChangeDiagram D i X).obj j) :=
    stageBaseChangeDiagram_obj_compact D i X
  have : IsEmpty (pullback X.hom (c.π.app i) : Scheme) :=
    inferInstanceAs (IsEmpty ((Over.pullback (c.π.app i)).obj X).left)
  have : IsEmpty (stageBaseChangeCone D c i X).pt :=
    ⟨fun x => isEmptyElim ((pullbackSymmetry (c.π.app i) X.hom).hom x)⟩
  obtain ⟨j, hj⟩ := exists_isEmpty_obj_of_isEmpty_limit (stageBaseChangeDiagram D i X)
    (stageBaseChangeCone D c i X) (stageBaseChangeConeIsLimit D c hc i X)
  have : IsEmpty (pullback (D.map j.hom) X.hom : Scheme) := hj
  exact ⟨j.left, j.hom,
    ⟨fun x => isEmptyElim ((pullbackSymmetry X.hom (D.map j.hom)).hom x)⟩⟩

/-- The initial thickening and the empty final term of a finite closed filtration
can be preserved when descending the whole filtration. -/
private lemma exists_closedFiltration_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (t : ℕ) (Z : Fin (t + 1) → Over c.pt)
    (hZ : ∀ a, FinitePresentation (Z a).hom)
    [∀ a, IsClosedImmersion (Z a).hom]
    (k : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc)
    (hthick : Stacks.Thickenings.IsThickening (Z 0).hom) [IsEmpty (Z (Fin.last t)).left] :
    ∃ (i : I) (Y : Fin (t + 1) → Over (D.obj i))
      (l : ∀ a : Fin t, Y a.succ ⟶ Y a.castSucc),
      (∀ a, FinitePresentation (Y a).hom) ∧
      (∀ a, IsClosedImmersion (Y a).hom) ∧
      Stacks.Thickenings.IsThickening (Y 0).hom ∧ IsEmpty (Y (Fin.last t)).left ∧
      (∀ a, IsClosedImmersion (l a).left) ∧
      (∀ a, Nonempty (Z a ≅ (Over.pullback (c.π.app i)).obj (Y a))) := by
  classical
  obtain ⟨i, Y, l, hY, hcl, hl, e⟩ := exists_closedSubscheme_chain_model D c hc t Z hZ k
  have : Surjective ((Over.pullback (c.π.app i)).obj (Y 0)).hom :=
    property_hom_of_iso _ (e 0).some ⟨hthick.2⟩
  have : QuasiCompact (Y (Fin.last t)).hom := (hY _).2.1
  have : IsEmpty ((Over.pullback (c.π.app i)).obj (Y (Fin.last t))).left :=
    ⟨fun x => isEmptyElim ((e (Fin.last t)).some.inv.left x)⟩
  obtain ⟨j₁, h₁, hsurj⟩ := exists_surjective_baseChange D c hc i (Y 0) (hY 0)
  obtain ⟨j₂, h₂, hempty⟩ := exists_isEmpty_baseChange D c hc i (Y (Fin.last t))
  obtain ⟨j, a, b, hab⟩ := IsCofiltered.cospan h₁ h₂
  let h := a ≫ h₁
  let Y' (r : Fin (t + 1)) := (Over.pullback (D.map h)).obj (Y r)
  have hcl' (r : Fin (t + 1)) : IsClosedImmersion (Y' r).hom :=
    property_hom_baseChange _ _ _ (hcl r)
  refine ⟨j, Y', fun r => (Over.pullback (D.map h)).map (l r),
    fun r => finitePresentation_pullback _ (Y r) (hY r), hcl', ⟨hcl' 0, ?_⟩, ?_, ?_, ?_⟩
  · have hs : Surjective (Y' 0).hom := by
      exact property_hom_baseChange_comp _ D h₁ a (Y 0) hsurj
    exact hs.1
  · show IsEmpty ((Over.pullback (D.map (a ≫ h₁))).obj (Y (Fin.last t))).left
    rw [hab, D.map_comp]
    have : IsEmpty ((Over.pullback (D.map h₂)).obj (Y (Fin.last t))).left := hempty
    exact ⟨fun x => isEmptyElim
      (pullback.fst ((Over.pullback (D.map h₂)).obj (Y (Fin.last t))).hom (D.map b)
        (((Over.pullbackComp (D.map b) (D.map h₂)).app (Y (Fin.last t))).hom.left x))⟩
  · intro r
    exact MorphismProperty.overPullbackMap _ (l r) (hl r)
  · intro r
    exact ⟨(e r).some ≪≫ pullbackConeCompIso D c h (Y r)⟩

/-! ### The principal localizations at a prime

The inverse system of principal localizations `R_a`, `a ∉ 𝔭`, with limit `R_𝔭`, by which the
stratification below is spread out from a generic point, together with the facts about it
that the spreading-out arguments of other files consume. -/

namespace PrincipalLocalization

/-- Denominators outside a prime, ordered so that later stages invert more elements. -/
abbrev Index {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :=
  StageFactor.Idx R p

/-- The principal localizations `R_a`, `a ∉ 𝔭`, as an inverse system of affine schemes. -/
noncomputable def diagram {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    (Index p)ᵒᵖ ⥤ Scheme.{u} :=
  (StageFactor.diag R p).op ⋙ Scheme.Spec

/-- The open immersion of a stage `Spec R_a` of the system into `Spec R`. -/
noncomputable def baseMap {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (i : (Index p)ᵒᵖ) : (diagram p).obj i ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (i.unop : R))))

/-- A stage of the system is an open subscheme of `Spec R`. -/
lemma baseMap_isOpenImmersion {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (i : (Index p)ᵒᵖ) : IsOpenImmersion (baseMap p i) := by
  dsimp [baseMap]
  exact IsOpenImmersion.of_isLocalization (i.unop : R)

/-- The transition morphisms of the system are affine. -/
theorem diagram_map_isAffine {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {i j : (Index p)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((diagram p).map f) := by
  dsimp [diagram]
  infer_instance

private theorem diagram_obj_compact
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (i : (Index p)ᵒᵖ) :
    CompactSpace ((diagram p).obj i) := by
  show CompactSpace (Spec (.of (Localization.Away (i.unop : R))))
  infer_instance

private theorem diagram_obj_quasiSeparated
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (i : (Index p)ᵒᵖ) :
    QuasiSeparatedSpace ((diagram p).obj i) := by
  show QuasiSeparatedSpace (Spec (.of (Localization.Away (i.unop : R))))
  infer_instance

/-- The cone over the system with vertex `Spec R_𝔭`. -/
noncomputable abbrev cone {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Cone (diagram p) where
  pt := Spec (.of (Localization.AtPrime p))
  π := (Scheme.Spec.mapCone (StageFactor.cocp R p).op).π

/-- The projection of `Spec R_𝔭` to a stage followed by its inclusion into `Spec R` is the
localization morphism. -/
lemma cone_comp_baseMap {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (i : (Index p)ᵒᵖ) :
    (cone p).π.app i ≫ baseMap p i =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) := by
  show Spec.map (CommRingCat.ofHom (StageFactor.leg R p i.unop)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (i.unop : R)))) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact StageFactor.leg_algebraMap R p i.unop r

/-- The inclusions of the stages into `Spec R` are compatible with the transition morphisms. -/
lemma baseMap_naturality {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {i j : (Index p)ᵒᵖ} (h : i ⟶ j) :
    (diagram p).map h ≫ baseMap p j = baseMap p i := by
  show Spec.map (CommRingCat.ofHom (StageFactor.trans R p j.unop i.unop h.unop.le)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (j.unop : R)))) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact StageFactor.trans_algebraMap R p j.unop i.unop h.unop.le r

/-- Every stage contains the point `𝔭`. -/
lemma baseMap_mem_range {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (i : (Index p.asIdeal)ᵒᵖ) : p ∈ Set.range (baseMap p.asIdeal i) := by
  let q : Spec (.of (Localization.AtPrime p.asIdeal)) :=
    IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)
  refine ⟨(cone p.asIdeal).π.app i q, ?_⟩
  show ((cone p.asIdeal).π.app i ≫
    baseMap p.asIdeal i) q = p
  rw [cone_comp_baseMap]
  exact PrimeSpectrum.ext
    (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal)

/-- `Spec R_𝔭` is the limit of the principal localizations `Spec R_a`, `a ∉ 𝔭`. -/
noncomputable def cone_isLimit {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsLimit (cone p) :=
  isLimitOfPreserves Scheme.Spec (StageFactor.cocpIsColimit R p).op

end PrincipalLocalization

private theorem genericLocalization_exists_finiteLocallyFree_cover_model
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (X : Over (Spec (.of (Localization.AtPrime p))))
    (hX : FinitePresentation X.hom)
    [Stacks.Morphisms.IsFiniteLocallyFree X.hom] [Surjective X.hom]
    [UniversallyInjective X.hom] :
    ∃ (i : (PrincipalLocalization.Index p)ᵒᵖ)
      (Y : Over ((PrincipalLocalization.diagram p).obj i)),
      FinitePresentation Y.hom ∧ Stacks.Morphisms.IsFiniteLocallyFree Y.hom ∧
        Surjective Y.hom ∧ UniversallyInjective Y.hom ∧
        Nonempty (X ≅ (Over.pullback ((PrincipalLocalization.cone p).π.app i)).obj Y) := by
  let I := ULiftHom.{u} (PrincipalLocalization.Index p)ᵒᵖ
  let F : I ⥤ (PrincipalLocalization.Index p)ᵒᵖ := ULiftHom.down
  have : IsCofiltered I := IsCofiltered.of_equivalence ULiftHom.equiv
  have : F.Initial := Functor.initial_of_adjunction ULiftHom.equiv.symm.toAdjunction
  let D := F ⋙ PrincipalLocalization.diagram p
  let c := (PrincipalLocalization.cone p).whisker F
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv F (PrincipalLocalization.cone p)).symm
      (PrincipalLocalization.cone_isLimit p)
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h) := fun h =>
    PrincipalLocalization.diagram_map_isAffine p (F.map h)
  have : ∀ i : I, CompactSpace (D.obj i) := fun i =>
    PrincipalLocalization.diagram_obj_compact p (F.obj i)
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun i =>
    PrincipalLocalization.diagram_obj_quasiSeparated p (F.obj i)
  let X' : Over c.pt := X
  have : Stacks.Morphisms.IsFiniteLocallyFree X'.hom := ‹Stacks.Morphisms.IsFiniteLocallyFree X.hom›
  have : Surjective X'.hom := ‹Surjective X.hom›
  have : UniversallyInjective X'.hom := ‹UniversallyInjective X.hom›
  obtain ⟨i, Y, hfp, hfree, hsurj, hinj, he⟩ :=
    exists_finiteLocallyFree_surjective_universallyInjective_model D c hc X' hX
  exact ⟨F.obj i, Y, hfp, hfree, hsurj, hinj, he⟩

/-- Constructible subsets of a spectral space are quasi-compact. -/
private lemma isCompact_of_isConstructible
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [QuasiSeparatedSpace T]
    [PrespectralSpace T] [QuasiSober T] {s : Set T} (hs : Topology.IsConstructible s) :
    IsCompact s := by
  let e : WithConstructibleTopology T ≃ T := WithTopology.equiv _ _
  have he : Continuous e := PrespectralSpace.isTopologicalBasis.continuous_iff.mpr fun _ hU =>
    WithConstructibleTopology.isOpen_iff.mpr (hU.2.isOpen_constructibleTopology_of_isOpen hU.1)
  have hclosed : IsClosed (e ⁻¹' s) := by
    apply WithConstructibleTopology.isClosed_iff.mpr
    show @IsClosed T (constructibleTopology T) s
    apply (@isOpen_compl_iff T s (constructibleTopology T)).mp
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem hs.compl
  simpa only [Set.image_preimage_eq _ e.surjective] using hclosed.isCompact.image he

/-- The open complement of a finitely presented closed subscheme is quasi-compact. -/
private lemma isCompact_compl_range
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : Z ⟶ X) [IsClosedImmersion j] [LocallyOfFinitePresentation j] :
    IsCompact (Set.range j)ᶜ := by
  refine isCompact_of_isConstructible (.compl ?_)
  simpa only [Set.image_univ] using
    (j.isLocallyConstructible_image Topology.IsLocallyConstructible.univ).isConstructible

/-- The locally closed difference of two closed subschemes, viewed in the first one. -/
private def stratumOpen {X Y Z : Scheme.{u}} (j : Y ⟶ X) (k : Z ⟶ X)
    [IsClosedImmersion k] : Y.Opens :=
  j ⁻¹ᵁ ⟨(Set.range k)ᶜ, k.isClosedEmbedding.isClosed_range.isOpen_compl⟩

private lemma stratumOpen_finitePresentation
    {X Y Z S : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : Y ⟶ X) (k : Z ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion j] [IsClosedImmersion k]
    (hj : FinitePresentation j) (hk : FinitePresentation k)
    (hf : FinitePresentation f) :
    FinitePresentation ((stratumOpen j k).ι ≫ j ≫ f) := by
  have : LocallyOfFinitePresentation j := hj.1
  have : LocallyOfFinitePresentation k := hk.1
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated j
  have hW : IsCompact (stratumOpen j k : Set Y) :=
    QuasiCompact.isCompact_preimage _
      k.isClosedEmbedding.isClosed_range.isOpen_compl (isCompact_compl_range k)
  have : CompactSpace (stratumOpen j k).toScheme := isCompact_iff_compactSpace.mp hW
  have : QuasiCompact (stratumOpen j k).ι := quasiCompact_of_compactSpace _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma range_of_isPullback
    {X Y Z T : Scheme.{u}} {a : T ⟶ Z} {j' : T ⟶ Y} {j : Z ⟶ X} {q : Y ⟶ X}
    (sq : IsPullback a j' j q) : Set.range j' = q ⁻¹' Set.range j := by
  rw [← sq.isoPullback_hom_snd]
  show Set.range (pullback.snd j q ∘ sq.isoPullback.hom) = _
  rw [Set.range_comp, sq.isoPullback.hom.surjective.range_eq, Set.image_univ]
  exact Scheme.Pullback.range_snd _ _

private lemma stratumOpen_baseChange
    {X X' Y Y' Z Z' : Scheme.{u}}
    (j : Y ⟶ X) (k : Z ⟶ X) (j' : Y' ⟶ X') (k' : Z' ⟶ X')
    [IsClosedImmersion k] [IsClosedImmersion k']
    (a : Y' ⟶ Y) (b : Z' ⟶ Z) (q : X' ⟶ X)
    (hj : a ≫ j = j' ≫ q) (hk : IsPullback b k' k q) :
    stratumOpen j' k' = a ⁻¹ᵁ stratumOpen j k := by
  ext x
  show j' x ∉ Set.range k' ↔ j (a x) ∉ Set.range k
  rw [range_of_isPullback hk]
  show q (j' x) ∉ Set.range k ↔ j (a x) ∉ Set.range k
  rw [← Scheme.Hom.comp_apply, ← hj, Scheme.Hom.comp_apply]

private lemma isPullback_of_overIso
    {S T : Scheme.{u}} (q : T ⟶ S) (Y : Over S) (Z : Over T)
    (e : Z ≅ (Over.pullback q).obj Y) :
    IsPullback (e.hom.left ≫ pullback.fst Y.hom q) Z.hom Y.hom q := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget T).mapIso e) rfl (Over.w e.hom)
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z => z ≫ q) (Over.w e.hom)

private lemma property_pullback_of_isPullback
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z T : Scheme.{u}} {a : T ⟶ Z} {j' : T ⟶ Y} {j : Z ⟶ X} {q : Y ⟶ X}
    (sq : IsPullback a j' j q) (h : P j') : P (pullback.snd j q) := by
  rw [← sq.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr h

/-- Smoothness on the inverse image of an open subset is exactly the smoothness needed
for applying smooth descent to the restricted model. -/
private lemma smooth_pullback_restriction
    {S T X Y : Scheme.{u}} (q : T ⟶ S) (f : X ⟶ S) (g : Y ⟶ T)
    (a : Y ⟶ X) (sq : IsPullback a g f q) (W : X.Opens)
    (h : Smooth ((a ⁻¹ᵁ W).ι ≫ g)) :
    Smooth (pullback.snd (W.ι ≫ f) q) := by
  exact property_pullback_of_isPullback _ ((isPullback_morphismRestrict a W).paste_vert sq) h

private lemma property_of_isPullback_of_pullback
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z T : Scheme.{u}} {a : T ⟶ Z} {j' : T ⟶ Y} {j : Z ⟶ X} {q : Y ⟶ X}
    (sq : IsPullback a j' j q) (h : P (pullback.snd j q)) : P j' := by
  rw [← sq.isoPullback_hom_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr h

/-- Descend a finite closed filtration, and then make its finitely many open strata smooth
at one common stage of a cartesian inverse system. -/
private lemma exists_smooth_closedFiltration_model
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (c : Cone D) (d : Cone E)
    (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (E.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, CompactSpace (E.obj i)] [∀ i : I, QuasiSeparatedSpace (E.obj i)]
    (φ : D ⟶ E) (f : c.pt ⟶ d.pt)
    (hφ : ∀ i, FinitePresentation (φ.app i))
    (hsq : ∀ i, IsPullback (c.π.app i) f (φ.app i) (d.π.app i))
    (htrans : ∀ {i j} (h : i ⟶ j),
      IsPullback (D.map h) (φ.app i) (φ.app j) (E.map h))
    (t : ℕ) (Z : Fin (t + 1) → Over c.pt)
    (hZ : ∀ a, FinitePresentation (Z a).hom)
    [∀ a, IsClosedImmersion (Z a).hom]
    (k : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc)
    (hthick : Stacks.Thickenings.IsThickening (Z 0).hom) [IsEmpty (Z (Fin.last t)).left]
    (hsm : ∀ a : Fin t, Smooth
      ((stratumOpen (Z a.castSucc).hom (Z a.succ).hom).ι ≫ (Z a.castSucc).hom ≫ f)) :
    ∃ (i : I) (Y : Fin (t + 1) → Over (D.obj i))
      (l : ∀ a : Fin t, Y a.succ ⟶ Y a.castSucc),
      (∀ a, FinitePresentation (Y a).hom) ∧
      (∀ a, IsClosedImmersion (Y a).hom) ∧
      Stacks.Thickenings.IsThickening (Y 0).hom ∧ IsEmpty (Y (Fin.last t)).left ∧
      (∀ a, IsClosedImmersion (l a).left) ∧
      (∀ a : Fin t, ∀ (hcl : IsClosedImmersion (Y a.succ).hom), Smooth
        ((@stratumOpen _ _ _ (Y a.castSucc).hom (Y a.succ).hom hcl).ι ≫
          (Y a.castSucc).hom ≫ φ.app i)) := by
  classical
  obtain ⟨i, Y, l, hY, hcl, hth, hempty, hl, e⟩ :=
    exists_closedFiltration_model D c hc t Z hZ k hthick
  have : ∀ a, IsClosedImmersion (Y a).hom := hcl
  let W (a : Fin t) := stratumOpen (Y a.castSucc).hom (Y a.succ).hom
  let T (a : Fin t) : Over (E.obj i) := Over.mk ((W a).ι ≫ (Y a.castSucc).hom ≫ φ.app i)
  have hT (a : Fin t) : FinitePresentation (T a).hom :=
    stratumOpen_finitePresentation _ _ _ (hY _) (hY _) (hφ i)
  let q (a : Fin (t + 1)) := (e a).some.hom.left ≫ pullback.fst (Y a).hom (c.π.app i)
  have sq (a : Fin (t + 1)) :
      IsPullback (q a) (Z a).hom (Y a).hom (c.π.app i) :=
    isPullback_of_overIso _ (Y a) (Z a) (e a).some
  have hW (a : Fin t) :
      stratumOpen (Z a.castSucc).hom (Z a.succ).hom = q a.castSucc ⁻¹ᵁ W a :=
    stratumOpen_baseChange _ _ _ _ _ _ _ (sq a.castSucc).w (sq a.succ)
  have (a : Fin t) : Smooth ((Over.pullback (d.π.app i)).obj (T a)).hom := by
    apply smooth_pullback_restriction _ _ _ _ ((sq a.castSucc).paste_vert (hsq i)) (W a)
    rw [← hW a]
    exact hsm a
  obtain ⟨j, h, hj⟩ := exists_smooth_baseChange_finite E d hd i T hT
  let Y' (a : Fin (t + 1)) := (Over.pullback (D.map h)).obj (Y a)
  have hcl' (a : Fin (t + 1)) : IsClosedImmersion (Y' a).hom :=
    property_hom_baseChange _ _ _ (hcl a)
  refine ⟨j, Y', fun a => (Over.pullback (D.map h)).map (l a),
    fun a => finitePresentation_pullback _ (Y a) (hY a), hcl', ?_, ?_, ?_, ?_⟩
  · have : Surjective (Y 0).hom := ⟨hth.2⟩
    have hs : Surjective (Y' (0 : Fin (t + 1))).hom :=
      property_hom_baseChange _ _ _ (inferInstanceAs (Surjective (Y 0).hom))
    exact ⟨hcl' 0, hs.1⟩
  · have : IsEmpty (Y (Fin.last t)).left := hempty
    exact ⟨fun x => isEmptyElim (pullback.fst (Y (Fin.last t)).hom (D.map h) x)⟩
  · intro a
    exact MorphismProperty.overPullbackMap _ (l a) (hl a)
  · intro a hclnext
    have hw : stratumOpen (Y' a.castSucc).hom (Y' a.succ).hom =
        pullback.fst (Y a.castSucc).hom (D.map h) ⁻¹ᵁ W a :=
      stratumOpen_baseChange _ _ _ _ _ _ _
        (pullback.condition) (IsPullback.of_hasPullback _ _)
    rw [hw]
    exact property_of_isPullback_of_pullback _
      ((isPullback_morphismRestrict _ (W a)).paste_vert
        ((IsPullback.of_hasPullback (Y a.castSucc).hom (D.map h)).paste_vert (htrans h)))
      (hj a)

private lemma isPullback_pullbackMap_fst
    {S X : Scheme.{u}} (f : X ⟶ S) {A B : Over S} (h : A ⟶ B) :
    IsPullback ((Over.pullback f).map h).left
      (pullback.fst A.hom f) (pullback.fst B.hom f) h.left := by
  apply ((IsPullback.of_hasPullback B.hom f).flip.paste_horiz_iff
    (by simp only [Over.pullback_map_left, pullback.lift_fst])).mp
  simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w h] using
    (IsPullback.of_hasPullback A.hom f).flip

private noncomputable def pullbackDiagramToBase
    {I : Type u} [Category.{u} I] {S X : Scheme.{u}}
    (F : I ⥤ Over S) (f : X ⟶ S) :
    F ⋙ Over.pullback f ⋙ Over.forget X ⟶ F ⋙ Over.forget S where
  app i := pullback.fst (F.obj i).hom f
  naturality i j h := by
    simp only [Over.pullback_map_left, pullback.lift_fst, Functor.comp_map, Over.forget_map]

/-- The cartesian system obtained by pulling a fixed finitely presented scheme back
along an inverse system admits descent of smooth closed filtrations. -/
private lemma exists_smooth_closedFiltration_overDiagram
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S X : Scheme.{u}}
    (F : I ⥤ Over S) (c : Cone F) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (F.map h).left]
    [∀ i : I, CompactSpace (F.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (F.obj i).left]
    (f : X ⟶ S) (hf : FinitePresentation f)
    (t : ℕ) (Z : Fin (t + 1) → Over ((Over.pullback f).obj c.pt).left)
    (hZ : ∀ a, FinitePresentation (Z a).hom)
    [∀ a, IsClosedImmersion (Z a).hom]
    (k : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc)
    (hthick : Stacks.Thickenings.IsThickening (Z 0).hom) [IsEmpty (Z (Fin.last t)).left]
    (hsm : ∀ a : Fin t, Smooth
      ((stratumOpen (Z a.castSucc).hom (Z a.succ).hom).ι ≫ (Z a.castSucc).hom ≫
        pullback.fst c.pt.hom f)) :
    ∃ (i : I) (Y : Fin (t + 1) → Over ((Over.pullback f).obj (F.obj i)).left)
      (l : ∀ a : Fin t, Y a.succ ⟶ Y a.castSucc),
      (∀ a, FinitePresentation (Y a).hom) ∧
      (∀ a, IsClosedImmersion (Y a).hom) ∧
      Stacks.Thickenings.IsThickening (Y 0).hom ∧ IsEmpty (Y (Fin.last t)).left ∧
      (∀ a, IsClosedImmersion (l a).left) ∧
      (∀ a : Fin t, ∀ (hcl : IsClosedImmersion (Y a.succ).hom), Smooth
        ((@stratumOpen _ _ _ (Y a.castSucc).hom (Y a.succ).hom hcl).ι ≫
          (Y a.castSucc).hom ≫ pullback.fst (F.obj i).hom f)) := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  let E := F ⋙ Over.forget S
  let D := F ⋙ Over.pullback f ⋙ Over.forget X
  let cD := (Over.pullback f ⋙ Over.forget X).mapCone c
  let cE := (Over.forget S).mapCone c
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (E.map h) := fun h =>
    inferInstanceAs (IsAffineHom (F.map h).left)
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h) := fun h =>
    MorphismProperty.overPullbackMap f (F.map h) inferInstance
  have : ∀ i : I, CompactSpace (E.obj i) := fun i =>
    inferInstanceAs (CompactSpace (F.obj i).left)
  have : ∀ i : I, QuasiSeparatedSpace (E.obj i) := fun i =>
    inferInstanceAs (QuasiSeparatedSpace (F.obj i).left)
  have : ∀ i : I, CompactSpace (D.obj i) := fun i =>
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (F.obj i).hom f)
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i) := fun i =>
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (F.obj i).hom f)
  exact exists_smooth_closedFiltration_model D E cD cE
    (isLimitOfPreserves _ hc) (isLimitOfPreserves _ hc)
    (pullbackDiagramToBase F f) (pullback.fst c.pt.hom f)
    (fun i => by
      show FinitePresentation (pullback.fst (F.obj i).hom f)
      exact ⟨inferInstance, inferInstance, inferInstance⟩)
    (fun i => isPullback_pullbackMap_fst f (c.π.app i))
    (fun h => isPullback_pullbackMap_fst f (F.map h)) t Z hZ k hthick hsm

private lemma stratumOpen_comp_iso
    {A B Y Z : Scheme.{u}} (j : Y ⟶ A) (k : Z ⟶ A)
    [IsClosedImmersion k] (e : A ≅ B) :
    stratumOpen (j ≫ e.hom) (k ≫ e.hom) = stratumOpen j k := by
  ext x
  show e.hom (j x) ∉ Set.range (e.hom ∘ k) ↔ j x ∉ Set.range k
  rw [Set.range_comp, e.hom.injective.mem_set_image]

private lemma finitePresentation_comp_iso
    {A B X : Scheme.{u}} (j : X ⟶ A) (hj : FinitePresentation j)
    (e : A ≅ B) : FinitePresentation (j ≫ e.hom) := by
  have : LocallyOfFinitePresentation j := hj.1
  have : QuasiCompact j := hj.2.1
  have : QuasiSeparated j := hj.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Canonical identification of two iterated base changes with isomorphic total bases. -/
private lemma exists_pullbackTowerIso
    {X S K K₀ P V : Scheme.{u}} (f : X ⟶ S) (ξ : K₀ ⟶ S) (g : K ⟶ K₀)
    (p : P ⟶ V) (v : V ⟶ S) (e : K ≅ P) (he : e.hom ≫ p ≫ v = g ≫ ξ) :
    ∃ a : pullback (pullback.snd f ξ) g ≅ pullback p (pullback.snd f v),
      a.hom ≫ pullback.fst p (pullback.snd f v) = pullback.snd (pullback.snd f ξ) g ≫ e.hom := by
  let e₀ : Over.mk (g ≫ ξ) ≅ Over.mk (p ≫ v) := Over.isoMk e he
  let e₁ := (Over.forget X).mapIso ((Over.pullback f).mapIso e₀)
  let a := pullbackLeftPullbackSndIso f ξ g ≪≫ pullbackSymmetry f (g ≫ ξ) ≪≫
    e₁ ≪≫ pullbackSymmetry (p ≫ v) f ≪≫
    (pullbackLeftPullbackSndIso f v p).symm ≪≫ pullbackSymmetry (pullback.snd f v) p
  refine ⟨a, ?_⟩
  simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_inv_snd_snd,
    pullbackSymmetry_hom_comp_snd]
  dsimp [e₁, e₀]
  simp only [Over.pullback_map_left, Over.mk_hom, Over.isoMk_hom_left, pullback.lift_fst]
  simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_hom_snd]

/-- A closed subscheme of a locally Noetherian scheme is cut out by a finite type ideal. -/
private theorem closedImmersion_idealSheaf_finiteType
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] :
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsFiniteType :=
  (finitePresentation_iff_isFiniteType_idealSheaf i).mp
    (AlgebraicGeometry.finitePresentation_of_finiteType i)

-- Converting the finite filtration to scheme arrows expands substantial subscheme data.
/-- Turn the field-valued stratification into a chain of closed subschemes. -/
private theorem field_stratification_as_schemes
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : Module.Finite k k') (_ : IsPurelyInseparable k k'),
      let g : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let Y : Scheme.{u} := pullback f g
      let p : Y ⟶ Spec (.of k') := pullback.snd f g
      ∃ (t : ℕ) (Z : Fin (t + 1) → Scheme.{u})
          (j : (i : Fin (t + 1)) → Z i ⟶ Y)
          (k : (i : Fin t) → Z i.succ ⟶ Z i.castSucc)
          (W : (i : Fin t) → (Z i.castSucc).Opens),
        (∀ i, IsClosedImmersion (j i)) ∧
        (∀ i, (Stacks.ClosedImmersion.idealSheaf (j i).toLRSHom.toShHom).IsFiniteType) ∧
        Stacks.Thickenings.IsThickening (j 0) ∧
        IsEmpty (Z (Fin.last t)) ∧
        (∀ i : Fin t, IsClosedImmersion (k i)) ∧
        (∀ i : Fin t, k i ≫ j i.castSucc = j i.succ) ∧
        (∀ (i : Fin t) (x : Z i.castSucc),
          x ∈ W i ↔ j i.castSucc x ∉ Set.range (j i.succ)) ∧
        (∀ i : Fin t, Smooth ((W i).ι ≫ j i.castSucc ≫ p)) := by
  obtain ⟨k', hField, hAlg, hFinite, hPure, h⟩ :=
    AlgebraicGeometry.exists_finite_purelyInseparable_extension_smooth_stratification k f
  let : Field k' := hField
  let : Algebra k k' := hAlg
  let : Module.Finite k k' := hFinite
  let : IsPurelyInseparable k k' := hPure
  let g : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let Y : Scheme.{u} := pullback f g
  let p : Y ⟶ Spec (.of k') := pullback.snd f g
  obtain ⟨t, J, hzero, htop, hmono, hopen⟩ := h
  let Z : Fin (t + 1) → Scheme.{u} := fun i => (J i).subscheme
  let j : (i : Fin (t + 1)) → Z i ⟶ Y := fun i => (J i).subschemeι
  let k : (i : Fin t) → Z i.succ ⟶ Z i.castSucc :=
    fun i => (J i.castSucc).inclusion (hmono i)
  let W : (i : Fin t) → (Z i.castSucc).Opens := fun i => Classical.choose (hopen i)
  refine ⟨k', hField, hAlg, hFinite, hPure, ?_⟩
  dsimp
  refine ⟨t, Z, j, k, W, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [j]
    infer_instance
  · intro i
    exact closedImmersion_idealSheaf_finiteType (j i)
  · refine ⟨inferInstance, ?_⟩
    show Function.Surjective (j 0)
    rw [← Set.range_eq_univ, ← (j 0).isClosedEmbedding.isClosed_range.closure_eq,
      ← Scheme.Hom.support_ker]
    rw [show (j 0).ker = J 0 by simp [j], hzero,
      Scheme.IdealSheafData.vanishingIdeal_top]
    show ((Y.nilradical.support : Set Y) = Set.univ)
    exact congrArg (fun Z : TopologicalSpace.Closeds Y => (Z : Set Y))
      (Scheme.support_nilradical Y)
  · have hlast : J (Fin.last t) = ⊤ := by simpa [Fin.last] using htop
    show IsEmpty ((J (Fin.last t)).subscheme)
    rw [hlast]
    infer_instance
  · intro i
    dsimp [k]
    infer_instance
  · intro i
    dsimp [k, j]
    simp
  · intro i x
    have hmem := congrArg (fun s : Set (Z i.castSucc) => x ∈ s)
      (Classical.choose_spec (hopen i)).1
    have hrange : Set.range ((J i.succ).subschemeι) = (J i.succ).support :=
      Scheme.IdealSheafData.range_subschemeι (J i.succ)
    have hsupp (y : Y) :
        y ∈ (J i.succ).support ↔ y ∈ Set.range ((J i.succ).subschemeι) := by
      show y ∈ ((J i.succ).support : Set Y) ↔ _
      rw [← hrange]
    exact (Iff.of_eq hmem).trans (not_congr (hsupp (j i.castSucc x)))
  · intro i
    exact (Classical.choose_spec (hopen i)).2

private theorem pureInseparable_field_specMap_good
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [IsPurelyInseparable k K] :
    Function.Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Stacks.Morphisms.IsFiniteLocallyFree (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact ⟨Classical.choice (inferInstance : Nonempty (Spec (.of K))),
      Subsingleton.elim _ _⟩
  · apply ((AlgebraicGeometry.tfae_universallyInjective g).out 2 1).mp
    intro L _ a b hab
    obtain ⟨a, rfl⟩ := Spec.map_surjective a
    obtain ⟨b, rfl⟩ := Spec.map_surjective b
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply IsPurelyInseparable.injective_comp_algebraMap k K L
    have hcat : CommRingCat.ofHom (algebraMap k K) ≫ a =
        CommRingCat.ofHom (algebraMap k K) ≫ b := by
      apply Spec.map_injective
      simpa only [g, ← Spec.map_comp] using hab
    exact congrArg CommRingCat.Hom.hom hcat
  · have hfin : IsFinite g := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    have hflat : Flat g := by
      rw [Flat.SpecMap_iff]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance
    have hfp : LocallyOfFinitePresentation g := by
      rw [LocallyOfFinitePresentation.SpecMap_iff]
      show (algebraMap k K).FinitePresentation
      let : Module.FinitePresentation k K := Module.finitePresentation_of_finite k K
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).2
      ⟨hfin, hflat, hfp⟩

private lemma finiteLocallyFree_finitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree f] : FinitePresentation f := by
  obtain ⟨hfinite, hflat, hfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      inferInstance
  have : IsFinite f := hfinite
  exact ⟨hfp, inferInstance, inferInstance⟩

namespace PrincipalLocalization

/-- A finite purely inseparable extension `K` of the fraction field `R_𝔭` at a minimal point
admits an exact model by a finite locally free universal injection over some stage of the
system: the base change of the model to `Spec R_𝔭` is `Spec K`. -/
theorem exists_purelyInseparable_cover {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (hp : IsField (Localization.AtPrime p)) (K : Type u) [Field K]
    [Algebra (Localization.AtPrime p) K] [Module.Finite (Localization.AtPrime p) K]
    (hpure : letI := hp.toField; IsPurelyInseparable (Localization.AtPrime p) K) :
    let g := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) K))
    ∃ (i : (Index p)ᵒᵖ) (Y : Over ((diagram p).obj i)),
      FinitePresentation Y.hom ∧ Stacks.Morphisms.IsFiniteLocallyFree Y.hom ∧
        Surjective Y.hom ∧ UniversallyInjective Y.hom ∧
        Nonempty (Over.mk g ≅ (Over.pullback ((cone p).π.app i)).obj Y) := by
  let := hp.toField
  have : IsPurelyInseparable (Localization.AtPrime p) K := hpure
  let g := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) K))
  obtain ⟨hsurj, hinj, hfree⟩ := pureInseparable_field_specMap_good (Localization.AtPrime p) K
  have : Stacks.Morphisms.IsFiniteLocallyFree g := hfree
  have : Surjective g := ⟨hsurj⟩
  have : UniversallyInjective g := hinj
  have : Stacks.Morphisms.IsFiniteLocallyFree (Over.mk g).hom := hfree
  have : Surjective (Over.mk g).hom := ⟨hsurj⟩
  have : UniversallyInjective (Over.mk g).hom := hinj
  exact genericLocalization_exists_finiteLocallyFree_cover_model p (Over.mk g)
    (finiteLocallyFree_finitePresentation g)

end PrincipalLocalization

/-- A generic point of an irreducible component of a reduced scheme has an affine open
neighbourhood `Spec R` in which it is a prime `𝔭` with `R_𝔭` a field. -/
theorem exists_affine_genericPoint_isField
    {S : Scheme.{u}} [IsReduced S] (η : S)
    (hη : ∃ C ∈ irreducibleComponents S, IsGenericPoint η C) :
    ∃ (R : CommRingCat.{u}) (α : Spec R ⟶ S) (_ : IsOpenImmersion α)
      (p : PrimeSpectrum R), α p = η ∧ IsField (Localization.AtPrime p.asIdeal) := by
  obtain ⟨R, α, hα, p, rfl⟩ := Scheme.exists_Spec_apply_eq η
  have : IsOpenImmersion α := hα
  obtain ⟨C, hC, hgen⟩ := hη
  have hfield : IsField (S.presheaf.stalk (α p)) :=
    isField_stalk_of_closure_mem_irreducibleComponents S (α p) (hgen.def.symm ▸ hC)
  have hfield' : IsField ((Spec R).presheaf.stalk p) :=
    (asIso (α.stalkMap p)).commRingCatIsoToRingEquiv.symm.isField hfield
  exact ⟨R, α, hα, p, rfl, (Spec.stalkIso R p).commRingCatIsoToRingEquiv.symm.isField hfield'⟩

/-- A generic point of an irreducible component of a reduced scheme has an affine open
neighbourhood `Spec R` in which it is a prime `𝔭` with `R_𝔭` a field. -/
alias exists_affine_isField_localization_of_isGenericPoint := exists_affine_genericPoint_isField

end Stacks.SmoothStrata

namespace AlgebraicGeometry

open Stacks.SmoothStrata

/-- **Stacks Project, Tag 0H43.** Smooth stratification near the generic
point of an irreducible component of a reduced base. -/
@[stacks 0H43]
theorem exists_smooth_stratification_at_generic_point
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
    [IsReduced S] (η : S)
    (hη : ∃ C ∈ irreducibleComponents S, IsGenericPoint η C) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      Function.Surjective g ∧ UniversallyInjective g ∧
        Stacks.Morphisms.IsFiniteLocallyFree g ∧
        ∃ (t : ℕ) (Z : Fin (t + 1) → Scheme.{u})
            (j : (i : Fin (t + 1)) → Z i ⟶ pullback f (g ≫ U.ι))
            (k : (i : Fin t) → Z i.succ ⟶ Z i.castSucc)
            (W : (i : Fin t) → (Z i.castSucc).Opens),
          (∀ i, IsClosedImmersion (j i)) ∧
          (∀ i, (Stacks.ClosedImmersion.idealSheaf (j i).toLRSHom.toShHom).IsFiniteType) ∧
          Stacks.Thickenings.IsThickening (j 0) ∧
          IsEmpty (Z (Fin.last t)) ∧
          (∀ i : Fin t, IsClosedImmersion (k i)) ∧
          (∀ i : Fin t, k i ≫ j i.castSucc = j i.succ) ∧
          (∀ (i : Fin t) (x : Z i.castSucc),
            x ∈ W i ↔ j i.castSucc x ∉ Set.range (j i.succ)) ∧
          (∀ i : Fin t, Smooth ((W i).ι ≫ j i.castSucc ≫
            pullback.snd f (g ≫ U.ι))) := by
  obtain ⟨R, α, hα, p, hpη, hp⟩ := exists_affine_genericPoint_isField η hη
  have : IsOpenImmersion α := hα
  let := hp.toField
  let ξ : Spec (.of (Localization.AtPrime p.asIdeal)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))) ≫ α
  let fη : pullback f ξ ⟶ Spec (.of (Localization.AtPrime p.asIdeal)) := pullback.snd f ξ
  have hfiber := finitePresentation_pullback ξ (Over.mk f) hf
  have : LocallyOfFinitePresentation fη := hfiber.1
  have : QuasiCompact fη := hfiber.2.1
  have : QuasiSeparated fη := hfiber.2.2
  obtain ⟨K, hK, hAlg, hFinite, hPure, hstrata⟩ :=
    field_stratification_as_schemes (Localization.AtPrime p.asIdeal) fη
  let : Field K := hK
  let : Algebra (Localization.AtPrime p.asIdeal) K := hAlg
  have : Module.Finite (Localization.AtPrime p.asIdeal) K := hFinite
  have : IsPurelyInseparable (Localization.AtPrime p.asIdeal) K := hPure
  obtain ⟨i, V, hVfp, hVfree, hVsurj, hVinj, ⟨eV⟩⟩ :=
    PrincipalLocalization.exists_purelyInseparable_cover p.asIdeal hp K hPure
  classical
  let I := ULiftHom.{u} (PrincipalLocalization.Index p.asIdeal)ᵒᵖ
  let F₀ : I ⥤ (PrincipalLocalization.Index p.asIdeal)ᵒᵖ :=
    { obj A := A
      map h := h.down }
  have : IsCofiltered I := IsCofiltered.of_equivalence ULiftHom.equiv
  have : F₀.Initial := Functor.initial_of_adjunction ULiftHom.equiv.symm.toAdjunction
  let D₀ := F₀ ⋙ PrincipalLocalization.diagram p.asIdeal
  let c₀ := (PrincipalLocalization.cone p.asIdeal).whisker F₀
  have hc₀ : IsLimit c₀ :=
    (Functor.Initial.isLimitWhiskerEquiv F₀ (PrincipalLocalization.cone p.asIdeal)).symm
      (PrincipalLocalization.cone_isLimit p.asIdeal)
  let i₀ : I := i
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (D₀.map h) :=
    fun h => PrincipalLocalization.diagram_map_isAffine p.asIdeal (F₀.map h)
  have : ∀ i : I, CompactSpace (D₀.obj i) :=
    fun i => PrincipalLocalization.diagram_obj_compact p.asIdeal (F₀.obj i)
  have : ∀ i : I, QuasiSeparatedSpace (D₀.obj i) :=
    fun i => PrincipalLocalization.diagram_obj_quasiSeparated p.asIdeal (F₀.obj i)
  have : QuasiCompact V.hom := hVfp.2.1
  have : QuasiSeparated V.hom := hVfp.2.2
  let F : Over i₀ ⥤ Over V.left := Over.post D₀ ⋙ Over.pullback V.hom
  let cF : Cone F := (Over.pullback V.hom).mapCone ((Over.conePost D₀ i₀).obj c₀)
  have hcF : IsLimit cF := isLimitOfPreserves _ (Over.isLimitConePost i₀ hc₀)
  have : ∀ {a b : Over i₀} (h : a ⟶ b), IsAffineHom (F.map h).left :=
    fun h => MorphismProperty.overPullbackMap V.hom ((Over.post D₀).map h)
      (inferInstanceAs (IsAffineHom (D₀.map h.left)))
  have : ∀ a : Over i₀, CompactSpace (F.obj a).left :=
    stageBaseChangeDiagram_obj_compact D₀ i₀ V
  have : ∀ a : Over i₀, QuasiSeparatedSpace (F.obj a).left :=
    stageBaseChangeDiagram_obj_quasiSeparated D₀ i₀ V
  let β := PrincipalLocalization.baseMap p.asIdeal i ≫ α
  let v := V.hom ≫ β
  let fV := pullback.snd f v
  let gK := Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
  let eK : Spec (.of K) ≅ cF.pt.left :=
    (Over.forget _).mapIso eV ≪≫ pullbackSymmetry V.hom (c₀.π.app i₀)
  have heK : eK.hom ≫ cF.pt.hom ≫ v = gK ≫ ξ := by
    show ((Over.forget _).mapIso eV ≪≫
      pullbackSymmetry V.hom (c₀.π.app i₀)).hom ≫
      pullback.snd (c₀.π.app i₀) V.hom ≫ V.hom ≫ β = _
    simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc,
      pullbackSymmetry_hom_comp_snd_assoc]
    show eV.hom.left ≫ pullback.fst V.hom (c₀.π.app i₀) ≫ V.hom ≫ β = _
    rw [pullback.condition_assoc, ← Category.assoc]
    rw [show eV.hom.left ≫ pullback.snd V.hom (c₀.π.app i₀) = gK from Over.w eV.hom]
    show gK ≫ (PrincipalLocalization.cone p.asIdeal).π.app i ≫
      PrincipalLocalization.baseMap p.asIdeal i ≫ α = gK ≫ ξ
    rw [← Category.assoc ((PrincipalLocalization.cone p.asIdeal).π.app i),
      PrincipalLocalization.cone_comp_baseMap]
  obtain ⟨eX, heX⟩ := exists_pullbackTowerIso f ξ gK cF.pt.hom v eK heK
  obtain ⟨t, Z, jZ, kZ, W, hclZ, hftZ, hthZ, hemptyZ, hkZ, hcommZ, hWZ, hsmZ⟩ := hstrata
  have : ∀ a, IsClosedImmersion (jZ a) := hclZ
  let Z' (a : Fin (t + 1)) : Over ((Over.pullback fV).obj cF.pt).left :=
    Over.mk (jZ a ≫ eX.hom)
  have hfpZ (a : Fin (t + 1)) : FinitePresentation (jZ a) :=
    (finitePresentation_iff_isFiniteType_idealSheaf (jZ a)).mpr (hftZ a)
  have hfpZ' (a : Fin (t + 1)) : FinitePresentation (Z' a).hom :=
    finitePresentation_comp_iso _ (hfpZ a) eX
  have : ∀ a, IsClosedImmersion (Z' a).hom := fun a => by
    show IsClosedImmersion (jZ a ≫ eX.hom)
    infer_instance
  let k' (a : Fin t) : Z' a.succ ⟶ Z' a.castSucc :=
    Over.homMk (kZ a) (by dsimp [Z']; rw [← Category.assoc, hcommZ])
  have hthZ' : Stacks.Thickenings.IsThickening (Z' 0).hom :=
    ⟨inferInstance, eX.hom.surjective.comp hthZ.2⟩
  have : IsEmpty (Z' (Fin.last t)).left := hemptyZ
  have hsmZ' (a : Fin t) : Smooth
      ((stratumOpen (Z' a.castSucc).hom (Z' a.succ).hom).ι ≫ (Z' a.castSucc).hom ≫
        pullback.fst cF.pt.hom fV) := by
    have hw : stratumOpen (Z' a.castSucc).hom (Z' a.succ).hom = W a := by
      show stratumOpen (jZ a.castSucc ≫ eX.hom) (jZ a.succ ≫ eX.hom) = _
      rw [stratumOpen_comp_iso]
      ext x
      exact (hWZ a x).symm
    rw [hw]
    show Smooth ((W a).ι ≫ (jZ a.castSucc ≫ eX.hom) ≫ pullback.fst cF.pt.hom fV)
    rw [Category.assoc, heX]
    have : Smooth ((W a).ι ≫ jZ a.castSucc ≫ pullback.snd fη gK) := hsmZ a
    simpa only [Category.assoc] using
      (inferInstance : Smooth (((W a).ι ≫ jZ a.castSucc ≫ pullback.snd fη gK) ≫ eK.hom))
  obtain ⟨a, Y, l, hYfp, hYcl, hYth, hYempty, hl, hYsm⟩ :=
    exists_smooth_closedFiltration_overDiagram F cF hcF fV
      (finitePresentation_pullback v (Over.mk f) hf) t Z' hfpZ' k' hthZ' hsmZ'
  let β' := PrincipalLocalization.baseMap p.asIdeal (F₀.obj a.left) ≫ α
  have : IsOpenImmersion (PrincipalLocalization.baseMap p.asIdeal (F₀.obj a.left)) :=
    PrincipalLocalization.baseMap_isOpenImmersion p.asIdeal _
  have : IsOpenImmersion β' := inferInstance
  have hηU : η ∈ β'.opensRange := by
    obtain ⟨z, hz⟩ := PrincipalLocalization.baseMap_mem_range p (F₀.obj a.left)
    rw [← hpη]
    exact ⟨z, by
      change α (PrincipalLocalization.baseMap p.asIdeal (F₀.obj a.left) z) = α p; rw [hz]⟩
  let q := (F.obj a).hom
  let v' : (F.obj a).left ⟶ D₀.obj a.left := pullback.fst (D₀.map a.hom) V.hom
  let g : (F.obj a).left ⟶ β'.opensRange.toScheme := v' ≫ β'.isoOpensRange.hom
  have hg (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
      (hV : P V.hom) : P g :=
    (P.cancel_right_of_respectsIso _ _).mpr
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D₀.map a.hom) V.hom).flip hV)
  have hsurj : Surjective g := hg _ hVsurj
  have hinj : UniversallyInjective g := hg _ hVinj
  have hfree : Stacks.Morphisms.IsFiniteLocallyFree g := hg _ hVfree
  have htotal : g ≫ β'.opensRange.ι = q ≫ v := by
    dsimp [g]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    have hn : D₀.map a.hom ≫ β = β' := by
      show (PrincipalLocalization.diagram p.asIdeal).map (F₀.map a.hom) ≫
        PrincipalLocalization.baseMap p.asIdeal i ≫ α = _
      rw [← Category.assoc, PrincipalLocalization.baseMap_naturality]
    rw [← hn, ← Category.assoc]
    show (pullback.fst (D₀.map a.hom) V.hom ≫ D₀.map a.hom) ≫ β =
      pullback.snd (D₀.map a.hom) V.hom ≫ V.hom ≫ β
    rw [pullback.condition, Category.assoc]
  let eA : ((Over.pullback fV).obj (F.obj a)).left ≅ pullback f (g ≫ β'.opensRange.ι) :=
    pullbackSymmetry q fV ≪≫ pullbackLeftPullbackSndIso f v q ≪≫
      pullback.congrHom rfl htotal.symm
  have heA : eA.hom ≫ pullback.snd f (g ≫ β'.opensRange.ι) = pullback.fst q fV := by
    simp only [eA, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map,
      pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
    exact pullbackSymmetry_hom_comp_snd q fV
  have : ∀ b, IsClosedImmersion (Y b).hom := hYcl
  refine ⟨β'.opensRange, hηU, (F.obj a).left, g, hsurj.1, hinj, hfree,
    t, (fun b => (Y b).left), (fun b => (Y b).hom ≫ eA.hom),
    (fun b => (l b).left), (fun b => stratumOpen (Y b.castSucc).hom (Y b.succ).hom),
    ?_, ?_, ?_, hYempty, hl, ?_, ?_, ?_⟩
  · exact fun _ => inferInstance
  · exact fun b => (finitePresentation_iff_isFiniteType_idealSheaf _).mp
      (finitePresentation_comp_iso _ (hYfp b) eA)
  · exact ⟨inferInstance, eA.hom.surjective.comp hYth.2⟩
  · intro b
    rw [← Category.assoc, Over.w]
  · intro b x
    show (Y b.castSucc).hom x ∉ Set.range (Y b.succ).hom ↔
      eA.hom ((Y b.castSucc).hom x) ∉ Set.range (eA.hom ∘ (Y b.succ).hom)
    rw [Set.range_comp, eA.hom.injective.mem_set_image]
  · intro b
    simp only [Category.assoc, heA]
    exact hYsm b inferInstance

end AlgebraicGeometry

end
