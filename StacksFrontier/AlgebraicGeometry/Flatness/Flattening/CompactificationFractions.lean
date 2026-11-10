module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactifications form a right multiplicative system

For a scheme `S`, consider compactifications consisting of a quasi-compact open immersion
into a scheme proper over `S`. Morphisms of compactifications inducing an isomorphism on the
open subschemes form a right multiplicative system.

## Main definitions

* `AlgebraicGeometry.IsCompactification` is the property of an arrow of schemes over `S` of
  being a compactification.
* `AlgebraicGeometry.Compactification` is the category of compactifications over `S`.
* `AlgebraicGeometry.interiorIsomorphisms` is the class of morphisms inducing an isomorphism
  on the open subschemes.

## Main results

* `AlgebraicGeometry.interiorIsomorphisms_hasRightCalculusOfFractions` says that these
  morphisms form a right multiplicative system.

## Implementation notes

The category of compactifications is implemented as a full subcategory of the arrow category
of schemes over `S`, so that its morphisms are precisely the commutative squares over `S` in
the source. Mathlib's `HasRightCalculusOfFractions` is the bundled form of the three right
multiplicative system axioms.

The right fraction axiom is witnessed by the fibre product of two compactifications, and the
cancellation axiom by the fibre product of a compactification with the equalizer of the two
morphisms of ambient schemes; `pullbackCompactification` and `equalizerCompactification`
construct these, together with their projections to the given compactifications.

The quasi-compactness and quasi-separatedness of `S` are not used by any of the three axioms,
so the result is stated for an arbitrary scheme `S`.

Here the interior of a compactification varies with the object, and quasi-compactness of the
open immersion is part of the definition. The variant with a fixed interior and no
quasi-compactness is `AlgebraicGeometry.IsCompactificationOf`; the two are genuinely
different objects.

## References

* [Stacks Project, Tag 0ATV](https://stacks.math.columbia.edu/tag/0ATV)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The property of an arrow of schemes over `S` being a compactification: its target is
proper over `S`, and its underlying arrow is a quasi-compact open immersion. -/
def IsCompactification (S : Scheme.{u}) : ObjectProperty (Arrow (Over S)) :=
  fun X => IsProper X.right.hom ∧ IsOpenImmersion X.hom.left ∧ QuasiCompact X.hom.left

/-- The category of compactifications over `S`. -/
abbrev Compactification (S : Scheme.{u}) :=
  (IsCompactification S).FullSubcategory

/-- Morphisms of compactifications that induce an isomorphism on the open subschemes. -/
def interiorIsomorphisms (S : Scheme.{u}) :
    MorphismProperty (Compactification S) :=
  fun _ _ f => IsIso (Arrow.Hom.left f.hom).left

/-- A morphism over `S` from a scheme proper over `S` to a scheme separated over `S` is
proper. -/
private lemma isProper_left_of_isProper {S : Scheme.{u}} {X Y : Over S}
    [IsProper X.hom] [IsSeparated Y.hom] (f : X ⟶ Y) : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    simpa only [Over.w] using (inferInstance : IsProper X.hom)
  exact IsProper.of_comp f.left Y.hom

/-- The open immersion of a compactification commutes with the morphism of ambient schemes
underlying a morphism of compactifications. -/
private lemma immersion_comp_right {S : Scheme.{u}} {X Z : Compactification S} (f : X ⟶ Z) :
    (Arrow.Hom.left f.hom).left ≫ Z.obj.hom.left =
      X.obj.hom.left ≫ (Arrow.Hom.right f.hom).left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (Arrow.w f.hom)

/-- The two projections of a fibre product of morphisms over `S` agree after composing with
the structure morphisms. -/
private lemma pullback_snd_comp_hom {S : Scheme.{u}} {A B C : Over S} (f : A ⟶ C) (g : B ⟶ C) :
    pullback.snd f.left g.left ≫ B.hom = pullback.fst f.left g.left ≫ A.hom := by
  rw [← Over.w g, ← Over.w f, ← Category.assoc, ← Category.assoc, ← pullback.condition]

section Pullback

variable {S : Scheme.{u}} {X Y Z : Compactification S}

/-- The structure morphism of the base of the fibre product of two compactifications over a
third: the first projection followed by the structure morphism of the first. -/
private noncomputable def pullbackBaseHom (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left ⟶ S :=
  pullback.fst (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left ≫ X.obj.right.hom

/-- Unfolding of `pullbackBaseHom`. -/
private lemma pullbackBaseHom_eq (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackBaseHom f g =
      pullback.fst (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left ≫
        X.obj.right.hom :=
  rfl

/-- The open immersion of the fibre product of two compactifications over a third: the map of
fibre products induced by the three open immersions. -/
private noncomputable def pullbackImmersion (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ⟶
      pullback (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left :=
  pullback.map _ _ _ _ X.obj.hom.left Y.obj.hom.left Z.obj.hom.left
    (immersion_comp_right f) (immersion_comp_right g)

/-- The open immersion of the fibre product commutes with the first projections. -/
private lemma pullbackImmersion_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackImmersion f g ≫
        pullback.fst (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left =
      pullback.fst (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        X.obj.hom.left :=
  pullback.lift_fst _ _ _

/-- The open immersion of the fibre product commutes with the second projections. -/
private lemma pullbackImmersion_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackImmersion f g ≫
        pullback.snd (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left =
      pullback.snd (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        Y.obj.hom.left :=
  pullback.lift_snd _ _ _

/-- The base over `S` of the fibre product of two compactifications over a third. -/
private noncomputable def pullbackBase (f : X ⟶ Z) (g : Y ⟶ Z) : Over S :=
  Over.mk (pullbackBaseHom f g)

/-- The interior over `S` of the fibre product of two compactifications over a third. -/
private noncomputable def pullbackInterior (f : X ⟶ Z) (g : Y ⟶ Z) : Over S :=
  Over.mk (pullbackImmersion f g ≫ pullbackBaseHom f g)

/-- The arrow of schemes over `S` underlying the fibre product of two compactifications. -/
private noncomputable def pullbackArrowHom (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackInterior f g ⟶ pullbackBase f g :=
  Over.homMk (pullbackImmersion f g) rfl

/-- The arrow underlying the fibre product of two compactifications is a compactification. -/
private lemma pullbackArrowHom_isCompactification (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsCompactification S (Arrow.mk (pullbackArrowHom f g)) := by
  have hX : IsOpenImmersion X.obj.hom.left := X.property.2.1
  have hY : IsOpenImmersion Y.obj.hom.left := Y.property.2.1
  have hZ : IsOpenImmersion Z.obj.hom.left := Z.property.2.1
  have hqX : QuasiCompact X.obj.hom.left := X.property.2.2
  have hqY : QuasiCompact Y.obj.hom.left := Y.property.2.2
  have hpX : IsProper X.obj.right.hom := X.property.1
  have hpY : IsProper Y.obj.right.hom := Y.property.1
  have hpZ : IsProper Z.obj.right.hom := Z.property.1
  have hpg : IsProper (Arrow.Hom.right g.hom).left :=
    isProper_left_of_isProper (Arrow.Hom.right g.hom)
  have him : IsOpenImmersion (pullbackImmersion f g) := by
    change IsOpenImmersion (pullback.map _ _ _ _ X.obj.hom.left Y.obj.hom.left Z.obj.hom.left
      (immersion_comp_right f) (immersion_comp_right g))
    infer_instance
  have hqc : QuasiCompact (pullbackImmersion f g) := by
    change QuasiCompact (pullback.map _ _ _ _ X.obj.hom.left Y.obj.hom.left Z.obj.hom.left
      (immersion_comp_right f) (immersion_comp_right g))
    rw [pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  have hpr : IsProper (pullbackBaseHom f g) := by
    rw [pullbackBaseHom_eq]
    infer_instance
  exact ⟨hpr, him, hqc⟩

/-- The fibre product of two compactifications over a third, again a compactification. -/
private noncomputable def pullbackCompactification (f : X ⟶ Z) (g : Y ⟶ Z) :
    Compactification S :=
  ⟨Arrow.mk (pullbackArrowHom f g), pullbackArrowHom_isCompactification f g⟩

/-- The first projection out of the fibre product of two compactifications. -/
private noncomputable def pullbackCompactificationFst (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackCompactification f g ⟶ X := by
  refine ObjectProperty.homMk (Arrow.homMk
    (Over.homMk (pullback.fst (Arrow.Hom.left f.hom).left
      (Arrow.Hom.left g.hom).left) ?_)
    (Over.homMk (pullback.fst (Arrow.Hom.right f.hom).left
      (Arrow.Hom.right g.hom).left) ?_) ?_)
  · change pullback.fst (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        X.obj.left.hom = pullbackImmersion f g ≫ pullbackBaseHom f g
    rw [pullbackBaseHom_eq, ← Category.assoc, pullbackImmersion_comp_fst, Category.assoc,
      Over.w X.obj.hom]
  · rfl
  · apply Over.OverMorphism.ext
    change pullback.fst (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        X.obj.hom.left =
      pullbackImmersion f g ≫
        pullback.fst (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left
    rw [pullbackImmersion_comp_fst]

/-- The second projection out of the fibre product of two compactifications. -/
private noncomputable def pullbackCompactificationSnd (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackCompactification f g ⟶ Y := by
  refine ObjectProperty.homMk (Arrow.homMk
    (Over.homMk (pullback.snd (Arrow.Hom.left f.hom).left
      (Arrow.Hom.left g.hom).left) ?_)
    (Over.homMk (pullback.snd (Arrow.Hom.right f.hom).left
      (Arrow.Hom.right g.hom).left) ?_) ?_)
  · change pullback.snd (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        Y.obj.left.hom = pullbackImmersion f g ≫ pullbackBaseHom f g
    rw [pullbackBaseHom_eq, ← Category.assoc, pullbackImmersion_comp_fst, Category.assoc,
      Over.w X.obj.hom]
    exact pullback_snd_comp_hom (Arrow.Hom.left f.hom) (Arrow.Hom.left g.hom)
  · exact pullback_snd_comp_hom (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)
  · apply Over.OverMorphism.ext
    change pullback.snd (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
        Y.obj.hom.left =
      pullbackImmersion f g ≫
        pullback.snd (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left
    rw [pullbackImmersion_comp_snd]

/-- The two projections out of the fibre product of two compactifications form a commutative
square with the given morphisms. -/
private lemma pullbackCompactification_condition (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackCompactificationFst f g ≫ f = pullbackCompactificationSnd f g ≫ g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · apply Over.OverMorphism.ext
    change pullback.fst (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
      (Arrow.Hom.left f.hom).left =
      pullback.snd (Arrow.Hom.left f.hom).left (Arrow.Hom.left g.hom).left ≫
      (Arrow.Hom.left g.hom).left
    exact pullback.condition
  · apply Over.OverMorphism.ext
    change pullback.fst (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left ≫
      (Arrow.Hom.right f.hom).left =
      pullback.snd (Arrow.Hom.right f.hom).left (Arrow.Hom.right g.hom).left ≫
      (Arrow.Hom.right g.hom).left
    exact pullback.condition

end Pullback

/-- The equalizer of the ambient morphisms of two parallel morphisms of compactifications
includes into the target by a closed immersion. -/
private lemma isClosedImmersion_equalizer_ι_left_compactification {S : Scheme.{u}}
    {X Y : Compactification S} (f g : X ⟶ Y) :
    IsClosedImmersion (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left := by
  have : IsProper X.obj.right.hom := X.property.1
  have : IsProper Y.obj.right.hom := Y.property.1
  exact isClosedImmersion_equalizer_ι_left _ _

/-- The fibre product of a compactification with the equalizer of the two ambient morphisms
of a pair of parallel morphisms of compactifications agreeing on the interiors. -/
private noncomputable def equalizerCompactification {S : Scheme.{u}}
    {X Y : Compactification S} (f g : X ⟶ Y)
    (_h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    Compactification S := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  have : IsProper X.obj.right.hom := X.property.1
  have : IsClosedImmersion e.left := isClosedImmersion_equalizer_ι_left_compactification f g
  let b : (equalizer fB gB).left ⟶ S := (equalizer fB gB).hom
  have : IsProper b := by
    have hb : e.left ≫ X.obj.right.hom = b := Over.w e
    rw [← hb]
    infer_instance
  let j := X.obj.hom.left
  let q := pullback.snd j e.left
  have : IsOpenImmersion j := X.property.2.1
  have : QuasiCompact j := X.property.2.2
  let a : pullback j e.left ⟶ S := q ≫ b
  let A : Over S := Over.mk a
  let B : Over S := Over.mk b
  let i : A ⟶ B := Over.homMk q rfl
  exact ⟨Arrow.mk i, by
    change IsProper b ∧ IsOpenImmersion q ∧ QuasiCompact q
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The projection from the equalizer compactification to the source compactification. -/
private noncomputable def equalizerCompactificationToX {S : Scheme.{u}}
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    equalizerCompactification f g h ⟶ X := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  let j := X.obj.hom.left
  let p := pullback.fst j e.left
  let q := pullback.snd j e.left
  let b := (equalizer fB gB).hom
  have hbase : p ≫ X.obj.left.hom = q ≫ b := by
    dsimp [b]
    rw [← Over.w X.obj.hom, ← Over.w e, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]
    rfl
  dsimp only [equalizerCompactification]
  refine ObjectProperty.homMk (Arrow.homMk (Over.homMk p hbase) e ?_)
  apply Over.OverMorphism.ext
  change p ≫ j = q ≫ e.left
  exact pullback.condition

/-- The projection from the equalizer compactification induces an isomorphism on the open
subschemes. -/
private lemma equalizerCompactificationToX_mem {S : Scheme.{u}}
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    interiorIsomorphisms S (equalizerCompactificationToX f g h) := by
  let fB := Arrow.Hom.right f.hom
  let gB := Arrow.Hom.right g.hom
  let e : equalizer fB gB ⟶ X.obj.right := equalizer.ι fB gB
  have heq : X.obj.hom ≫ fB = X.obj.hom ≫ gB := by
    calc
      X.obj.hom ≫ fB = Arrow.Hom.left f.hom ≫ Y.obj.hom := (Arrow.w f.hom).symm
      _ = Arrow.Hom.left g.hom ≫ Y.obj.hom := by
        congr 1
        exact Over.OverMorphism.ext h
      _ = X.obj.hom ≫ gB := Arrow.w g.hom
  let l : X.obj.left ⟶ equalizer fB gB := equalizer.lift X.obj.hom heq
  have hl : l.left ≫ e.left = X.obj.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (equalizer.lift_ι X.obj.hom heq)
  have : Mono e.left := by
    have := isClosedImmersion_equalizer_ι_left_compactification f g
    infer_instance
  dsimp only [interiorIsomorphisms, equalizerCompactificationToX]
  change IsIso (pullback.fst X.obj.hom.left e.left)
  rw [← hl]
  infer_instance

/-- The projection from the equalizer compactification equalizes the two given morphisms. -/
private lemma equalizerCompactificationToX_condition {S : Scheme.{u}}
    {X Y : Compactification S} (f g : X ⟶ Y)
    (h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left) :
    equalizerCompactificationToX f g h ≫ f = equalizerCompactificationToX f g h ≫ g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · apply Over.OverMorphism.ext
    dsimp only [equalizerCompactificationToX]
    change pullback.fst X.obj.hom.left
      (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.left f.hom).left =
      pullback.fst X.obj.hom.left
      (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.left g.hom).left
    rw [h]
  · apply Over.OverMorphism.ext
    dsimp only [equalizerCompactificationToX]
    change (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.right f.hom).left =
      (equalizer.ι (Arrow.Hom.right f.hom) (Arrow.Hom.right g.hom)).left ≫
      (Arrow.Hom.right g.hom).left
    exact congrArg Over.Hom.left (equalizer.condition _ _)

/-- **Stacks Project, Tag 0ATV.** Morphisms of compactifications inducing an isomorphism on
the open subschemes form a right multiplicative system. -/
@[stacks 0ATV]
instance interiorIsomorphisms_hasRightCalculusOfFractions (S : Scheme.{u}) :
    (interiorIsomorphisms S).HasRightCalculusOfFractions := by
  refine { toIsMultiplicative := ?_, exists_rightFraction := ?_, ext := ?_ }
  · refine { id_mem := ?_, comp_mem := ?_ }
    · intro X
      change IsIso (Arrow.Hom.left (𝟙 X : X ⟶ X).hom).left
      rw [ObjectProperty.FullSubcategory.id_hom, Arrow.id_left, Over.id_left]
      infer_instance
    · intro X Y Z f g hf hg
      change IsIso (Arrow.Hom.left (f ≫ g).hom).left
      change IsIso (Arrow.Hom.left f.hom).left at hf
      change IsIso (Arrow.Hom.left g.hom).left at hg
      rw [ObjectProperty.FullSubcategory.comp_hom, Arrow.comp_left, Over.comp_left]
      infer_instance
  · intro X Y φ
    let p := pullbackCompactificationFst φ.f φ.s
    let q := pullbackCompactificationSnd φ.f φ.s
    have hp : interiorIsomorphisms S p := by
      change IsIso (pullback.fst (Arrow.Hom.left φ.f.hom).left
        (Arrow.Hom.left φ.s.hom).left)
      have : IsIso (Arrow.Hom.left φ.s.hom).left := φ.hs
      infer_instance
    exact ⟨MorphismProperty.RightFraction.mk p hp q,
      pullbackCompactification_condition φ.f φ.s⟩
  · intro X Y Y' f g s hs hfg
    have : IsIso (Arrow.Hom.left s.hom).left := hs
    have h : (Arrow.Hom.left f.hom).left = (Arrow.Hom.left g.hom).left := by
      apply (cancel_mono (Arrow.Hom.left s.hom).left).1
      simpa only [ObjectProperty.FullSubcategory.comp_hom, Arrow.comp_left, Over.comp_left] using
        congrArg (fun k : X ⟶ Y' => (Arrow.Hom.left k.hom).left) hfg
    exact ⟨equalizerCompactification f g h, equalizerCompactificationToX f g h,
      equalizerCompactificationToX_mem f g h,
      equalizerCompactificationToX_condition f g h⟩

end AlgebraicGeometry
