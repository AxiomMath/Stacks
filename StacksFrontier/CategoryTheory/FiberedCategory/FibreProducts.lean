module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreProductsCartesian

/-!
# Fibre products in a fibred category (Stacks 06N5)

Let `p : 𝒮 ⥤ 𝒞` be a fibred category, and let `φ : x ⟶ y` and `g : z ⟶ y` be
morphisms of `𝒮` with `φ` strongly cartesian over its image `p φ`. Assume the fibre
product `p x ×_{p y} p z` exists in the base `𝒞`.

Because `p` is fibred, the second projection `pr₂ : p x ×_{p y} p z ⟶ p z` has a
strongly cartesian lift `a : w ⟶ z`; the object `w` is Stacks' `pr₂^* z`. Its image
`p w` is the fibre product of the images and `p a` is `pr₂`, so Stacks 06N4 applies
and identifies `w` with `x ×_y z`. Three consequences are recorded here: the fibre
product `x ×_y z` exists in `𝒮`; the functor `p` carries the resulting square to a
fibre product square in `𝒞`, so `p (x ×_y z) = p x ×_{p y} p z`; and the second
projection `x ×_y z ⟶ z` is again strongly cartesian, being the composite of the
canonical isomorphism `x ×_y z ≅ w` with `a`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- In a fibred category every morphism of the base lifts to a *strongly* cartesian
morphism, not merely a cartesian one. -/
lemma Functor.IsFibered.exists_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {Y : 𝒮} {R : 𝒞} (f : R ⟶ p.obj Y) :
    ∃ (W : 𝒮) (a : W ⟶ Y), p.IsStronglyCartesian f a := by
  obtain ⟨W, a, _⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := Y) f
  exact ⟨W, a, Functor.IsFibered.isStronglyCartesian_of_isCartesian p f a⟩

/-- A morphism that is strongly cartesian over some morphism `f` of the base is
strongly cartesian over its own image: being a lift of `f` forces `f` to agree
with `p φ`. -/
lemma Functor.IsStronglyCartesian.isStronglyCartesian_map
    (p : 𝒮 ⥤ 𝒞) {a b : 𝒮} (φ : a ⟶ b)
    {R S : 𝒞} (f : R ⟶ S) [p.IsStronglyCartesian f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  cases (Functor.IsStronglyCartesian.toIsHomLift : p.IsHomLift f φ)
  assumption

/-- The lift `w = pr₂^* z` of the fibre product of the images, together with the two
projections `b : w ⟶ x`, `a : w ⟶ z` and the proof that they exhibit `w` as `x ×_y z`.
Fibredness supplies `a`, and Stacks 06N4 supplies `b` and the limit property. -/
private lemma exists_isLimit_pullbackCone_of_isFibered
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)] :
    ∃ (w : 𝒮) (a : w ⟶ z) (b : w ⟶ x)
      (hw : p.obj w = Limits.pullback (p.map φ) (p.map g)) (hba : b ≫ φ = a ≫ g),
      p.IsStronglyCartesian (p.map a) a ∧
      p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g) ∧
      p.map b = eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g) ∧
      Nonempty (Limits.IsLimit (Limits.PullbackCone.mk b a hba)) := by
  obtain ⟨w, a, hacart⟩ := Functor.IsFibered.exists_isStronglyCartesian p
    (Limits.pullback.snd (p.map φ) (p.map g))
  have : Functor.IsStronglyCartesian p
      (Limits.pullback.snd (p.map φ) (p.map g)) a := hacart
  have hw : p.obj w = Limits.pullback (p.map φ) (p.map g) :=
    IsHomLift.domain_eq p (Limits.pullback.snd (p.map φ) (p.map g)) a
  have hamap : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g) := by
    simpa using IsHomLift.fac' p (Limits.pullback.snd (p.map φ) (p.map g)) a
  have : p.IsStronglyCartesian (p.map a) a :=
    Functor.IsStronglyCartesian.isStronglyCartesian_map p a
      (Limits.pullback.snd (p.map φ) (p.map g))
  obtain ⟨b, hba, hbmap, hlim⟩ :=
    exists_isLimit_pullbackCone_of_isStronglyCartesian p φ g w a hw hamap
  exact ⟨w, a, b, hw, hba, inferInstance, hamap, hbmap, hlim⟩

/-- A limit cone over the cospan `φ, g` is isomorphic to `pullback φ g`, compatibly with
both projections. -/
private lemma exists_iso_pullback_comp_eq {x y z w : 𝒮} {φ : x ⟶ y} {g : z ⟶ y}
    [Limits.HasPullback φ g] {a : w ⟶ z} {b : w ⟶ x} {hba : b ≫ φ = a ≫ g}
    (hlim : Limits.IsLimit (Limits.PullbackCone.mk b a hba)) :
    ∃ e : Limits.pullback φ g ≅ w,
      e.hom ≫ b = Limits.pullback.fst φ g ∧ e.hom ≫ a = Limits.pullback.snd φ g :=
  ⟨Limits.IsLimit.conePointUniqueUpToIso (Limits.pullback.isLimit φ g) hlim,
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (Limits.pullback.isLimit φ g) hlim Limits.WalkingCospan.left,
    Limits.IsLimit.conePointUniqueUpToIso_hom_comp
      (Limits.pullback.isLimit φ g) hlim Limits.WalkingCospan.right⟩

/-- **Stacks 06N5, existence half.**
In a fibred category `p : 𝒮 ⥤ 𝒞`, if `φ : x ⟶ y` is strongly cartesian over `p` and
the fibre product of `p φ` and `p g` exists in `𝒞`, then the fibre product of `φ` and
`g` exists in `𝒮`. -/
@[stacks 06N5]
theorem Functor.IsFibered.hasPullback_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)] :
    Limits.HasPullback φ g := by
  obtain ⟨w, a, b, hw, hba, -, -, -, ⟨hlim⟩⟩ :=
    exists_isLimit_pullbackCone_of_isFibered p φ g
  exact ⟨⟨⟨_, hlim⟩⟩⟩

/-- **Stacks 06N5, second projection strongly cartesian.**
Under the same hypotheses the second projection `Limits.pullback.snd φ g : x ×_y z ⟶ z`
is strongly cartesian over `p`, since it is the canonical isomorphism `x ×_y z ≅ w`
followed by the strongly cartesian morphism `a`. -/
@[stacks 06N5]
theorem Functor.IsFibered.snd_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    [Limits.HasPullback φ g] :
    Functor.IsStronglyCartesian p
      (p.map (Limits.pullback.snd φ g)) (Limits.pullback.snd φ g) := by
  obtain ⟨w, a, b, hw, hba, hacart, -, -, ⟨hlim⟩⟩ :=
    exists_isLimit_pullbackCone_of_isFibered p φ g
  have : p.IsStronglyCartesian (p.map a) a := hacart
  obtain ⟨e, -, he⟩ := exists_iso_pullback_comp_eq hlim
  rw [← he, p.map_comp]
  infer_instance

/-- **Stacks 06N5, image square is a fibre product square.**
Under the same hypotheses `p` sends the fibre product square of `φ, g` in `𝒮` to a
fibre product square in `𝒞`: the image `p (x ×_y z)`, with the images of the two
projections, is the fibre product of `p φ` and `p g`. -/
@[stacks 06N5]
theorem Functor.IsFibered.map_isPullback_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    [Limits.HasPullback φ g] :
    IsPullback (p.map (Limits.pullback.fst φ g)) (p.map (Limits.pullback.snd φ g))
      (p.map φ) (p.map g) := by
  obtain ⟨w, a, b, hw, hba, -, hamap, hbmap, ⟨hlim⟩⟩ :=
    exists_isLimit_pullbackCone_of_isFibered p φ g
  obtain ⟨e, hfst, hsnd⟩ := exists_iso_pullback_comp_eq hlim
  refine IsPullback.of_iso_pullback ?_ (p.mapIso e ≪≫ eqToIso hw) ?_ ?_
  · exact ⟨by rw [← p.map_comp, ← p.map_comp, Limits.pullback.condition]⟩
  · rw [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc, ← hbmap,
      ← p.map_comp, hfst]
  · rw [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc, ← hamap,
      ← p.map_comp, hsnd]

end CategoryTheory
