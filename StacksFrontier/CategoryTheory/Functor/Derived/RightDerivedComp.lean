module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksFrontier.CategoryTheory.Functor.Derived.CoresolutionCriterion

/-!
# Composing right derived functors, and objects local for a resolving class

Let `L : C ⥤ D` be a localization functor for a class of morphisms `W` admitting a right calculus
of fractions, and let `P` be a property of objects of `C` such that every object is the target of
a morphism of `W` out of an object with `P`. If an object `M` is *local* for the morphisms of `W`
between objects with `P` — precomposition with such a morphism is bijective on morphisms into
`M` — then `L` is bijective on the morphisms from an object with `P` into `M`. This is the shape
in which a K-flat or good resolution theory computes morphisms in a derived category without any
K-injective target.

The second result composes right derived functors. For functors `F : C₁ ⥤ C₂`, `G : C₂ ⥤ C₃`
and right derived functors `RF`, `RG` of `F ⋙ L₂` and of `G ⋙ L₃`, the composite `RF ⋙ RG`,
with the composite of the two comparison maps, is a right derived functor of `F ⋙ G ⋙ L₃` as
soon as there are enough coresolving objects `I` of `C₁` at which both comparison maps, of `F`
at `I` and of `G` at `F(I)`, are invertible. For the derived functors of the source this is the
step "`F` carries a coresolving object to an object acyclic for `G`".

## Main definitions

* `CategoryTheory.MorphismProperty.IsLocalOn`: locality of an object for the morphisms of `W`
  between objects with a property.
* `CategoryTheory.Functor.rightDerivedCompUnit`: the comparison map of a composite of two right
  derived functors.

## Main results

* `CategoryTheory.Localization.bijective_map_of_isLocalOn`: `L` is bijective on morphisms from
  an object with `P` into a local object.
* `CategoryTheory.Functor.isRightDerivedFunctor_comp_of_isIso`: the composite of two right derived
  functors is a right derived functor of the composite.
-/

@[expose] public noncomputable section

open CategoryTheory Category

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u₁} [Category.{v₁} C] (W : MorphismProperty C)

/-- An object `M` is *local* for the morphisms of `W` between objects with `P` when
precomposition with every such morphism is a bijection on morphisms into `M`. -/
def IsLocalOn (P : C → Prop) (M : C) : Prop :=
  ∀ ⦃Y X : C⦄ (s : Y ⟶ X), W s → P Y → P X → Function.Bijective (fun a : X ⟶ M => s ≫ a)

end MorphismProperty

namespace Localization

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

/-- **Morphisms into a local object.** If every object of `C` is the target of a morphism of `W`
out of an object with `P`, and `M` is local for the morphisms of `W` between objects with `P`,
then `L` is bijective on the morphisms from an object with `P` into `M`. Injectivity is the
precomposition criterion of a right calculus of fractions, surjectivity the presentation of a
morphism of `D` as a right fraction; in both the auxiliary object is first replaced by one with
`P`. -/
theorem bijective_map_of_isLocalOn [W.HasRightCalculusOfFractions] [W.IsMultiplicative]
    (P : C → Prop) (hres : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), W s ∧ P Y)
    {M : C} (hM : W.IsLocalOn P M) {X : C} (hX : P X) :
    Function.Bijective (L.map : (X ⟶ M) → (L.obj X ⟶ L.obj M)) := by
  refine ⟨fun a b hab => ?_, fun φ => ?_⟩
  · obtain ⟨Z, t, ht, fac⟩ := (MorphismProperty.map_eq_iff_precomp L W a b).1 hab
    obtain ⟨Y, p, hp, hY⟩ := hres Z
    exact (hM (p ≫ t) (W.comp_mem _ _ hp ht) hY hX).1
      (show (p ≫ t) ≫ a = (p ≫ t) ≫ b by rw [assoc, assoc, fac])
  · obtain ⟨ψ, rfl⟩ := Localization.exists_rightFraction L W φ
    obtain ⟨Y, p, hp, hY⟩ := hres ψ.X'
    obtain ⟨a, ha⟩ := (hM (p ≫ ψ.s) (W.comp_mem _ _ hp ψ.hs) hY hX).2 (p ≫ ψ.f)
    refine ⟨a, ?_⟩
    have : IsIso (L.map (p ≫ ψ.s)) := Localization.inverts L W _ (W.comp_mem _ _ hp ψ.hs)
    rw [← cancel_epi (L.map (p ≫ ψ.s)), ← L.map_comp,
      show (p ≫ ψ.s) ≫ a = p ≫ ψ.f from ha, L.map_comp, L.map_comp, assoc,
      MorphismProperty.RightFraction.map_s_comp_map]

include L in
/-- Postcomposition with a morphism of `W` between two local objects is bijective on morphisms out
of an object with `P`. -/
theorem bijective_comp_map_of_isLocalOn [W.HasRightCalculusOfFractions] [W.IsMultiplicative]
    (P : C → Prop) (hres : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), W s ∧ P Y)
    {M M' : C} (hM : W.IsLocalOn P M) (hM' : W.IsLocalOn P M') (s : M ⟶ M') (hs : W s)
    {X : C} (hX : P X) :
    Function.Bijective (fun a : X ⟶ M => a ≫ s) := by
  have : IsIso (L.map s) := Localization.inverts L W s hs
  have hcomp : (fun a : X ⟶ M => L.map (a ≫ s)) =
      (fun b : L.obj X ⟶ L.obj M => b ≫ L.map s) ∘ L.map := by
    funext a
    simp only [Function.comp_apply, L.map_comp]
  have hb : Function.Bijective (fun a : X ⟶ M => L.map (a ≫ s)) := by
    rw [hcomp]
    refine Function.Bijective.comp ?_ (bijective_map_of_isLocalOn L W P hres hM hX)
    exact ⟨fun b b' h => by simpa using congrArg (· ≫ inv (L.map s)) h,
      fun c => ⟨c ≫ inv (L.map s), by simp⟩⟩
  exact (Function.Bijective.of_comp_iff' (bijective_map_of_isLocalOn L W P hres hM' hX) _).1 hb

include L in
/-- **Invertibility in the localization, tested on objects with `P`.** A morphism `u : M ⟶ N`
between local objects becomes invertible in `D` as soon as postcomposition with `u` is bijective on
morphisms out of every object with `P`: every object of `D` is isomorphic to the image of an object
with `P`, and on morphisms out of such an object into a local object `L` is bijective. -/
theorem isIso_map_of_bijective_comp [W.HasRightCalculusOfFractions] [W.IsMultiplicative]
    (P : C → Prop) (hres : ∀ X : C, ∃ (Y : C) (s : Y ⟶ X), W s ∧ P Y)
    {M N : C} (hM : W.IsLocalOn P M) (hN : W.IsLocalOn P N) (u : M ⟶ N)
    (hu : ∀ X : C, P X → Function.Bijective (fun a : X ⟶ M => a ≫ u)) :
    IsIso (L.map u) := by
  have hess := Localization.essSurj L W
  refine isIso_of_yoneda_map_bijective _ fun T => ?_
  obtain ⟨X, s, hs, hX⟩ := hres (L.objPreimage T)
  have : IsIso (L.map s) := Localization.inverts L W s hs
  let e : L.obj X ≅ T := asIso (L.map s) ≪≫ L.objObjPreimageIso T
  have hX' : Function.Bijective (fun x : L.obj X ⟶ L.obj M => x ≫ L.map u) := by
    have hcomp : (fun x : L.obj X ⟶ L.obj M => x ≫ L.map u) ∘ L.map =
        L.map ∘ (fun a : X ⟶ M => a ≫ u) := by
      funext a
      simp only [Function.comp_apply, L.map_comp]
    have h3 : Function.Bijective (L.map ∘ (fun a : X ⟶ M => a ≫ u)) :=
      (bijective_map_of_isLocalOn L W P hres hN hX).comp (hu X hX)
    rw [← hcomp] at h3
    exact (Function.Bijective.of_comp_iff _ (bijective_map_of_isLocalOn L W P hres hM hX)).1 h3
  have hT : (fun x : T ⟶ L.obj M => x ≫ L.map u) =
      (fun y : L.obj X ⟶ L.obj N => e.inv ≫ y) ∘ (fun x : L.obj X ⟶ L.obj M => x ≫ L.map u) ∘
        (fun x : T ⟶ L.obj M => e.hom ≫ x) := by
    funext x
    simp
  rw [hT]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp hX' ?_)
  · exact ⟨fun y y' h => by simpa using congrArg (e.hom ≫ ·) h,
      fun z => ⟨e.hom ≫ z, by simp⟩⟩
  · exact ⟨fun y y' h => by simpa using congrArg (e.inv ≫ ·) h,
      fun z => ⟨e.inv ≫ z, by simp⟩⟩

end Localization

namespace Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {RF : D₁ ⥤ D₂} {RG : D₂ ⥤ D₃}

/-- The comparison map `F ⋙ G ⋙ L₃ ⟶ L₁ ⋙ RF ⋙ RG` of a composite of two right derived functors:
the comparison of `G` at the image of `F`, followed by `RG` of the comparison of `F`. -/
def rightDerivedCompUnit (βF : F ⋙ L₂ ⟶ L₁ ⋙ RF) (βG : G ⋙ L₃ ⟶ L₂ ⋙ RG) :
    (F ⋙ G) ⋙ L₃ ⟶ L₁ ⋙ RF ⋙ RG :=
  (Functor.associator F G L₃).hom ≫ Functor.whiskerLeft F βG ≫
    (Functor.associator F L₂ RG).inv ≫ Functor.whiskerRight βF RG ≫
      (Functor.associator L₁ RF RG).hom

/-- The component of `rightDerivedCompUnit βF βG` at `X` is `βG` at `F.obj X` followed by `RG`
applied to `βF` at `X`. -/
@[simp]
theorem rightDerivedCompUnit_app (βF : F ⋙ L₂ ⟶ L₁ ⋙ RF) (βG : G ⋙ L₃ ⟶ L₂ ⋙ RG) (X : C₁) :
    (rightDerivedCompUnit βF βG).app X = βG.app (F.obj X) ≫ RG.map (βF.app X) := by
  simp [rightDerivedCompUnit]

/-- **The composite of two right derived functors.** If every object of `C₁` admits a morphism of
`W₁` into a coresolving object, `L₁` is bijective on morphisms into a coresolving object, and at
every coresolving object `I` the comparison map of `F` at `I` and that of `G` at `F(I)` are
invertible, then `RF ⋙ RG` with `rightDerivedCompUnit` is a right derived functor of
`F ⋙ G ⋙ L₃`. -/
theorem isRightDerivedFunctor_comp_of_isIso (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
    (βF : F ⋙ L₂ ⟶ L₁ ⋙ RF) (βG : G ⋙ L₃ ⟶ L₂ ⋙ RG) (P : C₁ → Prop)
    (hres : ∀ X : C₁, ∃ (I : C₁) (s : X ⟶ I), W₁ s ∧ P I)
    (hbij : ∀ I : C₁, P I →
      ∀ Y : C₁, Function.Bijective (L₁.map : (Y ⟶ I) → (L₁.obj Y ⟶ L₁.obj I)))
    (hF : ∀ I : C₁, P I → IsIso (βF.app I)) (hG : ∀ I : C₁, P I → IsIso (βG.app (F.obj I))) :
    (RF ⋙ RG).IsRightDerivedFunctor (rightDerivedCompUnit βF βG) W₁ :=
  isRightDerivedFunctor_of_coresolutions W₁ _ P hres hbij fun I hI => by
    have := hF I hI
    have := hG I hI
    rw [rightDerivedCompUnit_app]
    infer_instance

end Functor

end CategoryTheory
