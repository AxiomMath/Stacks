module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt

/-!
# Left derived functors from an initial resolution

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`.  By [Stacks, Tag 05S9]
the left derived functor `LF` is *defined at* an object `X` when the pro-object

`W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')`

is essentially constant, `W/X` being the category of morphisms of `W` into `X`. This holds
whenever `W/X` has an *initial* object `s₀ : X₀ ⟶ X`, for every `F`, and the value of `LF` at `X`
is then `F(X₀)`.

In a pretriangulated category, let `𝒩 ⊆ 𝒞` be a shift-invariant class of objects and let
`W = 𝒩.trW` be the class of morphisms whose cone lies in `𝒩`. If `s₀ : P ⟶ X` lies in `W` and `P`
lies in the left orthogonal `⊥𝒩`, then `s₀` is initial in `W/X`. Hence, if every object receives
such a morphism, *every* functor out of `𝒞` is left derivable with respect to `𝒩.trW`.

## Main definitions

* `CategoryTheory.ObjectProperty.isInitialOverTrW`: a morphism of `𝒩.trW` out of an object of the
  left orthogonal of `𝒩` is an initial object of the index category `𝒩.trW/X`.

## Main results

* `CategoryTheory.Functor.isLeftDerivedValueAt_coneOfDiagramInitial`: an initial object of `W/X`
  exhibits the value of `LF` at `X`, for every `F`.
* `CategoryTheory.Functor.isLeftDerivable_of_forall_isInitial`: if `W/X` has an initial object for
  every `X`, then every `F` is left derivable with respect to `W` in the sense of
  [Stacks, Tag 05SV].
* `CategoryTheory.ObjectProperty.isLeftDerivable_trW_of_leftOrthogonal_resolutions`: if every
  object of a pretriangulated `𝒞` receives a morphism of `𝒩.trW` from an object of the left
  orthogonal of `𝒩`, then every `F : 𝒞 ⥤ ℋ` is left derivable with respect to `𝒩.trW`.

## References

* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
* [Stacks Project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Functor

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- If `s₀ : X₀ ⟶ X` is an initial object of the index category `W/X` of [Stacks, Tag 05S9], then
for every `F : 𝒟 ⥤ 𝒟'` the cone with vertex `F(X₀)` whose projection at `s : X' ⟶ X` is `F`
applied to the unique morphism `X₀ ⟶ X'` over `X` is a value of the left derived functor `LF` at
`X`. -/
theorem isLeftDerivedValueAt_coneOfDiagramInitial (F : D ⥤ D') (W : MorphismProperty D) (X : D)
    {s₀ : W.Over ⊤ X} (h : IsInitial s₀) :
    F.IsLeftDerivedValueAt W X
      (coneOfDiagramInitial h (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) := by
  refine ⟨s₀, 𝟙 _, ?_, fun s => ⟨s₀, h.to s, 𝟙 s₀, ?_⟩⟩ <;> simp

/-- If every index category `W/X` has an initial object, then `F` is left derivable with
respect to `W` in the sense of [Stacks, Tag 05SV]. -/
theorem isLeftDerivable_of_forall_isInitial (F : D ⥤ D') (W : MorphismProperty D)
    (h : ∀ X : D, ∃ s₀ : W.Over ⊤ X, Nonempty (IsInitial s₀)) :
    F.IsLeftDerivable W := fun X => by
  obtain ⟨s₀, ⟨hs₀⟩⟩ := h X
  exact ⟨_, F.isLeftDerivedValueAt_coneOfDiagramInitial W X hs₀⟩

end Functor

namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (𝒩 : ObjectProperty C) [𝒩.IsStableUnderShift ℤ]

/-- If `P` lies in the left orthogonal of `𝒩` and `t : Q ⟶ X` has its cone in `𝒩`, then two
morphisms `P ⟶ Q` with the same composite with `t` are equal. -/
theorem leftOrthogonal_cancel_trW {P Q X : C} (hP : 𝒩.leftOrthogonal P) {t : Q ⟶ X}
    (ht : 𝒩.trW t) {a b : P ⟶ Q} (hab : a ≫ t = b ≫ t) : a = b := by
  obtain ⟨Y, f, g, hT, hY⟩ := (𝒩.trW_iff' t).1 ht
  obtain ⟨e, he⟩ := (Triangle.mk f t g).coyoneda_exact₂ hT (a - b) (by
    show (a - b) ≫ t = 0
    rw [Preadditive.sub_comp, hab, sub_self])
  rw [← sub_eq_zero, he, hP e hY, zero_comp]

/-- Let `𝒩` be a shift-invariant class of objects of a pretriangulated category, let
`s₀ : P ⟶ X` be a morphism whose cone lies in `𝒩`, and let `P` lie in the left orthogonal of `𝒩`.
Then `s₀` is an initial object of the category `𝒩.trW/X` of morphisms of `𝒩.trW` into `X`. -/
noncomputable def isInitialOverTrW {X P : C} (s₀ : P ⟶ X) (hs₀ : 𝒩.trW s₀)
    (hP : 𝒩.leftOrthogonal P) :
    IsInitial (MorphismProperty.Over.mk ⊤ s₀ hs₀ : 𝒩.trW.Over ⊤ X) := by
  have key : ∀ s : 𝒩.trW.Over ⊤ X, ∃ a : P ⟶ s.left, a ≫ s.hom = s₀ := by
    intro s
    obtain ⟨Z, g, w, hT, hZ⟩ := (𝒩.trW_iff s.hom).1 s.prop
    obtain ⟨a, ha⟩ := (Triangle.mk s.hom g w).coyoneda_exact₂ hT s₀ (hP _ hZ)
    exact ⟨a, ha.symm⟩
  exact IsInitial.ofUniqueHom
    (fun s => MorphismProperty.Over.homMk (key s).choose (key s).choose_spec) fun s m =>
      MorphismProperty.Over.Hom.ext (𝒩.leftOrthogonal_cancel_trW hP s.prop
        ((MorphismProperty.Over.w m).trans (key s).choose_spec.symm))

variable {H : Type u₂} [Category.{v₂} H]

/-- If every object `X` of a pretriangulated category `𝒞` receives a morphism of `𝒩.trW` from
an object of the left orthogonal of `𝒩`, then every `F : 𝒞 ⥤ ℋ` is left derivable with respect
to `𝒩.trW` in the sense of [Stacks, Tag 05SV]. -/
theorem isLeftDerivable_trW_of_leftOrthogonal_resolutions (F : C ⥤ H)
    (hres : ∀ X : C, ∃ (P : C) (s : P ⟶ X), 𝒩.trW s ∧ 𝒩.leftOrthogonal P) :
    F.IsLeftDerivable 𝒩.trW :=
  F.isLeftDerivable_of_forall_isInitial 𝒩.trW fun X => by
    obtain ⟨P, s, hs, hP⟩ := hres X
    exact ⟨_, ⟨𝒩.isInitialOverTrW s hs hP⟩⟩

end ObjectProperty

end CategoryTheory

end
