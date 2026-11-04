module

public import Mathlib.CategoryTheory.Elements
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Schlessinger.Basic

/-!
# Schlessinger's conditions for a set-valued functor

For a category cofibered in sets over `𝒞_Λ`, that is for the category of elements of a
functor `F : 𝒞_Λ ⥤ Type t`, Schlessinger's conditions (S1) and (S2) take their elementary
form (Stacks 06HY): (S1) says that `F(A₁ ×_A A₂) → F(A₁) ×_{F(A)} F(A₂)` is surjective
whenever `A₂ → A` is surjective, and (S2) says that
`F(A ×_k k[ε]) → F(A) ×_{F(k)} F(k[ε])` is bijective.

## Main definitions

* `Deformation.fibreProductComparison` is the map from the value of a set-valued functor at
  the apex of a commutative square to the fibre product of its values on the two sides.

## Main results

* `Deformation.schlessingerConditionS1_elements_iff`: condition (S1) for a category of
  elements is surjectivity of that comparison map over every prescribed pullback square in
  `𝒞_Λ` whose second base map is surjective.
* `Deformation.schlessingerConditionS2_elements_iff`: condition (S2) for a category of
  elements is bijectivity of that comparison map over every prescribed pullback square in
  `𝒞_Λ` whose second base map is the dual-number projection.

## Implementation notes

A category cofibered in sets over `𝒞_Λ` is represented, as for Stacks 06HJ, by the category
of elements `F.Elements` of a set-valued functor together with its projection
`CategoryOfElements.π F`. A cospan in that category lying over a cospan of the base is
precisely a point of the set-theoretic fibre product, which is what turns the completion
clauses of the two conditions into surjectivity statements. The target of the comparison map
is the subtype of the product cut out by the defining equality, because `𝒞_Λ` has no chosen
fibre products and neither have the categories of elements. Both conditions quantify over
prescribed pullback squares, exactly as `Deformation.SchlessingerConditionS1` and
`Deformation.SchlessingerConditionS2` do, and the second base map of (S2) is recognized as
the dual-number projection by `Deformation.IsDualNumberProjection`.

Injectivity in (S2) comes from the comparison clause of
`Deformation.SchlessingerConditionS2`: two completions over the same prescribed square have
the prescribed apex as base object, so the comparison morphism lies over the identity, and a
morphism of a category of elements lying over the identity forces its two elements to agree.

## References

* [Stacks Project, Tag 06HY](https://stacks.math.columbia.edu/tag/06HY)
-/

@[expose] public section

namespace Deformation

/-! ### Schlessinger's conditions for a set-valued functor -/

section
open CategoryTheory
universe u v w t u₁ v₁

/-- The comparison map from the value of a set-valued functor at the apex of a commutative
square to the fibre product of its values on the two sides of that square. -/
def fibreProductComparison {C : Type u₁} [Category.{v₁} C] (F : C ⥤ Type t)
    {A₁₂ A₁ A₂ A : C} (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hw : g₂ ≫ f₂ = g₁ ≫ f₁) :
    F.obj A₁₂ → {q : F.obj A₁ × F.obj A₂ // F.map f₁ q.1 = F.map f₂ q.2} :=
  fun a => ⟨(F.map g₁ a, F.map g₂ a), by
    simp only [← Functor.map_comp_apply, hw]⟩

/-- The two components of the comparison map are the two functorial images. -/
@[simp]
theorem fibreProductComparison_val {C : Type u₁} [Category.{v₁} C] (F : C ⥤ Type t)
    {A₁₂ A₁ A₂ A : C} (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hw : g₂ ≫ f₂ = g₁ ≫ f₁) (a : F.obj A₁₂) :
    (fibreProductComparison F g₁ g₂ f₁ f₂ hw a).1 = (F.map g₁ a, F.map g₂ a) :=
  rfl

/-- The first projection of a completion in a category of elements carries the transported
apex element to the first element of the cospan. -/
private theorem PullbackCompletion.map_apex_fst {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Type t}
    {x₁ x₂ x : F.Elements} {f₁ : x₁ ⟶ x} {f₂ : x₂ ⟶ x} {A₁₂ : C}
    {g₁ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₁} {g₂ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₂}
    (P : PullbackCompletion (CategoryOfElements.π F) f₁ f₂ g₁ g₂) :
    F.map g₁ (F.map (eqToHom P.apex_eq) P.apex.2) = x₁.2 := by
  have hP : P.toFirst.val = eqToHom P.apex_eq ≫ g₁ := P.map_toFirst
  rw [← Functor.map_comp_apply, ← hP]
  exact P.toFirst.property

/-- The second projection of a completion in a category of elements carries the transported
apex element to the second element of the cospan. -/
private theorem PullbackCompletion.map_apex_snd {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Type t}
    {x₁ x₂ x : F.Elements} {f₁ : x₁ ⟶ x} {f₂ : x₂ ⟶ x} {A₁₂ : C}
    {g₁ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₁} {g₂ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₂}
    (P : PullbackCompletion (CategoryOfElements.π F) f₁ f₂ g₁ g₂) :
    F.map g₂ (F.map (eqToHom P.apex_eq) P.apex.2) = x₂.2 := by
  have hP : P.toSecond.val = eqToHom P.apex_eq ≫ g₂ := P.map_toSecond
  rw [← Functor.map_comp_apply, ← hP]
  exact P.toSecond.property

/-- The completion of a cospan in a category of elements given by an element over the apex
whose two images are the elements of the cospan. -/
private def PullbackCompletion.ofElement {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Type t}
    {x₁ x₂ x : F.Elements} (f₁ : x₁ ⟶ x) (f₂ : x₂ ⟶ x) {A₁₂ : C}
    (g₁ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₁) (g₂ : A₁₂ ⟶ (CategoryOfElements.π F).obj x₂)
    (hw : g₂ ≫ (CategoryOfElements.π F).map f₂ = g₁ ≫ (CategoryOfElements.π F).map f₁)
    (a : F.obj A₁₂) (h₁ : F.map g₁ a = x₁.2) (h₂ : F.map g₂ a = x₂.2) :
    PullbackCompletion (CategoryOfElements.π F) f₁ f₂ g₁ g₂ :=
  ⟨F.elementsMk A₁₂ a, rfl, CategoryOfElements.homMk _ x₁ g₁ h₁,
    CategoryOfElements.homMk _ x₂ g₂ h₂, Subtype.ext hw, by simp, by simp⟩

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- For the category of elements of `F : 𝒞_Λ ⥤ Type t`, Schlessinger's condition (S1) says
that the map `F(A₁ ×_A A₂) → F(A₁) ×_{F(A)} F(A₂)` is surjective whenever `A₂ → A` is
surjective. -/
@[stacks 06HY "condition (S1)"]
theorem schlessingerConditionS1_elements_iff
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t) :
    SchlessingerConditionS1 (CategoryOfElements.π F) ↔
      ∀ ⦃A₁ A₂ A A₁₂ : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A),
        Function.Surjective f₂.hom →
          ∀ (g₁ : A₁₂ ⟶ A₁) (g₂ : A₁₂ ⟶ A₂) (hPB : IsPullback g₂ g₁ f₂ f₁),
            Function.Surjective (fibreProductComparison F g₁ g₂ f₁ f₂ hPB.w) := by
  refine ⟨fun hS1 A₁ A₂ A A₁₂ f₁ f₂ hf g₁ g₂ hPB ⟨⟨a₁, a₂⟩, hq⟩ => ?_, fun h => ⟨?_⟩⟩
  · obtain ⟨P⟩ := hS1.completion
      (CategoryOfElements.homMk (F.elementsMk A₁ a₁)
        (F.elementsMk A (F.map f₁ a₁)) f₁ rfl)
      (CategoryOfElements.homMk (F.elementsMk A₂ a₂)
        (F.elementsMk A (F.map f₁ a₁)) f₂ hq.symm) hf g₁ g₂ hPB
    exact ⟨F.map (eqToHom P.apex_eq) P.apex.2, Subtype.ext (Prod.ext P.map_apex_fst P.map_apex_snd)⟩
  · intro x₁ x₂ x u₁ u₂ hf A₁₂ g₁ g₂ hPB
    obtain ⟨a, ha⟩ := h u₁.val u₂.val hf g₁ g₂ hPB
      ⟨(x₁.2, x₂.2), u₁.property.trans u₂.property.symm⟩
    exact ⟨.ofElement u₁ u₂ g₁ g₂ hPB.w a (congrArg (·.1.1) ha) (congrArg (·.1.2) ha)⟩

/-- For the category of elements of `F : 𝒞_Λ ⥤ Type t`, Schlessinger's condition (S2) says
that the map `F(A ×_k k[ε]) → F(A) ×_{F(k)} F(k[ε])` is bijective. -/
@[stacks 06HY "condition (S2)"]
theorem schlessingerConditionS2_elements_iff
    (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type t) :
    SchlessingerConditionS2 (CategoryOfElements.π F) ↔
      ∀ ⦃A A₀ Aε B : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (d : A ⟶ A₀) (e : Aε ⟶ A₀),
        IsDualNumberProjection e →
          ∀ (g : B ⟶ A) (gε : B ⟶ Aε) (hPB : IsPullback gε g e d),
            Function.Bijective (fibreProductComparison F g gε d e hPB.w) := by
  constructor
  · intro hS2 A A₀ Aε B d e hdual g gε hPB
    refine ⟨fun b b' hbb => ?_, fun ⟨⟨a, aε⟩, hq⟩ => ?_⟩
    · have hg : F.map g b' = F.map g b := (congrArg (·.1.1) hbb).symm
      have hgε : F.map gε b' = F.map gε b := (congrArg (·.1.2) hbb).symm
      have hw : F.map e (F.map gε b) = F.map d (F.map g b) := by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, hPB.w]
      obtain ⟨β, -, hmap⟩ := hS2.comparison
        (CategoryOfElements.homMk (F.elementsMk A (F.map g b))
          (F.elementsMk A₀ (F.map d (F.map g b))) d rfl)
        (CategoryOfElements.homMk (F.elementsMk Aε (F.map gε b))
          (F.elementsMk A₀ (F.map d (F.map g b))) e hw) hdual g gε hPB
        ⟨F.elementsMk B b, rfl,
          CategoryOfElements.homMk (F.elementsMk B b) (F.elementsMk A (F.map g b)) g rfl,
          CategoryOfElements.homMk (F.elementsMk B b) (F.elementsMk Aε (F.map gε b)) gε rfl,
          Subtype.ext hPB.w, by simp, by simp⟩
        ⟨F.elementsMk B b', rfl,
          CategoryOfElements.homMk (F.elementsMk B b') (F.elementsMk A (F.map g b)) g hg,
          CategoryOfElements.homMk (F.elementsMk B b') (F.elementsMk Aε (F.map gε b)) gε hgε,
          Subtype.ext hPB.w, by simp, by simp⟩
      have hval : β.val = 𝟙 B := by simpa using (hmap : β.val = eqToHom rfl ≫ eqToHom rfl)
      simpa [hval] using β.property
    · obtain ⟨P⟩ := hS2.completion
        (CategoryOfElements.homMk (F.elementsMk A a) (F.elementsMk A₀ (F.map d a)) d rfl)
        (CategoryOfElements.homMk (F.elementsMk Aε aε) (F.elementsMk A₀ (F.map d a)) e
          hq.symm) hdual g gε hPB
      exact ⟨F.map (eqToHom P.apex_eq) P.apex.2,
        Subtype.ext (Prod.ext P.map_apex_fst P.map_apex_snd)⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x xε x₀ ud ue hdual B g gε hPB
      obtain ⟨a, ha⟩ := (h ud.val ue.val hdual g gε hPB).2
        ⟨(x.2, xε.2), ud.property.trans ue.property.symm⟩
      exact ⟨.ofElement ud ue g gε hPB.w a (congrArg (·.1.1) ha) (congrArg (·.1.2) ha)⟩
    · intro x xε x₀ ud ue hdual B g gε hPB P Q
      have hPv : P.toFirst.val = eqToHom P.apex_eq ≫ g := P.map_toFirst
      have hQv : Q.toFirst.val = eqToHom Q.apex_eq ≫ g := Q.map_toFirst
      have hbb : F.map (eqToHom P.apex_eq) P.apex.2 = F.map (eqToHom Q.apex_eq) Q.apex.2 :=
        (h ud.val ue.val hdual g gε hPB).1 (Subtype.ext (Prod.ext
          (P.map_apex_fst.trans Q.map_apex_fst.symm)
          (P.map_apex_snd.trans Q.map_apex_snd.symm)))
      refine ⟨⟨eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm, ?_⟩, ?_, rfl⟩
      · rw [Functor.map_comp_apply, hbb, ← Functor.map_comp_apply]
        simp
      · refine Subtype.ext ?_
        simp only [CategoryOfElements.comp_val, hPv, hQv]
        simp

end

end Deformation

end
