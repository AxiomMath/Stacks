module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Final.Connected
import StacksCore.Tactic.StacksAttribute

/-! # Final and initial functors -/

@[expose] public section

open CategoryTheory Functor

add_to_stacks 04E7 "either colimit exists iff the other does" Final.isColimitWhiskerEquiv

add_to_stacks 09WP Initial

add_to_stacks 002R Initial.limitIso
add_to_stacks 002R "either limit exists iff the other does" Initial.isLimitWhiskerEquiv

/-- A functor `F : C ⥤ D` is *surjective on arrows* if every morphism in `D` is the image of some
morphism in `C` under `F`. This notion is evil in the sense that it is not invariant under
equivalence, but still occasionally useful.

Note that we can't state "`f : X ⟶ Y` is the image of a morphism in `C`" directly as
`∃ (X' Y' : C) (f' : X' ⟶ Y'), f' = f` because `f` and `f'` a priori have different types, and
equality of types is bad to work with; we get around this by instead stating that `f` lies in the
inductively defined `MorphismProperty.strictMap ⊤ F`. Given `hf : MorphismProperty.strictMap ⊤ F f`,
`obtain @⟨X', Y', f'⟩ := hf` will introduce new variables `X' Y' : C` and `f' : X' ⟶ Y'` and
replace all occurences of `X`, `Y` and `f` in the current context with
`F.obj X'`, `F.obj Y'` and `F.map f'`. -/
class CategoryTheory.Functor.SurjectiveOnArrows {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) : Prop where
  mem_strictMap_top {X Y : D} (f : X ⟶ Y) : MorphismProperty.strictMap ⊤ F f

lemma CategoryTheory.Functor.mem_strictMap_top {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.SurjectiveOnArrows] {X Y : D} (f : X ⟶ Y) : MorphismProperty.strictMap ⊤ F f :=
  SurjectiveOnArrows.mem_strictMap_top f

lemma CategoryTheory.Functor.exists_isHomLift {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.SurjectiveOnArrows] {X Y : D} (f : X ⟶ Y) :
    ∃ (X' Y' : C) (f' : X' ⟶ Y'), IsHomLift F f f' := by
  obtain @⟨X', Y', f'⟩ := F.mem_strictMap_top f
  exact ⟨X', Y', f', .map f'⟩

/-- Any functor `F : I ⥤ I'` whose fibre categories are all connected and which is surjective on
arrows is final. -/
@[stacks 05US "implies the lemma via `04E7`"]
lemma CategoryTheory.Functor.final_of_isConnected_fiber {I I' : Type*} [Category* I] [Category* I']
    (F : I ⥤ I') [∀ i, IsConnected (F.Fiber i)] [F.SurjectiveOnArrows] :
    F.Final := by
  refine ⟨fun X ↦ ?_⟩
  let ι {Y : I'} (f : X ⟶ Y) : F.Fiber Y ⥤ StructuredArrow X F := {
    obj Y' := .mk <| f ≫ eqToHom Y'.2.symm
    map g := StructuredArrow.homMk g.1 <|
      (congrArg (_ ≫ ·) (@IsHomLift.fac' _ _ _ _ F _ _ _ _ (𝟙 Y) g.1 g.2)).trans (by simp) }
  suffices h : ∀ f' : StructuredArrow X F, ∃ X' : F.Fiber X, Zigzag f' (.mk <| eqToHom X'.2.symm) by
    refine @zigzag_isConnected _ _ ⟨.mk <| eqToHom (Classical.arbitrary (F.Fiber X)).2.symm⟩ ?_
    intro f g
    obtain ⟨Y, hY⟩ := (h f)
    obtain ⟨Z, hZ⟩ := (h g)
    refine (hY.trans ?_).trans hZ.symm
    simpa [ι] using zigzag_obj_of_zigzag (ι (𝟙 X)) <| isPreconnected_zigzag Y Z
  intro ⟨_, Y, (f : X ⟶ _)⟩
  obtain ⟨X', Y', f', hf'⟩ := F.exists_isHomLift f
  refine ⟨⟨X', IsHomLift.domain_eq F f f'⟩, ?_⟩
  change Zigzag (StructuredArrow.mk f) _
  have := zigzag_obj_of_zigzag (ι f) <| isPreconnected_zigzag
    ⟨Y', IsHomLift.codomain_eq F f f'⟩ ⟨Y, rfl⟩
  simp only [eqToHom_refl, Category.comp_id, ι] at this
  refine this.symm.trans <| .of_inv <| StructuredArrow.homMk f' ?_
  simp [IsHomLift.fac' F f f']

add_to_stacks 0A2B "variant for the first projection; implies the lemma via `04E7`"
  CategoryTheory.final_fst
add_to_stacks 0A2B "variant for the second projection; implies the lemma via `04E7`"
  CategoryTheory.final_snd
