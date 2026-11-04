module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject

/-!
# Noetherian objects from essential constancy of chains of subobjects

Let `C` be a category with countable filtered colimits satisfying AB5 and let `X` be an object
of `C`. If a property `P` of objects of `C` passes to subobjects, holds for `X`, and makes every
ascending chain of `P`-subobjects of `X` with `P`-colimit essentially constant, then `X` is a
Noetherian object: every ascending chain of subobjects of `X` stabilizes.

## Main definitions

* `Stacks.Subobject.monoOverDiagram` — the diagram in `C` underlying a chain `ℕ ⥤ MonoOver X` of
  subobjects of `X`.
* `Stacks.Subobject.monoOverCocone` — the cocone on that diagram with vertex `X` whose legs are
  the inclusions.
* `Stacks.Subobject.monoOverColimitMap` — the canonical map from the colimit of the chain to `X`.

## Main results

* `Stacks.Subobject.mono_monoOverColimitMap` — under AB5 the map from the colimit of a chain of
  subobjects of `X` to `X` is again a monomorphism.
* `Stacks.Subobject.isNoetherianObject_of_subobject_essentiallyConstant` — if a property `P`
  passes to subobjects, holds for `X`, and makes every chain of `P`-subobjects of `X` with
  `P`-colimit essentially constant, then `X` is a Noetherian object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Subobject

variable {C : Type u} [Category.{v} C] {X : C}

/-- The diagram in `C` underlying a chain of subobjects of `X`. -/
public abbrev monoOverDiagram (F : ℕ ⥤ MonoOver X) : ℕ ⥤ C :=
  F ⋙ MonoOver.forget X ⋙ Over.forget X

/-- The cocone on `monoOverDiagram F` with vertex `X` whose legs are the inclusions. -/
public def monoOverCocone (F : ℕ ⥤ MonoOver X) : Cocone (monoOverDiagram F) where
  pt := X
  ι :=
    { app n := (F.obj n).arrow
      naturality := by
        intro n m f
        simp [monoOverDiagram] }

/-- The canonical map from the colimit of a chain of subobjects of `X` to `X`. -/
public def monoOverColimitMap [HasColimitsOfShape ℕ C] (F : ℕ ⥤ MonoOver X) :
    colimit (monoOverDiagram F) ⟶ X :=
  colimit.desc (monoOverDiagram F) (monoOverCocone F)

/-- Under AB5 the colimit of a chain of subobjects of `X` is again a subobject of `X`. -/
public theorem mono_monoOverColimitMap [HasFilteredColimitsOfSize.{0, 0} C]
    [AB5OfSize.{0, 0} C] (F : ℕ ⥤ MonoOver X) : Mono (monoOverColimitMap F) := by
  let G := monoOverDiagram F
  let α : G ⟶ (Functor.const ℕ).obj X :=
    { app n := (F.obj n).arrow
      naturality := by
        intro n m f
        dsimp [G, monoOverDiagram]
        simpa only [Category.comp_id] using MonoOver.w (F.map f) }
  have : Mono α := NatTrans.mono_of_mono_app α
  let : HasExactColimitsOfShape ℕ C := AB5OfSize.ofShape (C := C) ℕ
  let : PreservesLimitsOfShape WalkingCospan (colim (J := ℕ) (C := C)) := inferInstance
  let : IsConnected ℕ := IsFiltered.isConnected ℕ
  exact colim.map_mono' α (colimit.isColimit G) (isColimitConstCocone ℕ X)
    (monoOverColimitMap F) (by
      intro n
      show colimit.ι G n ≫ colimit.desc G (monoOverCocone F) = (F.obj n).arrow ≫ 𝟙 X
      rw [colimit.ι_desc]
      simp [monoOverCocone])

/-- If a property `P` of objects passes to subobjects, holds for `X`, and makes every chain of
`P`-subobjects of `X` with `P`-colimit essentially constant, then `X` is a Noetherian object. -/
public theorem isNoetherianObject_of_subobject_essentiallyConstant
    [HasFilteredColimitsOfSize.{0, 0} C] [AB5OfSize.{0, 0} C]
    (X : C) (P : C → Prop)
    (hsub : ∀ ⦃A B : C⦄ (f : A ⟶ B), Mono f → P B → P A)
    (hess : ∀ (F : ℕ ⥤ MonoOver X) (t : Cocone (monoOverDiagram F)), IsColimit t →
      (∀ n, P ((monoOverDiagram F).obj n)) → P t.pt →
      ∃ (i : ℕ) (r : t.pt ⟶ (monoOverDiagram F).obj i),
        EssentiallyConstantInd.IsEssentiallyConstantWith (monoOverDiagram F) t i r)
    (hX : P X) : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_isEventuallyConstant]
  intro F
  let G := monoOverDiagram F
  let t : Cocone G := colimit.cocone G
  have hf (n : ℕ) : t.ι.app n ≫ monoOverColimitMap F = (F.obj n).arrow := colimit.ι_desc _ _
  have hmono (n : ℕ) : Mono (t.ι.app n) := mono_of_mono_fac (hf n)
  obtain ⟨i, r, hr⟩ := hess F t (colimit.isColimit G) (fun n => hsub _ (F.obj n).2 hX)
    (hsub _ (mono_monoOverColimitMap F) hX)
  have := hmono i
  have : IsSplitEpi (t.ι.app i) := IsSplitEpi.mk' ⟨r, hr.retraction⟩
  have := isIso_of_mono_of_isSplitEpi (t.ι.app i)
  refine ⟨i, fun j g => ?_⟩
  have hg : G.map g ≫ t.ι.app j = t.ι.app i := t.w g
  have := hmono j
  have : IsSplitEpi (t.ι.app j) := IsSplitEpi.mk' ⟨inv (t.ι.app i) ≫ G.map g, by simp [hg]⟩
  have := isIso_of_mono_of_isSplitEpi (t.ι.app j)
  exact (MonoOver.isIso_iff_isIso_hom_left (F.map g)).2 (IsIso.of_isIso_fac_right hg)

end Stacks.Subobject

end
