module

public import Mathlib.Algebra.Homology.Additive

/-!
# Squares of additive functors read degreewise on complexes

For additive functors with `F ⋙ G ≅ F' ⋙ G''`, the induced isomorphism of the degreewise
functors on complexes is `cxIso`. This file proves that `cxIso` carries a pasting identity of
squares of functors to the corresponding identity of morphisms of complexes. Everything is stated
with every category and functor a variable.

## Main definitions

* `Stacks.LimitHomDescent.cxIso`: the isomorphism of degreewise functors induced by a square.

## Main results

* `Stacks.LimitHomDescent.cxIso_cocycle`: the pasting identity, on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LimitHomDescent

variable {ι : Type*} (c : ComplexShape ι)

/-- The isomorphism of the degreewise functors on complexes induced by an isomorphism of
composites `F ⋙ G ≅ F' ⋙ G''`. -/
def cxIso {X Y Z W : Type*} [Category* X] [Category* Y] [Category* Z] [Category* W]
    [Preadditive X] [Preadditive Y] [Preadditive Z] [Preadditive W]
    {F : X ⥤ Y} {G : Y ⥤ W} {F' : X ⥤ Z} {G' : Z ⥤ W}
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] (q : F ⋙ G ≅ F' ⋙ G') :
    F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      F'.mapHomologicalComplex c ⋙ G'.mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
    NatIso.mapHomologicalComplex q c ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G')) c).symm

variable {C₀ D₀ D₁ D₂ M₁ M₂ : Type*} [Category* C₀] [Category* D₀] [Category* D₁]
  [Category* D₂] [Category* M₁] [Category* M₂] [Preadditive C₀] [Preadditive D₀]
  [Preadditive D₁] [Preadditive D₂] [Preadditive M₁] [Preadditive M₂]
  {T : C₀ ⥤ D₀} {G₁ : D₀ ⥤ D₁} {G₂ : D₁ ⥤ D₂} {G : D₀ ⥤ D₂}
  {E₁ : C₀ ⥤ M₁} {E₂ : M₁ ⥤ M₂} {E : C₀ ⥤ M₂} {T₁ : M₁ ⥤ D₁} {T₂ : M₂ ⥤ D₂}
  [T.Additive] [G₁.Additive] [G₂.Additive] [G.Additive] [E₁.Additive] [E₂.Additive]
  [E.Additive] [T₁.Additive] [T₂.Additive]

/-- **The pasting identity of squares of functors, on complexes.** -/
theorem cxIso_cocycle (a : G ≅ G₁ ⋙ G₂) (p₁ : T ⋙ G₁ ≅ E₁ ⋙ T₁) (p₂ : T₁ ⋙ G₂ ≅ E₂ ⋙ T₂)
    (p : T ⋙ G ≅ E ⋙ T₂) (e : E ≅ E₁ ⋙ E₂)
    (h : p = Functor.isoWhiskerLeft T a ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight p₁ G₂ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E₁ p₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.symm T₂)
    (K : HomologicalComplex C₀ c) :
    (NatTrans.mapHomologicalComplex a.inv c).app ((T.mapHomologicalComplex c).obj K) ≫
        (cxIso c p).hom.app K =
      (G₂.mapHomologicalComplex c).map ((cxIso c p₁).hom.app K) ≫
        (cxIso c p₂).hom.app ((E₁.mapHomologicalComplex c).obj K) ≫
        (T₂.mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso e.symm c).app K).hom := by
  subst h
  ext n
  simp [cxIso, Functor.mapHomologicalComplexCompIso]

end Stacks.LimitHomDescent
