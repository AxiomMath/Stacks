module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Precomposing a right derived functor with an exact functor preserving injectives, naturally

Let `G : A ⥤ B` be an additive functor between abelian categories with injective resolutions
which preserves homology and injective objects, and let `H : B ⥤ C` be additive.
`CategoryTheory.Functor.rightDerivedCompIsoOfPreservesInjectiveObjects` identifies
`((G ⋙ H).rightDerived q).obj X` with `(H.rightDerived q).obj (G.obj X)` for each object `X`,
by carrying an injective resolution of `X` to one of `G X`. This file proves that this
identification, read without the intermediate comparison of mapped complexes, is natural in `X`,
and so assembles it into a natural isomorphism

`(G ⋙ H).rightDerived q ≅ G ⋙ H.rightDerived q`.

## Main results

* `CategoryTheory.Functor.rightDerivedCompObjIsoOfPreservesInjectiveObjects_hom_naturality`:
  the naturality.
* `CategoryTheory.Functor.rightDerivedCompNatIsoOfPreservesInjectiveObjects`: the natural
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (G : A ⥤ B) (H : B ⥤ C) [G.Additive] [H.Additive] [G.PreservesHomology]
  [G.PreservesInjectiveObjects]

/-- The identification of `R^q(G ⋙ H)` with `R^q H ∘ G` at an object `X`: the right derived
functor of `G ⋙ H` is computed by the chosen injective resolution of `X`, and that of `H` at `G X`
by its image under `G`, which is an injective resolution of `G X`; the two complexes computing the
cohomology are the same. -/
@[sga "4 V 2.2" "more general"]
def rightDerivedCompObjIsoOfPreservesInjectiveObjects (X : A) (q : ℕ) :
    ((G ⋙ H).rightDerived q).obj X ≅ (H.rightDerived q).obj (G.obj X) :=
  (injectiveResolution X).isoRightDerivedObj (G ⋙ H) q ≪≫
    ((mapInjectiveResolution G (injectiveResolution X)).isoRightDerivedObj H q).symm

/-- **The identification of `R^q(G ⋙ H)` with `R^q H ∘ G` is natural.** Both sides of a morphism
`f : X ⟶ Y` are computed from a morphism of injective resolutions lifting `f`, and its image
under `G` is a morphism of the image resolutions lifting `G f`. -/
@[reassoc]
lemma rightDerivedCompObjIsoOfPreservesInjectiveObjects_hom_naturality {X Y : A} (f : X ⟶ Y)
    (q : ℕ) :
    ((G ⋙ H).rightDerived q).map f ≫
        (rightDerivedCompObjIsoOfPreservesInjectiveObjects G H Y q).hom =
      (rightDerivedCompObjIsoOfPreservesInjectiveObjects G H X q).hom ≫
        (H.rightDerived q).map (G.map f) := by
  let RX := injectiveResolution X
  let RY := injectiveResolution Y
  let φ := InjectiveResolution.desc f RY RX
  have hc : (mapInjectiveResolution G RX).ι ≫ (G.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ B).map (G.map f) ≫ (mapInjectiveResolution G RY).ι := by
    show ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X ≫
        (G.mapHomologicalComplex _).map RX.ι) ≫ (G.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ B).map (G.map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app Y ≫
          (G.mapHomologicalComplex _).map RY.ι)
    rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.naturality
      f).symm
  have commG : (mapInjectiveResolution G RX).ι.f 0 ≫ ((G.mapHomologicalComplex _).map φ).f 0 =
      G.map f ≫ (mapInjectiveResolution G RY).ι.f 0 := by
    have := HomologicalComplex.congr_hom hc 0
    simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at this
    exact this
  have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality f RX RY φ
    (InjectiveResolution.desc_commutes_zero f RY RX) (G ⋙ H) q
  have h2 := InjectiveResolution.isoRightDerivedObj_inv_naturality (G.map f)
    (mapInjectiveResolution G RX) (mapInjectiveResolution G RY)
    ((G.mapHomologicalComplex _).map φ) commG H q
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm))

/-- **Precomposing with an exact functor which preserves injective objects, as a natural
isomorphism**: `(G ⋙ H).rightDerived q ≅ G ⋙ H.rightDerived q`, with components
`CategoryTheory.Functor.rightDerivedCompObjIsoOfPreservesInjectiveObjects`. -/
def rightDerivedCompNatIsoOfPreservesInjectiveObjects (q : ℕ) :
    (G ⋙ H).rightDerived q ≅ G ⋙ H.rightDerived q :=
  NatIso.ofComponents (fun X => rightDerivedCompObjIsoOfPreservesInjectiveObjects G H X q)
    (fun f => rightDerivedCompObjIsoOfPreservesInjectiveObjects_hom_naturality G H f q)

end CategoryTheory.Functor

end
