module

public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Naturality of the objectwise conjugate of a comparison of two composites

Let `e : C ≌ D` and `e' : C' ≌ D'` be equivalences, let `F : D ⥤ D'` and `G : C ⥤ C'` be
functors, and let

`α : F ⋙ e'.inverse ≅ e.inverse ⋙ G`

be an isomorphism comparing the two ways round the square. Its objectwise conjugate is the
isomorphism

`F.obj (e.functor.obj M) ≅ e'.functor.obj (G.obj M)`

for an object `M` of `C`, which is `α` read at `e.functor.obj M` and corrected by the unit of `e`
and the counit of `e'`. A family of isomorphisms given by that formula is natural in `M`, by the
naturality of `α`, of the unit of `e` and of the counit of `e'`. The family and the formula for it
are hypotheses, the formula being an equation of *isomorphisms*.

## Main results

* `Stacks.Equivalence.conjugateObjIso_naturality`: **the objectwise conjugate of `α` is natural
  in the object.**
* `Stacks.Equivalence.conjugateObjIso_naturality_trans`: the same for the conjugate followed by the
  image under `e'.functor` of a component of a natural isomorphism of the right-hand functor.
* `Stacks.Equivalence.trans_naturality`: an isomorphism presented as a composite of two
  isomorphisms is natural as soon as each factor is, with the presentations supplied as equations
  of *isomorphisms*.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.Equivalence

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']

/-- **The objectwise conjugate of a comparison `α : F ⋙ e'.inverse ≅ e.inverse ⋙ G` is natural
in the object.**

The family `Θ` is the comparison `α` read at `e.functor.obj M`, preceded by the inverse counit
of `e'` and followed by the image under `e'.functor` of the inverse unit of `e`; that formula is
the hypothesis `hΘ`. -/
theorem conjugateObjIso_naturality (e : C ≌ D) (e' : C' ≌ D') (F : D ⥤ D') (G : C ⥤ C')
    (α : F ⋙ e'.inverse ≅ e.inverse ⋙ G)
    (Θ : ∀ M : C, F.obj (e.functor.obj M) ≅ e'.functor.obj (G.obj M))
    (hΘ : ∀ M : C, Θ M = (e'.counitIso.app (F.obj (e.functor.obj M))).symm ≪≫
      e'.functor.mapIso (α.app (e.functor.obj M) ≪≫ G.mapIso (e.unitIso.app M).symm))
    {M N : C} (φ : M ⟶ N) :
    F.map (e.functor.map φ) ≫ (Θ N).hom = (Θ M).hom ≫ e'.functor.map (G.map φ) := by
  have hunit : e.inverse.map (e.functor.map φ) ≫ e.unitIso.inv.app N =
      e.unitIso.inv.app M ≫ φ := e.unitIso.inv.naturality φ
  have hG : G.map (e.inverse.map (e.functor.map φ)) ≫ G.map (e.unitIso.inv.app N) =
      G.map (e.unitIso.inv.app M) ≫ G.map φ := by
    rw [← G.map_comp, ← G.map_comp, hunit]
  have hα : e'.inverse.map (F.map (e.functor.map φ)) ≫ α.hom.app (e.functor.obj N) =
      α.hom.app (e.functor.obj M) ≫ G.map (e.inverse.map (e.functor.map φ)) :=
    α.hom.naturality (e.functor.map φ)
  have hmid : e'.inverse.map (F.map (e.functor.map φ)) ≫
        (α.hom.app (e.functor.obj N) ≫ G.map (e.unitIso.inv.app N)) =
      (α.hom.app (e.functor.obj M) ≫ G.map (e.unitIso.inv.app M)) ≫ G.map φ := by
    rw [← Category.assoc, hα, Category.assoc, hG, Category.assoc]
  have hcounit : F.map (e.functor.map φ) ≫ e'.counitIso.inv.app (F.obj (e.functor.obj N)) =
      e'.counitIso.inv.app (F.obj (e.functor.obj M)) ≫
        e'.functor.map (e'.inverse.map (F.map (e.functor.map φ))) :=
    e'.counitIso.inv.naturality (F.map (e.functor.map φ))
  rw [hΘ M, hΘ N]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [← Category.assoc, hcounit, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hmid]

/-- **The same, for a conjugate followed by a component of a natural isomorphism.**

If `Θ` is the objectwise conjugate of `α` and `Ξ M = Θ M ≪≫ e'.functor.mapIso (β.app M)` for a
natural isomorphism `β : G ≅ H` of the right-hand functor, then `Ξ` is natural in `M`. -/
theorem conjugateObjIso_naturality_trans (e : C ≌ D) (e' : C' ≌ D') (F : D ⥤ D') (G H : C ⥤ C')
    (α : F ⋙ e'.inverse ≅ e.inverse ⋙ G) (β : G ≅ H)
    (Θ : ∀ M : C, F.obj (e.functor.obj M) ≅ e'.functor.obj (G.obj M))
    (hΘ : ∀ M : C, Θ M = (e'.counitIso.app (F.obj (e.functor.obj M))).symm ≪≫
      e'.functor.mapIso (α.app (e.functor.obj M) ≪≫ G.mapIso (e.unitIso.app M).symm))
    (Ξ : ∀ M : C, F.obj (e.functor.obj M) ≅ e'.functor.obj (H.obj M))
    (hΞ : ∀ M : C, Ξ M = Θ M ≪≫ e'.functor.mapIso (β.app M))
    {M N : C} (φ : M ⟶ N) :
    F.map (e.functor.map φ) ≫ (Ξ N).hom = (Ξ M).hom ≫ e'.functor.map (H.map φ) := by
  have hβ : G.map φ ≫ β.hom.app N = β.hom.app M ≫ H.map φ := β.hom.naturality φ
  have hΘnat := conjugateObjIso_naturality e e' F G α Θ hΘ φ
  rw [hΞ M, hΞ N]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc, hΘnat, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hβ]

/-- **A comparison presented as a composite of two isomorphisms is natural as soon as each
factor is.**

If `Ξ = Θ ≪≫ γ` and `Ξ' = Θ' ≪≫ γ'` as isomorphisms, and the squares of `Θ`, `Θ'` and of `γ`,
`γ'` commute on `hom` components, then so does the square of `Ξ`, `Ξ'`. -/
theorem trans_naturality {𝒳 : Type u₁} [Category.{v₁} 𝒳] {P P' R R' Q Q' : 𝒳}
    {p : P ⟶ P'} {r : R ⟶ R'} {q : Q ⟶ Q'} {Θ : P ≅ R} {Θ' : P' ≅ R'} {γ : R ≅ Q} {γ' : R' ≅ Q'}
    {Ξ : P ≅ Q} {Ξ' : P' ≅ Q'} (hΞ : Ξ = Θ ≪≫ γ) (hΞ' : Ξ' = Θ' ≪≫ γ')
    (hΘ : p ≫ Θ'.hom = Θ.hom ≫ r) (hγ : r ≫ γ'.hom = γ.hom ≫ q) :
    p ≫ Ξ'.hom = Ξ.hom ≫ q := by
  rw [hΞ, hΞ', Iso.trans_hom, Iso.trans_hom]
  exact square_comp hΘ hγ

end Stacks.Equivalence

end
