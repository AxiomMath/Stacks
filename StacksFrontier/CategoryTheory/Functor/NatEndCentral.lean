module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Whiskering

/-!
# Functors whose natural endomorphisms are central

A functor `F : C ⥤ D` has *central natural endomorphisms* when every natural endomorphism `δ` of
`F` commutes with every morphism `F.obj X ⟶ F.obj Y`, including those that are not of the form
`F.map g`. Extension of scalars along a homomorphism of commutative rings is the basic example
(`ModuleCat.ExtendScalars.natTrans_app_comp_eq`): its natural endomorphisms are multiplications
by scalars.

The property is invariant under isomorphism of functors, passes to a composite with a fully
faithful functor, and descends along precomposition with an essentially surjective functor.
These are the operations that carry it from extension of scalars of modules to the inverse image
of quasi-coherent modules along a morphism of affine schemes, read on any of its equivalent
models.

## Main definitions

* `CategoryTheory.Functor.NatEndCentral`: every natural endomorphism commutes with every morphism
  between values.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']

/-- Every natural endomorphism of `F` commutes with every morphism between values of `F`. -/
def NatEndCentral (F : C ⥤ D) : Prop :=
  ∀ (δ : F ⟶ F) {X Y : C} (φ : F.obj X ⟶ F.obj Y), δ.app X ≫ φ = φ ≫ δ.app Y

/-- Commutation of `dX` and `dY` with `φ` follows from commutation after conjugating `φ` by an
epimorphism and a monomorphism that are compatible with the endomorphisms. -/
private theorem comm_of_conj {E : Type*} [Category E] {X X' Y Y' : E}
    {dX : X ⟶ X} {dX' : X' ⟶ X'} {dY : Y ⟶ Y} {dY' : Y' ⟶ Y'} {φ : X ⟶ Y}
    (a : X' ⟶ X) (b : Y ⟶ Y') [Epi a] [Mono b] (ha : a ≫ dX = dX' ≫ a)
    (hb : b ≫ dY' = dY ≫ b) (h : dX' ≫ a ≫ φ ≫ b = (a ≫ φ ≫ b) ≫ dY') : dX ≫ φ = φ ≫ dY := by
  rw [← cancel_epi a, ← cancel_mono b]
  simpa [reassoc_of% ha, ← hb] using h

/-- Central natural endomorphisms are invariant under isomorphism of functors. -/
theorem NatEndCentral.of_iso {F F' : C ⥤ D} (e : F ≅ F') (h : F'.NatEndCentral) :
    F.NatEndCentral := fun δ X Y φ =>
  comm_of_conj (e.inv.app X) (e.hom.app Y) (by simp) (by simp)
    (h (e.inv ≫ δ ≫ e.hom) (e.inv.app X ≫ φ ≫ e.hom.app Y))

/-- Central natural endomorphisms pass to a composite with a fully faithful functor. -/
theorem NatEndCentral.comp {F : C ⥤ D} {d : D ⥤ D'} (hd : d.FullyFaithful)
    (h : F.NatEndCentral) : (F ⋙ d).NatEndCentral := by
  intro δ X Y φ
  let δ' : F ⟶ F :=
    { app := fun X => hd.preimage (δ.app X)
      naturality := fun X Y g => hd.map_injective (by
        rw [Functor.map_comp, Functor.map_comp, FullyFaithful.map_preimage,
          FullyFaithful.map_preimage]
        exact δ.naturality g) }
  obtain ⟨ψ, rfl⟩ := hd.map_surjective φ
  have h₁ : δ.app X = d.map (δ'.app X) := (hd.map_preimage _).symm
  have h₂ : δ.app Y = d.map (δ'.app Y) := (hd.map_preimage _).symm
  rw [h₁, h₂, ← d.map_comp, ← d.map_comp, h δ' ψ]

/-- Central natural endomorphisms descend from a composite with a faithful functor. -/
theorem NatEndCentral.of_comp_faithful {F : C ⥤ D} {d : D ⥤ D'} [d.Faithful]
    (h : (F ⋙ d).NatEndCentral) : F.NatEndCentral := by
  intro δ X Y φ
  apply d.map_injective
  rw [d.map_comp, d.map_comp]
  exact h (Functor.whiskerRight δ d) (d.map φ)

/-- Central natural endomorphisms descend along precomposition with an essentially surjective
functor. -/
theorem NatEndCentral.of_comp {F : C ⥤ D} {e : C' ⥤ C} [e.EssSurj]
    (h : (e ⋙ F).NatEndCentral) : F.NatEndCentral := by
  intro δ X Y φ
  let iX := e.objObjPreimageIso X
  let iY := e.objObjPreimageIso Y
  exact comm_of_conj (F.map iX.hom) (F.map iY.inv) (δ.naturality _) (δ.naturality _)
    (h (Functor.whiskerLeft e δ) (F.map iX.hom ≫ φ ≫ F.map iY.inv))

end CategoryTheory.Functor

end
