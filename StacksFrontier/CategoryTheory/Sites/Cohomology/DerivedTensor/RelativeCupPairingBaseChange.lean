module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.CategoryTheory.Adjunction.TransportedBaseChangeSquare

/-!
# The pairing of a relative cup product and base change, over abstract adjunctions

Let `Lf ⊣ Rf` (between `S` and `T`) and `Lf' ⊣ Rf'` (between `S'` and `T'`) be adjunctions, with
functors `Lg : S ⥤ S'`, `Lg' : T ⥤ T'`, bifunctors `A`, `A'`, `B`, `B'` on the four categories
and comparisons along the four functors, and let `bc : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` be a base change
morphism compatible with the cup products (`hcup`, the form of [Stacks, Tag 0H9A]).

For an object `E` of `T`, a multiplication `w : B(E, E) ⟶ E`, a trace `t : Rf E ⟶ Z` and an
identification `u : Lg' E ≅ E'`, the pairing `(a, b) ↦ t(w_*(b ∪ a))` on `Rf E` is carried by
`Lg` to the pairing on `Rf' E'` built from the multiplication `w'` and the trace `t'` read
through `u` and through the base change map (`adjunctionCupPairing_baseChange`).

## Main results

In `Stacks.Cohomology.RelativeCupProductOnRingedTopoi`:

* `adjunctionCupProduct_baseChange_comp`: base change carries the cup product on `Rf E`
  followed by `Rf w` to the cup product on `Rf' E'` followed by `Rf' w'`.
* `adjunctionCupPairing_baseChange`: base change carries the pairing on `Rf E` to the pairing
  on `Rf' E'`.

In `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi`:

* `TensorHomAdjunction.uncurry_transportTensor_map_braiding`: a transported commutativity
  constraint is natural.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

/-- **A transported commutativity constraint is natural**: for `b : T ⟶ T.flip` on `D` and an
equivalence `e : D' ≌ D`, the constraint `e⁻¹(b(e -, e -))` of the transported bifunctor commutes
with the transported bifunctor applied to a pair of morphisms. -/
theorem uncurry_transportTensor_map_braiding {D D' : Type*} [Category D] [Category D']
    (e : D' ≌ D) (T : D ⥤ D ⥤ D) (b : T ⟶ T.flip) {x x' y y' : D'} (u : x ⟶ x') (v : y ⟶ y') :
    (Functor.uncurry.obj (transportTensor e T)).map (u ×ₘ v) ≫
        e.inverse.map ((b.app (e.functor.obj x')).app (e.functor.obj y')) =
      e.inverse.map ((b.app (e.functor.obj x)).app (e.functor.obj y)) ≫
        (Functor.uncurry.obj (transportTensor e T)).map (v ×ₘ u) := by
  have h := Stacks.CategoryTheory.ProjectionMapTransport.uncurry_map_braiding T b
    (e.functor.map u) (e.functor.map v)
  have h' := congrArg e.inverse.map h
  simp only [Functor.map_comp, Functor.uncurry_obj_map] at h'
  simpa only [Functor.uncurry_obj_map, transportTensor_map_app, transportTensor_obj_map,
    Category.assoc] using h'

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

variable {S T S' T' : Type*} [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ≅ Lg'.prod Lg' ⋙ B')
  (bc : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')

/-- **The cup product followed by a multiplication, carried to the base change.** If the cup
products are compatible with the base change morphism `bc` at `(E, E)` (`hcup`, the form of
[Stacks, Tag 0H9A]), then for `u : Lg' E ≅ E'` and `w : B(E, E) ⟶ E`, the image under `Lg` of
the cup product followed by `Rf w`, followed by `κ := bc_E ≫ Rf'(u)`, is the comparison along
`Lg`, then `κ` in both factors, the cup product of `adj'` and `Rf'` of the multiplication
`w' := B'(u⁻¹, u⁻¹) ≫ αg'⁻¹ ≫ Lg'(w) ≫ u` read through `u`. -/
theorem adjunctionCupProduct_baseChange_comp (E : T) {E' : T'} (u : Lg'.obj E ≅ E')
    (w : B.obj (E, E) ⟶ E)
    (hcup : αg.app (Rf.obj E, Rf.obj E) ≫ A'.map (bc.app E ×ₘ bc.app E) ≫
        adjunctionCupProduct adjf' A' B' αf' (Lg'.obj E) (Lg'.obj E) =
      Lg.map (adjunctionCupProduct adjf A B αf E E) ≫ bc.app (B.obj (E, E)) ≫
        Rf'.map (αg'.hom.app (E, E))) :
    αg.app (Rf.obj E, Rf.obj E) ≫
        A'.map ((bc.app E ≫ Rf'.map u.hom) ×ₘ (bc.app E ≫ Rf'.map u.hom)) ≫
          adjunctionCupProduct adjf' A' B' αf' E' E' ≫
            Rf'.map (B'.map (u.inv ×ₘ u.inv) ≫ αg'.inv.app (E, E) ≫ Lg'.map w ≫ u.hom) =
      Lg.map (adjunctionCupProduct adjf A B αf E E ≫ Rf.map w) ≫ bc.app E ≫ Rf'.map u.hom := by
  have hnat := adjunctionCupProduct_natural adjf' A' B' αf' u.hom u.hom
  have hbc := bc.naturality w
  simp only [Functor.comp_obj, Functor.comp_map] at hbc
  have hinner : αg'.hom.app (E, E) ≫ B'.map (u.hom ×ₘ u.hom) ≫ B'.map (u.inv ×ₘ u.inv) ≫
      αg'.inv.app (E, E) ≫ Lg'.map w ≫ u.hom = Lg'.map w ≫ u.hom := by
    have h2 : B'.map (u.hom ×ₘ u.hom) ≫ B'.map (u.inv ×ₘ u.inv) = 𝟙 _ := by
      rw [← B'.map_comp, prod_comp]
      simp
    rw [reassoc_of% h2, Iso.hom_inv_id_app_assoc]
  rw [bifunctor_map_comp_both, Category.assoc, reassoc_of% hnat, reassoc_of% hcup,
    ← Rf'.map_comp_assoc, ← Rf'.map_comp, Category.assoc, hinner, Functor.map_comp,
    Functor.map_comp, Category.assoc, reassoc_of% hbc]

/-- If a morphism intertwines the forward maps of two automorphisms, it intertwines their
inverses. -/
private theorem inv_comp_comm_of_hom_comp_comm {C : Type*} [Category C] {X Y : C} (e : X ≅ X)
    (e' : Y ≅ Y) (a : X ⟶ Y) (h : e.hom ≫ a = a ≫ e'.hom) : e.inv ≫ a = a ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h]

/-- **The pairing of a relative cup product, carried to the base change.** Let `K := Rf E`,
`K' := Rf' E'` and `κ : Lg K ≅ K'` an isomorphism whose forward map is `bc_E ≫ Rf'(u)`, and let
`β`, `β₁`, `β₂` be commutativity constraints at `(K, K)`, `(Lg K, Lg K)` and `(K', K')`,
compatible with `αg` (`hβ`) and with `κ` (`hβ'`). For a multiplication `w : B(E, E) ⟶ E`, a trace
`t : K ⟶ Z` and `ψ : Lg Z ⟶ Z'`, the image under `Lg` of the pairing `β⁻¹ ≫ cup ≫ Rf(w) ≫ t`,
followed by `ψ`, is the comparison along `Lg`, then `κ` in both factors, then the pairing
`β₂⁻¹ ≫ cup' ≫ Rf'(w') ≫ t'` with `w' := B'(u⁻¹, u⁻¹) ≫ αg'⁻¹ ≫ Lg'(w) ≫ u` and
`t' := κ⁻¹ ≫ Lg(t) ≫ ψ`. -/
theorem adjunctionCupPairing_baseChange (E : T) {E' : T'} (u : Lg'.obj E ≅ E')
    (w : B.obj (E, E) ⟶ E) {Z : S} {Z' : S'} (t : Rf.obj E ⟶ Z) (ψ : Lg.obj Z ⟶ Z')
    (κ : Lg.obj (Rf.obj E) ≅ Rf'.obj E') (hκ : κ.hom = bc.app E ≫ Rf'.map u.hom)
    (hcup : αg.app (Rf.obj E, Rf.obj E) ≫ A'.map (bc.app E ×ₘ bc.app E) ≫
        adjunctionCupProduct adjf' A' B' αf' (Lg'.obj E) (Lg'.obj E) =
      Lg.map (adjunctionCupProduct adjf A B αf E E) ≫ bc.app (B.obj (E, E)) ≫
        Rf'.map (αg'.hom.app (E, E)))
    (β : A.obj (Rf.obj E, Rf.obj E) ≅ A.obj (Rf.obj E, Rf.obj E))
    (β₁ : A'.obj (Lg.obj (Rf.obj E), Lg.obj (Rf.obj E)) ≅
      A'.obj (Lg.obj (Rf.obj E), Lg.obj (Rf.obj E)))
    (β₂ : A'.obj (Rf'.obj E', Rf'.obj E') ≅ A'.obj (Rf'.obj E', Rf'.obj E'))
    (hβ : Lg.map β.hom ≫ αg.app (Rf.obj E, Rf.obj E) = αg.app (Rf.obj E, Rf.obj E) ≫ β₁.hom)
    (hβ' : A'.map (κ.hom ×ₘ κ.hom) ≫ β₂.hom = β₁.hom ≫ A'.map (κ.hom ×ₘ κ.hom)) :
    αg.app (Rf.obj E, Rf.obj E) ≫ A'.map (κ.hom ×ₘ κ.hom) ≫
          β₂.inv ≫ adjunctionCupProduct adjf' A' B' αf' E' E' ≫
            Rf'.map (B'.map (u.inv ×ₘ u.inv) ≫ αg'.inv.app (E, E) ≫ Lg'.map w ≫ u.hom) ≫
              (κ.inv ≫ Lg.map t ≫ ψ) =
      Lg.map (β.inv ≫ adjunctionCupProduct adjf A B αf E E ≫ Rf.map w ≫ t) ≫ ψ := by
  have hβinv : Lg.map β.inv ≫ αg.app (Rf.obj E, Rf.obj E) =
      αg.app (Rf.obj E, Rf.obj E) ≫ β₁.inv :=
    inv_comp_comm_of_hom_comp_comm (Lg.mapIso β) β₁ _ hβ
  have hβ'inv : A'.map (κ.hom ×ₘ κ.hom) ≫ β₂.inv = β₁.inv ≫ A'.map (κ.hom ×ₘ κ.hom) :=
    (inv_comp_comm_of_hom_comp_comm β₁ β₂ _ hβ'.symm).symm
  have hcomp := adjunctionCupProduct_baseChange_comp adjf adjf' A A' B B' αf αf' αg αg' bc E u w
    hcup
  rw [← hκ] at hcomp
  rw [reassoc_of% hβ'inv, ← reassoc_of% hβinv, reassoc_of% hcomp]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
