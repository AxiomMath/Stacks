module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Transposing a mate built out of a compositor

Let `A ⊣ A'`, `B ⊣ B'` and `C ⊣ Pn` be adjunctions, let `Lc ⊣ Pc` be a fourth one with
comparisons `κ : Lc ≅ A ⋙ B` of left adjoints and `e : Pc ≅ B' ⋙ A'` of right adjoints that are
mates of one another, and let `T : Pn ⟶ Pc` be a transformation of right adjoints. Then `C ⟶ Lc`
has the mate `T` of `Pn ⟶ Pc` behind it, and composing with `κ.inv` turns it into a
transformation `A ⋙ B ⟶ C`. This file transposes such a transformation: it computes its
`B`-adjunct against the unit of `A ⊣ A'`, and uses that to recognise it as a given map once the
corresponding identity of direct images is known.

This is the shape in which the pullback transition of sheaves of modules of Stacks 09WF is
compared with the transition in direct-image form: `A` and `C` are the pullbacks of modules along
two morphisms of ringed topoi, `B` the pullback along a third, `κ` and `e` are the compositors of
Stacks 03D8, and `T` is the transformation of direct images of a 2-morphism of Stacks 04IC.

## Main results

* `Stacks.CategoryTheory.unit_comp_map_homEquiv`: the unit of `A ⊣ A'` against a `B`-adjunct is
  the unit of the composite adjunction against the map itself.
* `Stacks.CategoryTheory.unit_comp_homEquiv_conjugate`: the transpose of `κ.inv` followed by the
  mate of `T`, against the unit of `A ⊣ A'`, is `T` followed by `e` against the unit of `C ⊣ Pn`.
* `Stacks.CategoryTheory.homEquiv_comp_map_eq`: hence a transformation of that shape, read
  through isomorphisms `k` and `j` of its two ends, is a given map `w` as soon as the
  corresponding identity of direct images holds.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.CategoryTheory

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  {A : 𝒜 ⥤ ℬ} {A' : ℬ ⥤ 𝒜} (adjA : A ⊣ A')
  {B : ℬ ⥤ 𝒞} {B' : 𝒞 ⥤ ℬ} (adjB : B ⊣ B')

/-- The unit of `A ⊣ A'` followed by `A'` applied to the `B`-adjunct of a map is the unit of the
composite adjunction `A ⋙ B ⊣ B' ⋙ A'` followed by `B' ⋙ A'` applied to the map. -/
theorem unit_comp_map_homEquiv (M : 𝒜) {W : 𝒞} (x : B.obj (A.obj M) ⟶ W) :
    adjA.unit.app M ≫ A'.map (adjB.homEquiv (A.obj M) W x) =
      (adjA.comp adjB).unit.app M ≫ (B' ⋙ A').map x := by
  rw [Adjunction.comp_unit_app, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  rfl

variable {C : 𝒜 ⥤ 𝒞} {Pn : 𝒞 ⥤ 𝒜} (adjC : C ⊣ Pn)
  {Lc : 𝒜 ⥤ 𝒞} {Pc : 𝒞 ⥤ 𝒜} (adjC' : Lc ⊣ Pc)

/-- **Transposing a mate built out of a compositor.** Let `κ : Lc ≅ A ⋙ B` and `e : Pc ≅ B' ⋙ A'`
be mates of one another, and let `α : A ⋙ B ⟶ C` be a transformation whose composite with `κ.hom`
is the mate of `T : Pn ⟶ Pc`. Then the `B`-adjunct of `α` at `M`, read against the unit of
`A ⊣ A'`, is `T` followed by `e` read against the unit of `C ⊣ Pn`. -/
theorem unit_comp_homEquiv_conjugate (e : Pc ≅ B' ⋙ A') (κ : Lc ≅ A ⋙ B)
    (hκ : conjugateEquiv (adjA.comp adjB) adjC' κ.hom = e.inv) (T : Pn ⟶ Pc) {M : 𝒜}
    (α : (A ⋙ B).obj M ⟶ C.obj M)
    (hα : κ.hom.app M ≫ α = ((conjugateEquiv adjC adjC').symm T).app M) :
    adjA.unit.app M ≫ A'.map (adjB.homEquiv (A.obj M) (C.obj M) α) =
      adjC.unit.app M ≫ (T.app (C.obj M) ≫ e.hom.app (C.obj M)) := by
  have hsymm : (conjugateEquiv (adjA.comp adjB) adjC').symm e.inv = κ.hom :=
    (Equiv.symm_apply_eq _).mpr hκ.symm
  have hu2 := unit_conjugateEquiv_symm (adjA.comp adjB) adjC' e.inv M
  rw [hsymm] at hu2
  have hu1 := unit_conjugateEquiv_symm adjC adjC' T M
  rw [← hα, Pc.map_comp, ← Category.assoc, ← hu2, Category.assoc,
    ← e.inv.naturality α] at hu1
  rw [unit_comp_map_homEquiv adjA adjB M]
  refine (((Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ e.hom.app (C.obj M)) hu1)).trans ?_).symm
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **Recognising a transposed mate.** With the transposition of
`Stacks.CategoryTheory.unit_comp_homEquiv_conjugate` as hypothesis `hC1`, the `B`-adjunct of `α`
followed by `B'` applied to `k` is `j` followed by `w`, as soon as the corresponding identity
`hC4` of transposes of direct images holds. -/
theorem homEquiv_comp_map_eq (e : Pc ≅ B' ⋙ A') (T : Pn ⟶ Pc) {M : 𝒜} {Nn : 𝒞} {Nm : ℬ}
    (α : (A ⋙ B).obj M ⟶ C.obj M)
    (hC1 : adjA.unit.app M ≫ A'.map (adjB.homEquiv (A.obj M) (C.obj M) α) =
      adjC.unit.app M ≫ (T.app (C.obj M) ≫ e.hom.app (C.obj M)))
    (k : C.obj M ⟶ Nn) (j : A.obj M ⟶ Nm) (w : Nm ⟶ B'.obj Nn)
    (hC4 : (adjC.unit.app M ≫ Pn.map k) ≫ (T.app Nn ≫ e.hom.app Nn) =
      (adjA.unit.app M ≫ A'.map j) ≫ A'.map w) :
    adjB.homEquiv (A.obj M) (C.obj M) α ≫ B'.map k = j ≫ w := by
  refine (adjA.homEquiv M (B'.obj Nn)).injective ?_
  refine Eq.trans (Adjunction.homEquiv_unit adjA M (B'.obj Nn) _) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit adjA M (B'.obj Nn) (j ≫ w)).symm
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hC1]
  refine Eq.trans ?_ hC4
  rw [Category.assoc, Category.assoc, Category.assoc]
  refine congrArg (adjC.unit.app M ≫ ·) ?_
  refine Eq.trans (congrArg (fun q => T.app (C.obj M) ≫ q) (e.hom.naturality k).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun q => q ≫ e.hom.app Nn) (T.naturality k).symm) ?_
  exact Category.assoc _ _ _

end Stacks.CategoryTheory

end
