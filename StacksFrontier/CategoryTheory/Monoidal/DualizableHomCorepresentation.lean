module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Morphisms out of a dualizable object into an inverse image

Let `F : C ⥤ D` be a functor between monoidal categories with a right adjoint `G`, and with
`F (𝟙_ C) ≅ 𝟙_ D`. Let `E` be an object of `D` with a right dual `E'`, let `Q` be an object of
`C` with a right dual `Q'`, and let `H : M ⥤ C` be a functor such that

`G (F (H m) ⊗ E') ≅ Q ⊗ H m`

naturally in `m` (a projection formula, read along `H`). Then morphisms out of `E` into the
inverse image of `H m` are morphisms out of `Q'` into `H m`:

`Hom_D(E, F (H m)) ≃ Hom_C(Q', H m)`,

naturally in `m`. The bijection is the composite of the duality of `E`
(`CategoryTheory.tensorRightHomEquiv`), the adjunction at the unit, the projection formula and
the duality of `Q` (`CategoryTheory.tensorLeftHomEquiv`).

This is the formal core of the identification, for a perfect complex `E` on a scheme `X` proper
and flat over `Spec R`, of `Hom(E, O_X ⊗_R M)` with `Hom(Q', M)` for a perfect complex `Q'` of
`R`-modules, which is how the source proves [Stacks, Tag 0D2Q].

## Main definitions

* `CategoryTheory.MonoidalCategory.dualHomEquiv`: the bijection
  `Hom_D(E, F (H m)) ≃ Hom_C(Q', H m)`.

## Main results

* `CategoryTheory.MonoidalCategory.dualHomEquiv_naturality`: it is natural in `m`.

## References

* [Stacks Project, Tag 0D2Q](https://stacks.math.columbia.edu/tag/0D2Q)
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {M : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} M] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (eF : F.obj (𝟙_ C) ≅ 𝟙_ D) (H : M ⥤ C)
  (E E' : D) [ExactPairing E E'] (Q Q' : C) [ExactPairing Q Q']
  (p : H ⋙ F ⋙ tensorRight E' ⋙ G ≅ H ⋙ tensorLeft Q)

/-- `(tensorLeftHomEquiv X Y Y' Z).symm` is natural in `Z`. -/
lemma tensorLeftHomEquiv_symm_comp_whiskerLeft {X Y Y' Z Z' : C} [ExactPairing Y Y']
    (f : X ⟶ Y ⊗ Z) (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z').symm (f ≫ Y ◁ g) =
      (tensorLeftHomEquiv X Y Y' Z).symm f ≫ g := by
  rw [Equiv.symm_apply_eq, tensorLeftHomEquiv_naturality, Equiv.apply_symm_apply]

/-- **Morphisms out of a dualizable object into an inverse image.** For `E` with right dual
`E'`, `Q` with right dual `Q'`, and a projection formula `G (F (H m) ⊗ E') ≅ Q ⊗ H m` natural
in `m`, the bijection `Hom_D(E, F (H m)) ≃ Hom_C(Q', H m)`. -/
def dualHomEquiv (m : M) : (E ⟶ F.obj (H.obj m)) ≃ (Q' ⟶ H.obj m) :=
  ((λ_ E).homCongr (Iso.refl _)).symm.trans <|
    (tensorRightHomEquiv (𝟙_ D) E E' _).trans <|
    (eF.homCongr (Iso.refl _)).symm.trans <|
    (adj.homEquiv _ _).trans <|
    ((Iso.refl _).homCongr (p.app m)).trans <|
    (tensorLeftHomEquiv (𝟙_ C) Q Q' (H.obj m)).symm.trans <|
    (ρ_ Q').homCongr (Iso.refl _)

/-- `dualHomEquiv` is natural in `m`. -/
lemma dualHomEquiv_naturality {m m' : M} (g : m ⟶ m') (φ : E ⟶ F.obj (H.obj m)) :
    dualHomEquiv adj eF H E E' Q Q' p m' (φ ≫ F.map (H.map g)) =
      dualHomEquiv adj eF H E E' Q Q' p m φ ≫ H.map g := by
  have hp : G.map (F.map (H.map g) ▷ E') ≫ p.hom.app m' = p.hom.app m ≫ Q ◁ H.map g :=
    p.hom.naturality g
  simp only [dualHomEquiv, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
    Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv, Category.comp_id, Category.id_comp,
    Iso.app_hom, Category.assoc]
  rw [← Category.assoc (λ_ E).hom φ, tensorRightHomEquiv_naturality, ← Category.assoc eF.hom,
    adj.homEquiv_naturality_right, Category.assoc, hp, ← Category.assoc _ (p.hom.app m),
    tensorLeftHomEquiv_symm_comp_whiskerLeft]

end CategoryTheory.MonoidalCategory
