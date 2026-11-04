module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Internal homs carried along a functor followed by an equivalence

Declarations built on `StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer`.

## Main results

* `isIso_of_tensorHomBijective_of_iso_comp`
-/

/-!
# Internal homs are carried along a functor with a fully faithful left adjoint

Let `C` and `D` be categories with tensor bifunctors `⊗_C` and `⊗_D`, and let `R : C ⥤ D` be a
functor with a left adjoint `E` whose unit is an isomorphism. Suppose `R` carries tensor
products to tensor products, `c : R(A ⊗ B) ≅ R A ⊗ R B`, naturally in `A`, and suppose the
*projection formula* `E Z ⊗ L ≅ E (Z ⊗ R L)` holds for *some* isomorphism, with no
compatibility asked of it. Let `e : H ⊗ L ⟶ M` exhibit `H` as an internal hom from `L` to `M`
in `C` — every `Z ⟶ H` corresponds to exactly one `Z ⊗ L ⟶ M` under `g ↦ (g ⊗ 1) ≫ e` — and
let `e' : H' ⊗ R L ⟶ R M` exhibit `H'` as one from `R L` to `R M` in `D`. Then the **canonical
comparison** `t : R H ⟶ H'`, the morphism whose transpose is

`R H ⊗ R L ≅ R(H ⊗ L) ⟶ R M`,

is an isomorphism.

This is the formal half of the statement that restriction to an open commutes with the derived
internal hom ([Stacks, Tag 08DL]) *through the canonical map* of [Stacks, Tag 08I3]: with `R`
restriction to an open, `E` extension by zero, and the projection formula
[Stacks, Tag 0GL1], it says that the transpose of the restricted evaluation morphism is an
isomorphism. It applies just as well when `R` is an equivalence, with `E` its inverse.

## Main results

* `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective`: the comparison is an
  isomorphism.
* `CategoryTheory.InternalHomTransfer.isIso_map_iff_of_tensorHomBijective`: consequently `R`
  carries the evaluation morphism `e` to an isomorphism exactly when `e'` is one.
* `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective_of_iso_comp`: the comparison is
  an isomorphism when `R` is, up to isomorphism, such a functor followed by an equivalence.

## Implementation notes

The proof is Yoneda's lemma. Postcomposition with `t` on morphisms out of `Z`, followed by the
bijection of `H'`, is `g ↦ (g ⊗ 1) ≫ c⁻¹ ≫ R e`. Entered through the adjunction, this becomes
`f ↦ p ≫ R((f ⊗ 1) ≫ e)` for an isomorphism `p : Z ⊗ R L ⟶ R(E Z ⊗ L)` built from the unit and
from `c`, which is bijective because the bijection of `H` is and because, through the projection
formula and the unit at `Z ⊗ R L`, applying `R` to morphisms out of `E Z ⊗ L` is the adjunction
bijection up to isomorphisms. Only the existence of the projection isomorphism is used, never a
formula for it.

Tensor products are taken as bifunctors rather than as monoidal structures, so that the
statement can be read at a tensor bifunctor that is not, or not syntactically, the tensor
product of a monoidal structure.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.InternalHomTransfer

variable {C D : Type*} [Category C] [Category D]
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R)
  (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))

/-- **The comparison of internal homs along a functor isomorphic to `R₁ ⋙ Φ`** is an isomorphism,
for `R₁` with a left adjoint `E₁` whose unit is invertible and satisfying the projection formula
for some isomorphism `ρ₁`, and `Φ` an equivalence carrying tensor products to tensor products for
some isomorphism `cΦ`. Neither `ρ₁` nor `cΦ` need be compatible with anything: the left adjoint of
`R` is `Φ⁻¹ ⋙ E₁`, and its projection isomorphism is assembled from `ρ₁`, `cΦ` and `R ≅ R₁ ⋙ Φ`. -/
theorem isIso_of_tensorHomBijective_of_iso_comp {M' : Type*} [Category M'] (TM : M' ⥤ M' ⥤ M')
    {R₁ : C ⥤ M'} {E₁ : M' ⥤ C} (adj₁ : E₁ ⊣ R₁) [IsIso adj₁.unit] (Φ : M' ≌ D)
    (eR : R ≅ R₁ ⋙ Φ.functor)
    (ρ₁ : ∀ (Z : M') (L : C), (TC.obj (E₁.obj Z)).obj L ≅ E₁.obj ((TM.obj Z).obj (R₁.obj L)))
    (cΦ : ∀ A B, Φ.functor.obj ((TM.obj A).obj B) ≅
      (TD.obj (Φ.functor.obj A)).obj (Φ.functor.obj B))
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e'))
    (t : R.obj H ⟶ H')
    (ht : (TD.map t).app (R.obj L) ≫ e' = (c H L).inv ≫ R.map e) :
    IsIso t := by
  let adj : Φ.inverse ⋙ E₁ ⊣ R := (Φ.symm.toAdjunction.comp adj₁).ofNatIsoRight eR.symm
  have : E₁.Full := adj₁.fullyFaithfulLOfIsIsoUnit.full
  have : E₁.Faithful := adj₁.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful adj
  let ρ : ∀ (Z : D) (L : C), (TC.obj ((Φ.inverse ⋙ E₁).obj Z)).obj L ≅
      (Φ.inverse ⋙ E₁).obj ((TD.obj Z).obj (R.obj L)) := fun Z L =>
    ρ₁ (Φ.inverse.obj Z) L ≪≫ E₁.mapIso (Φ.unitIso.app _ ≪≫ Φ.inverse.mapIso
      (cΦ _ _ ≪≫ (TD.mapIso (Φ.counitIso.app Z)).app _ ≪≫ (TD.obj Z).mapIso (eR.app L).symm))
  exact isIso_of_tensorHomBijective TC TD adj c hc ρ e he e' he' t ht

end CategoryTheory.InternalHomTransfer
