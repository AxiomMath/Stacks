module

public import StacksFrontier.CategoryTheory.Monoidal.InternalEndTensorIso
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# A monoidal functor and the internal endomorphism monoid

Let `F : C ⥤ D` be a lax monoidal functor between closed monoidal categories. There is a
canonical comparison

`F (X ⟶[C] Y) ⟶ (F X ⟶[D] F Y)`,

obtained by currying `F X ⊗ F (X ⟶[C] Y) ⟶ F (X ⊗ (X ⟶[C] Y)) ⟶ F Y`, the tensorator of `F`
followed by the image of the evaluation. This file proves two things about it.

First, at `Y = X` it is a **morphism of monoid objects** from the image under
`CategoryTheory.Functor.mapMon` of the internal endomorphism monoid of `X` to the internal
endomorphism monoid of `F X`: it carries the internal identity to the internal identity and
internal composition to internal composition. Only lax monoidality is used.

Second, when `X` has a right dual and `F` is braided monoidal, the comparison is an
**isomorphism**, so `F` carries the internal endomorphism monoid of a dualizable object to the
internal endomorphism monoid of its image. The proof is the dual description of the internal
hom: `CategoryTheory.MonoidalClosed.ihomDualHom` identifies `X ⟶[C] Y` with `Y ⊗ Xᘁ`, the image
pairing `CategoryTheory.ExactPairing.map` makes `F Xᘁ` a right dual of `F X`, and the comparison
is the tensorator read through those two identifications — so it is invertible because the
tensorator is.

Together these say that a braided monoidal functor commutes with the formation of endomorphism
algebras of dualizable objects. For the pullback of sheaves of modules along a morphism of
schemes this is the statement that the pullback of a matrix algebra is a matrix algebra.

## Main definitions

* `CategoryTheory.MonoidalClosed.ihomFunctorComparison`: the comparison
  `F (X ⟶[C] Y) ⟶ (F X ⟶[D] F Y)`.
* `CategoryTheory.MonoidalClosed.internalEndFunctorHom`: the comparison at `Y = X`, as a
  morphism of monoid objects `F.mapMon (End X) ⟶ End (F X)`.
* `CategoryTheory.MonoidalClosed.internalEndFunctorIso`: **that morphism is an isomorphism when
  `X` has a right dual and `F` is braided.**

## Main results

* `CategoryTheory.MonoidalClosed.isMonHom_ihomFunctorComparison`: **the comparison is a
  morphism of monoid objects.**
* `CategoryTheory.MonoidalClosed.ihomDualHom_map`: the comparison read through the dual
  description of the internal hom in both categories is the tensorator.
* `CategoryTheory.MonoidalClosed.isIso_ihomFunctorComparison_of_exactPairing` and
  `isIso_ihomFunctorComparison`: **the comparison is invertible for a dualizable `X`.**

## Implementation notes

The comparison is defined here by currying rather than taken from
`Stacks.DerivedHom.ExtensionOfScalars.internalHomBaseChange`, which is the same morphism in the
`CategoryTheory.TwoSquare` spelling, obtained as the mate of the tensorator. Two reasons. That
declaration lives in a file about derived Hom complexes which imports the whole derived-category
and K-flatness development, and nothing in the closed-monoidal core should depend on that. And
the one computation rule a consumer needs — the value of the uncurried comparison, here
`uncurry_ihomFunctorComparison` — is not available in the mate spelling, where it would have to
be extracted from `CategoryTheory.mateEquiv_counit`. The two agree, but the identification is
not stated, for the same reason: it would require the import.

`pairingCounit_map` and `ihomDualHom_map` are stated with `letI := ExactPairing.map F X X'` in
the statement, because the right-hand side mentions the evaluation of the image pairing, which
is not an instance.

## References

* [Stacks Project, Tag 0FFL](https://stacks.math.columbia.edu/tag/0FFL) — duals in a monoidal
  category.
* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J) — the Brauer group of a
  scheme, where this is used for the pullback of a matrix algebra.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

noncomputable section

namespace CategoryTheory.MonoidalClosed

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F : C ⥤ D)

/-! ### The comparison morphism -/

section Lax

variable [F.LaxMonoidal]

/-- Internal composition, evaluated: whiskering the internal composition
`MonoidalClosed.comp` and evaluating is the transpose `MonoidalClosed.compTranspose`. -/
@[reassoc]
lemma whiskerLeft_comp_ev (X Y Z : C) :
    X ◁ MonoidalClosed.comp X Y Z ≫ (ihom.ev X).app Z = compTranspose X Y Z := by
  rw [← uncurry_eq, MonoidalClosed.comp, uncurry_curry]

/-- **The internal-hom comparison of a lax monoidal functor**,
`F (X ⟶[C] Y) ⟶ (F X ⟶[D] F Y)`: the curried form of the tensorator of `F` followed by the
image of the evaluation. -/
def ihomFunctorComparison (X Y : C) :
    F.obj ((ihom X).obj Y) ⟶ (ihom (F.obj X)).obj (F.obj Y) :=
  curry («μ» F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y))

/-- **The computation rule for the internal-hom comparison**: its uncurried form is the
tensorator followed by the image of the evaluation. This determines it. -/
lemma uncurry_ihomFunctorComparison (X Y : C) :
    uncurry (ihomFunctorComparison F X Y) =
      «μ» F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y) := by
  rw [ihomFunctorComparison, uncurry_curry]

/-- The computation rule for the internal-hom comparison, in whiskered form. -/
@[reassoc]
lemma whiskerLeft_ihomFunctorComparison_ev (X Y : C) :
    F.obj X ◁ ihomFunctorComparison F X Y ≫ (ihom.ev (F.obj X)).app (F.obj Y) =
      «μ» F X ((ihom X).obj Y) ≫ F.map ((ihom.ev X).app Y) := by
  rw [← uncurry_eq, uncurry_ihomFunctorComparison]

/-! ### The comparison is a morphism of monoid objects -/

/-- **The internal-hom comparison carries the internal identity to the internal identity.** -/
theorem one_comp_ihomFunctorComparison (X : C) :
    (ε F ≫ F.map (MonoidalClosed.id X)) ≫ ihomFunctorComparison F X X =
      MonoidalClosed.id (F.obj X) := by
    apply uncurry_injective
    rw [uncurry_eq, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Category.assoc, whiskerLeft_ihomFunctorComparison_ev,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp, ← uncurry_eq]
    simp [MonoidalClosed.id, Functor.LaxMonoidal.right_unitality]

/-- **The internal-hom comparison carries internal composition to internal composition**, up to
the tensorator. -/
theorem mul_comp_ihomFunctorComparison (X : C) :
    («μ» F ((ihom X).obj X) ((ihom X).obj X) ≫ F.map (MonoidalClosed.comp X X X)) ≫
        ihomFunctorComparison F X X =
      (ihomFunctorComparison F X X ⊗ₘ ihomFunctorComparison F X X) ≫
        MonoidalClosed.comp (F.obj X) (F.obj X) (F.obj X) := by
    apply uncurry_injective
    simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whiskerLeft_ihomFunctorComparison_ev, whiskerLeft_comp_ev]
    rw [whiskerLeft_tensorHom_compTranspose (W := F.obj X) (ihomFunctorComparison F X X)
        (ihomFunctorComparison F X X), uncurry_ihomFunctorComparison,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
      whiskerLeft_comp_ev, Functor.LaxMonoidal.whiskerLeft_μ_comp_μ_assoc,
      MonoidalClosed.compTranspose_eq, Functor.map_comp, Functor.map_comp,
      ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
    rfl

/-- **The internal-hom comparison of a lax monoidal functor is a morphism of monoid objects**
from the image of the internal endomorphism monoid of `X` to the internal endomorphism monoid
of `F X`. -/
instance isMonHom_ihomFunctorComparison (X : C) :
    IsMonHom (ihomFunctorComparison F X X) where
  one_hom := one_comp_ihomFunctorComparison F X
  mul_hom := mul_comp_ihomFunctorComparison F X

/-- **The internal-hom comparison at `Y = X`, as a morphism of monoid objects.** -/
def internalEndFunctorHom (X : C) :
    F.mapMon.obj (internalEnd X) ⟶ internalEnd (F.obj X) :=
  Mon.Hom.mk' (ihomFunctorComparison F X X)
    (one_comp_ihomFunctorComparison F X) (mul_comp_ihomFunctorComparison F X)

/-- The underlying morphism of `internalEndFunctorHom F X` is `ihomFunctorComparison F X X`. -/
@[simp]
lemma internalEndFunctorHom_hom (X : C) :
    (internalEndFunctorHom F X).hom = ihomFunctorComparison F X X := rfl

end Lax

/-! ### Invertibility for a dualizable object -/

section Dual

variable [SymmetricCategory C] [SymmetricCategory D] [F.Braided]

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- **The counit of the pairing commutes with the tensorator.** The left-hand side is the image
under `F` of the counit of the pairing `(X, X')` in `C`, the right-hand side the counit of the
image pairing. -/
theorem pairingCounit_map (X X' Y : C) [ExactPairing X X'] :
    letI := ExactPairing.map F X X'
    «μ» F (Y ⊗ X') X ≫ F.map (pairingCounit X X' Y) =
      (δ F Y X' ▷ F.obj X) ≫ pairingCounit (F.obj X) (F.obj X') (F.obj Y) :=
  let := ExactPairing.map F X X'
  by
  rw [pairingCounit, pairingCounit, ExactPairing.map_evaluation, Functor.map_comp,
    Functor.map_comp, Functor.Monoidal.map_associator]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.Monoidal.map_rightUnitor, Functor.Monoidal.μ_δ_assoc]

/-- **The internal-hom comparison read through the dual description of the internal hom is the
tensorator.** `CategoryTheory.MonoidalClosed.ihomDualHom` identifies `X ⟶[C] Y` with `Y ⊗ X'`
and `F X ⟶[D] F Y` with `F Y ⊗ F X'`, and under those identifications the comparison becomes
the inverse tensorator `F (Y ⊗ X') ⟶ F Y ⊗ F X'`. -/
theorem ihomDualHom_map (X X' Y : C) [ExactPairing X X'] :
    letI := ExactPairing.map F X X'
    F.map (ihomDualHom X X' Y) ≫ ihomFunctorComparison F X Y =
      δ F Y X' ≫ ihomDualHom (F.obj X) (F.obj X') (F.obj Y) := by
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_ihomFunctorComparison_ev]
  rw [← uncurry_eq, uncurry_ihomDualHom, Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp, ← uncurry_eq, uncurry_ihomDualHom, Functor.map_comp,
    Functor.LaxBraided.braided_assoc, pairingCounit_map,
    ← BraidedCategory.braiding_naturality_right_assoc]

/-- **The internal-hom comparison of a braided monoidal functor is invertible when the source
object is dualizable.** -/
theorem isIso_ihomFunctorComparison_of_exactPairing (X X' Y : C) [ExactPairing X X'] :
    IsIso (ihomFunctorComparison F X Y) := by
  let := ExactPairing.map F X X'
  have h : IsIso (F.map (ihomDualHom X X' Y) ≫ ihomFunctorComparison F X Y) := by
    rw [ihomDualHom_map]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (ihomDualHom X X' Y)) _

/-- **The internal-hom comparison of a braided monoidal functor is invertible when the source
object has a right dual.** -/
instance isIso_ihomFunctorComparison (X Y : C) [HasRightDual X] :
    IsIso (ihomFunctorComparison F X Y) :=
  isIso_ihomFunctorComparison_of_exactPairing F X (Xᘁ) Y

/-- The morphism of monoid objects `internalEndFunctorHom F X` is an isomorphism when `X` has a
right dual. -/
instance isIso_internalEndFunctorHom (X : C) [HasRightDual X] :
    IsIso (internalEndFunctorHom F X) := by
  have : IsIso ((Mon.forget D).map (internalEndFunctorHom F X)) :=
    isIso_ihomFunctorComparison F X X
  exact isIso_of_reflects_iso _ (Mon.forget D)

/-- **A braided monoidal functor commutes with the internal endomorphism monoid of a dualizable
object**: `F (End X) ≅ End (F X)` as monoid objects. -/
def internalEndFunctorIso (X : C) [HasRightDual X] :
    F.mapMon.obj (internalEnd X) ≅ internalEnd (F.obj X) :=
  asIso (internalEndFunctorHom F X)

/-- **A braided monoidal functor commutes with the internal endomorphism monoid of an object
that merely admits a right dual.** -/
theorem nonempty_internalEndFunctorIso (X : C) (h : Nonempty (HasRightDual X)) :
    Nonempty (F.mapMon.obj (internalEnd X) ≅ internalEnd (F.obj X)) := by
  obtain ⟨hd⟩ := h
  let := hd
  exact ⟨internalEndFunctorIso F X⟩

end Dual

end CategoryTheory.MonoidalClosed

end
