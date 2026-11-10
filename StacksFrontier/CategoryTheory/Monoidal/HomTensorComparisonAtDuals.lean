module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomStrength

/-!
# The tensor product of two internal homs, at dualizable objects

Let `C` be a symmetric monoidal category and let `A`, `B` be objects of `C` for which tensoring
on the right has a right adjoint: adjunctions

`- ⊗ A ⊣ H_A`,  `- ⊗ B ⊣ H_B`,  `- ⊗ (A ⊗ B) ⊣ H_{A ⊗ B}`.

For objects `A'`, `B'` of `C` there is a canonical morphism

`H_A(A') ⊗ H_B(B') ⟶ H_{A ⊗ B}(A' ⊗ B')`,

the morphism adjoint to the interchange of the two middle factors
`CategoryTheory.MonoidalCategory.tensorμ` followed by the tensor product of the two counits.
This is the shape of the canonical morphism of [Stacks, Tag 0FXP] on a ringed space, where
`H_A = R𝓗om(A, -)` and the counits are the derived evaluation morphisms.

**This file proves that morphism is an isomorphism as soon as `A` and `B` are dualizable**, that
is, as soon as each carries an exact pairing with some object.  On a ringed space a perfect
object is dualizable, with dual `A^∨ = R𝓗om(A, 𝒪)`, so the hypothesis is the perfectness that
[Stacks, Tag 0FXZ] assumes of `K` and of `M`.

## The argument

Write `P = H_A(A')` and `G = H_B(B')`.  The two strengths of
`CategoryTheory.MonoidalCategory.internalHomStrength` — the adjunction-theoretic diagonals of
[Stacks, Tag 0BYS] —

`G ⊗ H_A(A') ⟶ H_A(G ⊗ A')`,  `A' ⊗ H_B(B') ⟶ H_B(A' ⊗ B')`

are invertible because `A` and `B` are dualizable, by
`CategoryTheory.MonoidalCategory.isIso_internalHomStrength_of_source_dual`.  Composing them with
two braidings gives an invertible morphism

`homTensorStrengthComp : P ⊗ G ⟶ H_A(H_B(A' ⊗ B'))`,

and the composite of hom-set bijections

`(T ⟶ P ⊗ G) ≃ (T ⟶ H_A(H_B(A' ⊗ B'))) ≃ (T ⊗ A ⟶ H_B(A' ⊗ B')) ≃ ((T ⊗ A) ⊗ B ⟶ A' ⊗ B')
  ≃ (T ⊗ (A ⊗ B) ⟶ A' ⊗ B') ≃ (T ⟶ H_{A ⊗ B}(A' ⊗ B'))`

is, by `homTensorComparison_yoneda`, composition with the canonical morphism.  So composition
with the canonical morphism is bijective on every `T`, and the morphism is invertible by Yoneda.

The one computation of substance is `tensorMu_whiskerRight_counit`: that the composite of the
two strengths, uncurried twice, is the interchange followed by the two counits.  Unwinding the
strengths leaves a braided identity with a single occurrence of the counit, and
`braiding_associator_braiding` reduces it to pure monoidal coherence — this is where the
*symmetry* of the braiding is used, in the one place where a braiding of `P` past `G` has to
cancel against a braiding of `G` past `P`.

## Main definitions

* `Stacks.DerivedTensorHomDiagonal.homTensorStrengthComp`: the composite of the two strengths
  and two braidings.
* `Stacks.DerivedTensorHomDiagonal.homTensorComparison`: the canonical morphism
  `H_A(A') ⊗ H_B(B') ⟶ H_{A ⊗ B}(A' ⊗ B')`.

## Main results

* `Stacks.DerivedTensorHomDiagonal.isIso_homTensorComparison`: the canonical morphism is an
  isomorphism when `A` and `B` are dualizable.

## Implementation notes

The strength `CategoryTheory.MonoidalCategory.internalHomStrength` and its invertibility at a
dualizable object come from `StacksFrontier/CategoryTheory/Monoidal/InternalHomStrength.lean`,
stated for an arbitrary monoidal category and an arbitrary adjunction, which is the generality
needed here.

## References

* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u

namespace Stacks.DerivedTensorHomDiagonal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The uncurried form of the strength.**  Whiskering the strength with `M` and composing with
the counit returns the morphism it is adjoint to. -/
@[reassoc]
theorem internalHomStrength_uncurry {M : C} {H : C ⥤ C} (a : tensorRight M ⊣ H) (K L : C) :
    internalHomStrength a K L ▷ M ≫ a.counit.app (K ⊗ L) =
      (α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L :=
  (a.homEquiv (K ⊗ H.obj L) (K ⊗ L)).symm_apply_apply _

section Braided

variable [SymmetricCategory C]

/-- **Braiding `P` past `G` and then `G` past `P ⊗ A` is braiding `G` past `A`.**  The two
braidings of `P` with `G` cancel, which is where the symmetry of the braiding enters. -/
@[reassoc]
theorem braiding_associator_braiding (P G A : C) :
    (β_ P G).hom ▷ A ≫ (α_ G P A).hom ≫ (β_ G (P ⊗ A)).hom =
      (α_ P G A).hom ≫ P ◁ (β_ G A).hom ≫ (α_ P A G).inv := by
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]

/-- The interchange of the two middle factors, written with the braiding of `G` past `A`
whiskered on the outside: pure monoidal coherence. -/
@[reassoc]
theorem associator_whiskerRight_eq_tensorMu (P G A B : C) :
    (α_ (P ⊗ G) A B).inv ≫ (α_ P G A).hom ▷ B ≫ (P ◁ (β_ G A).hom) ▷ B ≫
        (α_ P A G).inv ▷ B ≫ (α_ (P ⊗ A) G B).hom = tensorμ P G A B := by
  dsimp only [tensorμ]
  monoidal

/-- **The braided identity behind the comparison.**  For any `f : P ⊗ A ⟶ A''`, braiding `P`
past `G`, reassociating, applying `f` and braiding back is the interchange of the two middle
factors followed by `f`. -/
@[reassoc]
theorem tensorMu_whiskerRight (P G A B A'' : C) (f : P ⊗ A ⟶ A'') :
    (α_ (P ⊗ G) A B).inv ≫ ((β_ P G).hom ▷ A) ▷ B ≫ (α_ G P A).hom ▷ B ≫
        (G ◁ f) ▷ B ≫ (β_ G A'').hom ▷ B ≫ (α_ A'' G B).hom =
      tensorμ P G A B ≫ f ▷ (G ⊗ B) := by
  have hfb : G ◁ f ≫ (β_ G A'').hom = (β_ G (P ⊗ A)).hom ≫ f ▷ G := by
    simp
  have hinner : (β_ P G).hom ▷ A ≫ (α_ G P A).hom ≫ G ◁ f ≫ (β_ G A'').hom =
      (α_ P G A).hom ≫ (P ◁ (β_ G A).hom) ≫ (α_ P A G).inv ≫ f ▷ G := by
    rw [hfb, braiding_associator_braiding_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [hinner]
  simp only [comp_whiskerRight, Category.assoc, associator_naturality_left]
  rw [associator_whiskerRight_eq_tensorMu_assoc]

end Braided

section HomTensor

variable [SymmetricCategory C]

/-- **The composite of the two strengths**, `H_A(A') ⊗ H_B(B') ⟶ H_A(H_B(A' ⊗ B'))`: braid the
two internal homs, apply the strength of `A` and then, inside `H_A`, braid and apply the
strength of `B`. -/
def homTensorStrengthComp {A B : C} {HA HB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (A' B' : C) :
    HA.obj A' ⊗ HB.obj B' ⟶ HA.obj (HB.obj (A' ⊗ B')) :=
  (β_ (HA.obj A') (HB.obj B')).hom ≫ internalHomStrength aA (HB.obj B') A' ≫
    HA.map ((β_ (HB.obj B') A').hom ≫ internalHomStrength aB A' B')

/-- The composite of the two strengths is invertible when `A` and `B` are dualizable. -/
theorem isIso_homTensorStrengthComp {A B DA DB : C} [ExactPairing A DA] [ExactPairing B DB]
    {HA HB : C ⥤ C} (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (A' B' : C) :
    IsIso (homTensorStrengthComp aA aB A' B') := by
  have : IsIso (internalHomStrength aA (HB.obj B') A') :=
    isIso_internalHomStrength_of_source_dual (N := DA) aA _ _
  have : IsIso (internalHomStrength aB A' B') :=
    isIso_internalHomStrength_of_source_dual (N := DB) aB _ _
  rw [homTensorStrengthComp]
  infer_instance

/-- The composite of the two strengths, uncurried once. -/
theorem homTensorStrengthComp_uncurry {A B : C} {HA HB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (A' B' : C) :
    homTensorStrengthComp aA aB A' B' ▷ A ≫ aA.counit.app (HB.obj (A' ⊗ B')) =
      (β_ (HA.obj A') (HB.obj B')).hom ▷ A ≫
        (α_ (HB.obj B') (HA.obj A') A).hom ≫
          HB.obj B' ◁ aA.counit.app A' ≫
            (β_ (HB.obj B') A').hom ≫ internalHomStrength aB A' B' := by
  change (aA.homEquiv (HA.obj A' ⊗ HB.obj B') (HB.obj (A' ⊗ B'))).symm
      ((β_ (HA.obj A') (HB.obj B')).hom ≫ internalHomStrength aA (HB.obj B') A' ≫
        HA.map ((β_ (HB.obj B') A').hom ≫ internalHomStrength aB A' B')) = _
  rw [aA.homEquiv_naturality_left_symm, aA.homEquiv_naturality_right_symm,
    show (aA.homEquiv (HB.obj B' ⊗ HA.obj A') (HB.obj B' ⊗ A')).symm
          (internalHomStrength aA (HB.obj B') A') =
        (α_ (HB.obj B') (HA.obj A') A).hom ≫ HB.obj B' ◁ aA.counit.app A' from
      internalHomStrength_uncurry aA _ _]
  simp only [Category.assoc]
  rfl

/-- **The composite of the two strengths, uncurried twice, is the interchange followed by the
two counits.**  This is the computation that identifies the composite of the strengths with the
canonical comparison. -/
theorem tensorMu_whiskerRight_counit {A B : C} {HA HB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (A' B' : C) :
    (α_ (HA.obj A' ⊗ HB.obj B') A B).inv ≫
        (homTensorStrengthComp aA aB A' B' ▷ A) ▷ B ≫
          aA.counit.app (HB.obj (A' ⊗ B')) ▷ B ≫ aB.counit.app (A' ⊗ B') =
      tensorμ (HA.obj A') (HB.obj B') A B ≫
        (aA.counit.app A' ⊗ₘ aB.counit.app B') := by
  rw [← comp_whiskerRight_assoc, homTensorStrengthComp_uncurry]
  simp only [comp_whiskerRight, Category.assoc]
  rw [internalHomStrength_uncurry,
    tensorMu_whiskerRight_assoc (HA.obj A') (HB.obj B') A B A' (aA.counit.app A'),
    tensorHom_def]
  rfl

/-- **The canonical comparison of [Stacks, Tag 0FXP]**, in its purely adjunction-theoretic
form: the morphism `H_A(A') ⊗ H_B(B') ⟶ H_{A ⊗ B}(A' ⊗ B')` adjoint to the interchange of the
two middle factors followed by the tensor product of the two counits. -/
def homTensorComparison {A B : C} {HA HB HAB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (aAB : tensorRight (A ⊗ B) ⊣ HAB)
    (A' B' : C) :
    HA.obj A' ⊗ HB.obj B' ⟶ HAB.obj (A' ⊗ B') :=
  aAB.homEquiv (HA.obj A' ⊗ HB.obj B') (A' ⊗ B')
    (tensorμ (HA.obj A') (HB.obj B') A B ≫ (aA.counit.app A' ⊗ₘ aB.counit.app B'))

/-- **Composition with the comparison is the composite of hom-set bijections.**  So when the
composite of the two strengths is invertible, composition with the comparison is bijective. -/
theorem homTensorComparison_yoneda {A B : C} {HA HB HAB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (aAB : tensorRight (A ⊗ B) ⊣ HAB)
    (A' B' : C) (hc : IsIso (homTensorStrengthComp aA aB A' B')) (T : C)
    (f : T ⟶ HA.obj A' ⊗ HB.obj B') :
    (((Iso.homCongr (Iso.refl T) (@asIso _ _ _ _ (homTensorStrengthComp aA aB A' B') hc)).trans
        ((aA.homEquiv T (HB.obj (A' ⊗ B'))).symm.trans
          ((aB.homEquiv (T ⊗ A) (A' ⊗ B')).symm.trans
            ((Iso.homCongr (α_ T A B) (Iso.refl (A' ⊗ B'))).trans
              (aAB.homEquiv T (A' ⊗ B')))))) f) =
      f ≫ homTensorComparison aA aB aAB A' B' := by
  rw [homTensorComparison, ← aAB.homEquiv_naturality_left]
  dsimp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom, asIso_hom]
  rw [aA.homEquiv_symm_apply, aB.homEquiv_symm_apply]
  congr 1
  change (α_ T A B).inv ≫
      (((𝟙 T ≫ f ≫ homTensorStrengthComp aA aB A' B') ▷ A ≫
        aA.counit.app (HB.obj (A' ⊗ B'))) ▷ B ≫ aB.counit.app (A' ⊗ B')) ≫ 𝟙 _ =
    f ▷ (A ⊗ B) ≫ tensorμ (HA.obj A') (HB.obj B') A B ≫
      (aA.counit.app A' ⊗ₘ aB.counit.app B')
  rw [Category.id_comp, Category.comp_id]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_left_assoc]
  congr 1
  exact tensorMu_whiskerRight_counit aA aB A' B'

/-- **The comparison of [Stacks, Tag 0FXP] is an isomorphism at dualizable objects.**  Let `C`
be a symmetric monoidal category, let `A` and `B` be objects admitting exact pairings with `DA`
and `DB`, and let `- ⊗ A ⊣ H_A`, `- ⊗ B ⊣ H_B`, `- ⊗ (A ⊗ B) ⊣ H_{A ⊗ B}` be adjunctions.  Then
for all `A'`, `B'` the canonical morphism

`H_A(A') ⊗ H_B(B') ⟶ H_{A ⊗ B}(A' ⊗ B')`

is an isomorphism. -/
theorem isIso_homTensorComparison {A B DA DB : C} [ExactPairing A DA] [ExactPairing B DB]
    {HA HB HAB : C ⥤ C}
    (aA : tensorRight A ⊣ HA) (aB : tensorRight B ⊣ HB) (aAB : tensorRight (A ⊗ B) ⊣ HAB)
    (A' B' : C) : IsIso (homTensorComparison aA aB aAB A' B') := by
  have hc : IsIso (homTensorStrengthComp aA aB A' B') :=
    isIso_homTensorStrengthComp (DA := DA) (DB := DB) aA aB A' B'
  refine (isIso_iff_yoneda_map_bijective _).mpr fun T => ?_
  simp only [← homTensorComparison_yoneda aA aB aAB A' B' hc T]
  exact Equiv.bijective _

end HomTensor

end Stacks.DerivedTensorHomDiagonal

end
