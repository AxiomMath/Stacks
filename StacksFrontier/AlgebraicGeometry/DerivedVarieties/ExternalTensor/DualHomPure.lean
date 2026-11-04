module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomAdditive
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftLocal

/-!
# The value of the duality bijection at a pure map

`AlgebraicGeometry.externalTensorDualTensorHomEquiv` is the bijection

`Hom_{𝒪_{X ×_S Y}}(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))`.

This file computes its value, and in particular its value at a pure map `a ⊠ b`. The bijection
is the formula

`q ↦ η ≫ q ▷ (ℰ^∨ ⊠ 𝒢^∨)`,

the coevaluation of `AlgebraicGeometry.externalTensorProductExactPairing` followed by `q`
tensored with the identity, and that coevaluation is computed factorwise, from the coevaluations
of the two pullback pairings out of which the exact pairing is built.

## Main definitions

* `CategoryTheory.nestedTensorSection`: the global section `𝟙_ ⟶ (A ⊗ C) ⊗ (D ⊗ B)` built from
  sections `s : 𝟙_ ⟶ A ⊗ B` and `t : 𝟙_ ⟶ C ⊗ D` by inserting `t` between the two factors of
  `s`. This is the shape of the coevaluation of `CategoryTheory.ExactPairing.tensor`.
* `CategoryTheory.nestedTensorPairing`: the evaluation `(D ⊗ B) ⊗ (A ⊗ C) ⟶ 𝟙_` built the same
  way from pairings `B ⊗ A ⟶ 𝟙_` and `D ⊗ C ⟶ 𝟙_`.
* `CategoryTheory.swappedTensorSection`: the same global section `𝟙_ ⟶ (A ⊗ C) ⊗ (D ⊗ B)`
  written as the monoidal product `s ⊗ₘ t` followed by a swap of `B` past `C ⊗ D` — the shape in
  which the two sections enter *separately*.

## Main results

* `CategoryTheory.coevaluation_comp_whiskerLeft_rightDualIso` and
  `CategoryTheory.coevaluation_comp_whiskerRight_comp_whiskerLeft_rightDualIso`: **the
  comparison of two left duals carries one coevaluation to the other.**
* `CategoryTheory.coevaluation_comp_whiskerRight_eq_tensorRightHomEquiv`: the hom-set bijection
  of an exact pairing at the unit object *is* `q ↦ η ≫ q ▷ Y'`.
* `CategoryTheory.exactPairingCongrRight_coevaluation` and
  `CategoryTheory.exactPairingCongrRight_evaluation`: the coevaluation and the evaluation of a
  pairing transported along an isomorphism of the dual.
* `CategoryTheory.ExactPairing.tensor_coevaluation_eq` and
  `CategoryTheory.ExactPairing.tensor_evaluation_eq`: the coevaluation and the evaluation of a
  tensor product of exact pairings, in the two shapes above.
* `CategoryTheory.coevaluation_tensor_comp_whiskerRight_tensorHom`: **the value of the hom-set
  bijection of a tensor product of exact pairings at a pure map `a ⊗ b`** is the nested section
  built from the two one-factor values.
* `AlgebraicGeometry.dualTensorHomEquiv_eq_coevaluation_comp` and
  `AlgebraicGeometry.externalTensorDualTensorHomEquiv_eq_coevaluation_comp`: **the two duality
  bijections written as formulas**, `q ↦ η ≫ q ▷ P^∨` for the canonical pairing of `P` and for
  `AlgebraicGeometry.externalTensorProductExactPairing`.
* `AlgebraicGeometry.externalTensorProductFirstPairing_coevaluation`,
  `…_evaluation`, `AlgebraicGeometry.externalTensorProductSecondPairing_coevaluation`,
  `…_evaluation`: the two factor pairings' coevaluations and evaluations, in terms of the
  canonical ones of the pulled-back modules and the base-change comparison
  `AlgebraicGeometry.VectorBundleKZero.pullbackDualSheafIso`.
* `AlgebraicGeometry.externalTensorProductExactPairing_coevaluation` and
  `AlgebraicGeometry.externalTensorProductExactPairing_evaluation`: **the coevaluation and the
  evaluation of `ℰ^∨ ⊠ 𝒢^∨` as a left dual of `ℰ ⊠ 𝒢`, computed factorwise.**
* `AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap`: **the value of
  the duality bijection at a pure map `a ⊠ b`** — the nested section built from the duality
  section of `pr₁^*a` and that of `pr₂^*b`, read through the symmetry of the tensor product
  sheaf.
* `CategoryTheory.nestedTensorSection_eq_swappedTensorSection` and
  `…_braiding`: the nested section **is** the monoidal product of the two sections, read through
  a swap; the hypothesis is one instance of naturality of that swap, and holds for the braiding
  of a braided category.
* `AlgebraicGeometry.whiskerLeft_comp_tensorSheafBraiding_hom`: that instance of naturality
  for the symmetry of [Stacks, Tag 01CA].
* `AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_swapped`: **the
  value at `a ⊠ b` as a product of the two factor sections** — it depends on `a` and on `b` only
  through their one-factor duality sections, and depends on them separately.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FFS](https://stacks.math.columbia.edu/tag/0FFS)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Two nested shapes -/

/-- **The nested product of two global sections.** From `s : 𝟙_ ⟶ A ⊗ B` and `t : 𝟙_ ⟶ D₀ ⊗ E`
this builds a section of `(A ⊗ D₀) ⊗ (E ⊗ B)` by inserting `t` between the two factors of `s`.
It is the coevaluation of `CategoryTheory.ExactPairing.tensor` when `s` and `t` are
coevaluations. -/
def nestedTensorSection {A B D₀ E : C} (s : 𝟙_ C ⟶ A ⊗ B) (t : 𝟙_ C ⟶ D₀ ⊗ E) :
    𝟙_ C ⟶ (A ⊗ D₀) ⊗ (E ⊗ B) :=
  s ⊗≫ (A ◁ t) ▷ B ⊗≫ 𝟙 _

/-- **The monoidal product of two global sections, read into the nested target through a
swap.**  From `s : 𝟙_ ⟶ A ⊗ B` and `t : 𝟙_ ⟶ D₀ ⊗ E` and a morphism
`γ : B ⊗ (D₀ ⊗ E) ⟶ (D₀ ⊗ E) ⊗ B` this builds a section of `(A ⊗ D₀) ⊗ (E ⊗ B)` as `s ⊗ₘ t`
followed by `γ` tensored in. -/
def swappedTensorSection {A B D₀ E : C} (γ : B ⊗ (D₀ ⊗ E) ⟶ (D₀ ⊗ E) ⊗ B)
    (s : 𝟙_ C ⟶ A ⊗ B) (t : 𝟙_ C ⟶ D₀ ⊗ E) :
    𝟙_ C ⟶ (A ⊗ D₀) ⊗ (E ⊗ B) :=
  (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ⊗≫ A ◁ γ ⊗≫ 𝟙 _

/-- **The nested product of two sections is their monoidal product, read through a swap of the
second factor of the first section past the whole of the second.**  The hypothesis is that the
swap carries `B ◁ t` to `t ▷ B`, up to the unitors. -/
theorem nestedTensorSection_eq_swappedTensorSection {A B D₀ E : C}
    (s : 𝟙_ C ⟶ A ⊗ B) (t : 𝟙_ C ⟶ D₀ ⊗ E) (γ : B ⊗ (D₀ ⊗ E) ⟶ (D₀ ⊗ E) ⊗ B)
    (hγ : B ◁ t ≫ γ = (ρ_ B).hom ≫ (λ_ B).inv ≫ t ▷ B) :
    nestedTensorSection s t = swappedTensorSection γ s t := by
  dsimp only [nestedTensorSection, swappedTensorSection]
  calc
    s ⊗≫ (A ◁ t) ▷ B ⊗≫ 𝟙 _
        = s ⊗≫ A ◁ ((ρ_ B).hom ≫ (λ_ B).inv ≫ t ▷ B) ⊗≫ 𝟙 _ := by monoidal
    _ = s ⊗≫ A ◁ (B ◁ t ≫ γ) ⊗≫ 𝟙 _ := by rw [hγ]
    _ = _ := by rw [tensorHom_def]; monoidal

/-- **In a braided category the nested product of two sections is their monoidal product, read
through the braiding.** -/
theorem nestedTensorSection_eq_swappedTensorSection_braiding [BraidedCategory C]
    {A B D₀ E : C} (s : 𝟙_ C ⟶ A ⊗ B) (t : 𝟙_ C ⟶ D₀ ⊗ E) :
    nestedTensorSection s t = swappedTensorSection (β_ B (D₀ ⊗ E)).hom s t :=
  nestedTensorSection_eq_swappedTensorSection s t (β_ B (D₀ ⊗ E)).hom (by
    rw [BraidedCategory.braiding_naturality_right, braiding_tensorUnit_right, Category.assoc])

/-- **The nested pairing of two pairings**, the evaluation shape matching
`CategoryTheory.nestedTensorSection`: from `u : B ⊗ A ⟶ 𝟙_` and `v : E ⊗ D₀ ⟶ 𝟙_` it builds
`(E ⊗ B) ⊗ (A ⊗ D₀) ⟶ 𝟙_`. It is the evaluation of `CategoryTheory.ExactPairing.tensor` when
`u` and `v` are evaluations. -/
def nestedTensorPairing {A B D₀ E : C} (u : B ⊗ A ⟶ 𝟙_ C) (v : E ⊗ D₀ ⟶ 𝟙_ C) :
    (E ⊗ B) ⊗ (A ⊗ D₀) ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ E ◁ (u ▷ D₀) ⊗≫ v

/-- The coevaluation of a tensor product of exact pairings is the nested product of the two
coevaluations. -/
theorem ExactPairing.tensor_coevaluation_eq {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] :
    η_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = nestedTensorSection (η_ X₁ Y₁) (η_ X₂ Y₂) :=
  rfl

/-- The evaluation of a tensor product of exact pairings is the nested pairing of the two
evaluations. -/
theorem ExactPairing.tensor_evaluation_eq {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] :
    ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = nestedTensorPairing (ε_ X₁ Y₁) (ε_ X₂ Y₂) :=
  rfl

/-! ### The comparison of two left duals, on coevaluations -/

/-- **The comparison of two left duals of the same object carries one coevaluation to the
other.** If `A₁` and `A₂` are both left duals of `A` then `η₁ ≫ A ◁ (rightDualIso p₁ p₂).hom`
is `η₂`. -/
theorem coevaluation_comp_whiskerLeft_rightDualIso {A A₁ A₂ : C}
    (p₁ : ExactPairing A A₁) (p₂ : ExactPairing A A₂) :
    @ExactPairing.coevaluation _ _ _ A A₁ p₁ ≫ A ◁ (rightDualIso p₁ p₂).hom =
      @ExactPairing.coevaluation _ _ _ A A₂ p₂ := by
  have h := @coevaluation_comp_rightAdjointMate C _ _ A A ⟨A₂⟩ ⟨A₁⟩ (𝟙 A)
  rwa [MonoidalCategory.id_whiskerRight, Category.comp_id] at h

/-- **The comparison of two left duals carries one value of the hom-set bijection to the
other.** For `q : A ⟶ Z`, `(η₁ ≫ q ▷ A₁) ≫ Z ◁ (rightDualIso p₁ p₂).hom` is `η₂ ≫ q ▷ A₂`. -/
theorem coevaluation_comp_whiskerRight_comp_whiskerLeft_rightDualIso {A A₁ A₂ Z : C}
    (p₁ : ExactPairing A A₁) (p₂ : ExactPairing A A₂) (q : A ⟶ Z) :
    (@ExactPairing.coevaluation _ _ _ A A₁ p₁ ≫ q ▷ A₁) ≫ Z ◁ (rightDualIso p₁ p₂).hom =
      @ExactPairing.coevaluation _ _ _ A A₂ p₂ ≫ q ▷ A₂ := by
  rw [Category.assoc, ← whisker_exchange, ← Category.assoc,
    coevaluation_comp_whiskerLeft_rightDualIso]

/-! ### The hom-set bijection at the unit object -/

/-- **The hom-set bijection of an exact pairing, at the unit object, is
`f ↦ η ≫ f ▷ Y'`.** `CategoryTheory.tensorRightHomEquiv`, read on the morphism `λ ≫ f` out of
`𝟙_ ⊗ Y`, is the coevaluation followed by `f` tensored with the identity. -/
theorem coevaluation_comp_whiskerRight_eq_tensorRightHomEquiv {Y Y' Z : C}
    (p : ExactPairing Y Y') (f : Y ⟶ Z) :
    @ExactPairing.coevaluation _ _ _ Y Y' p ≫ f ▷ Y' =
      @tensorRightHomEquiv C _ _ (𝟙_ C) Y Y' Z p ((λ_ Y).hom ≫ f) :=
  (Equiv.symm_apply_eq (@tensorRightHomEquiv C _ _ (𝟙_ C) Y Y' Z p)).1
    (@tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight C _ _ Y Y' Z p f)

/-! ### Transport of a pairing along an isomorphism of the dual -/

/-- The coevaluation of `CategoryTheory.exactPairingCongrRight i` is the coevaluation of the
given pairing followed by `i.inv` tensored in. -/
theorem exactPairingCongrRight_coevaluation {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') :
    @ExactPairing.coevaluation _ _ _ X Y (exactPairingCongrRight i) = η_ X Y' ≫ X ◁ i.inv :=
  rfl

/-- The evaluation of `CategoryTheory.exactPairingCongrRight i` is `i.hom` tensored in, followed
by the evaluation of the given pairing. -/
theorem exactPairingCongrRight_evaluation {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') :
    @ExactPairing.evaluation _ _ _ X Y (exactPairingCongrRight i) = i.hom ▷ X ≫ ε_ X Y' :=
  rfl

/-! ### The value at a pure map -/

/-- **The value of the hom-set bijection of a tensor product of exact pairings at a pure map.**
For `a : X₁ ⟶ Z₁` and `b : X₂ ⟶ Z₂`, the coevaluation of
`CategoryTheory.ExactPairing.tensor` followed by `(a ⊗ₘ b)` tensored with the identity is the
nested product of the two one-factor values `η₁ ≫ a ▷ Y₁` and `η₂ ≫ b ▷ Y₂`. -/
theorem coevaluation_tensor_comp_whiskerRight_tensorHom {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] (a : X₁ ⟶ Z₁) (b : X₂ ⟶ Z₂) :
    η_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) ≫ (a ⊗ₘ b) ▷ (Y₂ ⊗ Y₁) =
      nestedTensorSection (η_ X₁ Y₁ ≫ a ▷ Y₁) (η_ X₂ Y₂ ≫ b ▷ Y₂) := by
  rw [ExactPairing.tensor_coevaluation, tensorHom_def]
  calc
    _ = η_ X₁ Y₁ ⊗≫ ((X₁ ◁ η_ X₂ Y₂ ≫ a ▷ (X₂ ⊗ Y₂)) ▷ Y₁) ⊗≫
          (Z₁ ◁ b ▷ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ := by
      monoidal
    _ = η_ X₁ Y₁ ⊗≫ ((a ▷ (𝟙_ C) ≫ Z₁ ◁ η_ X₂ Y₂) ▷ Y₁) ⊗≫
          (Z₁ ◁ b ▷ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      dsimp only [nestedTensorSection]
      monoidal

/-- **The value at a pure map, for a pairing transported along an isomorphism of the dual.**
For `i : Y ≅ Y₂ ⊗ Y₁`, it is the value of
`CategoryTheory.coevaluation_tensor_comp_whiskerRight_tensorHom` followed by one whiskering of
`i.inv`. -/
theorem coevaluation_congrRight_tensor_comp_whiskerRight_tensorHom {X₁ X₂ Y₁ Y₂ Y Z₁ Z₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] (i : Y ≅ Y₂ ⊗ Y₁) (a : X₁ ⟶ Z₁) (b : X₂ ⟶ Z₂) :
    @ExactPairing.coevaluation _ _ _ (X₁ ⊗ X₂) Y (exactPairingCongrRight i) ≫
        (a ⊗ₘ b) ▷ Y =
      nestedTensorSection (η_ X₁ Y₁ ≫ a ▷ Y₁) (η_ X₂ Y₂ ≫ b ▷ Y₂) ≫ (Z₁ ⊗ Z₂) ◁ i.inv := by
  rw [exactPairingCongrRight_coevaluation, Category.assoc, whisker_exchange, ← Category.assoc,
    coevaluation_tensor_comp_whiskerRight_tensorHom]

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal

/-! ### The duality bijection of a finite locally free module, as a formula -/

/-- **`Hom(P, ℱ) ≃ Γ(W, ℱ ⊗ P^∨)` is `q ↦ η ≫ q ▷ P^∨`**: the coevaluation of the canonical
pairing between `P` and `P^∨` followed by `q` tensored with the identity of `P^∨`. -/
theorem dualTensorHomEquiv_eq_coevaluation_comp (W : Scheme.{u}) (P F : W.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) P) (q : P ⟶ F) :
    dualTensorHomEquiv W P F hP q =
      @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal W) P (dualSheaf P)
          (dualSheafExactPairing W P hP) ≫
        MonoidalCategory.whiskerRight q (dualSheaf P) := by
  rw [dualTensorHomEquiv_apply]
  exact (@coevaluation_comp_whiskerRight_eq_tensorRightHomEquiv W.Modules _
    (onSpaceModulesMonoidal W) P (dualSheaf P) F (dualSheafExactPairing W P hP) q).symm

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **`Hom(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))` is `q ↦ η ≫ q ▷ (ℰ^∨ ⊠ 𝒢^∨)`**, the
coevaluation now being that of `AlgebraicGeometry.externalTensorProductExactPairing`. -/
theorem externalTensorDualTensorHomEquiv_eq_coevaluation_comp (E : X.Modules) (G : Y.Modules)
    (F : (Limits.pullback f g).Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (q : externalTensorProduct f g E G ⟶ F) :
    externalTensorDualTensorHomEquiv f g E G F hE hG q =
      @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          (externalTensorProduct f g E G)
          (externalTensorProduct f g (dualSheaf E) (dualSheaf G))
          (externalTensorProductExactPairing f g E G hE hG) ≫
        MonoidalCategory.whiskerRight q
          (externalTensorProduct f g (dualSheaf E) (dualSheaf G)) := by
  show dualTensorHomEquiv (Limits.pullback f g) (externalTensorProduct f g E G) F
        (isFiniteLocallyFree_externalTensorProduct f g E G hE hG) q ≫
      MonoidalCategory.whiskerLeft F (externalTensorProductDualIso f g E G hE hG).hom = _
  rw [dualTensorHomEquiv_eq_coevaluation_comp]
  exact @coevaluation_comp_whiskerRight_comp_whiskerLeft_rightDualIso _ _
    (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
    (dualSheafExactPairing (Limits.pullback f g) (externalTensorProduct f g E G)
      (isFiniteLocallyFree_externalTensorProduct f g E G hE hG))
    (externalTensorProductExactPairing f g E G hE hG) q

/-! ### The two factor pairings -/

/-- The coevaluation of `AlgebraicGeometry.externalTensorProductFirstPairing`: the canonical
coevaluation of `pr₁^*ℰ` read through the base-change comparison `pr₁^*(ℰ^∨) ≅ (pr₁^*ℰ)^∨`. -/
theorem externalTensorProductFirstPairing_coevaluation (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
        (externalTensorProductFirstPairing f g E hE) =
      @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
          (dualSheaf ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E))
          (dualSheafExactPairing (Limits.pullback f g)
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
            (isFiniteLocallyFree_pullback (Limits.pullback.fst f g) E hE)) ≫
        MonoidalCategory.whiskerLeft
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
          (pullbackDualSheafIso (Limits.pullback.fst f g) E hE).inv :=
  rfl

/-- The evaluation of `AlgebraicGeometry.externalTensorProductFirstPairing`. -/
theorem externalTensorProductFirstPairing_evaluation (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    @ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
        (externalTensorProductFirstPairing f g E hE) =
      @MonoidalCategory.whiskerRight _ _
          (onSpaceModulesMonoidal (Limits.pullback f g)).toMonoidalCategoryStruct _ _
          (pullbackDualSheafIso (Limits.pullback.fst f g) E hE).hom
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E) ≫
        @ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
          (dualSheaf ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E))
          (dualSheafExactPairing (Limits.pullback f g)
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
            (isFiniteLocallyFree_pullback (Limits.pullback.fst f g) E hE)) :=
  rfl

/-- The coevaluation of `AlgebraicGeometry.externalTensorProductSecondPairing`: the canonical
coevaluation of `pr₂^*𝒢` read through the base-change comparison `pr₂^*(𝒢^∨) ≅ (pr₂^*𝒢)^∨`. -/
theorem externalTensorProductSecondPairing_coevaluation (G : Y.Modules)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))
        (externalTensorProductSecondPairing f g G hG) =
      @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
          (dualSheaf ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G))
          (dualSheafExactPairing (Limits.pullback f g)
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
            (isFiniteLocallyFree_pullback (Limits.pullback.snd f g) G hG)) ≫
        MonoidalCategory.whiskerLeft
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
          (pullbackDualSheafIso (Limits.pullback.snd f g) G hG).inv :=
  rfl

/-- The evaluation of `AlgebraicGeometry.externalTensorProductSecondPairing`. -/
theorem externalTensorProductSecondPairing_evaluation (G : Y.Modules)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    @ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))
        (externalTensorProductSecondPairing f g G hG) =
      @MonoidalCategory.whiskerRight _ _
          (onSpaceModulesMonoidal (Limits.pullback f g)).toMonoidalCategoryStruct _ _
          (pullbackDualSheafIso (Limits.pullback.snd f g) G hG).hom
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G) ≫
        @ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
          (dualSheaf ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G))
          (dualSheafExactPairing (Limits.pullback f g)
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
            (isFiniteLocallyFree_pullback (Limits.pullback.snd f g) G hG)) :=
  rfl

/-! ### The coevaluation and the evaluation of the box pairing, factorwise -/

/-- **The coevaluation of `ℰ^∨ ⊠ 𝒢^∨` as a left dual of `ℰ ⊠ 𝒢`, computed factorwise.** It is
the nested product `CategoryTheory.nestedTensorSection` of the coevaluations of the two factor
pairings, followed by the symmetry of the tensor product sheaf, which puts the two duals in the
order they are written in. -/
theorem externalTensorProductExactPairing_coevaluation (E : X.Modules) (G : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        (externalTensorProduct f g E G)
        (externalTensorProduct f g (dualSheaf E) (dualSheaf G))
        (externalTensorProductExactPairing f g E G hE hG) =
      @nestedTensorSection _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
            (externalTensorProductFirstPairing f g E hE))
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
            (externalTensorProductSecondPairing f g G hG)) ≫
        MonoidalCategory.whiskerLeft (externalTensorProduct f g E G)
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).inv :=
  rfl

/-- **The evaluation of `ℰ^∨ ⊠ 𝒢^∨` as a left dual of `ℰ ⊠ 𝒢`, computed factorwise.** It is
the symmetry of the tensor product sheaf followed by the nested pairing
`CategoryTheory.nestedTensorPairing` of the evaluations of the two factor pairings. -/
theorem externalTensorProductExactPairing_evaluation (E : X.Modules) (G : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    @ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        (externalTensorProduct f g E G)
        (externalTensorProduct f g (dualSheaf E) (dualSheaf G))
        (externalTensorProductExactPairing f g E G hE hG) =
      @MonoidalCategory.whiskerRight _ _
          (onSpaceModulesMonoidal (Limits.pullback f g)).toMonoidalCategoryStruct _ _
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).hom
          (externalTensorProduct f g E G) ≫
        @nestedTensorPairing _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
          (@ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
            (externalTensorProductFirstPairing f g E hE))
          (@ExactPairing.evaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
            (externalTensorProductSecondPairing f g G hG)) :=
  rfl

/-! ### The symmetry of the tensor product sheaf on a section out of the unit -/

section Symmetry

open Stacks.SheafOfModules.OnSpace

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-- **The symmetry of the tensor product sheaf exchanges the two factors of a local pure
tensor**, at the spelling `Stacks.SheafOfModules.OnSpace.tensorObjTmul` of a local pure
tensor. -/
theorem tensorSheafBraiding_tensorObjTmul (W : AlgebraicGeometry.RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureSheafRing W))
    (U : (TopologicalSpace.Opens W.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (((Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
        (structureSheafRing W).property A B).hom).val.app U).hom (tensorObjTmul W A B U a b) =
      tensorObjTmul W B A U b a :=
  Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt
    W.presheaf (structureSheafRing W).property U A B a b

/-- **The symmetry of the tensor product sheaf carries `B ◁ t` to `t ▷ B` for a morphism `t`
out of the structure sheaf**, up to the unitors, for the symmetry of [Stacks, Tag 01CA] at the
monoidal structure `Stacks.SheafOfModules.OnSpace.monoidal`. -/
theorem whiskerLeft_comp_tensorSheafBraiding_hom (W : AlgebraicGeometry.RingedSpace.{u, u})
    (B M : SheafOfModules.{u} (structureSheafRing W))
    (t : 𝟙_ (SheafOfModules.{u} (structureSheafRing W)) ⟶ M) :
    B ◁ t ≫ (Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
        (structureSheafRing W).property B M).hom =
      (ρ_ B).hom ≫ (λ_ B).inv ≫ t ▷ B := by
  have key : ∀ (U : (TopologicalSpace.Opens W.carrier)ᵒᵖ) (b : B.val.obj U)
      (r : W.presheaf.obj U),
      (((B ◁ t) ≫ (Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
            (structureSheafRing W).property B M).hom).val.app U).hom
          (tensorObjTmul W B (𝟙_ (SheafOfModules.{u} (structureSheafRing W))) U b
            (unitSection W U r)) =
        ((((ρ_ B).hom ≫ (λ_ B).inv ≫ t ▷ B)).val.app U).hom
          (tensorObjTmul W B (𝟙_ (SheafOfModules.{u} (structureSheafRing W))) U b
            (unitSection W U r)) := by
    intro U b r
    have hl : (((B ◁ t) ≫ (Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
          (structureSheafRing W).property B M).hom).val.app U).hom
        (tensorObjTmul W B (𝟙_ (SheafOfModules.{u} (structureSheafRing W))) U b
          (unitSection W U r)) =
        tensorObjTmul W M B U ((t.val.app U).hom (unitSection W U r)) b :=
      (sheaf_comp_app_apply W (B ◁ t) (Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
          (structureSheafRing W).property B M).hom U _).trans
        ((congrArg (fun z => (((Stacks.SheafOfModules.tensorSheafBraiding W.presheaf
              (structureSheafRing W).property B M).hom).val.app U).hom z)
            (whiskerLeft_tmul W B t U b (unitSection W U r))).trans
          (tensorSheafBraiding_tensorObjTmul W B M U b _))
    have hr : ((((ρ_ B).hom ≫ (λ_ B).inv ≫ t ▷ B)).val.app U).hom
        (tensorObjTmul W B (𝟙_ (SheafOfModules.{u} (structureSheafRing W))) U b
          (unitSection W U r)) =
        tensorObjTmul W M B U ((t.val.app U).hom (unitSection W U 1)) (r • b) :=
      sheaf_comp3_app_apply_of W (ρ_ B).hom (λ_ B).inv (t ▷ B) U _ (rightUnitor_tmul W B U b r)
        (leftUnitor_inv_apply W B U (r • b)) (whiskerRight_tmul W t B U _ (r • b))
    refine hl.trans (Eq.trans ?_ hr.symm)
    have hone : (unitSection W U r) = r • (unitSection W U 1) := by
      show r = r • (1 : W.presheaf.obj U)
      rw [smul_eq_mul, mul_one]
    rw [hone, map_smul, ← tensorObjTmul_smul_right]
  exact tensor_hom_ext W fun U c d => key U c d

end Symmetry

/-! ### The value at a pure map -/

/-- **A pure map `a ⊠ b` is the monoidal product of the two pullbacks.**  `ℰ ⊠ 𝒢` is the
monoidal product `pr₁^*ℰ ⊗ pr₂^*𝒢`, and `a ⊠ b` is the monoidal product of `pr₁^*a` and
`pr₂^*b`. -/
theorem externalTensorProductMap_eq_tensorHom {E E₂ : X.Modules} {G G₂ : Y.Modules}
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorProductMap f g a b =
      @MonoidalCategory.tensorHom _ _
        (onSpaceModulesMonoidal (Limits.pullback f g)).toMonoidalCategoryStruct
        _ _ _ _ ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b) :=
  (Stacks.SheafOfModules.OnSpace.tensorHom_eq_tensorSheafMap (Limits.pullback f g).toRingedSpace
    ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
    ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)).symm

/-- **The value of the duality bijection at a pure map `a ⊠ b`.** For `a : ℰ ⟶ ℰ₂` and
`b : 𝒢 ⟶ 𝒢₂` between finite locally free modules, the bijection

`Hom(ℰ ⊠ 𝒢, ℰ₂ ⊠ 𝒢₂) ≃ Γ(X ×_S Y, (ℰ₂ ⊠ 𝒢₂) ⊗ (ℰ^∨ ⊠ 𝒢^∨))`

carries `a ⊠ b` to the nested product of the duality section of `pr₁^*a` for the first factor
pairing and the duality section of `pr₂^*b` for the second, read through the symmetry of the
tensor product sheaf. -/
theorem externalTensorDualTensorHomEquiv_externalTensorProductMap
    (E E₂ : X.Modules) (G G₂ : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
        (externalTensorProductMap f g a b) =
      @nestedTensorSection _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
              (externalTensorProductFirstPairing f g E hE) ≫
            MonoidalCategory.whiskerRight
              ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
              ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E)))
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
              (externalTensorProductSecondPairing f g G hG) ≫
            MonoidalCategory.whiskerRight
              ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)
              ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))) ≫
        MonoidalCategory.whiskerLeft (externalTensorProduct f g E₂ G₂)
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).inv := by
  rw [externalTensorDualTensorHomEquiv_eq_coevaluation_comp,
    externalTensorProductMap_eq_tensorHom]
  exact @coevaluation_congrRight_tensor_comp_whiskerRight_tensorHom _ _
    (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _ _ _ _
    (externalTensorProductFirstPairing f g E hE)
    (externalTensorProductSecondPairing f g G hG)
    (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
      ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G)))
    ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
    ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)

/-- **The value of the duality bijection at a pure map `a ⊠ b`, as a product of the two factor
sections.**  The nested section of
`AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap` is the monoidal
product `s_a ⊗ₘ s_b` of the two factor sections, read into its target through the symmetry of
the tensor product sheaf; so the value of the bijection at `a ⊠ b` depends on `a` and on `b`
only through their two one-factor duality sections, and depends on them *separately*.  Two
symmetries appear: the inner one puts the second factor section past `pr₁^*(ℰ^∨)`, the outer one
is the symmetry already present in `AlgebraicGeometry.externalTensorProductExactPairing`. -/
theorem externalTensorDualTensorHomEquiv_externalTensorProductMap_swapped
    (E E₂ : X.Modules) (G G₂ : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
        (externalTensorProductMap f g a b) =
      @swappedTensorSection _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  (⟨(Limits.pullback f g).toRingedSpace.presheaf,
                      (Limits.pullback f g).toRingedSpace.IsSheaf⟩ :
                    Sheaf (JX (Limits.pullback f g).toRingedSpace) CommRingCat.{u})).obj
                ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G₂)).obj
              ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))))).hom
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
              (externalTensorProductFirstPairing f g E hE) ≫
            MonoidalCategory.whiskerRight
              ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
              ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E)))
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _
              (externalTensorProductSecondPairing f g G hG) ≫
            MonoidalCategory.whiskerRight
              ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)
              ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))) ≫
        MonoidalCategory.whiskerLeft (externalTensorProduct f g E₂ G₂)
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).inv := by
  rw [externalTensorDualTensorHomEquiv_externalTensorProductMap]
  exact congrArg (· ≫ _) (@nestedTensorSection_eq_swappedTensorSection _ _
    (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _ _ _ _
    (whiskerLeft_comp_tensorSheafBraiding_hom _ _ _ _))

end AlgebraicGeometry

end
