module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# The abstract projection-formula map at an object that tensors to a functor

`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` proves that the
abstract projection-formula map

`A(R G, V) ⟶ R (B(G, L V))`

of `CategoryTheory.adjunctionTensorMap` is invertible when `V` is a *unit object* for the
bifunctor `A`, i.e. when `A(-, V)` is isomorphic to the identity.  This file removes the
restriction to the identity: it is enough that `A(-, V)` be isomorphic to **some** functor `Φ`
and `B(-, V')` to some functor `Ψ`, where `V' ≅ L V`, provided the comparison `α` is coherent for
those isomorphisms and provided the mate of the commutation `c : Φ ⋙ L ⟶ L ⋙ Ψ` is invertible.

The case this is for is `Φ = Ψ = ` a shift.  In a triangulated setting the object `V` is the
structure sheaf placed in a degree, `A(-, V)` is a shift of the identity rather than the identity,
and the mate of `c` is then the commutation of the right adjoint with that shift, which is an
isomorphism: that is `commutationMate_shift` below.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectionFormula.commutationMate` — the mate
  `Φ (R G) ⟶ R (Ψ G)` of a commutation `c : Φ ⋙ L ⟶ L ⋙ Ψ`, i.e. its adjoint transpose
  composed with the counit.

## Main results

* `adjunctionTensorMap_tensorFunctor_comp` — the projection-formula map at `V`, composed with the
  two isomorphisms that identify its target with `R (Ψ G)`, is `ρA` followed by the mate of `c`.
* `isIso_adjunctionTensorMap_of_tensorFunctorIso` — hence it is invertible as soon as the mate of
  `c` is.
* `commutationMate_shift` — for a shift, and an adjunction compatible with it, the mate of the
  commutation isomorphism of the left adjoint is the inverse commutation isomorphism of the right
  adjoint; `isIso_commutationMate_shift` reads off that it is invertible.
* `tensorFunctorCoherence_of_iso` and `tensorFunctorCoherence_of_essSurj` — the coherence of `α`
  need only be checked on an essentially surjective family of objects, exactly as
  `Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_essSurj` does for a unit
  object.

## Implementation notes

*Why the mate is a hypothesis and not a conclusion.*  For general `Φ` and `Ψ` the mate of an
isomorphism `c` need not be invertible — nothing relates `Φ` and `Ψ` to the adjunction.  What
makes the shift case work is `CategoryTheory.Adjunction.CommShift`, and the identification of the
mate it provides is `commutationMate_shift`.  Keeping the two apart means the first three results
need no shift, no additivity and no triangulated structure.

*The product morphisms are ascribed*, as in
`StacksFrontier/AlgebraicGeometry/Duality/RightUnitorCoherenceInvariance.lean`: each `u ×ₘ 𝟙`
names its source and target in the product category, so that the statements match the shape
`CategoryTheory.adjunctionTensorMap` is stated at syntactically.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open CategoryTheory

open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

universe v₁ v₂ v₃ u₁ u₂ u₃

section Abstract

/-- Whiskering on the two sides of a bifunctor commutes. -/
private theorem map_prod_whisker_comm {D : Type u₂} [Category.{v₂} D] (B : D × D ⥤ D)
    {X Y P Q : D} (f : X ⟶ Y) (g : P ⟶ Q) :
    B.map ((f ×ₘ 𝟙 P) : ((X, P) : D × D) ⟶ (Y, P)) ≫
        B.map ((𝟙 Y ×ₘ g) : ((Y, P) : D × D) ⟶ (Y, Q)) =
      B.map ((𝟙 X ×ₘ g) : ((X, P) : D × D) ⟶ (X, Q)) ≫
        B.map ((f ×ₘ 𝟙 Q) : ((X, Q) : D × D) ⟶ (Y, Q)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Prod.ext <;> simp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {V : C} {V' : D} {Φ : C ⥤ C} {Ψ : D ⥤ D}
  (ρA : ∀ Z : C, A.obj (Z, V) ≅ Φ.obj Z) (ρB : ∀ W : D, B.obj (W, V') ≅ Ψ.obj W)
  (ν : L.obj V ≅ V') (c : Φ ⋙ L ⟶ L ⋙ Ψ)

/-- **The mate of a commutation `c : Φ ⋙ L ⟶ L ⋙ Ψ`** for an adjunction `L ⊣ R`: the adjoint
transpose of `c` at `R G` followed by `Ψ` of the counit, a morphism `Φ (R G) ⟶ R (Ψ G)`. -/
def commutationMate (G : D) : Φ.obj (R.obj G) ⟶ R.obj (Ψ.obj G) :=
  adj.homEquiv _ _ (c.app (R.obj G) ≫ Ψ.map (adj.counit.app G))

/-- **The abstract projection-formula map at `V`, composed with the isomorphisms that identify
its target with `R (Ψ G)`, is `ρA` followed by the mate of `c`.**  The two hypotheses are the
naturality of `ρB` and the coherence of `α`; everything else is the triangle identity of
`L ⊣ R`.

At `Φ = 𝟭`, `Ψ = 𝟭` and `c = 𝟙` this is
`Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_unitObj_comp`, whose right-hand
side is `ρA (R G)` alone. -/
lemma adjunctionTensorMap_tensorFunctor_comp
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 V') : ((W, V') : D × D) ⟶ (W', V')) ≫ (ρB W').hom =
        (ρB W).hom ≫ Ψ.map u)
    (hcoh : ∀ Z : C, α.app (Z, V) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z, V')) ≫ (ρB (L.obj Z)).hom =
        L.map (ρA Z).hom ≫ c.app Z)
    (G : D) :
    adjunctionTensorMap adj A B α G V ≫
        R.map (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj V) : D × D) ⟶ (G, V')) ≫ (ρB G).hom) =
      (ρA (R.obj G)).hom ≫ commutationMate adj c G := by
  unfold adjunctionTensorMap commutationMate
  rw [← Adjunction.homEquiv_naturality_right]
  have h1 := map_prod_whisker_comm B (X := L.obj (R.obj G)) (Y := G) (adj.counit.app G) ν.hom
  calc adj.homEquiv _ _ ((α.app (R.obj G, V) ≫ B.map ((adj.counit.app G ×ₘ 𝟙 (L.obj V)) :
          ((L.obj (R.obj G), L.obj V) : D × D) ⟶ (G, L.obj V))) ≫
          (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj V) : D × D) ⟶ (G, V')) ≫ (ρB G).hom))
      = adj.homEquiv _ _ (L.map (ρA (R.obj G)).hom ≫
          (c.app (R.obj G) ≫ Ψ.map (adj.counit.app G))) := by
        congr 1
        rw [Category.assoc, ← Category.assoc (B.map ((adj.counit.app G ×ₘ 𝟙 (L.obj V)) :
            ((L.obj (R.obj G), L.obj V) : D × D) ⟶ (G, L.obj V))), h1,
          Category.assoc, hρB (W := L.obj (R.obj G)) (W' := G) (adj.counit.app G),
          ← Category.assoc (B.map ((𝟙 (L.obj (R.obj G)) ×ₘ ν.hom) :
            ((L.obj (R.obj G), L.obj V) : D × D) ⟶ (L.obj (R.obj G), V'))),
          ← Category.assoc, hcoh (R.obj G), Category.assoc]
    _ = (ρA (R.obj G)).hom ≫ adj.homEquiv _ _ (c.app (R.obj G) ≫ Ψ.map (adj.counit.app G)) := by
        rw [Adjunction.homEquiv_naturality_left]

/-- **The abstract projection-formula map at `V` is invertible** as soon as the coherence holds
and the mate of `c` is invertible at `G`. -/
lemma isIso_adjunctionTensorMap_of_tensorFunctorIso
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 V') : ((W, V') : D × D) ⟶ (W', V')) ≫ (ρB W').hom =
        (ρB W).hom ≫ Ψ.map u)
    (hcoh : ∀ Z : C, α.app (Z, V) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z, V')) ≫ (ρB (L.obj Z)).hom =
        L.map (ρA Z).hom ≫ c.app Z)
    (G : D) (hG : IsIso (commutationMate adj c G)) :
    IsIso (adjunctionTensorMap adj A B α G V) := by
  have hν : IsIso ((𝟙 G ×ₘ ν.hom) : ((G, L.obj V) : D × D) ⟶ (G, V')) :=
    ⟨(𝟙 G ×ₘ ν.inv), by apply Prod.ext <;> simp, by apply Prod.ext <;> simp⟩
  have h2 : IsIso (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj V) : D × D) ⟶ (G, V')) ≫ (ρB G).hom) :=
    inferInstance
  have h := adjunctionTensorMap_tensorFunctor_comp adj A B α ρA ρB ν c hρB hcoh G
  have h3 : adjunctionTensorMap adj A B α G V =
      ((ρA (R.obj G)).hom ≫ commutationMate adj c G) ≫
        inv (R.map (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj V) : D × D) ⟶ (G, V')) ≫
          (ρB G).hom)) := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h3]
  have := hG
  infer_instance

end Abstract

section CoherenceTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {V : C} {V' : D} {Φ : C ⥤ C} {Ψ : D ⥤ D}
  (ρA : ∀ Z : C, A.obj (Z, V) ≅ Φ.obj Z) (ρB : ∀ W : D, B.obj (W, V') ≅ Ψ.obj W)
  (ν : L.obj V ≅ V') (c : Φ ⋙ L ⟶ L ⋙ Ψ)

/-- **The coherence of `α` transports backwards along an isomorphism of the object.**  This is
`Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_iso` with the identity
functor replaced by `Φ` and `Ψ`; the extra ingredient is the naturality of `c`, and what is
cancelled at the end is `Ψ` of `L` of the isomorphism rather than `L` of it. -/
theorem tensorFunctorCoherence_of_iso
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 V) : ((Z, V) : C × C) ⟶ (Z', V)) ≫ (ρA Z').hom =
        (ρA Z).hom ≫ Φ.map u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 V') : ((W, V') : D × D) ⟶ (W', V')) ≫ (ρB W').hom =
        (ρB W).hom ≫ Ψ.map u)
    {Z Z' : C} (i : Z ≅ Z')
    (h : α.app (Z', V) ≫ B.map ((𝟙 (L.obj Z') ×ₘ ν.hom) :
          ((L.obj Z', L.obj V) : D × D) ⟶ (L.obj Z', V')) ≫ (ρB (L.obj Z')).hom =
        L.map (ρA Z').hom ≫ c.app Z') :
    α.app (Z, V) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
        ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z, V')) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom ≫ c.app Z := by
  have hL : IsIso (L.map i.hom) := (L.mapIso i).isIso_hom
  have hΨ : IsIso (Ψ.map (L.map i.hom)) := (Ψ.mapIso (L.mapIso i)).isIso_hom
  have hα := α.naturality ((i.hom ×ₘ 𝟙 V) : ((Z, V) : C × C) ⟶ (Z', V))
  dsimp only [Functor.comp_map, Functor.prod_map] at hα
  rw [CategoryTheory.Functor.map_id] at hα
  have hc := c.naturality i.hom
  dsimp only [Functor.comp_map] at hc
  have hmid := map_prod_whisker_comm B (L.map i.hom) ν.hom
  apply (cancel_mono (Ψ.map (L.map i.hom))).1
  calc (α.app (Z, V) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z, V')) ≫ (ρB (L.obj Z)).hom) ≫
          Ψ.map (L.map i.hom)
      = α.app (Z, V) ≫ B.map ((L.map i.hom ×ₘ 𝟙 (L.obj V)) :
            ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z', L.obj V)) ≫
          B.map ((𝟙 (L.obj Z') ×ₘ ν.hom) :
            ((L.obj Z', L.obj V) : D × D) ⟶ (L.obj Z', V')) ≫ (ρB (L.obj Z')).hom := by
        simp only [Category.assoc]
        rw [← hρB (L.map i.hom)]
        congr 1
        rw [← Category.assoc, ← Category.assoc, hmid]
    _ = L.map (A.map ((i.hom ×ₘ 𝟙 V) : ((Z, V) : C × C) ⟶ (Z', V))) ≫
          L.map (ρA Z').hom ≫ c.app Z' := by
        rw [← Category.assoc, ← hα, Category.assoc, h]
    _ = (L.map (ρA Z).hom ≫ c.app Z) ≫ Ψ.map (L.map i.hom) := by
        rw [← Functor.map_comp_assoc, hρA i.hom, Functor.map_comp, Category.assoc,
          Category.assoc, hc]

/-- **The coherence of `α` needs checking only on an essentially surjective family.**  The
analogue of `Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_essSurj`. -/
theorem tensorFunctorCoherence_of_essSurj {E : Type u₃} [Category.{v₃} E] (G : E ⥤ C) [G.EssSurj]
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 V) : ((Z, V) : C × C) ⟶ (Z', V)) ≫ (ρA Z').hom =
        (ρA Z).hom ≫ Φ.map u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 V') : ((W, V') : D × D) ⟶ (W', V')) ≫ (ρB W').hom =
        (ρB W).hom ≫ Ψ.map u)
    (h : ∀ e : E, α.app (G.obj e, V) ≫ B.map ((𝟙 (L.obj (G.obj e)) ×ₘ ν.hom) :
          ((L.obj (G.obj e), L.obj V) : D × D) ⟶ (L.obj (G.obj e), V')) ≫
            (ρB (L.obj (G.obj e))).hom = L.map (ρA (G.obj e)).hom ≫ c.app (G.obj e))
    (Z : C) :
    α.app (Z, V) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
        ((L.obj Z, L.obj V) : D × D) ⟶ (L.obj Z, V')) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom ≫ c.app Z :=
  tensorFunctorCoherence_of_iso A B α ρA ρB ν c hρA hρB (G.objObjPreimageIso Z).symm
    (h (G.objPreimage Z))

end CoherenceTransport

section Shift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  [L.CommShift M] [R.CommShift M] [adj.CommShift M]

/-- **For a shift, the mate of the commutation isomorphism of the left adjoint is the inverse
commutation isomorphism of the right adjoint.**  This is
`CategoryTheory.Adjunction.shift_counit_app`, which is the counit half of
`CategoryTheory.Adjunction.CommShift`, transposed. -/
lemma commutationMate_shift (m : M) (G : D) :
    commutationMate adj (L.commShiftIso m).hom G = (R.commShiftIso m).inv.app G := by
  apply (adj.homEquiv _ _).symm.injective
  rw [commutationMate, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    adj.shift_counit_app m G]
  simp

/-- The mate of the commutation isomorphism of the left adjoint is invertible. -/
instance isIso_commutationMate_shift (m : M) (G : D) :
    IsIso (commutationMate adj (L.commShiftIso m).hom G) := by
  rw [commutationMate_shift adj m G]
  infer_instance

end Shift

end Stacks.AlgebraicGeometry.ProjectionFormula

end
