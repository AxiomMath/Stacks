module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The intersection computation behind the duality of `h(X)`

Let `k` be a field and let `X` be smooth and proper over `k` of constant dimension `d`, and write
`U = Spec k`. The proof of Stacks 0FGI shows that `h(X)(d)` is a left dual of `h(X)` with unit and
counit both the class of the diagonal, by computing the composite of `[Δ] ⊗ 1` with `1 ⊗ [Δ]`:
on the product of the five factors the two cycles meet in the small diagonal, which projects onto
the diagonal. This file carries out that computation on the actual Chow groups, for the canonical
family of diagonal classes.

In the first triangle identity the composite in question is a correspondence from `U × X` to
`X × U` through `X × (X × X)`:

* `[A]`, the unit tensored with the identity and moved by the associator, is the class of
  `X × X ⟶ (U × X) × (X × (X × X))`, `(x, y) ↦ ((⋆, y), (x, (x, y)))`;
* `[B]`, the identity tensored with the counit, is the class of
  `X × X ⟶ (X × (X × X)) × (X × U)`, `(u, v) ↦ ((u, (v, v)), (u, ⋆))`;

and `A ×_{X × (X × X)} B` is the small diagonal `X`, embedded in `(U × X) × (X × U)` by
`z ↦ ((⋆, z), (z, ⋆))`. In the second triangle identity the roles are mirrored.

## Main results

* `Stacks.WeilCohomology.compositionInt_unitTensor_tensorCounit`: `[B] ∘ [A] = [X]` for the first
  triangle identity, `A` and `B` as above.
* `Stacks.WeilCohomology.compositionInt_tensorUnit_counitTensor`: the same for the second triangle
  identity, with `A : (y, a) ↦ ((y, ⋆), ((y, a), a))` in `(X × U) × ((X × X) × X)`,
  `B : (b, z) ↦ (((b, b), z), (⋆, z))` in `((X × X) × X) × (U × X)` and the small diagonal
  `z ↦ ((z, ⋆), (⋆, z))` in `(X × U) × (U × X)`.
* `Stacks.WeilCohomology.unitTensorFibreIso`, `Stacks.WeilCohomology.tensorUnitFibreIso`: the
  fibre products over the middle factor are the small diagonal, scheme-theoretically.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)

/-! ### The schemes and morphisms of the first triangle identity -/

section Maps

/-- The structure morphism of the base point `U = Spec k`. -/
abbrev pointBase : (fieldChowSituation k).S ⟶ (fieldChowSituation k).S :=
  𝟙 (fieldChowSituation k).S

/-- The two projections of `X × X` agree over the base. -/
theorem fst_comp_eq_snd_comp : pullback.fst sX sX ≫ sX = pullback.snd sX sX ≫ sX :=
  pullback.condition

/-- `(x, y) ↦ (⋆, y)`, from `X × X` to `U × X`. -/
def pointSnd : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback (pointBase k) sX :=
  pullback.lift (pullback.snd sX sX ≫ sX) (pullback.snd sX sX) (by simp)

/-- `(x, y) ↦ (x, (x, y))`, from `X × X` to `X × (X × X)`. -/
def diagFstPair : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback sX (prodBase sX sX) :=
  pullback.lift (pullback.fst sX sX) (𝟙 _) (by simp [prodBase])

/-- The unit tensored with the identity, moved by the associator:
`(x, y) ↦ ((⋆, y), (x, (x, y)))`, from `X × X` to `(U × X) × (X × (X × X))`. -/
def unitTensorMap : (Limits.pullback sX sX : Scheme.{u}) ⟶
    Limits.pullback (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)) :=
  pullback.lift (pointSnd k sX) (diagFstPair k sX) (by
    simp only [pointSnd, diagFstPair, prodBase, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id, fst_comp_eq_snd_comp k sX])

/-- `(u, v) ↦ (u, (v, v))`, from `X × X` to `X × (X × X)`. -/
def sndDiagPair : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback sX (prodBase sX sX) :=
  pullback.lift (pullback.fst sX sX) (pullback.snd sX sX ≫ pullback.diagonal sX) (by
    simp [prodBase, fst_comp_eq_snd_comp k sX])

/-- `(u, v) ↦ (u, ⋆)`, from `X × X` to `X × U`. -/
def fstPoint : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback sX (pointBase k) :=
  pullback.lift (pullback.fst sX sX) (pullback.fst sX sX ≫ sX) (by simp)

/-- The identity tensored with the counit: `(u, v) ↦ ((u, (v, v)), (u, ⋆))`, from `X × X` to
`(X × (X × X)) × (X × U)`. -/
def tensorCounitMap : (Limits.pullback sX sX : Scheme.{u}) ⟶
    Limits.pullback (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)) :=
  pullback.lift (sndDiagPair k sX) (fstPoint k sX) (by
    simp only [sndDiagPair, fstPoint, prodBase, pullback.lift_fst_assoc,
      fst_comp_eq_snd_comp k sX])

/-- `z ↦ (⋆, z)`, from `X` to `U × X`. -/
def pointPair : X ⟶ Limits.pullback (pointBase k) sX :=
  pullback.lift sX (𝟙 X) (by simp)

/-- `z ↦ (z, ⋆)`, from `X` to `X × U`. -/
def pairPoint : X ⟶ Limits.pullback sX (pointBase k) :=
  pullback.lift (𝟙 X) sX (by simp)

/-- The small diagonal `z ↦ ((⋆, z), (z, ⋆))`, from `X` to `(U × X) × (X × U)`. -/
def pointSwapMap : X ⟶ Limits.pullback (prodBase (pointBase k) sX) (prodBase sX (pointBase k)) :=
  pullback.lift (pointPair k sX) (pairPoint k sX) (by
    rw [prodBase, prodBase, pointPair, pairPoint, pullback.lift_fst_assoc,
      pullback.lift_fst_assoc, Category.comp_id, Category.id_comp])

section Simp

/-- The first coordinate of `pointSnd` is the structure morphism of the second factor. -/
@[reassoc (attr := simp)] theorem pointSnd_fst :
    pointSnd k sX ≫ pullback.fst (pointBase k) sX = pullback.snd sX sX ≫ sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pointSnd` is the second projection of `X × X`. -/
@[reassoc (attr := simp)] theorem pointSnd_snd :
    pointSnd k sX ≫ pullback.snd (pointBase k) sX = pullback.snd sX sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `diagFstPair` is the first projection of `X × X`. -/
@[reassoc (attr := simp)] theorem diagFstPair_fst :
    diagFstPair k sX ≫ pullback.fst sX (prodBase sX sX) = pullback.fst sX sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `diagFstPair` is the identity of `X × X`. -/
@[reassoc (attr := simp)] theorem diagFstPair_snd :
    diagFstPair k sX ≫ pullback.snd sX (prodBase sX sX) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `sndDiagPair` is the first projection of `X × X`. -/
@[reassoc (attr := simp)] theorem sndDiagPair_fst :
    sndDiagPair k sX ≫ pullback.fst sX (prodBase sX sX) = pullback.fst sX sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `sndDiagPair` is the second projection followed by the diagonal. -/
@[reassoc (attr := simp)] theorem sndDiagPair_snd :
    sndDiagPair k sX ≫ pullback.snd sX (prodBase sX sX) =
      pullback.snd sX sX ≫ pullback.diagonal sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `fstPoint` is the first projection of `X × X`. -/
@[reassoc (attr := simp)] theorem fstPoint_fst :
    fstPoint k sX ≫ pullback.fst sX (pointBase k) = pullback.fst sX sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `fstPoint` is the structure morphism of the first factor. -/
@[reassoc (attr := simp)] theorem fstPoint_snd :
    fstPoint k sX ≫ pullback.snd sX (pointBase k) = pullback.fst sX sX ≫ sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `unitTensorMap` is `pointSnd`. -/
@[reassoc (attr := simp)] theorem unitTensorMap_fst :
    unitTensorMap k sX ≫ pullback.fst (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)) =
      pointSnd k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `unitTensorMap` is `diagFstPair`. -/
@[reassoc (attr := simp)] theorem unitTensorMap_snd :
    unitTensorMap k sX ≫ pullback.snd (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)) =
      diagFstPair k sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `tensorCounitMap` is `sndDiagPair`. -/
@[reassoc (attr := simp)] theorem tensorCounitMap_fst :
    tensorCounitMap k sX ≫ pullback.fst (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)) =
      sndDiagPair k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `tensorCounitMap` is `fstPoint`. -/
@[reassoc (attr := simp)] theorem tensorCounitMap_snd :
    tensorCounitMap k sX ≫ pullback.snd (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)) =
      fstPoint k sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `pointPair` is the structure morphism of `X`. -/
@[reassoc (attr := simp)] theorem pointPair_fst :
    pointPair k sX ≫ pullback.fst (pointBase k) sX = sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pointPair` is the identity of `X`. -/
@[reassoc (attr := simp)] theorem pointPair_snd :
    pointPair k sX ≫ pullback.snd (pointBase k) sX = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `pairPoint` is the identity of `X`. -/
@[reassoc (attr := simp)] theorem pairPoint_fst :
    pairPoint k sX ≫ pullback.fst sX (pointBase k) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pairPoint` is the structure morphism of `X`. -/
@[reassoc (attr := simp)] theorem pairPoint_snd :
    pairPoint k sX ≫ pullback.snd sX (pointBase k) = sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `pointSwapMap` is `pointPair`. -/
@[reassoc (attr := simp)] theorem pointSwapMap_fst :
    pointSwapMap k sX ≫ pullback.fst (prodBase (pointBase k) sX) (prodBase sX (pointBase k)) =
      pointPair k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pointSwapMap` is `pairPoint`. -/
@[reassoc (attr := simp)] theorem pointSwapMap_snd :
    pointSwapMap k sX ≫ pullback.snd (prodBase (pointBase k) sX) (prodBase sX (pointBase k)) =
      pairPoint k sX :=
  pullback.lift_snd _ _ _

end Simp

end Maps

/-! ### Closed immersions with a retraction -/

/-- A morphism with a retraction over a base is a closed immersion as soon as its target is
separated over the base: it is a section of the retraction, which is separated. -/
@[sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
theorem isClosedImmersion_of_retraction {A B S : Scheme.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (h : g ≫ r = 𝟙 A) (sA : A ⟶ S) (sB : B ⟶ S) [IsSeparated sB] (hr : r ≫ sA = sB) :
    IsClosedImmersion g := by
  have : IsSeparated (r ≫ sA) := hr ▸ inferInstance
  have : IsSeparated r := IsSeparated.of_comp r sA
  have : IsClosedImmersion (g ≫ r) := h ▸ inferInstance
  exact IsClosedImmersion.of_comp g r

/-! ### The first triangle identity -/

section FirstTriangle

variable [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX]

/-- The fibre product `A ×_{X × (X × X)} B` of the first triangle identity. -/
abbrev unitTensorFibre : Scheme.{u} :=
  compositionFibre (unitTensorMap k sX) (tensorCounitMap k sX)

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The three coordinate equations on `A ×_{X × (X × X)} B`: a point `((x, y), (u, v))` with
`(x, (x, y)) = (u, (v, v))` has `x = u`, `x = v` and `y = v`. -/
theorem unitTensorFibre_eqs :
    (pullback.fst _ _ ≫ pullback.fst sX sX =
        (pullback.snd _ _ ≫ pullback.fst sX sX : unitTensorFibre k sX ⟶ X)) ∧
      (pullback.fst _ _ ≫ pullback.fst sX sX =
        (pullback.snd _ _ ≫ pullback.snd sX sX : unitTensorFibre k sX ⟶ X)) ∧
      (pullback.fst _ _ ≫ pullback.snd sX sX =
        (pullback.snd _ _ ≫ pullback.snd sX sX : unitTensorFibre k sX ⟶ X)) := by
  have hc := pullback.condition
    (f := unitTensorMap k sX ≫
      pullback.snd (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)))
    (g := tensorCounitMap k sX ≫
      pullback.fst (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)))
  have h₁ := congrArg (· ≫ pullback.fst sX (prodBase sX sX)) hc
  have h₂ := congrArg (· ≫ pullback.snd sX (prodBase sX sX) ≫ pullback.fst sX sX) hc
  have h₃ := congrArg (· ≫ pullback.snd sX (prodBase sX sX) ≫ pullback.snd sX sX) hc
  simp only [Category.assoc, unitTensorMap_snd_assoc, tensorCounitMap_fst_assoc,
    diagFstPair_fst, diagFstPair_snd_assoc, sndDiagPair_fst, sndDiagPair_snd_assoc,
    pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

/-- The small diagonal `X ⟶ A ×_{X × (X × X)} B`, `z ↦ ((z, z), (z, z))`. -/
def unitTensorFibreInv : X ⟶ unitTensorFibre k sX :=
  pullback.lift (pullback.diagonal sX) (pullback.diagonal sX) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, unitTensorMap_snd_assoc, tensorCounitMap_fst_assoc,
        diagFstPair_fst, sndDiagPair_fst]
    · simp only [Category.assoc, unitTensorMap_snd_assoc, tensorCounitMap_fst_assoc,
        diagFstPair_snd, sndDiagPair_snd, Category.comp_id, pullback.diagonal_snd_assoc])

/-- **`A ×_{X × (X × X)} B` is the small diagonal.** -/
def unitTensorFibreIso : unitTensorFibre k sX ≅ X where
  hom := pullback.fst _ _ ≫ pullback.fst sX sX
  inv := unitTensorFibreInv k sX
  hom_inv_id := by
    obtain ⟨h₁, h₂, h₃⟩ := unitTensorFibre_eqs k sX
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp only [unitTensorFibreInv, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, Category.id_comp]
    · exact h₂.trans h₃.symm
    · exact h₁
    · exact h₂
  inv_hom_id := by
    rw [unitTensorFibreInv, pullback.lift_fst_assoc, pullback.diagonal_fst]

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The small diagonal maps to `(U × X) × (X × U)` by `z ↦ ((⋆, z), (z, ⋆))`. -/
theorem unitTensorFibreIso_hom_pointSwapMap :
    (unitTensorFibreIso k sX).hom ≫ pointSwapMap k sX =
      compositionFibre.toProduct (unitTensorMap k sX) (tensorCounitMap k sX) := by
  obtain ⟨h₁, h₂, h₃⟩ := unitTensorFibre_eqs k sX
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp only [unitTensorFibreIso, compositionFibre.toProduct, Category.assoc,
      pointSwapMap_fst_assoc, pointSwapMap_snd_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, unitTensorMap_fst_assoc, tensorCounitMap_snd_assoc,
      pointPair_fst, pointPair_snd, pairPoint_fst, pairPoint_snd, pointSnd_fst, pointSnd_snd,
      fstPoint_fst, fstPoint_snd, Category.comp_id]
  all_goals first
    | exact h₁
    | exact h₂.trans h₃.symm
    | (rw [fst_comp_eq_snd_comp k sX]; done)
    | rw [reassoc_of% h₁]

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- `A` is a closed subscheme of `(U × X) × (X × (X × X))`: the projection to the last two
coordinates retracts it. -/
theorem isClosedImmersion_unitTensorMap : IsClosedImmersion (unitTensorMap k sX) := by
  refine isClosedImmersion_of_retraction _
    (pullback.snd _ _ ≫ pullback.snd sX (prodBase sX sX)) (by simp) (prodBase sX sX)
    (prodBase (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX))) ?_
  have c₁ : pullback.fst sX (prodBase sX sX) ≫ sX =
      pullback.snd sX (prodBase sX sX) ≫ prodBase sX sX := pullback.condition
  have c₂ : pullback.fst (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)) ≫
      prodBase (pointBase k) sX = pullback.snd _ _ ≫ prodBase sX (prodBase sX sX) :=
    pullback.condition
  calc (pullback.snd _ _ ≫ pullback.snd sX (prodBase sX sX)) ≫ prodBase sX sX
      = pullback.snd _ _ ≫ (pullback.fst sX (prodBase sX sX) ≫ sX) := by
        rw [Category.assoc, c₁]
    _ = pullback.snd _ _ ≫ prodBase sX (prodBase sX sX) := rfl
    _ = _ := c₂.symm

/-- The retraction `((u, (v, w)), (u', ⋆)) ↦ (u, w)` of `B`. -/
def tensorCounitRetraction :
    Limits.pullback (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)) ⟶
      Limits.pullback sX sX :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.fst _ _ ≫ pullback.snd _ _ ≫ pullback.snd sX sX) (by
      rw [Category.assoc, Category.assoc, pullback.condition (f := sX) (g := prodBase sX sX),
        prodBase, Category.assoc, pullback.condition (f := sX) (g := sX)])

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The first coordinate of `tensorCounitRetraction` is `((u, (v, w)), (u', ⋆)) ↦ u`. -/
@[reassoc (attr := simp)] theorem tensorCounitRetraction_fst :
    tensorCounitRetraction k sX ≫ pullback.fst sX sX = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The second coordinate of `tensorCounitRetraction` is `((u, (v, w)), (u', ⋆)) ↦ w`. -/
@[reassoc (attr := simp)] theorem tensorCounitRetraction_snd :
    tensorCounitRetraction k sX ≫ pullback.snd sX sX =
      pullback.fst _ _ ≫ pullback.snd _ _ ≫ pullback.snd sX sX :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- `B` is a closed subscheme of `(X × (X × X)) × (X × U)`. -/
theorem isClosedImmersion_tensorCounitMap : IsClosedImmersion (tensorCounitMap k sX) := by
  refine isClosedImmersion_of_retraction _ (tensorCounitRetraction k sX) ?_ (prodBase sX sX)
    (prodBase (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k))) ?_
  · apply pullback.hom_ext
    · rw [Category.assoc, tensorCounitRetraction_fst, tensorCounitMap_fst_assoc, sndDiagPair_fst,
        Category.id_comp]
    · rw [Category.assoc, tensorCounitRetraction_snd, tensorCounitMap_fst_assoc,
        sndDiagPair_snd_assoc, pullback.diagonal_snd, Category.comp_id, Category.id_comp]
  · change tensorCounitRetraction k sX ≫ pullback.fst sX sX ≫ sX = _
    rw [tensorCounitRetraction_fst_assoc]

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- The small diagonal `z ↦ ((⋆, z), (z, ⋆))` is a closed subscheme of `(U × X) × (X × U)`. -/
theorem isClosedImmersion_pointSwapMap : IsClosedImmersion (pointSwapMap k sX) := by
  refine isClosedImmersion_of_retraction _
    (pullback.fst _ _ ≫ pullback.snd (pointBase k) sX) (by simp) sX
    (prodBase (prodBase (pointBase k) sX) (prodBase sX (pointBase k))) ?_
  rw [Category.assoc, ← pullback.condition]

attribute [local instance] isClosedImmersion_unitTensorMap isClosedImmersion_tensorCounitMap
  isClosedImmersion_pointSwapMap

/-- **The first triangle identity on cycles.** For `X` smooth and proper over `k` of constant
dimension `d`, the composite of `[A]`, the unit `[Δ]` tensored with the identity and moved by the
associator, with `[B]`, the identity tensored with the counit `[Δ]`, is the class of the small
diagonal `z ↦ ((⋆, z), (z, ⋆))` in `(U × X) × (X × U)`, for the canonical family of diagonal
classes. -/
theorem compositionInt_unitTensor_tensorCounit {d dU eY fZ : ℕ} (hX : RelativeDimension sX d)
    (hXa : RelativeDimension (prodBase (pointBase k) sX) dU)
    (hYb : RelativeDimension (prodBase sX (prodBase sX sX)) eY)
    (hZc : RelativeDimension (prodBase sX (pointBase k)) fZ) (r s : ℤ)
    (hr : ((d + d : ℕ) : ℤ) = eY - r) (hs : ((d + d : ℕ) : ℤ) = fZ - s)
    (hrs : (d : ℤ) = fZ - (r + s)) :
    compositionInt k (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX))
        (prodBase sX (pointBase k)) (canonicalDiagonalClassFamily k) hXa hYb hZc r s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase (pointBase k) sX) (prodBase sX (prodBase sX sX)))
          (unitTensorMap k sX) ((eY : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX (prodBase sX sX)) (prodBase sX (pointBase k)))
          (tensorCounitMap k sX) ((fZ : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase (pointBase k) sX) (prodBase sX (pointBase k)))
        (pointSwapMap k sX) ((fZ : ℤ) - (r + s))) := by
  refine compositionInt_smoothTransversal k _ _ _ hXa hYb hZc r s (unitTensorMap k sX)
    (tensorCounitMap k sX) (pointSwapMap k sX) (unitTensorFibreIso k sX)
    (unitTensorFibreIso_hom_pointSwapMap k sX) (qA := prodBase sX sX) (qB := prodBase sX sX)
    (qF := sX) ?_ ?_ ?_ (relativeDimension_prodBase k sX sX hX hX)
    (relativeDimension_prodBase k sX sX hX hX) hX hr hs hrs
  · change unitTensorMap k sX ≫ pullback.fst _ _ ≫ pullback.fst (pointBase k) sX ≫ 𝟙 _ = _
    rw [unitTensorMap_fst_assoc, pointSnd_fst_assoc, Category.comp_id]
    exact (fst_comp_eq_snd_comp k sX).symm
  · change tensorCounitMap k sX ≫ pullback.fst _ _ ≫ pullback.fst sX (prodBase sX sX) ≫ sX = _
    rw [tensorCounitMap_fst_assoc, sndDiagPair_fst_assoc]
  · change pointSwapMap k sX ≫ pullback.fst _ _ ≫ pullback.fst (pointBase k) sX ≫ 𝟙 _ = _
    rw [pointSwapMap_fst_assoc, pointPair_fst_assoc, Category.comp_id]

end FirstTriangle

/-! ### The second triangle identity -/

section SecondTriangle

/-- `(y, a) ↦ ((y, a), a)`, from `X × X` to `(X × X) × X`. -/
def pairDiagSnd : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback (prodBase sX sX) sX :=
  pullback.lift (𝟙 _) (pullback.snd sX sX) (by
    rw [Category.id_comp]
    exact pullback.condition)

/-- The identity tensored with the unit, moved by the inverse associator:
`(y, a) ↦ ((y, ⋆), ((y, a), a))`, from `X × X` to `(X × U) × ((X × X) × X)`. -/
def tensorUnitMap : (Limits.pullback sX sX : Scheme.{u}) ⟶
    Limits.pullback (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX) :=
  pullback.lift (fstPoint k sX) (pairDiagSnd k sX) (by
    change fstPoint k sX ≫ pullback.fst sX (pointBase k) ≫ sX =
      pairDiagSnd k sX ≫ pullback.fst (prodBase sX sX) sX ≫ pullback.fst sX sX ≫ sX
    simp only [fstPoint, pairDiagSnd, pullback.lift_fst_assoc, Category.id_comp])

/-- `(b, z) ↦ ((b, b), z)`, from `X × X` to `(X × X) × X`. -/
def diagPairFst : (Limits.pullback sX sX : Scheme.{u}) ⟶ Limits.pullback (prodBase sX sX) sX :=
  pullback.lift (pullback.fst sX sX ≫ pullback.diagonal sX) (pullback.snd sX sX) (by
    change (pullback.fst sX sX ≫ pullback.diagonal sX) ≫ pullback.fst sX sX ≫ sX = _
    rw [Category.assoc, pullback.diagonal_fst_assoc]
    exact pullback.condition)

/-- The counit tensored with the identity: `(b, z) ↦ (((b, b), z), (⋆, z))`, from `X × X` to
`((X × X) × X) × (U × X)`. -/
def counitTensorMap : (Limits.pullback sX sX : Scheme.{u}) ⟶
    Limits.pullback (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX) :=
  pullback.lift (diagPairFst k sX) (pointSnd k sX) (by
    change diagPairFst k sX ≫ pullback.fst (prodBase sX sX) sX ≫ pullback.fst sX sX ≫ sX =
      pointSnd k sX ≫ pullback.fst (pointBase k) sX ≫ 𝟙 (fieldChowSituation k).S
    simp only [diagPairFst, pointSnd, pullback.lift_fst_assoc, Category.assoc,
      pullback.diagonal_fst_assoc, Category.comp_id, pullback.lift_fst]
    exact pullback.condition (f := sX) (g := sX))

/-- The small diagonal `z ↦ ((z, ⋆), (⋆, z))`, from `X` to `(X × U) × (U × X)`. -/
def swapPointMap : X ⟶ Limits.pullback (prodBase sX (pointBase k)) (prodBase (pointBase k) sX) :=
  pullback.lift (pairPoint k sX) (pointPair k sX) (by
    rw [prodBase, prodBase, pointPair, pairPoint, pullback.lift_fst_assoc,
      pullback.lift_fst_assoc, Category.comp_id, Category.id_comp])

section Simp

/-- The first coordinate of `pairDiagSnd` is the identity of `X × X`. -/
@[reassoc (attr := simp)] theorem pairDiagSnd_fst :
    pairDiagSnd k sX ≫ pullback.fst (prodBase sX sX) sX = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `pairDiagSnd` is the second projection of `X × X`. -/
@[reassoc (attr := simp)] theorem pairDiagSnd_snd :
    pairDiagSnd k sX ≫ pullback.snd (prodBase sX sX) sX = pullback.snd sX sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `diagPairFst` is the first projection followed by the diagonal. -/
@[reassoc (attr := simp)] theorem diagPairFst_fst :
    diagPairFst k sX ≫ pullback.fst (prodBase sX sX) sX =
      pullback.fst sX sX ≫ pullback.diagonal sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `diagPairFst` is the second projection of `X × X`. -/
@[reassoc (attr := simp)] theorem diagPairFst_snd :
    diagPairFst k sX ≫ pullback.snd (prodBase sX sX) sX = pullback.snd sX sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `tensorUnitMap` is `fstPoint`. -/
@[reassoc (attr := simp)] theorem tensorUnitMap_fst :
    tensorUnitMap k sX ≫ pullback.fst (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX) =
      fstPoint k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `tensorUnitMap` is `pairDiagSnd`. -/
@[reassoc (attr := simp)] theorem tensorUnitMap_snd :
    tensorUnitMap k sX ≫ pullback.snd (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX) =
      pairDiagSnd k sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `counitTensorMap` is `diagPairFst`. -/
@[reassoc (attr := simp)] theorem counitTensorMap_fst :
    counitTensorMap k sX ≫ pullback.fst (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX) =
      diagPairFst k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `counitTensorMap` is `pointSnd`. -/
@[reassoc (attr := simp)] theorem counitTensorMap_snd :
    counitTensorMap k sX ≫ pullback.snd (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX) =
      pointSnd k sX :=
  pullback.lift_snd _ _ _

/-- The first coordinate of `swapPointMap` is `pairPoint`. -/
@[reassoc (attr := simp)] theorem swapPointMap_fst :
    swapPointMap k sX ≫ pullback.fst (prodBase sX (pointBase k)) (prodBase (pointBase k) sX) =
      pairPoint k sX :=
  pullback.lift_fst _ _ _

/-- The second coordinate of `swapPointMap` is `pointPair`. -/
@[reassoc (attr := simp)] theorem swapPointMap_snd :
    swapPointMap k sX ≫ pullback.snd (prodBase sX (pointBase k)) (prodBase (pointBase k) sX) =
      pointPair k sX :=
  pullback.lift_snd _ _ _

end Simp

/-- The fibre product `A ×_{(X × X) × X} B` of the second triangle identity. -/
abbrev tensorUnitFibre : Scheme.{u} :=
  compositionFibre (tensorUnitMap k sX) (counitTensorMap k sX)

/-- The three coordinate equations on `A ×_{(X × X) × X} B`: a point `((y, a), (b, z))` with
`((y, a), a) = ((b, b), z)` has `y = b`, `a = b` and `a = z`. -/
theorem tensorUnitFibre_eqs :
    (pullback.fst _ _ ≫ pullback.fst sX sX =
        (pullback.snd _ _ ≫ pullback.fst sX sX : tensorUnitFibre k sX ⟶ X)) ∧
      (pullback.fst _ _ ≫ pullback.snd sX sX =
        (pullback.snd _ _ ≫ pullback.fst sX sX : tensorUnitFibre k sX ⟶ X)) ∧
      (pullback.fst _ _ ≫ pullback.snd sX sX =
        (pullback.snd _ _ ≫ pullback.snd sX sX : tensorUnitFibre k sX ⟶ X)) := by
  have hc := pullback.condition
    (f := tensorUnitMap k sX ≫
      pullback.snd (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX))
    (g := counitTensorMap k sX ≫
      pullback.fst (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX))
  have h₁ := congrArg (· ≫ pullback.fst (prodBase sX sX) sX ≫ pullback.fst sX sX) hc
  have h₂ := congrArg (· ≫ pullback.fst (prodBase sX sX) sX ≫ pullback.snd sX sX) hc
  have h₃ := congrArg (· ≫ pullback.snd (prodBase sX sX) sX) hc
  simp only [Category.assoc, tensorUnitMap_snd_assoc, counitTensorMap_fst_assoc,
    pairDiagSnd_fst_assoc, pairDiagSnd_snd, diagPairFst_fst_assoc, diagPairFst_snd,
    pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

/-- The small diagonal `X ⟶ A ×_{(X × X) × X} B`, `z ↦ ((z, z), (z, z))`. -/
def tensorUnitFibreInv : X ⟶ tensorUnitFibre k sX :=
  pullback.lift (pullback.diagonal sX) (pullback.diagonal sX) (by
    apply pullback.hom_ext
    · simp only [Category.assoc, tensorUnitMap_snd_assoc, counitTensorMap_fst_assoc,
        pairDiagSnd_fst, diagPairFst_fst, Category.comp_id, pullback.diagonal_fst_assoc]
    · simp only [Category.assoc, tensorUnitMap_snd_assoc, counitTensorMap_fst_assoc,
        pairDiagSnd_snd, diagPairFst_snd])

/-- **`A ×_{(X × X) × X} B` is the small diagonal.** -/
def tensorUnitFibreIso : tensorUnitFibre k sX ≅ X where
  hom := pullback.fst _ _ ≫ pullback.fst sX sX
  inv := tensorUnitFibreInv k sX
  hom_inv_id := by
    obtain ⟨h₁, h₂, h₃⟩ := tensorUnitFibre_eqs k sX
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp only [tensorUnitFibreInv, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, Category.id_comp]
    all_goals first
      | exact h₁
      | exact h₁.trans h₂.symm | exact (h₁.trans h₂.symm).trans h₃
  inv_hom_id := by
    rw [tensorUnitFibreInv, pullback.lift_fst_assoc, pullback.diagonal_fst]

/-- The small diagonal maps to `(X × U) × (U × X)` by `z ↦ ((z, ⋆), (⋆, z))`. -/
theorem tensorUnitFibreIso_hom_swapPointMap :
    (tensorUnitFibreIso k sX).hom ≫ swapPointMap k sX =
      compositionFibre.toProduct (tensorUnitMap k sX) (counitTensorMap k sX) := by
  obtain ⟨h₁, h₂, h₃⟩ := tensorUnitFibre_eqs k sX
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp only [tensorUnitFibreIso, compositionFibre.toProduct, Category.assoc,
      swapPointMap_fst_assoc, swapPointMap_snd_assoc, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, tensorUnitMap_fst_assoc, counitTensorMap_snd_assoc,
      pointPair_fst, pointPair_snd, pairPoint_fst, pairPoint_snd, pointSnd_fst, pointSnd_snd,
      fstPoint_fst, fstPoint_snd, Category.comp_id]
  all_goals first
    | exact (h₁.trans h₂.symm).trans h₃
    | (rw [fst_comp_eq_snd_comp k sX]; done)
    | (rw [reassoc_of% h₁]; done)
    | rw [reassoc_of% h₁, ← reassoc_of% h₂, reassoc_of% h₃]

variable [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX]

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- `A` is a closed subscheme of `(X × U) × ((X × X) × X)`. -/
theorem isClosedImmersion_tensorUnitMap : IsClosedImmersion (tensorUnitMap k sX) := by
  refine isClosedImmersion_of_retraction _
    (pullback.snd _ _ ≫ pullback.fst (prodBase sX sX) sX) (by simp) (prodBase sX sX)
    (prodBase (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX)) ?_
  have c₂ : pullback.fst (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX) ≫
      prodBase sX (pointBase k) = pullback.snd _ _ ≫ prodBase (prodBase sX sX) sX :=
    pullback.condition
  rw [Category.assoc]
  exact c₂.symm

/-- The retraction `(((b, b'), z), (⋆, z')) ↦ (b, z)` of `B`. -/
def counitTensorRetraction :
    Limits.pullback (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX) ⟶
      Limits.pullback sX sX :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst sX sX)
    (pullback.fst _ _ ≫ pullback.snd (prodBase sX sX) sX) (by
      have c : pullback.fst (prodBase sX sX) sX ≫ pullback.fst sX sX ≫ sX =
          pullback.snd (prodBase sX sX) sX ≫ sX := pullback.condition
      simp only [Category.assoc, c])

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The first coordinate of `counitTensorRetraction` is `(((b, b'), z), (⋆, z')) ↦ b`. -/
@[reassoc (attr := simp)] theorem counitTensorRetraction_fst :
    counitTensorRetraction k sX ≫ pullback.fst sX sX =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst sX sX :=
  pullback.lift_fst _ _ _

omit [LocallyOfFiniteType sX] [Smooth sX] [IsProper sX] in
/-- The second coordinate of `counitTensorRetraction` is `(((b, b'), z), (⋆, z')) ↦ z`. -/
@[reassoc (attr := simp)] theorem counitTensorRetraction_snd :
    counitTensorRetraction k sX ≫ pullback.snd sX sX =
      pullback.fst _ _ ≫ pullback.snd (prodBase sX sX) sX :=
  pullback.lift_snd _ _ _

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- `B` is a closed subscheme of `((X × X) × X) × (U × X)`. -/
theorem isClosedImmersion_counitTensorMap : IsClosedImmersion (counitTensorMap k sX) := by
  refine isClosedImmersion_of_retraction _ (counitTensorRetraction k sX) ?_ (prodBase sX sX)
    (prodBase (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX)) ?_
  · apply pullback.hom_ext
    · rw [Category.assoc, counitTensorRetraction_fst, counitTensorMap_fst_assoc,
        diagPairFst_fst_assoc, pullback.diagonal_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, counitTensorRetraction_snd, counitTensorMap_fst_assoc, diagPairFst_snd,
        Category.id_comp]
  · change counitTensorRetraction k sX ≫ pullback.fst sX sX ≫ sX = _
    rw [counitTensorRetraction_fst_assoc]

omit [LocallyOfFiniteType sX] [Smooth sX] in
/-- The small diagonal `z ↦ ((z, ⋆), (⋆, z))` is a closed subscheme of `(X × U) × (U × X)`. -/
theorem isClosedImmersion_swapPointMap : IsClosedImmersion (swapPointMap k sX) := by
  refine isClosedImmersion_of_retraction _
    (pullback.fst _ _ ≫ pullback.fst sX (pointBase k)) (by simp) sX
    (prodBase (prodBase sX (pointBase k)) (prodBase (pointBase k) sX)) ?_
  rw [Category.assoc]

attribute [local instance] isClosedImmersion_tensorUnitMap isClosedImmersion_counitTensorMap
  isClosedImmersion_swapPointMap

/-- **The second triangle identity on cycles.** For `X` smooth and proper over `k` of constant
dimension `d`, the composite of `[A]`, the identity tensored with the unit `[Δ]` and moved by the
inverse associator, with `[B]`, the counit `[Δ]` tensored with the identity, is the class of the
small diagonal `z ↦ ((z, ⋆), (⋆, z))` in `(X × U) × (U × X)`, for the canonical family of
diagonal classes. -/
theorem compositionInt_tensorUnit_counitTensor {d dU eY fZ : ℕ} (hX : RelativeDimension sX d)
    (hXa : RelativeDimension (prodBase sX (pointBase k)) dU)
    (hYb : RelativeDimension (prodBase (prodBase sX sX) sX) eY)
    (hZc : RelativeDimension (prodBase (pointBase k) sX) fZ) (r s : ℤ)
    (hr : ((d + d : ℕ) : ℤ) = eY - r) (hs : ((d + d : ℕ) : ℤ) = fZ - s)
    (hrs : (d : ℤ) = fZ - (r + s)) :
    compositionInt k (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX)
        (prodBase (pointBase k) sX) (canonicalDiagonalClassFamily k) hXa hYb hZc r s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase sX (pointBase k)) (prodBase (prodBase sX sX) sX))
          (tensorUnitMap k sX) ((eY : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase (prodBase (prodBase sX sX) sX) (prodBase (pointBase k) sX))
          (counitTensorMap k sX) ((fZ : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (prodBase sX (pointBase k)) (prodBase (pointBase k) sX))
        (swapPointMap k sX) ((fZ : ℤ) - (r + s))) := by
  refine compositionInt_smoothTransversal k _ _ _ hXa hYb hZc r s (tensorUnitMap k sX)
    (counitTensorMap k sX) (swapPointMap k sX) (tensorUnitFibreIso k sX)
    (tensorUnitFibreIso_hom_swapPointMap k sX) (qA := prodBase sX sX) (qB := prodBase sX sX)
    (qF := sX) ?_ ?_ ?_ (relativeDimension_prodBase k sX sX hX hX)
    (relativeDimension_prodBase k sX sX hX hX) hX hr hs hrs
  · change tensorUnitMap k sX ≫ pullback.fst _ _ ≫ pullback.fst sX (pointBase k) ≫ sX = _
    rw [tensorUnitMap_fst_assoc, fstPoint_fst_assoc]
  · change counitTensorMap k sX ≫ pullback.fst _ _ ≫ pullback.fst (prodBase sX sX) sX ≫
      pullback.fst sX sX ≫ sX = _
    rw [counitTensorMap_fst_assoc, diagPairFst_fst_assoc, pullback.diagonal_fst_assoc]
  · change swapPointMap k sX ≫ pullback.fst _ _ ≫ pullback.fst sX (pointBase k) ≫ sX = _
    rw [swapPointMap_fst_assoc, pairPoint_fst_assoc]

end SecondTriangle

end Stacks.WeilCohomology

end
