module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference

/-!
# The intersection pairing on a surface and Hilbert functions

Let `X` be a scheme proper over a field `k`. For an invertible `𝒪_X`-module `𝓛` the
*Hilbert function* of `𝓛` is `n ↦ χ(X, 𝓛^{⊗ n})`; its values for `n ≥ 0` are those of the
Hilbert polynomial of `𝓛` ([Stacks, Tag 0BEM]).

If `dim X ≤ 2`, the intersection number of two invertible modules is, by its definition
([Stacks, Tag 0BEP]), the mixed second difference

`(𝓝 · 𝓛) = χ(X, 𝓝 ⊗ 𝓛) - χ(X, 𝓝) - χ(X, 𝓛) + χ(X, 𝒪_X)`,

so it is read off from the values at `1` and `0` of the Hilbert functions of `𝓝`, `𝓛` and
`𝓝 ⊗ 𝓛`. Euler characteristics, and hence Hilbert functions, are invariant under automorphisms
of `X` over `k`.

## Main definitions

* `AlgebraicGeometry.hilbertFunction`: `n ↦ χ(X, 𝓛^{⊗ n})`.

## Main results

* `AlgebraicGeometry.intersectionNumber_two_eq_eulerCharacteristic`: the formula above.
* `AlgebraicGeometry.eulerCharacteristic_pullback_of_isIso`: `χ(X, g^*ℱ) = χ(X, ℱ)` for an
  automorphism `g` over `k`.
* `AlgebraicGeometry.hilbertFunction_pullback_of_isIso`: `g^*𝓛` and `𝓛` have the same Hilbert
  function.

## References

* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-- A sum over the four subsets of `Fin 2`. -/
private theorem sum_finset_fin_two {M : Type*} [AddCommMonoid M] (g : Finset (Fin 2) → M) :
    ∑ T, g T = g ∅ + g {0} + g {1} + g {0, 1} := by
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  abel

/-- The Euler characteristics of isomorphic modules, the first computed over `𝟙 X ≫ p`. -/
private theorem eulerCharacteristic_id_comp_eq_of_iso {F G : X.Modules} [F.IsCoherent]
    [G.IsCoherent] (e : F ≅ G) :
    @eulerCharacteristic k _ X (𝟙 X ≫ p) inferInstance F ‹_› = eulerCharacteristic k p G := by
  rw [eulerCharacteristic_eq_of_iso k (𝟙 X ≫ p) e]
  simp only [Category.id_comp]

/-- **The intersection pairing on a surface through Euler characteristics**: for invertible
modules `𝓝`, `𝓛` on a scheme `X` of dimension at most two, proper over `k`,

`(𝓝 · 𝓛) = χ(X, 𝓝 ⊗ 𝓛) - χ(X, 𝓝) - χ(X, 𝓛) + χ(X, 𝒪_X)`.

This is the definition of [Stacks, Tag 0BEP] for `d = 2`, the four twists
`𝒪_X ⊗ 𝓝^{⊗ a} ⊗ 𝓛^{⊗ b}`, `a, b ∈ {0, 1}`, being identified with `𝒪_X`, `𝓝`, `𝓛` and
`𝓝 ⊗ 𝓛` by the unit constraints of the tensor product. -/
theorem intersectionNumber_two_eq_eulerCharacteristic (hX : topologicalKrullDim X ≤ (2 : ℕ))
    (F : Fin 2 → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (F j)] :
    intersectionNumber k p (𝟙 X) 2 hX F =
      @eulerCharacteristic k _ X p _ (Scheme.Modules.tensorObj (F 0) (F 1))
          (SheafOfModules.isCoherent_of_isInvertible k p _) -
        @eulerCharacteristic k _ X p _ (F 0) (SheafOfModules.isCoherent_of_isInvertible k p _) -
        @eulerCharacteristic k _ X p _ (F 1) (SheafOfModules.isCoherent_of_isInvertible k p _) +
        @eulerCharacteristic k _ X p _ (SheafOfModules.unit X.ringCatSheaf)
          (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p) := by
  have := SheafOfModules.isCoherent_of_isInvertible k p (F 0)
  have := SheafOfModules.isCoherent_of_isInvertible k p (F 1)
  have := SheafOfModules.isCoherent_of_isInvertible k p (Scheme.Modules.tensorObj (F 0) (F 1))
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
  rw [intersectionNumber_eq_sum_eulerCharacteristic, sum_finset_fin_two]
  have hN := tensorPowerOneIso X.presheaf X.ringCatSheaf.2 _ ≪≫
    (Scheme.Modules.pullbackId X).app (F 0)
  have hL := tensorPowerOneIso X.presheaf X.ringCatSheaf.2 _ ≪≫
    (Scheme.Modules.pullbackId X).app (F 1)
  have key : ∀ (T : Finset (Fin 2)) (G : X.Modules) [G.IsCoherent],
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (F j))
        (fun j => if j ∈ T then 1 else 0) ≅ G) →
      @eulerCharacteristic k _ X (𝟙 X ≫ p) inferInstance (twistedSheaf
        (SheafOfModules.unit X.ringCatSheaf)
        (fun j => (Scheme.Modules.pullback (𝟙 X)).obj (F j))
        (fun j => if j ∈ T then 1 else 0))
        (isCoherent_twistedSheafUnitPullback k p (𝟙 X) F _) = eulerCharacteristic k p G :=
    fun T G _ e =>
      have := isCoherent_twistedSheafUnitPullback k p (𝟙 X) F
        (fun j => if j ∈ T then 1 else 0)
      eulerCharacteristic_id_comp_eq_of_iso k p e
  rw [key ∅ (SheafOfModules.unit X.ringCatSheaf)
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _),
    key {0} (F 0)
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (1 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ hN),
    key {1} (F 1)
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (0 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (1 : ℤ))) ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 _) (Iso.refl _) ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ hL),
    key {0, 1} (Scheme.Modules.tensorObj (F 0) (F 1))
      (tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductIso X.presheaf X.ringCatSheaf.2 (Iso.refl _)
            (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (1 : ℤ))))
          (tensorPowerReindex X.presheaf X.ringCatSheaf.2 _ (by decide : _ = (1 : ℤ))) ≪≫
        tensorProductIso X.presheaf X.ringCatSheaf.2
          (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫ hN) hL)]
  have h2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [Finset.card_empty, Finset.card_singleton, h2]
  ring

/-! ### The Hilbert function of an invertible module -/

/-- **The Hilbert function** `n ↦ χ(X, 𝓛^{⊗ n})`, `n ≥ 0`, of an invertible module `𝓛` on a
scheme proper over `k`. Its values are those of the Hilbert polynomial of `𝓛`
([Stacks, Tag 0BEM]). -/
def hilbertFunction (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (n : ℕ) : ℤ :=
  @eulerCharacteristic k _ X p _ (tensorPower X.presheaf X.ringCatSheaf.2 L n)
    (SheafOfModules.isCoherent_of_isInvertible k p _)

variable (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The value of the Hilbert function at `0` is `χ(X, 𝒪_X)`. -/
theorem hilbertFunction_zero :
    hilbertFunction k p L 0 = @eulerCharacteristic k _ X p _ (SheafOfModules.unit X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p) :=
  rfl

/-- The value of the Hilbert function at `1` is `χ(X, 𝓛)`. -/
theorem hilbertFunction_one :
    hilbertFunction k p L 1 =
      @eulerCharacteristic k _ X p _ L (SheafOfModules.isCoherent_of_isInvertible k p _) := by
  have := SheafOfModules.isCoherent_of_isInvertible k p L
  have := SheafOfModules.isCoherent_of_isInvertible k p
    (tensorPower X.presheaf X.ringCatSheaf.2 L ((1 : ℕ) : ℤ))
  exact eulerCharacteristic_eq_of_iso k p (tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L)

/-- **The Euler characteristic is invariant under an automorphism over `k`**:
`χ(X, g^*ℱ) = χ(X, ℱ)` for an automorphism `g` of `X` with `g ≫ p = p`. -/
theorem eulerCharacteristic_pullback_of_isIso (g : X ⟶ X) [IsIso g] (hg : g ≫ p = p)
    (F : X.Modules) [F.IsCoherent] [((Scheme.Modules.pullback g).obj F).IsCoherent] :
    eulerCharacteristic k p ((Scheme.Modules.pullback g).obj F) = eulerCharacteristic k p F := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  refine finsum_congr fun n => ?_
  have h := finrank_cohomologyOverField_pullback k g p F n
  rw [hg] at h
  rw [h]

/-- **An automorphism over `k` preserves Hilbert functions**: `g^*𝓛` and `𝓛` have the same
Hilbert function, since `g^*(𝓛^{⊗ n}) ≅ (g^*𝓛)^{⊗ n}`. -/
theorem hilbertFunction_pullback_of_isIso (g : X ⟶ X) [IsIso g] (hg : g ≫ p = p) :
    hilbertFunction k p ((Scheme.Modules.pullback g).obj L) = hilbertFunction k p L := by
  funext n
  have := SheafOfModules.isCoherent_of_isInvertible k p
    (tensorPower X.presheaf X.ringCatSheaf.2 L n)
  have := SheafOfModules.isCoherent_of_isInvertible k p
    (tensorPower X.presheaf X.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj L) n)
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (tensorPower X.presheaf X.ringCatSheaf.2 L n) :=
    tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L n
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (tensorPower X.presheaf X.ringCatSheaf.2 L n)) :=
    isInvertible_pullbackObj g (tensorPower X.presheaf X.ringCatSheaf.2 L n)
  have := SheafOfModules.isCoherent_of_isInvertible k p
    ((Scheme.Modules.pullback g).obj (tensorPower X.presheaf X.ringCatSheaf.2 L n))
  exact (eulerCharacteristic_eq_of_iso k p (Scheme.Modules.pullbackTensorPowerIso g L n)).symm.trans
    (eulerCharacteristic_pullback_of_isIso k p g hg _)

end AlgebraicGeometry

end
