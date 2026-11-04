module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategoryTransitivity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TransitiveFiberConnected

/-!
# The Artin–Schreier character of `a t` on the affine line over a field

Let `k` be a finite field with `q` elements, `Ω` a field over `k` and `a ∈ Ω`. The Artin–Schreier
cover `T^q - T = a t` of `𝔸¹_Ω = Spec Ω[t]`:

* for `a ≠ 0` is again an affine line: `Ω[t][T]/(T^q - T - a t) ≅ Ω[T]`, `t ↦ a⁻¹(T^q - T)`
  (`Stacks.ArtinSchreier.scaledLineRingEquiv`); so it is connected and its character
  `π₁(𝔸¹_Ω, ȳ) → k` is surjective, `π₁` acting transitively on the fibres of a connected cover
  (`Stacks.ArtinSchreier.surjective_torsorCover_character_scaledLine`);
* for `a = 0` has the section `T ↦ 0`, so its character is trivial
  (`Stacks.ArtinSchreier.torsorCover_character_scaledLine_zero`).

These are the two kinds of geometric fibres of the first projection of Laumon's plane
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), where the kernel `t h(x)` restricts to
`t h(x̄)`.

## Main definitions

* `Stacks.ArtinSchreier.scaledLineRingEquiv`.

## Main results

* `Stacks.ArtinSchreier.connectedSpace_cover_scaledLine`.
* `Stacks.ArtinSchreier.surjective_torsorCover_character_scaledLine`.
* `Stacks.ArtinSchreier.torsorCover_character_scaledLine_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {Ω : Type u} [Field Ω] [Algebra k Ω]

/-- `t ↦ a⁻¹(T^q - T)`, `T ↦ T`, from the Artin–Schreier algebra of `a t` over `Ω[t]` to
`Ω[T]`. -/
def scaledLineRingHom (a : Ω) (ha : a ≠ 0) :
    Ring k (C a * Polynomial.X : Polynomial Ω) →+* Polynomial Ω :=
  AdjoinRoot.lift (eval₂RingHom C (C a⁻¹ * (Polynomial.X ^ Fintype.card k - Polynomial.X)))
    Polynomial.X (by
    rw [poly, eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X, eval₂_C, coe_eval₂RingHom, eval₂_mul,
      eval₂_C, eval₂_X, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    ring)

/-- **`Ω[t][T]/(T^q - T - a t) ≅ Ω[T]` for `a ≠ 0`**: the Artin–Schreier cover of `a t` is an
affine line, `t = a⁻¹(T^q - T)`. -/
def scaledLineRingEquiv (a : Ω) (ha : a ≠ 0) :
    Ring k (C a * Polynomial.X : Polynomial Ω) ≃+* Polynomial Ω :=
  RingEquiv.ofRingHom (scaledLineRingHom k a ha)
    (eval₂RingHom ((AdjoinRoot.of _).comp C) (AdjoinRoot.root _))
    (Polynomial.ringHom_ext (fun b => by simp [scaledLineRingHom, AdjoinRoot.lift_of])
      (by simp [scaledLineRingHom, AdjoinRoot.lift_root]))
    (AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun b => by
        simp [scaledLineRingHom, AdjoinRoot.lift_of]) (by
        have hr' : AdjoinRoot.root (poly k (C a * Polynomial.X : Polynomial Ω)) ^ Fintype.card k -
            AdjoinRoot.root (poly k (C a * Polynomial.X : Polynomial Ω)) =
            AdjoinRoot.of _ (C a) * AdjoinRoot.of _ Polynomial.X := by
          rw [root_pow_card, add_sub_cancel_left, AdjoinRoot.algebraMap_eq, map_mul]
        simp only [RingHom.coe_comp, Function.comp_apply, scaledLineRingHom, AdjoinRoot.lift_of,
          coe_eval₂RingHom, eval₂_X, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X_pow, RingHom.id_apply]
        rw [hr', ← mul_assoc, ← map_mul, ← map_mul, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]))
      (by simp [scaledLineRingHom, AdjoinRoot.lift_root]))

/-- **The Artin–Schreier cover of `a t`, `a ≠ 0`, is connected**: it is an affine line. -/
theorem connectedSpace_cover_scaledLine (a : Ω) (ha : a ≠ 0) :
    ConnectedSpace (cover k (Polynomial Ω) (C a * Polynomial.X)).left := by
  have : IsDomain (Ring k (C a * Polynomial.X : Polynomial Ω)) :=
    Function.Injective.isDomain (scaledLineRingEquiv k a ha).toRingHom
      (scaledLineRingEquiv k a ha).injective
  show ConnectedSpace (Spec (.of (Ring k (C a * Polynomial.X : Polynomial Ω))))
  infer_instance

/-- **The Artin–Schreier character of `a t`, `a ≠ 0`, is surjective**: the cover is connected, so
`π₁(𝔸¹_Ω, ȳ)` acts transitively on its fibre at `ȳ`, which is a `k`-torsor. -/
theorem surjective_torsorCover_character_scaledLine (a : Ω) (ha : a ≠ 0)
    (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    (p : (finiteEtaleFiberFunctor y).obj (cover k (Polynomial Ω) (C a * Polynomial.X))) :
    Function.Surjective ((torsorCover k (Polynomial Ω) (C a * Polynomial.X)).character y p) := by
  intro c
  have : PreGaloisCategory.IsConnected (cover k (Polynomial Ω) (C a * Polynomial.X)) :=
    (isConnected_iff_connectedSpace_left _).2 (connectedSpace_cover_scaledLine k a ha)
  let : IsGaloisCategory (setValuedFiberFunctor
      (finiteEtaleFiberFintypeFunctor (Spec (.of (Polynomial Ω))) y)) :=
    Stacks.FundamentalGroup.isGaloisCategory_finiteEtaleFiberFunctor y
  obtain ⟨g, hg⟩ := (Stacks.FundamentalGroup.isPretransitive_fiber_of_isConnected
    (finiteEtaleFiberFintypeFunctor (Spec (.of (Polynomial Ω))) y)
    (cover k (Polynomial Ω) (C a * Polynomial.X))).exists_smul_eq p
    ((finiteEtaleFiberFunctor y).map ((torsorCover k (Polynomial Ω) (C a * Polynomial.X)).τ
      (Multiplicative.toAdd c)) p)
  exact ⟨autMulEquivEtaleFundamentalGroup _ y g, Multiplicative.toAdd.injective <|
    (torsorCover k (Polynomial Ω) (C a * Polynomial.X)).character_eq_of_smul y p _ p hg⟩

/-- **The Artin–Schreier character of `0 · t` is trivial**: the cover has the section `T ↦ 0`. -/
theorem torsorCover_character_scaledLine_zero (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    (p : (finiteEtaleFiberFunctor y).obj (cover k (Polynomial Ω) (C 0 * Polynomial.X))) :
    (torsorCover k (Polynomial Ω) (C 0 * Polynomial.X)).character y p = 1 :=
  (torsorCover k (Polynomial Ω) (C 0 * Polynomial.X)).character_eq_one_of_hom_terminalCover
    (coverSection k (Polynomial Ω) (C 0 * Polynomial.X) 0 (by
      rw [zero_pow Fintype.card_ne_zero, sub_zero, C_0, zero_mul])) y p

end Stacks.ArtinSchreier

end
