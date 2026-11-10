module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# Sections of a pulled-back module given by coordinates

Let `p : Y ⟶ X` and `q : Y ⟶ T` be morphisms of schemes, `L` an `𝒪_X`-module, `w₁, …, wₙ`
global sections of `L` and `c₁, …, cₙ` global functions on `T`. The *coordinate section*
`Σⱼ q^*(cⱼ) · p^*(wⱼ)` is a global section of `p^* L`. When the square formed by `p`, `q` and two
morphisms `X ⟶ S ⟵ T` is cartesian, `S` and `T` are affine, `T ⟶ S` is flat and the `wⱼ` form a
basis of `Γ(X, L)` over `Γ(S, 𝒪_S)`, every global section of `p^* L` is a coordinate section for
exactly one family `c`: this is degree-zero flat base change ([Stacks, Tag 02KH]).

## Main definitions

* `Stacks.LinearSystemScheme.coordSection`: the coordinate section `Σⱼ q^*(cⱼ) · p^*(wⱼ)`.

## Main results

* `Stacks.LinearSystemScheme.coordSection_pullback`: pulling a coordinate section back along
  `h : Y' ⟶ Y` gives the coordinate section for `h ≫ p`, `h ≫ q`.
* `Stacks.LinearSystemScheme.coordSection_bijective`: for a cartesian square over affine bases
  with a flat bottom edge, coordinates against a basis are unique and exist.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange
open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul pullbackGlobalSections_comp
  pullbackGlobalSections_unit)

universe u

namespace Stacks.LinearSystemScheme

variable {X Y Y' T S : Scheme.{u}}

/-- **The coordinate section** `Σⱼ q^*(cⱼ) · p^*(wⱼ)` of `p^* L`. -/
def coordSection (p : Y ⟶ X) (q : Y ⟶ T) (L : X.Modules) {n : ℕ} (w : Fin n → Γ(L, ⊤))
    (c : Fin n → Γ(T, ⊤)) : Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
  ∑ j, q.appTop (c j) • pullbackGlobalSections p L (w j)

/-- The coordinate section is additive in the family of coordinates `c`. -/
theorem coordSection_add (p : Y ⟶ X) (q : Y ⟶ T) (L : X.Modules) {n : ℕ}
    (w : Fin n → Γ(L, ⊤)) (c c' : Fin n → Γ(T, ⊤)) :
    coordSection p q L w (c + c') = coordSection p q L w c + coordSection p q L w c' := by
  simp only [coordSection, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

/-- Scaling the coordinates `c` by `r ∈ Γ(T, 𝒪_T)` scales the coordinate section by `q^*(r)`. -/
theorem coordSection_smul (p : Y ⟶ X) (q : Y ⟶ T) (L : X.Modules) {n : ℕ}
    (w : Fin n → Γ(L, ⊤)) (r : Γ(T, ⊤)) (c : Fin n → Γ(T, ⊤)) :
    coordSection p q L w (r • c) = q.appTop r • coordSection p q L w c := by
  simp only [coordSection, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

/-- **Coordinate sections pull back to coordinate sections.** Pulling `Σⱼ q^*(cⱼ) · p^*(wⱼ)` back
along `h : Y' ⟶ Y`, and identifying `h^* p^* L` with `(h ≫ p)^* L`, gives
`Σⱼ (h ≫ q)^*(cⱼ) · (h ≫ p)^*(wⱼ)`. -/
theorem coordSection_pullback (h : Y' ⟶ Y) (p : Y ⟶ X) (q : Y ⟶ T) (L : X.Modules) {n : ℕ}
    (w : Fin n → Γ(L, ⊤)) (c : Fin n → Γ(T, ⊤)) :
    ((Scheme.Modules.pullbackComp h p).hom.app L).app ⊤
        (pullbackGlobalSections h ((Scheme.Modules.pullback p).obj L)
          (coordSection p q L w c)) =
      coordSection (h ≫ p) (h ≫ q) L w c := by
  simp only [coordSection, map_sum, pullbackGlobalSections_smul, Scheme.Modules.Hom.app_smul,
    pullbackGlobalSections_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The `Γ(T, ⊤)`-module structure on the sections of `p^* L` over `Y` given by `q` acts through
`q.appTop`. -/
theorem baseModule_smul_eq (q : Y ⟶ T) (M : Y.Modules) (r : Γ(T, ⊤)) (s : Γ(M, ⊤)) :
    (letI := baseModule q M ⊤; r • s) = q.appTop r • s := by
  change (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom r • s = _
  rw [show q.appLE ⊤ ⊤ (le_preimage_top q ⊤) = q.app ⊤ from Scheme.Hom.appLE_preimage_self q ⊤]

/-- **Degree-zero flat base change in coordinates.** For a cartesian square
`Y = X ×_S T` with `S`, `T` affine, `T ⟶ S` flat and `X` quasi-compact and quasi-separated, a
quasi-coherent `L` and a basis `w` of `Γ(X, L)` over `Γ(S, 𝒪_S)`, every global section of `p^* L`
is `Σⱼ q^*(cⱼ) · p^*(wⱼ)` for exactly one family `c` of functions on `T`. -/
theorem coordSection_bijective {g : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback p q iX g) [IsAffine S] [IsAffine T] [Flat g] [CompactSpace X]
    [QuasiSeparatedSpace X] (L : X.Modules) [L.IsQuasicoherent] {n : ℕ}
    (w : letI := baseModule iX L ⊤; Module.Basis (Fin n) Γ(S, ⊤) Γ(L, ⊤)) :
    Function.Bijective (coordSection p q L w) := by
  let := baseAlgebra g
  let := baseModule iX L ⊤
  let := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj L) ⊤
  let := baseModule q ((Scheme.Modules.pullback p).obj L) ⊤
  let := baseTower H ((Scheme.Modules.pullback p).obj L) ⊤
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange H L
  let b := Algebra.TensorProduct.basis Γ(T, ⊤) w
  have key : (coordSection p q L w : (Fin n → Γ(T, ⊤)) → _) =
      (e : _ → _) ∘ (b.equivFun.symm : (Fin n → Γ(T, ⊤)) → _) := by
    funext c
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul,
      b, Algebra.TensorProduct.basis_apply, he, one_smul, coordSection]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [baseModule_smul_eq, pullbackSectionsHom_top, pullbackGlobalSections_unit]
    rfl
  rw [key]
  exact e.bijective.comp b.equivFun.symm.bijective

end Stacks.LinearSystemScheme

end
