module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedFibreTwoChartVanishing

/-!
# Vanishing above the size of an affine cover, by Mayer–Vietoris

Let `X` be a scheme with affine diagonal, `i : Z ⟶ X` a morphism and `F` an abelian sheaf on the
small étale site of `Z` whose cohomology over `i⁻¹(V)` vanishes in positive degrees for every
affine open `V` of `X`. If `W ⊆ X` is a union of `n + 1` affine opens, then the cohomology of `F`
over `i⁻¹(W)` vanishes in degrees `q > n`.

This is the induction step of the proof of Stacks 0A51. Writing `W = W' ∪ V` with `W'` a union of
`n` affine opens and `V` affine, the intersection `W' ∩ V` is again a union of `n` affine opens
because the diagonal of `X` is affine, and the Mayer–Vietoris sequence
`H^{q-1}(i⁻¹(W' ∩ V)) → H^q(i⁻¹W) → H^q(i⁻¹W') ⊕ H^q(i⁻¹V)` gives the vanishing.

Cohomology over an open is `CategoryTheory.Sheaf.H'` on the one-universe model
`Stacks.EtaleCohomology.MayerVietoris.Site` of the small étale site, where the Mayer–Vietoris
sequence lives.

## Main results

* `subsingleton_cohomologyPresheaf_preimage_iSup_of_affine`: the vanishing over the preimage of a
  union of `n + 1` affine opens.
* `subsingleton_H_of_affine_cover`: the global vanishing when the `n + 1` affine opens cover `X`.

## References

* [Stacks Project, Tag 0A51](https://stacks.math.columbia.edu/tag/0A51)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.MayerVietoris

variable {X Z : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))] (i : Z ⟶ X)
  (F : Sheaf (topology Z) AddCommGrpCat.{u + 1})

/-- A union of `n + 2` opens splits off its last member. -/
theorem iSup_fin_succ_eq_sup {n : ℕ} (U : Fin (n + 2) → X.Opens) :
    ⨆ k, U k = (⨆ k : Fin (n + 1), U k.castSucc) ⊔ U (Fin.last _) := by
  refine le_antisymm (iSup_le fun k => ?_) (sup_le (iSup_le fun k => le_iSup U _) (le_iSup U _))
  induction k using Fin.lastCases with
  | last => exact le_sup_right
  | cast k => exact le_sup_of_le_left (le_iSup (fun k : Fin (n + 1) => U k.castSucc) k)

include i in
/-- **Vanishing over the preimage of a union of `n + 1` affine opens**, in degrees `q > n`, from
the vanishing over the preimages of the affine opens in positive degrees. -/
theorem subsingleton_cohomologyPresheaf_preimage_iSup_of_affine
    (hF : ∀ V : X.Opens, IsAffineOpen V → ∀ q, 0 < q →
      Subsingleton (F.H' q ((opensToSite Z).obj (i ⁻¹ᵁ V)))) :
    ∀ (n : ℕ) (U : Fin (n + 1) → X.Opens), (∀ k, IsAffineOpen (U k)) → ∀ q, n < q →
      Subsingleton (F.H' q ((opensToSite Z).obj (i ⁻¹ᵁ ⨆ k, U k))) := by
  intro n
  induction n with
  | zero =>
    intro U hU q hq
    have : ⨆ k, U k = U 0 := le_antisymm (iSup_le fun k => by rw [Fin.fin_one_eq_zero k])
      (le_iSup U 0)
    rw [this]
    exact hF _ (hU 0) q hq
  | succ n ih =>
    intro U hU q hq
    obtain ⟨q₀, rfl⟩ : ∃ q₀, q = q₀ + 1 := ⟨q - 1, by omega⟩
    rw [iSup_fin_succ_eq_sup U, Scheme.Hom.preimage_sup]
    refine subsingleton_cohomologySup_of_subsingleton F _ _ q₀ (q₀ + 1) rfl ?_ ?_ ?_
    · rw [← Scheme.Hom.preimage_inf, iSup_inf_eq]
      exact ih _ (fun k => (hU k.castSucc).inf (hU (Fin.last _))) q₀ (by omega)
    · exact ih _ (fun k => hU k.castSucc) _ (by omega)
    · exact hF _ (hU _) _ (by omega)

include i in
/-- **Vanishing above the size of an affine cover.** If `X` has affine diagonal and is covered
by `n + 1` affine opens, and the cohomology of `F` over the preimage of every affine open of `X`
vanishes in positive degrees, then `H^q(Z, F) = 0` for every `q > n`. -/
theorem subsingleton_H_of_affine_cover
    (hF : ∀ V : X.Opens, IsAffineOpen V → ∀ q, 0 < q →
      Subsingleton (F.H' q ((opensToSite Z).obj (i ⁻¹ᵁ V))))
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ k, IsAffineOpen (U k)) (hcov : ⨆ k, U k = ⊤)
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} F q) := by
  have h := subsingleton_cohomologyPresheaf_preimage_iSup_of_affine i F hF n U hU q hq
  rw [hcov, Scheme.Hom.preimage_top] at h
  exact AddCommGrpCat.subsingleton_of_isZero
    (Limits.IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton
      (G := F.H' q ((opensToSite Z).obj ⊤)))
      (cohomologyTopIsoH Z F q).symm)

end Stacks.EtaleCohomology.MayerVietoris
