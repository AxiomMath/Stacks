module

public import StacksFrontier.RingTheory.Valuation.AbhyankarRationalRank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Abhyankar's inequality

Let `R` be a Noetherian local domain and `V` a valuation ring dominating `R` whose fraction
field is algebraic over that of `R` (for instance a valuation ring of `Frac R` containing `R`
with `𝔪_V ∩ R = 𝔪_R`). If `x₁, …, x_r ∈ V` have `ℤ`-linearly independent values and
`y₁, …, y_t ∈ V` have residues algebraically independent over `κ(R)`, then `r + t ≤ dim R`.

## Main results

* `Stacks.Abhyankar.add_le_ringKrullDim`: `r + t ≤ dim R`, for explicit families.

## References

* S. Abhyankar, *On the valuations centered in a local domain*, Amer. J. Math. 78 (1956),
  Theorem 1.
* O. Zariski, P. Samuel, *Commutative Algebra*, vol. II, Appendix 2.
* N. Bourbaki, *Algèbre commutative*, chapitre VI, §10, no. 3.
* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
-/

@[expose] public section

namespace Stacks.Abhyankar

open IsLocalRing

universe u v

section Residue

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]

omit [IsDomain R] in
/-- The preimage of the maximal ideal of `κ(R)` under the residue map is the maximal ideal of
`R`. -/
theorem comap_residue_maximalIdeal :
    Ideal.comap (residue R) (maximalIdeal (ResidueField R)) = maximalIdeal R := by
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]

/-- The map `R_{𝔪_R} → κ(R)` induced by the residue map is a local homomorphism. -/
instance isLocalHom_liftAtPrime_residue :
    IsLocalHom (liftAtPrime (residue R) (maximalIdeal R) comap_residue_maximalIdeal) :=
  isLocalHom_liftAtPrime _ _ _

/-- The comparison `κ(𝔪_R) → κ(R)` between the residue field of `R` at its maximal ideal and
the residue field of `R`. -/
noncomputable def residueFieldMaximalIdealHom :
    (maximalIdeal R).ResidueField →+* ResidueField R :=
  IsLocalRing.ResidueField.lift (liftAtPrime (residue R) (maximalIdeal R)
    comap_residue_maximalIdeal)

omit [IsDomain R] in
/-- The comparison `κ(𝔪_R) → κ(R)` sends the image of `r : R` to the residue of `r`. -/
theorem residueFieldMaximalIdealHom_algebraMap (r : R) :
    residueFieldMaximalIdealHom (algebraMap R (maximalIdeal R).ResidueField r) = residue R r := by
  rw [residueFieldMaximalIdealHom, IsScalarTower.algebraMap_apply R
    (Localization.AtPrime (maximalIdeal R)) (maximalIdeal R).ResidueField]
  exact (IsLocalRing.ResidueField.lift_residue_apply _ _).trans
    (liftAtPrime_algebraMap _ _ _ r)

end Residue

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
  [IsLocalHom (algebraMap R V)]

/-- The residue field extension `κ(𝔪_R) → κ(𝔮)` for the centre `𝔮` of `V` on `R[w]`. -/
noncomputable instance instAlgebraResidueFieldAdjoinPrime {k : ℕ} (w : Fin k → V) :
    Algebra (maximalIdeal R).ResidueField (adjoinPrime (algebraMap R V) w).ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver _ _

/-- The residues in `κ(𝔮)` of adjoined elements whose residues in `κ(V)` are algebraically
independent over `κ(R)` are algebraically independent over `κ(𝔪_R)`, so
`trdeg_{κ(𝔪_R)} κ(𝔮) ≥ t`. -/
theorem le_toNat_trdeg_residueField (_hinj : Function.Injective (algebraMap R V)) {k : ℕ}
    (w : Fin k → V) {t : ℕ} (j : Fin t → Fin k)
    (hy : AlgebraicIndependent (ResidueField R) (residue V ∘ w ∘ j)) :
    t ≤ Cardinal.toNat (Algebra.trdeg (maximalIdeal R).ResidueField
      (adjoinPrime (algebraMap R V) w).ResidueField) := by
  classical
  set φ := algebraMap R V
  set Q := adjoinPrime φ w
  let g : Q.ResidueField →+* ResidueField V := IsLocalRing.ResidueField.map (adjoinLocHom φ w)
  let yb : Fin t → Q.ResidueField := fun l =>
    algebraMap (Adjoin φ w) Q.ResidueField (Ideal.Quotient.mk _ (MvPolynomial.X (j l)))
  have hgy : g ∘ yb = residue V ∘ w ∘ j := by
    funext l
    simp only [Function.comp_apply, g, yb]
    rw [IsScalarTower.algebraMap_apply (Adjoin φ w) (AdjoinLoc φ w) Q.ResidueField]
    exact (IsLocalRing.ResidueField.map_residue _ _).trans
      (congrArg _ (adjoinLocHom_adjoinGen φ w (j l)))
  have hcomp : (algebraMap (ResidueField R) (ResidueField V)).comp residueFieldMaximalIdealHom =
      g.comp (algebraMap (maximalIdeal R).ResidueField Q.ResidueField) := by
    apply (RingHom.cancel_right IsLocalRing.residue_surjective).mp
    apply IsLocalization.ringHom_ext (maximalIdeal R).primeCompl
    ext r
    simp only [RingHom.comp_apply]
    have e1 : residue (Localization.AtPrime (maximalIdeal R))
        (algebraMap R (Localization.AtPrime (maximalIdeal R)) r) =
        algebraMap R (maximalIdeal R).ResidueField r :=
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime (maximalIdeal R))
        (maximalIdeal R).ResidueField r).symm
    have e2 : algebraMap (maximalIdeal R).ResidueField Q.ResidueField
        (algebraMap R (maximalIdeal R).ResidueField r) =
        algebraMap (Adjoin φ w) Q.ResidueField (algebraMap R (Adjoin φ w) r) :=
      Ideal.ResidueField.map_algebraMap (maximalIdeal R) Q (algebraMap R (Adjoin φ w))
        Ideal.LiesOver.over r
    rw [e1, residueFieldMaximalIdealHom_algebraMap, e2,
      IsScalarTower.algebraMap_apply (Adjoin φ w) (AdjoinLoc φ w) Q.ResidueField]
    change _ = IsLocalRing.ResidueField.map (adjoinLocHom φ w) (residue _ _)
    rw [IsLocalRing.ResidueField.map_residue, ← IsScalarTower.algebraMap_apply,
      adjoinLocHom_algebraMap]
    rfl
  have hind : AlgebraicIndependent (maximalIdeal R).ResidueField yb :=
    AlgebraicIndependent.of_ringHom_of_comp_eq (f := residueFieldMaximalIdealHom) (g := g)
      (by rw [hgy]; exact hy) residueFieldMaximalIdealHom.injective hcomp
  have hfin : Algebra.trdeg (maximalIdeal R).ResidueField Q.ResidueField < Cardinal.aleph0 :=
    resfield_trdeg_lt_aleph0_general (maximalIdeal R) Q
  have hle : (Cardinal.mk (Set.range yb)) ≤ Algebra.trdeg (maximalIdeal R).ResidueField
      Q.ResidueField := hind.to_subtype_range.cardinalMk_le_trdeg
  rw [Cardinal.mk_fintype, Set.card_range_of_injective hind.injective, Fintype.card_fin] at hle
  obtain ⟨N, hN⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hN] at hle
  rw [hN, Cardinal.toNat_natCast]
  exact_mod_cast hle

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain V] [ValuationRing V]
  [IsLocalHom (algebraMap R V)] in
/-- The ring `Adjoin (algebraMap R V) w` generated over `R` by the `w i` is algebraic over `R`
when `V` is. -/
theorem isAlgebraic_adjoin_of_isAlgebraic (_hinj : Function.Injective (algebraMap R V))
    [Algebra.IsAlgebraic R V] {k : ℕ} (w : Fin k → V) :
    Algebra.IsAlgebraic R (Adjoin (algebraMap R V) w) := by
  let f : Adjoin (algebraMap R V) w →ₐ[R] V :=
    { adjoinLift (algebraMap R V) w with
      commutes' := adjoinLift_algebraMap (algebraMap R V) w }
  exact ⟨fun s => (isAlgebraic_algHom_iff f (adjoinLift_injective (algebraMap R V) w)).mp
    (Algebra.IsAlgebraic.isAlgebraic (f s))⟩

/-- **Abhyankar's inequality.** Let `R` be a Noetherian local domain and `V` a valuation ring
dominating `R` (`R → V` injective and local), algebraic over `R`. If `x₁, …, x_r ∈ V` have
`ℤ`-linearly independent values and `y₁, …, y_t ∈ V` have residues in `κ(V)` algebraically
independent over `κ(R)`, then `r + t ≤ dim R`. -/
theorem add_le_ringKrullDim (hinj : Function.Injective (algebraMap R V))
    [Algebra.IsAlgebraic R V] {r t : ℕ} (x : Fin r → V) (hx : MonomialIndependent x)
    (y : Fin t → V) (hy : AlgebraicIndependent (ResidueField R) (residue V ∘ y)) :
    ((r + t : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by
  set φ := algebraMap R V
  set w : Fin (r + t) → V := Fin.append x y
  have h02 := height_maximalIdeal_adjoinLoc_add_trdeg_le φ w hinj
  have := isAlgebraic_adjoin_of_isAlgebraic hinj w
  have h0 : Algebra.trdeg R (Adjoin φ w) = 0 := trdeg_eq_zero_iff.mpr inferInstance
  rw [h0, map_zero, Nat.cast_zero, add_zero] at h02
  have hxC : MonomialIndependent (adjoinLocHom φ w ∘ fun i => adjoinGen φ w (Fin.castAdd t i)) := by
    have : (adjoinLocHom φ w ∘ fun i => adjoinGen φ w (Fin.castAdd t i)) = x := by
      funext i
      simp only [Function.comp_apply, adjoinLocHom_adjoinGen, w, Fin.append_left]
    rwa [this]
  have hr := card_le_height_maximalIdeal (adjoinLocHom φ w) (adjoinLocHom_injective φ w) _ hxC
  rw [Fintype.card_fin] at hr
  have ht := le_toNat_trdeg_residueField hinj w (Fin.natAdd r) (by
    have : residue V ∘ w ∘ Fin.natAdd r = residue V ∘ y := by
      funext j
      simp only [Function.comp_apply, w, Fin.append_right]
    rwa [this])
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have : ((r + t : ℕ) : ℕ∞) ≤ (maximalIdeal R).height := by
    refine le_trans ?_ h02
    push_cast
    exact add_le_add hr (by exact_mod_cast ht)
  exact_mod_cast this

end Main

end Stacks.Abhyankar
