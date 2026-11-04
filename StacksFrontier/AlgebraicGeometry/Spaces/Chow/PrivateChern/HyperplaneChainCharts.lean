module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingAffineSituation
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.HyperplaneChain
public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin

/-!
# Closed subspaces of a represented algebraic space cut out by a chain of ideal sheaves

Let `T` be a scheme of the big fppf site and `h_T` the algebraic space it represents. Closed
subspaces of `h_T` are the ideal sheaves of `T`, inclusion-reversingly
(`AlgebraicGeometry.Space.schemeSpaceIdealOrderIso`). This file shows that the intersection of two
closed subspaces is cut out by the sum of their ideal sheaves, and that if a closed subspace
`C ⊆ h_T` is the closed subscheme `R ⊆ T` and a second closed subspace `Z` pulls back to an
effective Cartier divisor of `R`, then `Z ∩ C` is an effective Cartier divisor of the algebraic
space `C` (Stacks 083C, condition (2), on the chart `h_R ≅ C`).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.schemeSpaceIdeal_inf`: the ideal sheaf of `Z ∩ Y` is the
  sum of the ideal sheaves of `Z` and `Y`.
* `AlgebraicGeometry.Space.PrivateChern.isEffectiveCartierDivisor_preimage_of_schemeSpaceIdeal`:
  effective Cartier divisors of a closed subspace read on the representing closed subscheme.
* `AlgebraicGeometry.Space.PrivateChern.hyperplaneChainSubspaces_spec`: the chain of closed
  subspaces of `h_V` cut out by a hyperplane chain consists of effective Cartier cuts and ends at
  a closed subspace cut out by a closed immersion.

## References

* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : BigFppfOver B S hS)

/-- The intersection of two closed subspaces of the algebraic space represented by `V`. -/
abbrev representedInf (Z Y : ClosedSubspaces B S hS (yoneda.obj V)) :
    ClosedSubspaces B S hS (yoneda.obj V) :=
  ⟨Z.1 ⊓ Y.1, inf_isClosedSubspace B S hS _ (isAlgebraicSpace_yoneda B S hS V) Z Y⟩

/-- The intersection of two closed subspaces of `h_V` is cut out by the sum of their ideal
sheaves. -/
theorem schemeSpaceIdeal_inf (Z Y : ClosedSubspaces B S hS (yoneda.obj V)) :
    schemeSpaceIdeal B S hS V (representedInf B S hS V Z Y) =
      schemeSpaceIdeal B S hS V Z ⊔ schemeSpaceIdeal B S hS V Y := by
  refine le_antisymm ?_ (sup_le (schemeSpaceIdeal_antitone B S hS V _ Z inf_le_left)
    (schemeSpaceIdeal_antitone B S hS V _ Y inf_le_right))
  obtain ⟨W, hW⟩ := exists_schemeSpaceIdeal_eq B S hS V
    (schemeSpaceIdeal B S hS V Z ⊔ schemeSpaceIdeal B S hS V Y)
  have hWZ : W.1 ≤ Z.1 := le_of_schemeSpaceIdeal_le B S hS V W Z (hW ▸ le_sup_left)
  have hWY : W.1 ≤ Y.1 := le_of_schemeSpaceIdeal_le B S hS V W Y (hW ▸ le_sup_right)
  rw [← hW]
  exact schemeSpaceIdeal_antitone B S hS V W _ (le_inf hWZ hWY)

/-- Let `C ⊆ h_V` be a closed subspace whose ideal sheaf is the kernel of a closed
immersion `ι : R ⟶ V` of schemes, and `Z ⊆ h_V` a closed subspace whose ideal sheaf pulls back to
an effective Cartier divisor of `R`. Then `Z ∩ C`, as a closed subspace of `C`, is an effective
Cartier divisor of `C`. -/
theorem isEffectiveCartierDivisor_preimage_of_schemeSpaceIdeal
    (C Z : ClosedSubspaces B S hS (yoneda.obj V)) {R : Scheme.{u}}
    (ι : R ⟶ (BigFppfOver.toScheme B S hS).obj V) [_root_.AlgebraicGeometry.IsClosedImmersion ι]
    (hC : schemeSpaceIdeal B S hS V C = ι.ker)
    (hZ : Stacks.Divisors.IsEffectiveCartierDivisor ((schemeSpaceIdeal B S hS V Z).comap ι)) :
    IsEffectiveCartierDivisor B S hS ⟨C.1.toFunctor, C.2.1⟩
      ⟨Z.1.preimage C.1.ι, isClosedSubspace_preimage B S hS C.1.ι Z.1
        (isAlgebraicSpace_yoneda B S hS V) C.2.1 Z.2⟩ := by
  obtain ⟨R', j', hj', hrange, hker⟩ := exists_closedImmersion_range_eq B S hS V C
  have := hj'
  obtain ⟨C₀, hC₀⟩ := C
  dsimp only at hrange hC hker ⊢
  subst hrange
  have hkerj : ((BigFppfOver.toScheme B S hS).map j').ker = ι.ker := hker.trans hC
  let e : (BigFppfOver.toScheme B S hS).obj R' ⟶ R :=
    _root_.AlgebraicGeometry.IsClosedImmersion.lift ι ((BigFppfOver.toScheme B S hS).map j')
      hkerj.ge
  have : IsIso e := _root_.AlgebraicGeometry.IsClosedImmersion.isIso_lift ι _ hkerj.symm
  have he : e ≫ ι = (BigFppfOver.toScheme B S hS).map j' :=
    _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have := isIso_toRange_yoneda_map B S hS j' hj'
  let g := Subfunctor.toRange (yoneda.map j')
  have hg : g ≫ (Subfunctor.range (yoneda.map j')).ι = yoneda.map j' := Subfunctor.toRange_ι _
  refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
    ⟨R', g, isEtale_of_isIso B S hS g, isSurjective_of_isIso B S hS g, ?_⟩
  let Zp : ClosedSubspaces B S hS (yoneda.obj R') :=
    ⟨Z.1.preimage (yoneda.map j'), isClosedSubspace_preimage B S hS (yoneda.map j') Z.1
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS R') Z.2⟩
  have hZp : schemeSpaceIdeal B S hS R' Zp =
      (schemeSpaceIdeal B S hS V Z).comap ((BigFppfOver.toScheme B S hS).map j') :=
    schemeSpaceIdeal_eq_comap_of_preimage_eq B S hS V j' Z Zp rfl
  obtain ⟨R'', j'', hj'', hr'', hk''⟩ := exists_closedImmersion_range_eq B S hS R' Zp
  have := hj''
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      ((BigFppfOver.toScheme B S hS).map j'').ker := by
    rw [hk'', hZp, ← he, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat e _ hZ
  refine ⟨_, R'', j'', Stacks.Divisors.closedImmersionKerIso _, hcart,
    Stacks.Divisors.closedImmersion_eq_kerIso_comp _, ?_⟩
  rw [hr'']
  show (Z.1.preimage (Subfunctor.range (yoneda.map j')).ι).preimage g =
    Z.1.preimage (yoneda.map j')
  rw [← Subfunctor.preimage_comp, hg]

/-- The condition that `Z ∩ C` is an effective Cartier divisor of the algebraic space `C`. -/
abbrev IsCartierCut (C Z : ClosedSubspaces B S hS (yoneda.obj V)) : Prop :=
  IsEffectiveCartierDivisor B S hS ⟨C.1.toFunctor, C.2.1⟩
    ⟨Z.1.preimage C.1.ι, isClosedSubspace_preimage B S hS C.1.ι Z.1
      (isAlgebraicSpace_yoneda B S hS V) C.2.1 Z.2⟩

/-- The chain of closed subspaces cut out by `Z_n, Z_{n-1}, …, Z_1` from `C`: at `j ≥ n` it is
`C`, and at `j < n` it is the intersection of the subspace at `j + 1` with `Z_{j+1}`. -/
def hyperplaneChainSubspaces (Zs : ℕ → ClosedSubspaces B S hS (yoneda.obj V)) :
    ℕ → ClosedSubspaces B S hS (yoneda.obj V) → ℕ → ClosedSubspaces B S hS (yoneda.obj V)
  | 0, C, _ => C
  | n + 1, C, j => if n + 1 ≤ j then C else
      hyperplaneChainSubspaces Zs n (representedInf B S hS V C (Zs (n + 1))) j

variable {B S hS V} (Zs : ℕ → ClosedSubspaces B S hS (yoneda.obj V))

/-- The top member of the chain is `C`. -/
theorem hyperplaneChainSubspaces_self :
    ∀ (n : ℕ) (C : ClosedSubspaces B S hS (yoneda.obj V)),
      hyperplaneChainSubspaces B S hS V Zs n C n = C
  | 0, _ => rfl
  | _ + 1, _ => if_pos le_rfl

/-- Below the top, the chain of length `n + 1` from `C` is the chain of length `n` from
`C ∩ Z_{n+1}`. -/
theorem hyperplaneChainSubspaces_succ_of_le (n : ℕ) (C : ClosedSubspaces B S hS (yoneda.obj V))
    {j : ℕ} (hj : j ≤ n) :
    hyperplaneChainSubspaces B S hS V Zs (n + 1) C j =
      hyperplaneChainSubspaces B S hS V Zs n (representedInf B S hS V C (Zs (n + 1))) j :=
  if_neg (by omega)

/-- Each member of the chain below the top is the intersection of the next one with a cut. -/
theorem hyperplaneChainSubspaces_eq_inf :
    ∀ (n : ℕ) (C : ClosedSubspaces B S hS (yoneda.obj V)) (j : ℕ), j < n →
      (hyperplaneChainSubspaces B S hS V Zs n C j).1 =
        (hyperplaneChainSubspaces B S hS V Zs n C (j + 1)).1 ⊓ (Zs (j + 1)).1
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, C, j, hj => by
    rw [hyperplaneChainSubspaces_succ_of_le Zs n C (j := j) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hyperplaneChainSubspaces_succ_of_le Zs n C (j := j + 1) (by omega)]
      exact hyperplaneChainSubspaces_eq_inf n _ j hj
    · rw [hyperplaneChainSubspaces_self, hyperplaneChainSubspaces_self]

/-- Let `ι : R ⟶ V` be a closed immersion with `R ⟶ A` a hyperplane chain of length `n` lying over
`q : V ⟶ W` (along a morphism `i : A ⟶ W`), let `C ⊆ h_V` be the closed subspace cut out by `ι`,
and suppose the ideal sheaves of the chain are the inverse images along `ι` of the ideal sheaves of
closed subspaces `Z_j ⊆ h_V`. Then in the chain `C_n = C`, `C_j = C_{j+1} ∩ Z_{j+1}`, every cut
`Z_{j+1} ∩ C_{j+1}` is an effective Cartier divisor of `C_{j+1}`, and `C_0` is cut out by a closed
immersion `s : A ⟶ V` over `W`. -/
theorem hyperplaneChainSubspaces_spec {W : Scheme.{u}}
    (q : (BigFppfOver.toScheme B S hS).obj V ⟶ W)
    {n : ℕ} {R A : Scheme.{u}} {πR : R ⟶ A} {JR : ℕ → R.IdealSheafData}
    (h : Stacks.Chow.IsHyperplaneChain n πR JR) :
    ∀ (ι : R ⟶ (BigFppfOver.toScheme B S hS).obj V)
      (_ : _root_.AlgebraicGeometry.IsClosedImmersion ι) (i : A ⟶ W), ι ≫ q = πR ≫ i →
      ∀ (C : ClosedSubspaces B S hS (yoneda.obj V)), schemeSpaceIdeal B S hS V C = ι.ker →
      (∀ j ≤ n, JR j = (schemeSpaceIdeal B S hS V (Zs j)).comap ι) →
      (∀ j < n, IsCartierCut B S hS V (hyperplaneChainSubspaces B S hS V Zs n C (j + 1))
        (Zs (j + 1))) ∧
      ∃ s : A ⟶ (BigFppfOver.toScheme B S hS).obj V,
        _root_.AlgebraicGeometry.IsClosedImmersion s ∧ s ≫ q = i ∧
          schemeSpaceIdeal B S hS V (hyperplaneChainSubspaces B S hS V Zs n C 0) = s.ker := by
  induction h with
  | zero πR JR hπ =>
    intro ι hι i hq C hC _
    have := hπ
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), inv πR ≫ ι, inferInstance, ?_, ?_⟩
    · rw [Category.assoc, hq, IsIso.inv_hom_id_assoc]
    · show schemeSpaceIdeal B S hS V C = _
      rw [hC, Scheme.Hom.ker_comp_of_isIso]
  | succ n πR JR hD _ ih =>
    intro ι hι i hq C hC hJ
    have := hι
    set D := JR (n + 1) with hDdef
    have hJD : D = (schemeSpaceIdeal B S hS V (Zs (n + 1))).comap ι := hJ (n + 1) le_rfl
    have hC' : schemeSpaceIdeal B S hS V (representedInf B S hS V C (Zs (n + 1))) =
        (D.subschemeι ≫ ι).ker := by
      rw [schemeSpaceIdeal_inf, hC, ← Stacks.Chow.map_comap_of_isClosedImmersion, ← hJD,
        ← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    obtain ⟨hcart, s, hs₁, hs₂, hs₃⟩ := ih (D.subschemeι ≫ ι) inferInstance i
      (by rw [Category.assoc, hq, Category.assoc]) _ hC'
      (fun j hj => by
        show (JR j).comap D.subschemeι = _
        rw [hJ j (by omega), Scheme.IdealSheafData.comap_comp])
    refine ⟨fun j hj => ?_, s, hs₁, hs₂, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hyperplaneChainSubspaces_succ_of_le Zs n C (j := j + 1) (by omega)]
        exact hcart j hj
      · rw [hyperplaneChainSubspaces_self]
        exact isEffectiveCartierDivisor_preimage_of_schemeSpaceIdeal B S hS V C (Zs (j + 1)) ι hC
          (hJD ▸ hD.1)
    · rwa [hyperplaneChainSubspaces_succ_of_le Zs n C (Nat.zero_le n)]

end AlgebraicGeometry.Space.PrivateChern

end
