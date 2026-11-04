module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRankIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportComponentLength

/-!
# The dévissage behind Stacks 0EDE

Let `X` be a Noetherian algebraic space, let `T ⊆ |X|` be a closed set of points of dimension
`d`, and let `C₁, …, C_s` be the irreducible components of `T` of dimension `d`, with
geometric points `x̄ᵢ` over their generic points and with `Zᵢ` the reduced closed subspace on
`Cᵢ`.  Let `χ` be a function of an `𝒪_X`-module with values in the functions `ℤ^r → ℚ` which is
additive along short exact sequences of coherent modules and which, on every coherent module
`H`, is the function of a rational polynomial of total degree at most `dim Supp(H)`.

Then for every coherent `F` supported in `T` the function

`χ(F) - ∑ᵢ mᵢ(F) · χ(i_*𝒪_{Zᵢ})`, where `mᵢ(F) = length_{𝒪_{X, x̄ᵢ}}(F_{x̄ᵢ})`,

is the function of a polynomial of total degree `< d`.  This is the argument of the proof of
Stacks 0EDE, with `χ(H) = χ(X, H ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`; its two hypotheses are then
Stacks 0DN2 together with the exactness of twisting, and Stacks 0DN4.

## Main results

* `AlgebraicGeometry.Space.exists_polynomial_sub_finsum_toNat_geometricLength_mul`: the
  statement above.

## Implementation notes

The source runs the dévissage of Stacks 08AN on the scheme-theoretic support of `F`.  Here it is
run on `X` itself, through the dévissage of Stacks 07US fed by the filtration of Stacks 07UR, for
the property "*if `H` is supported in `T`, then the function above is of degree `< d` for `H`*".
That property is closed under extensions, which is all Stacks 07US needs, and it avoids the
comparison of the components of `T` read in the scheme-theoretic support and in `X`.  The pieces
of the dévissage are direct images `i_*I` of quasi-coherent sheaves of ideals on reduced closed
subspaces `Z` with `|Z|` irreducible; for `I ≠ 0` the support of `i_*I` is all of `|Z|`, so
`|Z| ⊆ T`, and either `|Z|` is one of the `Cᵢ`, where the sequence
`0 → i_*I → i_*𝒪_Z → i_*(𝒪_Z/I) → 0` reduces the claim to a module of smaller support, or
`|Z|` has dimension `< d` and misses every generic point of the `Cᵢ`.

The total degree bound uses the convention of
`AlgebraicGeometry.Space.HasTwistedEulerPolynomialOfDegreeLE`: the zero polynomial satisfies
every bound, in particular `< d` for every `d`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

/-! ### Polynomials of total degree below a bound -/

namespace MvPolynomial

variable {σ : Type*}

/-- Being zero or of total degree `< d` is stable under addition. -/
private theorem eq_zero_or_totalDegree_lt_add {P Q : MvPolynomial σ ℚ} {d : WithBot ℕ∞}
    (hP : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < d)
    (hQ : Q = 0 ∨ (Q.totalDegree : WithBot ℕ∞) < d) :
    P + Q = 0 ∨ ((P + Q).totalDegree : WithBot ℕ∞) < d := by
  rcases hP with rfl | hP
  · simpa using hQ
  rcases hQ with rfl | hQ
  · simpa using Or.inr hP
  refine Or.inr ?_
  rcases le_total P.totalDegree Q.totalDegree with h | h
  · exact lt_of_le_of_lt (by exact_mod_cast (totalDegree_add P Q).trans (max_eq_right h).le) hQ
  · exact lt_of_le_of_lt (by exact_mod_cast (totalDegree_add P Q).trans (max_eq_left h).le) hP

/-- Being zero or of total degree `< d` is stable under negation. -/
private theorem eq_zero_or_totalDegree_lt_neg {P : MvPolynomial σ ℚ} {d : WithBot ℕ∞}
    (hP : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < d) :
    -P = 0 ∨ ((-P).totalDegree : WithBot ℕ∞) < d := by
  simpa [totalDegree_neg] using hP

/-- From a bound `≤ s` to a bound `< d`, when `s ≤ d` and `s < d` whenever `d` is finite. -/
private theorem eq_zero_or_totalDegree_lt_of_le {P : MvPolynomial σ ℚ} {s d : WithBot ℕ∞}
    (hP : P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ s) (hsd : s ≤ d)
    (hfin : ∀ n : ℕ, d = n → s < n) :
    P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < d := by
  rcases hP with rfl | hP
  · exact Or.inl rfl
  refine Or.inr ?_
  induction d using WithBot.recBotCoe with
  | bot => exact absurd (hP.trans hsd) (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _)
    | coe n => exact hP.trans_lt (hfin n rfl)

end MvPolynomial

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The direct image `i_*𝒪_Z` of the structure sheaf of the reduced closed subspace `Z` on an
irreducible component of a closed set `T` of points of `X`. -/
abbrev componentStructureSheaf {T : Set (points B S hS X.1)} (hT : IsClosed T)
    (C : irreducibleComponents T) : Modules.{u, u} B S hS X.1 X.2 :=
  structureSheafPushforward B S hS (closedSubfunctorι B S hS
    (isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 _
      (closedSetComponentPoints B S hS T hT C).isClosed))

/-- **The dévissage behind Stacks 0EDE.**  Let `X` be a Noetherian algebraic space, `T ⊆ |X|` a
closed set of points and `x̄_C` a geometric point over the generic point of each irreducible
component `C` of `T`.  Let `χ` assign to every `𝒪_X`-module a function `ℤ^r → ℚ` which is
additive along short exact sequences of coherent modules and which, on a coherent `H`, is the
function of a rational polynomial of total degree at most `dim Supp(H)` (or zero).  Then for a
coherent `F` supported in `T` the function

`n ↦ χ(F)(n) - ∑_C length_{𝒪_{X, x̄_C}}(F_{x̄_C}) · χ(i_{C,*}𝒪_{Z_C})(n)`,

the sum running over the components `C` of `T` of dimension `dim T` and `Z_C` being the reduced
closed subspace on `C`, is the function of a rational polynomial which is zero or of total
degree `< dim T`.

The property "*if `H` is supported in `T`, the conclusion holds for `H`*" is closed under
extensions, holds for zero modules and for every direct image `i_*I` of a quasi-coherent sheaf
of ideals on a reduced closed subspace with irreducible space of points, so by Stacks 07US and
Stacks 07UR it holds for every coherent module.  See the module documentation for the case
analysis on `i_*I`. -/
theorem exists_polynomial_sub_finsum_toNat_geometricLength_mul
    (hN : IsNoetherian B S hS B.contains_terminal X.1)
    {T : Set (points B S hS X.1)} (hT : IsClosed T)
    (x : irreducibleComponents T → GeometricPoint B S hS X.1)
    (hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)))
    {r : ℕ} (χ : Modules.{u, u} B S hS X.1 X.2 → (Fin r → ℤ) → ℚ)
    (hadd : ∀ σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2), σ.ShortExact →
      IsCoherent B S hS X.1 X.2 σ.X₁ → IsCoherent B S hS X.1 X.2 σ.X₂ →
      IsCoherent B S hS X.1 X.2 σ.X₃ → ∀ n, χ σ.X₂ n = χ σ.X₁ n + χ σ.X₃ n)
    (hpoly : ∀ H : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 H →
      ∃ P : MvPolynomial (Fin r) ℚ, (∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) P = χ H n) ∧
        (P = 0 ∨
          (P.totalDegree : WithBot ℕ∞) ≤ topologicalKrullDim (moduleSupportSet B S hS X H)))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hFT : moduleSupportSet B S hS X F ⊆ T) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) < topologicalKrullDim T) ∧
      ∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) P = χ F n -
        ∑ᶠ C ∈ {C : irreducibleComponents T |
            topologicalKrullDim (Subtype.val '' (C : Set T)) = topologicalKrullDim T},
          ((geometricLength B S hS X (x C) F).toNat : ℚ) *
            χ (componentStructureSheaf B S hS X hT C) n := by
  classical
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  have hLN := hN.2.2
  have hdec : IsDecentSpace B S hS X.1 :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X.1 X.2 hN.2.1
  have : NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hN.1 hLN
  have : Finite (irreducibleComponents T) :=
    (NoetherianSpace.finite_irreducibleComponents (α := T)).to_subtype
  set d := topologicalKrullDim T with hd
  set top := {C : irreducibleComponents T |
    topologicalKrullDim (Subtype.val '' (C : Set T)) = d} with htop
  have hfin : top.Finite := Set.toFinite _
  set E : Modules.{u, u} B S hS X.1 X.2 → (Fin r → ℤ) → ℚ := fun H n =>
    χ H n - ∑ᶠ C ∈ top, ((geometricLength B S hS X (x C) H).toNat : ℚ) *
      χ (componentStructureSheaf B S hS X hT C) n with hE
  -- additivity of `E`
  have hEadd : ∀ σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2), σ.ShortExact →
      IsCoherent B S hS X.1 X.2 σ.X₁ → IsCoherent B S hS X.1 X.2 σ.X₂ →
      IsCoherent B S hS X.1 X.2 σ.X₃ → moduleSupportSet B S hS X σ.X₂ ⊆ T →
      ∀ n, E σ.X₂ n = E σ.X₁ n + E σ.X₃ n := by
    intro σ hσ h₁ h₂ h₃ hT₂ n
    have hm : ∀ C : irreducibleComponents T,
        ((geometricLength B S hS X (x C) σ.X₂).toNat : ℚ) =
          ((geometricLength B S hS X (x C) σ.X₁).toNat : ℚ) +
            ((geometricLength B S hS X (x C) σ.X₃).toNat : ℚ) := by
      intro C
      rw [toNat_geometricLength_add_of_shortExact B S hS X hLN hdec C.2 (x C) (hx C) σ hσ hT₂]
      push_cast
      rfl
    simp only [hE, hadd σ hσ h₁ h₂ h₃ n, hm, add_mul]
    rw [finsum_mem_add_distrib hfin]
    ring
  -- a component whose generic point is off the support of `H` contributes nothing to `E H`
  have hterm : ∀ (H : Modules.{u, u} B S hS X.1 X.2) [H.IsQuasicoherentOnSite]
      (C : irreducibleComponents T), (x C).image ∉ moduleSupportSet B S hS X H → ∀ n,
      ((geometricLength B S hS X (x C) H).toNat : ℚ) *
        χ (componentStructureSheaf B S hS X hT C) n = 0 := by
    intro H _ C hC n
    rw [geometricLength_eq_zero_of_image_notMem B S hS X H (x C) hC]
    simp
  -- `E` is `χ` on a module missing every generic point of a top-dimensional component
  have hEχ : ∀ H : Modules.{u, u} B S hS X.1 X.2, H.IsQuasicoherentOnSite →
      (∀ C ∈ top, (x C).image ∉ moduleSupportSet B S hS X H) → ∀ n, E H n = χ H n := by
    intro H hq hgen n
    simp only [hE, finsum_mem_eq_zero_of_forall_eq_zero fun C hC => hterm H C (hgen C hC) n,
      sub_zero]
  -- the case of a module of small support
  have hsmall : ∀ H : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 H →
      moduleSupportSet B S hS X H ⊆ T →
      (∀ C ∈ top, (x C).image ∉ moduleSupportSet B S hS X H) →
      (∀ k : ℕ, d = k → topologicalKrullDim (moduleSupportSet B S hS X H) < k) →
      ∃ Q : MvPolynomial (Fin r) ℚ, (Q = 0 ∨ (Q.totalDegree : WithBot ℕ∞) < d) ∧
        ∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) Q = E H n := by
    intro H hH hHT hgen hdim
    obtain ⟨Q, hQ, hdeg⟩ := hpoly H hH
    refine ⟨Q, MvPolynomial.eq_zero_or_totalDegree_lt_of_le hdeg
      (topologicalKrullDim_le_of_subset hHT) hdim, fun n => ?_⟩
    rw [hQ, hEχ H hH.toIsQuasicoherentOnSite hgen]
  -- the property run through the dévissage
  let P : Modules.{u, u} B S hS X.1 X.2 → Prop := fun H => IsCoherent B S hS X.1 X.2 H →
    moduleSupportSet B S hS X H ⊆ T → ∃ Q : MvPolynomial (Fin r) ℚ,
      (Q = 0 ∨ (Q.totalDegree : WithBot ℕ∞) < d) ∧
        ∀ n, MvPolynomial.eval (fun j => (n j : ℚ)) Q = E H n
  have hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M := by
    intro M hM hMc hMT
    let σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
      ShortComplex.mk (0 : M ⟶ M) (0 : M ⟶ M) (by simp)
    have hσ : σ.ShortExact :=
      { exact := ShortComplex.exact_of_isZero_X₂ _ hM
        mono_f := ⟨fun g h _ => hM.eq_of_tgt g h⟩
        epi_g := ⟨fun g h _ => hM.eq_of_src g h⟩ }
    refine ⟨0, Or.inl rfl, fun n => ?_⟩
    have h := hEadd σ hσ hMc hMc hMc hMT n
    rw [map_zero]
    change E M n = E M n + E M n at h
    linarith
  have hext : ClosedUnderCoherentExtensions B S hS X P := by
    intro σ hσ h₁ h₂ h₃ hP₁ hP₃ _ hT₂
    have hT₁ := (moduleSupportSet_subset_of_mono B S hS X σ.f hσ.mono_f).trans hT₂
    have hT₃ := (moduleSupportSet_subset_of_epi B S hS X σ.g hσ.epi_g).trans hT₂
    obtain ⟨Q₁, hQ₁, hE₁⟩ := hP₁ h₁ hT₁
    obtain ⟨Q₃, hQ₃, hE₃⟩ := hP₃ h₃ hT₃
    exact ⟨Q₁ + Q₃, MvPolynomial.eq_zero_or_totalDegree_lt_add hQ₁ hQ₃, fun n => by
      rw [map_add, hE₁, hE₃, hEadd σ hσ h₁ h₂ h₃ hT₂ n]⟩
  have hideal : ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          I.1.toSheafOfModules) := by
    intro Z hZ hint I hH hHT
    by_cases hI : I.1 = ⊥
    · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ I hI) hH hHT
    have hsupp := moduleSupportSet_idealPushforward_eq_image B S hS X hLN hZ hint I hI
    rw [Set.image_univ] at hsupp
    have hWT : Set.range (pointsMap B S hS Z.toFunctor Z.ι) ⊆ T := hsupp ▸ hHT
    have hWcl : IsClosed (Set.range (pointsMap B S hS Z.toFunctor Z.ι)) :=
      isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 Z.ι hZ.2
    have hWirr : IsIrreducible (Set.range (pointsMap B S hS Z.toFunctor Z.ι)) := by
      have := hint.2
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (continuous_pointsMap B S hS Z.ι).continuousOn
    by_cases htop' : ∃ C ∈ top,
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) = Subtype.val '' (C : Set T)
    · obtain ⟨C₀, hC₀, hWC₀⟩ := htop'
      have hZeq : Z = reducedClosedSubspace B S hS X.1 X.2 _
          (closedSetComponentPoints B S hS T hT C₀).isClosed :=
        eq_reducedClosedSubspace B S hS X.1 X.2 _ _ Z hZ hWC₀ hint.1
      subst hZeq
      let Zs := closedSubfunctorSpace B S hS hZ
      let i := closedSubfunctorι B S hS hZ
      let _ : Abelian (Modules.{u, u} B S hS Zs.1 Zs.2) := spaceModulesAbelian B S hS Zs
      have hLNZ := hasEtaleLocalProperty_isLocallyNoetherian_closedSubfunctor B S hS X hLN hZ
      -- the sequence `0 → I → 𝒪_Z → 𝒪_Z/I → 0` and its direct image
      let σZ : ShortComplex (Modules.{u, u} B S hS Zs.1 Zs.2) :=
        ShortComplex.mk I.1.ι (cokernel.π (C := Modules.{u, u} B S hS Zs.1 Zs.2) I.1.ι)
          (cokernel.condition (C := Modules.{u, u} B S hS Zs.1 Zs.2) _)
      have hσZ : σZ.ShortExact :=
        ShortComplex.ShortExact.mk'
          (ShortComplex.exact_of_g_is_cokernel _
            (cokernelIsCokernel (C := Modules.{u, u} B S hS Zs.1 Zs.2) _))
          (SheafOfModules.Submodule.mono_ι_via_forget I.1)
          (coequalizer.π_epi (C := Modules.{u, u} B S hS Zs.1 Zs.2))
      have := modulePushforward_additive B S hS i
      let σ := σZ.map (modulePushforward B S hS i)
      have hσ : σ.ShortExact :=
        shortExact_map_modulePushforward_of_isClosedImmersion B S hS i hZ.2 σZ hσZ
      have h₂ : IsCoherent B S hS X.1 X.2 σ.X₂ :=
        isCoherent_structureSheafPushforward B S hS hLN i hZ.2
      have h₃ : IsCoherent B S hS X.1 X.2 σ.X₃ :=
        isCoherent_of_iso B S hS X.2 (modulePushforwardCokernelIso B S hS i hZ.2 I.1.ι)
          (isCoherent_cokernel B S hS X.1 X.2 hH h₂ _)
      have hOZ : IsCoherent B S hS Zs.1 Zs.2 σZ.X₂ :=
        @isCoherent_structureSheaf B S hS Zs.1 Zs.2 ⟨hLNZ⟩
      have hT₂W : moduleSupportSet B S hS X σ.X₂ ⊆
          Set.range (pointsMap B S hS _ (reducedClosedSubspace B S hS X.1 X.2 _
            (closedSetComponentPoints B S hS T hT C₀).isClosed).ι) := by
        refine (supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS i hZ.2 _
          (isClosed_supportOfSheaf_of_isCoherentOnSite B S hS Zs _)).le.trans ?_
        exact Set.image_subset_range _ _
      have hT₂ : moduleSupportSet B S hS X σ.X₂ ⊆ T := hT₂W.trans hWT
      have hT₃W := (moduleSupportSet_subset_of_epi B S hS X σ.g hσ.epi_g).trans hT₂W
      have hT₃ : moduleSupportSet B S hS X σ.X₃ ⊆ T := hT₃W.trans hWT
      -- the generic points of the other top-dimensional components lie off `|Z|`
      have hother : ∀ C ∈ top, C ≠ C₀ → (x C).image ∉
          Set.range (pointsMap B S hS _ (reducedClosedSubspace B S hS X.1 X.2 _
            (closedSetComponentPoints B S hS T hT C₀).isClosed).ι) := by
        intro C _ hne hmem
        refine hne (Subtype.ext ?_)
        have h := eq_image_of_isGenericPoint_mem_of_mem_irreducibleComponents C.2 (hx C) hWirr
          hWcl hWT hmem
        exact (Set.image_injective.2 Subtype.val_injective) (h.symm.trans hWC₀)
      -- the integral closed subspace on `C₀` and the length one of `i_*𝒪_Z` there
      let Zi := closedSetComponent B S hS X.2 hdec T hT C₀
      have hξ₀ : (x C₀).image = Zi.ambientGenericPoint B S hS :=
        eq_pointsMap_genericPoint_of_isGenericPoint B S hS X.2 Zi _
          (by rw [subspacePointSet_closedSetComponent]; exact hx C₀)
      have hlen₂ : geometricLength B S hS X (x C₀) σ.X₂ = 1 :=
        geometricLength_modulePushforward_unit_eq_one B S hS X Zi (x C₀) hξ₀
      have hξ₀W : (x C₀).image ∈ Set.range (pointsMap B S hS _ (reducedClosedSubspace B S hS
          X.1 X.2 _ (closedSetComponentPoints B S hS T hT C₀).isClosed).ι) := by
        rw [hWC₀]; exact (hx C₀).mem
      have hξ₀₁ : (x C₀).image ∈ moduleSupportSet B S hS X σ.X₁ := hsupp ▸ hξ₀W
      -- so the length of `i_*(𝒪_Z/I)` at the generic point of `C₀` is zero
      have hξ₀₃ : (x C₀).image ∉ moduleSupportSet B S hS X σ.X₃ := by
        have : IsCoherent B S hS X.1 X.2 σ.X₁ := hH
        have := h₂; have := h₃
        intro hmem
        have hpos₁ := (geometricLength_pos_iff_image_mem B S hS X σ.X₁ (x C₀)).2 hξ₀₁
        have hpos₃ := (geometricLength_pos_iff_image_mem B S hS X σ.X₃ (x C₀)).2 hmem
        have hadd₂ := geometricLength_add_of_shortExact B S hS X (x C₀) σ hσ
        rw [hlen₂] at hadd₂
        have : (2 : ℕ∞) ≤ 1 := by
          rw [hadd₂]
          exact (add_le_add (Order.one_le_iff_pos.2 hpos₁) (Order.one_le_iff_pos.2 hpos₃)).trans_eq'
            (by norm_num)
        exact absurd this (by norm_num)
      -- `E` vanishes on `i_*𝒪_Z`
      have hE₂ : ∀ n, E σ.X₂ n = 0 := by
        intro n
        have hsplit : top = insert C₀ (top \ {C₀}) := by
          rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hC₀]
        simp only [hE]
        rw [hsplit, finsum_mem_insert (s := top \ {C₀}) _
          (fun h => h.2 (Set.mem_singleton C₀)) hfin.sdiff,
          finsum_mem_eq_zero_of_forall_eq_zero fun C hC => hterm _ C
            (fun hmem => hother C hC.1 hC.2 (hT₂W hmem)) n, hlen₂]
        simp only [ENat.toNat_one, Nat.cast_one, one_mul, add_zero]
        exact sub_self _
      -- and `i_*(𝒪_Z/I)` has small support
      obtain ⟨Q₃, hQ₃, hE₃⟩ := hsmall σ.X₃ h₃ hT₃ (fun C hC hmem => by
          by_cases hCC : C = C₀
          · exact hξ₀₃ (hCC ▸ hmem)
          · exact hother C hC hCC (hT₃W hmem))
        fun k hk => by
          have hC₀k : topologicalKrullDim (Subtype.val '' (C₀ : Set T)) = k :=
            (hC₀ : _ = d).trans hk
          exact topologicalKrullDim_lt_of_isGenericPoint_notMem C₀.2 (hx C₀) hC₀k
            (isClosed_moduleSupportSet B S hS X _ h₃) (hWC₀ ▸ hT₃W) hξ₀₃
      refine ⟨-Q₃, MvPolynomial.eq_zero_or_totalDegree_lt_neg hQ₃, fun n => ?_⟩
      have h := hEadd σ hσ hH h₂ h₃ hT₂ n
      rw [hE₂ n] at h
      rw [map_neg, hE₃ n]
      change -E σ.X₃ n = E σ.X₁ n
      linarith
    · push Not at htop'
      have hgen : ∀ C ∈ top, (x C).image ∉ moduleSupportSet B S hS X
          ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
            I.1.toSheafOfModules) := by
        intro C hC hmem
        rw [hsupp] at hmem
        exact htop' C hC (eq_image_of_isGenericPoint_mem_of_mem_irreducibleComponents C.2
          (hx C) hWirr hWcl hWT hmem)
      refine hsmall _ hH hHT hgen fun k hk => ?_
      rw [hsupp]
      exact topologicalKrullDim_lt_of_forall_ne (hd ▸ hk) hWirr hWcl hWT
        fun C hC hCdim => htop' ⟨C, hC⟩ (by simpa [htop, hk] using hCdim)
  exact property_of_forall_hasIdealDevissage B S hS X
    (fun M hM => hasIdealDevissage_of_isCoherent B S hS B.contains_terminal X hN M hM)
    P hzero hext hideal F hF hF hFT

end AlgebraicGeometry.Space
