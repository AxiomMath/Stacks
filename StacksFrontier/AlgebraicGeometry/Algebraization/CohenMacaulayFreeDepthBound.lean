module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkFreeOfFiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesLocallyFreeOutside
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Dualizing.IsDualizingComplexModels
public import StacksFrontier.RingTheory.Serre.LocalizationDepthCodimension

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u w

namespace Stacks.Algebraization

/-- A bound `n < a + b + c` between a depth `a`, a dimension `b` and a distance `c`, in
`WithBot ℕ∞`, is the same bound after the passage to `EInt`. -/
theorem natCast_lt_enatToEInt_add_krullDimToEInt_add_enatToEInt {a c : ℕ∞} {b : WithBot ℕ∞}
    (n : ℕ) (h : ((n : ℕ) : WithBot ℕ∞) < (a : WithBot ℕ∞) + b + (c : WithBot ℕ∞)) :
    ((n : ℤ) : EInt) < enatToEInt a + krullDimToEInt b + enatToEInt c := by
  have h1 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + b + (c : WithBot ℕ∞) := by
    generalize (a : WithBot ℕ∞) + b + (c : WithBot ℕ∞) = v at h ⊢
    cases v using WithBot.recBotCoe with
    | bot => exact absurd h not_lt_bot
    | coe w =>
      have hn : ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := rfl
      have hn1 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [hn, WithBot.coe_lt_coe] at h
      rw [hn1, WithBot.coe_le_coe]
      exact_mod_cast Order.add_one_le_of_lt h
  have hm := krullDimToEInt_mono h1
  rw [krullDimToEInt_add, krullDimToEInt_add, krullDimToEInt_coe, krullDimToEInt_coe] at hm
  refine lt_of_lt_of_le ?_ hm
  show ((n : ℤ) : EInt) < (((n + 1 : ℕ) : ℤ) : EInt)
  exact WithBotTop.coe_lt_coe.mpr (by omega)

/-- A Krull-dimension value that is neither `⊥` nor `⊤` is a natural number. -/
private theorem exists_natCast_eq_of_ne_bot_of_ne_top {x : WithBot ℕ∞} (hb : x ≠ ⊥)
    (ht : x ≠ ⊤) : ∃ n : ℕ, x = n := by
  cases x using WithBot.recBotCoe with
  | bot => exact absurd rfl hb
  | coe w =>
    cases w using ENat.recTopCoe with
    | top => exact absurd rfl ht
    | coe n => exact ⟨n, rfl⟩

/-- A sum `a + b + ⊤` with `b ≠ ⊥` exceeds every natural number. -/
private theorem natCast_lt_add_add_top {b : WithBot ℕ∞} (hb : b ≠ ⊥) (a : ℕ∞) (n : ℕ) :
    ((n : ℕ) : WithBot ℕ∞) < (a : WithBot ℕ∞) + b + ((⊤ : ℕ∞) : WithBot ℕ∞) := by
  cases b using WithBot.recBotCoe with
  | bot => exact absurd rfl hb
  | coe b =>
    rw [← WithBot.coe_add, ← WithBot.coe_add, add_top]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

/-- The arithmetic closing the proof of Stacks 0EJP: from `dim(A) ≤ a + b + dim(A/𝔮)`,
`δ^Y_Z(y) ≥ dim(A/𝔮) - m` with `m ≤ dim(Z)` and `dim(Z) + d + 2 < dim(A)`, the sum
`a + b + δ^Y_Z(y)` exceeds `d + 2`. -/
private theorem natCast_lt_add_add_of_le_of_toNat_le {NA Na Nq Nw d : ℕ} {a c : ℕ∞}
    {b : WithBot ℕ∞} (hb : b ≠ ⊥)
    (h1 : ((NA : ℕ) : WithBot ℕ∞) ≤ ((a : WithBot ℕ∞) + b) + ((Nq : ℕ) : WithBot ℕ∞))
    (hdist : ((((Nq : ℤ) - Nw).toNat : ℕ) : ℕ∞) ≤ c) (hw : Nw ≤ Na) (hdim : Na + (d + 2) < NA) :
    (((d + 2 : ℕ) : ℕ) : WithBot ℕ∞) < (a : WithBot ℕ∞) + b + (c : WithBot ℕ∞) := by
  cases c using ENat.recTopCoe with
  | top => exact natCast_lt_add_add_top hb a _
  | coe c =>
  have htop : ∀ x : ℕ, ((x : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) := fun x =>
    WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top x)
  cases b using WithBot.recBotCoe with
  | bot => exact absurd rfl hb
  | coe b =>
  cases a using ENat.recTopCoe with
  | top =>
    rw [← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add]
    exact htop _
  | coe a =>
  cases b using ENat.recTopCoe with
  | top =>
    rw [← WithBot.coe_add, add_top, ← WithBot.coe_add, top_add]
    exact htop _
  | coe b =>
  have h1' : NA ≤ a + b + Nq := by exact_mod_cast h1
  have hdist' : ((Nq : ℤ) - Nw).toNat ≤ c := by exact_mod_cast hdist
  rw [Int.toNat_le] at hdist'
  have : d + 2 < a + b + c := by omega
  have h2 : ((d + 2 : ℕ) : ℕ∞) < (a : ℕ∞) + b + c := by
    have h3 := (Nat.cast_lt (α := ℕ∞)).mpr this
    push_cast at h3 ⊢
    exact h3
  rw [← WithBot.coe_add, ← WithBot.coe_add]
  show (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) < _
  exact WithBot.coe_lt_coe.mpr h2

/-- **The depth bound of Stacks 0EJP at a point of `U ∩ Y`.** In Situation 0EHC assume that `A` is
a local ring with a dualizing complex, that all irreducible components of `X = Spec(A)` have the
same dimension, that `X \ Y` is Cohen–Macaulay, that `dim(X) - dim(Z) > d + 2`, and that at
`y ∈ U ∩ Y` the module `ℱ_y^∧` is finite locally free outside `V(I𝒪_{X,y}^∧)`. Then for every
prime `𝔭 ⊂ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`,

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > d + 2`,

which is hypothesis (3)(b) of Stacks 0EJN.

As in the source: the contraction `𝔓 ⊂ A` of `𝔭` lies off `V(I)` and below the prime `𝔮` under
`y`, and `depth(A_𝔓) + dim(A/𝔓) ≤ depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + dim(A/𝔮)`
(`exists_depth_add_dim_le_completedStalkDepth_of_free`, by freeness and Stacks 0EHW). As `A_𝔓` is
Cohen–Macaulay its depth is its dimension `height(𝔓)`, and `height(𝔓) + dim(A/𝔓) = dim(A)`
because `A` is catenary (Stacks 0A80) and equidimensional. Finally `δ(y) = dim(A/𝔮)` is a
dimension function on `Y` (`A/I` is catenary and local), so Stacks 0EIY gives
`δ^Y_Z(y) ≥ dim(A/𝔮) - dim(Z)`, and the bound follows from `dim(X) - dim(Z) > d + 2`.

The dualizing complex is taken in an arbitrary model of the derived category; it is carried to
`HasDerivedCategory.standard`, where the results it is passed to (Stacks 0A80, 0DWD, 0EHW) are
stated, by `Dualizing.exists_isDualizingComplex_iff_of_models`. -/
public theorem depthAddDimAddDistance_gt_of_isCohenMacaulay_of_free
    (S : AlgebraizationSituation.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    [IsLocalRing S.A] (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hequi : Equidimensional (PrimeSpectrum S.A))
    (hCM : ∀ q : PrimeSpectrum S.A, ¬ S.I ≤ q.asIdeal →
      IsCohenMacaulayLocalRing (Localization.AtPrime q.asIdeal))
    (d : ℕ)
    (hdim : ringKrullDim (S.A ⧸ S.a) + ((d + 2 : ℕ) : WithBot ℕ∞) < ringKrullDim S.A)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hfree : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y))) :
    depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt) := by
  classical
  have hdual : let := HasDerivedCategory.standard (ModuleCat.{u} S.A)
      ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K :=
    (Dualizing.exists_isDualizingComplex_iff_of_models ‹_›
      (HasDerivedCategory.standard (ModuleCat.{u} S.A))).mp hdual
  let := HasDerivedCategory.standard (ModuleCat.{u} S.A)
  obtain ⟨⟨P, _⟩, hPnot, -, hle⟩ :=
    exists_depth_add_dim_le_completedStalkDepth_of_free S hdual F y z hyz p hp hfree
  change ¬ S.I ≤ P at hPnot
  obtain ⟨K, hK⟩ := hdual
  have hcatA : Ring.IsUniversallyCatenary S.A :=
    Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
  -- `depth(A_𝔓) + dim(A/𝔓) = dim(A)`.
  have hCMP := (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp (hCM ⟨P, ‹_›⟩ hPnot)
  change (Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
    (Localization.AtPrime P) : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P) at hCMP
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)] at hCMP
  have hsplit :=
    Serre.LocalizationDepth.ringKrullDim_eq_height_add_ringKrullDim_quotient_of_equidimensional
      S.A (hcatA S.A) hequi P
  have h1 : ringKrullDim S.A ≤
      ((completedStalkDepth (idealOnOpen S) F y p : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
        ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) := by
    rw [hsplit, ← hCMP]
    exact hle
  -- The prime `𝔮` under `y` contains `I`, so `A/I` is a catenary local ring.
  set q := underlyingPrime S y with hqdef
  have hqI : S.I ≤ q.asIdeal := by
    have hx₀ : q = S.Yι.base z := congrArg (fun t : S.X => (t : PrimeSpectrum S.A)) hyz
    rw [show q.asIdeal = (S.Yι.base z : PrimeSpectrum S.A).asIdeal from
      congrArg PrimeSpectrum.asIdeal hx₀]
    intro x hx
    show Ideal.Quotient.mk S.I x ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Submodule.zero_mem _
  have hIne : S.I ≠ ⊤ := fun h => q.isPrime.ne_top (top_le_iff.mp (h ▸ hqI))
  have _ : Nontrivial (S.A ⧸ S.I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have _ : IsLocalRing (S.A ⧸ S.I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk S.I) Ideal.Quotient.mk_surjective
  have hcatUQ : Ring.IsUniversallyCatenary (S.A ⧸ S.I) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hcatA
  have hcatB : Ring.IsCatenary (S.A ⧸ S.I) := hcatUQ (S.A ⧸ S.I)
  have hdimfun := (catenary_iff_isDimensionFunction (S.A ⧸ S.I)).mp
    (_root_.isCatenaryRingSaturated_of_isCatenary hcatB)
  -- `δ(x) = dim(A/𝔮ₓ)` is a dimension function on `Y`.
  let δ : DimensionFunction S.Y :=
    ⟨fun x => deltaDim (x : PrimeSpectrum (S.A ⧸ S.I)),
      fun x x' hxx' hne => hdimfun.1 x x' hxx' hne,
      fun x x' h => hdimfun.2 x x' h⟩
  -- Finite values.
  have hcoheight : ∀ x : PrimeSpectrum (S.A ⧸ S.I),
      ∃ N : ℕ, (N : ℕ∞) = Order.coheight x ∧ δ x = (N : ℤ) := fun x => by
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (coheight_lt_top_of_noetherianLocal x).ne
    exact ⟨N, hN, by change ((Order.coheight x).toNat : ℤ) = _; rw [← hN]; rfl⟩
  let zP : PrimeSpectrum (S.A ⧸ S.I) := z
  obtain ⟨NA, hNA⟩ := exists_natCast_eq_of_ne_bot_of_ne_top
    (ringKrullDim_ne_bot (R := S.A)) ringKrullDim_lt_top.ne
  have hNq : (Order.coheight zP : WithBot ℕ∞) =
      ringKrullDim (S.A ⧸ q.asIdeal) :=
    coheight_eq_ringKrullDim_quotient_underlyingPrime S y z hyz
  obtain ⟨Nq, hNqz, hδz⟩ := hcoheight zP
  rw [← hNqz] at hNq
  have hb : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) ≠ ⊥ := by
    have _ : Nontrivial (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top
    exact ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial
  have hgoal : (((d + 2 : ℕ) : ℕ) : WithBot ℕ∞) <
      (completedStalkDepth (idealOnOpen S) F y p : WithBot ℕ∞) +
        ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) +
        (S.distanceToZ z : WithBot ℕ∞) := by
    by_cases hZ : (S.closedSubsetZ : Set S.Y).Nonempty
    · obtain ⟨m, hm⟩ := exists_max_dimensionFunction_on_closed S.Y S.closedSubsetZ hZ δ
      obtain ⟨w, hwZ, rfl⟩ := hm.1
      let wP : PrimeSpectrum (S.A ⧸ S.I) := w
      have hdist := distanceFunction_ge_dimensionFunction_sub_max S.Y S.closedSubsetZ δ (δ w) hm z
      -- `δ(w) ≤ dim(Z)`.
      have hwle : S.a.map (Ideal.Quotient.mk S.I) ≤ wP.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus _ _).mp hwZ
      have haw : (Order.coheight wP : WithBot ℕ∞) ≤
          ringKrullDim (S.A ⧸ S.a) := by
        rw [coheight_eq_ringKrullDim_quotient]
        calc ringKrullDim ((S.A ⧸ S.I) ⧸ wP.asIdeal)
            ≤ ringKrullDim ((S.A ⧸ S.I) ⧸ S.a.map (Ideal.Quotient.mk S.I)) :=
              ringKrullDim_le_of_surjective (Ideal.Quotient.factor hwle)
                (Ideal.Quotient.factor_surjective hwle)
          _ = ringKrullDim (S.A ⧸ S.a) :=
              ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE S.I_le_a)
      obtain ⟨Nw, hNw, hδw⟩ := hcoheight wP
      rw [← hNw] at haw
      have hane : ringKrullDim (S.A ⧸ S.a) ≠ ⊤ :=
        (lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.mk S.a)
          Ideal.Quotient.mk_surjective) ringKrullDim_lt_top).ne
      have hanb : ringKrullDim (S.A ⧸ S.a) ≠ ⊥ :=
        (lt_of_lt_of_le (WithBot.bot_lt_coe _) haw).ne'
      obtain ⟨Na, hNa⟩ := exists_natCast_eq_of_ne_bot_of_ne_top hanb hane
      rw [hNa] at haw hdim
      rw [hNA] at hdim h1
      rw [← hNq] at h1
      rw [hδz, hδw] at hdist
      refine natCast_lt_add_add_of_le_of_toNat_le hb h1 hdist (by exact_mod_cast haw) ?_
      exact_mod_cast hdim
    · have htop : S.distanceToZ z = ⊤ :=
        distanceFunction_eq_top_of_disjoint S.Y S.closedSubsetZ z
          (fun ⟨x, hx⟩ => hZ ⟨x, hx.2⟩)
      rw [htop]
      exact natCast_lt_add_add_top hb _ _
  have h := natCast_lt_enatToEInt_add_krullDimToEInt_add_enatToEInt (d + 2) hgoal
  show ((d + 2 : ℤ) : EInt) < _
  exact_mod_cast h

/-- **The example in hypothesis (6) of Stacks 0EJP.** If every term `ℱₙ` of an object of
`Coh(U, I𝒪_U)` is a finite locally free `𝒪_U/Iⁿ𝒪_U`-module, then at every `y ∈ U ∩ Y` the module
`ℱ_y^∧` is finite locally free outside `V(I𝒪_{X,y}^∧)`: it is even free over `𝒪_{X,y}^∧`
(`free_completedStalk_of_isFiniteLocallyFreeAdic`), so each of its localizations is free. -/
public theorem free_localizedModule_completedStalk_of_isFiniteLocallyFreeAdic
    (S : AlgebraizationSituation.{u}) (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hF : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y)) :
    Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y)) := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have hy : y ∈ (idealOnOpen S).support := by
    by_contra h
    have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support (idealOnOpen S) y).mpr h
    exact (maximalIdeal.isMaximal _).ne_top
      (top_le_iff.mp (htop ▸ stalk_idealOnOpen_le_maximalIdeal S y z hyz))
  have : Module.Free (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) :=
    free_completedStalk_of_isFiniteLocallyFreeAdic (idealOnOpen S) F hF hy
  have : Module.Finite (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) :=
    finite_completedStalk (idealOnOpen S) F y
  exact Module.free_of_isLocalizedModule p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y))

end Stacks.Algebraization

end
