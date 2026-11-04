module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DepthDimension.DepthSpecialization
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.SupportInjectivity.Basic
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationDepthCollapse
import all StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion
import all StacksFrontier.RingTheory.Dualizing.FiniteDimension

/-!
# The depth locus behind the stabilizing data of Stacks 0EFI

Comparisons of depth values with integer bounds, the vanishing of local cohomology below the
depth, the semicontinuity of `depth + δ` for the dimension function `δ` of a dualizing complex
(Stacks 0ECM, clause (4), over a ring), and the closure of a set of primes of bounded depth.
These are the inputs to Claims I and II of Stacks 0EFI in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Topology TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### Comparing depth values with integer bounds -/

/-- An integer bound `n` dominates a depth value exactly when the depth is the finite value of
some natural number at most `n`. -/
theorem enatToEInt_le_intCast_iff (e : ℕ∞) (s : ℤ) :
    enatToEInt e ≤ (s : EInt) ↔ ∃ n : ℕ, e = (n : ℕ∞) ∧ (n : ℤ) ≤ s := by
  cases e using ENat.recTopCoe with
  | top =>
      show (⊤ : EInt) ≤ (s : EInt) ↔ _
      simp
  | coe n => simp [enatToEInt]

/-- A depth value exceeds the integer `n` exactly when it exceeds `n` in `ℕ∞`. -/
private theorem intCast_lt_enatToEInt_iff (n : ℕ) (e : ℕ∞) :
    ((n : ℤ) : EInt) < enatToEInt e ↔ (n : ℕ∞) < e := by
  induction e using ENat.recTopCoe with
  | top =>
      show ((n : ℤ) : EInt) < ⊤ ↔ (n : ℕ∞) < ⊤
      exact iff_of_true (lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top _))
        (ENat.natCast_lt_top n)
  | coe d => simp [enatToEInt]

/-- Depth is never smaller than a nonpositive integer: the only values it takes are `⊤` and the
natural numbers. -/
private theorem not_enatToEInt_lt_intCast (e : ℕ∞) {s : ℤ} (hs : s ≤ 0) :
    ¬ enatToEInt e < (s : EInt) := by
  intro hlt
  obtain ⟨n, hn, hns⟩ := (enatToEInt_le_intCast_iff e s).mp hlt.le
  rw [hn] at hlt
  change ((n : ℤ) : EInt) < (s : EInt) at hlt
  have := WithBotTop.coe_lt_coe.mp hlt
  omega

/-- Depth is strictly larger than a negative integer. -/
private theorem intCast_lt_enatToEInt_of_neg (e : ℕ∞) {s : ℤ} (hs : s < 0) :
    (s : EInt) < enatToEInt e := by
  cases e using ENat.recTopCoe with
  | top =>
      show (s : EInt) < ⊤
      exact lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top _)
  | coe n =>
      show (s : EInt) < ((n : ℤ) : EInt)
      exact WithBotTop.coe_lt_coe.mpr (by omega)

/-- A relative dimension is never negative: for `𝔭 ⊆ 𝔮` the ring `(A/𝔭)_𝔮` is nonzero, so its
Krull dimension is the height of a prime and in particular not `⊥`. -/
private theorem zero_le_krullDimToEInt_localization_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    (0 : EInt) ≤ krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) := by
  have hcoe (k : ℕ∞) : krullDimToEInt (k : WithBot ℕ∞) = enatToEInt k := by
    cases k using ENat.recTopCoe <;> rfl
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, hcoe]
  have h0 : enatToEInt (0 : ℕ∞) ≤ enatToEInt (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    enatToEInt_mono bot_le
  change ((0 : ℤ) : EInt) ≤ _ at h0
  exact h0

/-! ### The two models of local cohomology supported in `V(I)` -/

/-- The two models of local cohomology supported in `V(I)` agree: derived sections with support in
the closed subset `V(I)`, and the coreflection of Stacks 0A6Q onto the objects with
`I`-power-torsion cohomology. This is the comparison of Stacks 0955 in degree `i`. -/
private noncomputable def localCohomologyWithSupportInIsoObj
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u w} A)) (i : ℤ) :
    Stacks.LocalCohomology.localCohomologyWithSupportIn A
        (PrimeSpectrum.zeroLocus (I : Set A)) K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max u w} A) i).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj K)) :=
  haveI := Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app.{u, w}
    A I hI K
  (DerivedCategory.homologyFunctor (ModuleCat.{max u w} A) i).mapIso
    (asIso ((Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology.{u, w}
      A I hI).app K))

/-- **`H^i_{V(I)}(N) = 0` below the depth**, transported to the coreflection model. -/
private theorem isZero_localCohomologyModule_of_lt_depth
    (B : Type u) [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    (N : ModuleCat.{max u w} B) [Module.Finite B (N : Type (max u w))]
    (hIN : I • (⊤ : Submodule B (N : Type (max u w))) ≠ ⊤)
    (n : ℕ) (hn : (n : ℕ∞) ≤ Module.depth B I (N : Type (max u w)))
    (i : ℤ) (hi : i < n) :
    IsZero (Stacks.LocalCohomology.localCohomologyModule B I I.fg_of_isNoetherianRing N i) :=
  (Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth.{u, w} I N hIN n hn i hi).of_iso
    (localCohomologyWithSupportInIsoObj.{u, w} B I I.fg_of_isNoetherianRing
      ((DerivedCategory.singleFunctor (ModuleCat.{max u w} B) 0).obj N) i).symm

/-- Local cohomology of a trivial module vanishes in every degree. -/
private theorem isZero_localCohomologyModule_of_subsingleton
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (N : ModuleCat.{w} A) [Subsingleton (N : Type w)] (i : ℤ) :
    IsZero (Stacks.LocalCohomology.localCohomologyModule A I hI N i) := by
  have hX : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj N) :=
    Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton N)
  have hL : IsZero ((Dualizing.localCohomologyFunctor A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj N)) := by
    let : (Dualizing.localCohomologyFunctor A I hI).IsRightAdjoint :=
      ⟨_, ⟨Dualizing.localCohomologyAdjunction A I hI⟩⟩
    exact Functor.map_isZero _ hX
  exact Functor.map_isZero _ (Functor.map_isZero _ hL)

/-- **`H^i_𝔪(N) = 0` below the depth**, over a Noetherian local ring, with the bound read in
`EInt` so that an infinite depth is allowed. -/
private theorem isZero_localCohomologyModule_maximal_of_lt_depth
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (N : ModuleCat.{max u w} B) [Module.Finite B (N : Type (max u w))]
    (i : ℤ) (hi : (i : EInt) <
      enatToEInt (Module.depth B (maximalIdeal B) (N : Type (max u w)))) :
    IsZero (Stacks.LocalCohomology.localCohomologyModule B (maximalIdeal B)
      (maximalIdeal B).fg_of_isNoetherianRing N i) := by
  by_cases hneg : i < 0
  · exact Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg B _ _ N i hneg
  rcases subsingleton_or_nontrivial (N : Type (max u w)) with hN | hN
  · exact isZero_localCohomologyModule_of_subsingleton B _ _ N i
  lift i to ℕ using le_of_not_gt hneg with k
  have hIN : (maximalIdeal B) • (⊤ : Submodule B (N : Type (max u w))) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  have hlt : (k : ℕ∞) < Module.depth B (maximalIdeal B) (N : Type (max u w)) :=
    (intCast_lt_enatToEInt_iff k _).mp hi
  refine isZero_localCohomologyModule_of_lt_depth.{u, w} B _ N hIN (k + 1) ?_ (k : ℤ) ?_
  · simpa only [Nat.cast_add, Nat.cast_one] using Order.add_one_le_of_lt hlt
  · exact_mod_cast Nat.lt_succ_self k

/-! ### Semicontinuity of `depth + δ`

Over a Noetherian ring with a dualizing complex `K` and dimension function `δ`, the locus where
`depth(M_𝔭) + δ(𝔭) ≤ c` is the union of the supports of the finitely many relevant
`Ext^j(M, K)`, hence closed. This is Stacks 0ECM, clause (4), at the level of a ring. -/

/-- **The depth read off a normalized dualizing complex.** Over a Noetherian local ring, some
`Ext^j(N, ω)` with `j ≥ -c` is nonzero exactly when the depth of `N` is finite and at most `c`.

This is Stacks 0A7U, parts (2) and (3): the depth is the least `n` with `Ext^{-n}(N, ω) ≠ 0`, and
`Ext^j(N, ω)` vanishes for `j > 0`. -/
private theorem exists_nontrivial_ext_ge_iff_depth_le
    {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    {N : Type u} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (omega : DerivedCategory (ModuleCat.{u} B))
    (homega : Dualizing.IsNormalizedDualizingComplex omega) (c : ℤ) :
    (∃ j : ℤ, -c ≤ j ∧ Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B N)) omega j)) ↔
      ∃ n : ℕ, Module.depth B (maximalIdeal B) N = (n : ℕ∞) ∧ (n : ℤ) ≤ c := by
  rcases subsingleton_or_nontrivial N with hN | hN
  · have hdepth : Module.depth B (maximalIdeal B) N = ⊤ := by
      simp [Module.depth, Subsingleton.elim ((maximalIdeal B) • (⊤ : Submodule B N)) ⊤]
    have hX : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B N)) :=
      Functor.map_isZero _ (ModuleCat.isZero_iff_subsingleton.mpr hN)
    constructor
    · rintro ⟨j, -, hj⟩
      exact absurd ⟨fun f g => hX.eq_of_src f g⟩ (not_subsingleton_iff_nontrivial.mpr hj)
    · rintro ⟨n, hn, -⟩
      exact (ENat.natCast_ne_top n (hn.symm.trans hdepth)).elim
  · obtain ⟨n, hn, hdepth⟩ :=
      Dualizing.depth_eq_least_nonzero_negative_ext omega homega hN
    constructor
    · rintro ⟨j, hjc, hj⟩
      obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast B N
      have hj0 := (Dualizing.ext_degree_mem_Icc_of_nontrivial omega homega d hd j hj).2
      have hj' : -(((-j).toNat : ℕ) : ℤ) = j := by omega
      have hnle : n ≤ (-j).toNat := by
        refine hn.2 ?_
        show Nontrivial (DerivedCategory.Ext _ omega (-(((-j).toNat : ℕ) : ℤ)))
        rwa [hj']
      exact ⟨n, hdepth, by omega⟩
    · rintro ⟨m, hm, hmc⟩
      obtain rfl : n = m := ENat.natCast_inj.mp (hdepth.symm.trans hm)
      exact ⟨-(n : ℤ), by omega, hn.1⟩

/-- **Stacks 0ECM, clause (4), over a ring.** For a finite module `M` over a Noetherian ring with
a dualizing complex `K` and dimension function `δ`, some `Ext^j(M, K)` with `j ≥ -c` survives
localization at `𝔭` exactly when `depth(M_𝔭)` is finite and `depth(M_𝔭) + δ(𝔭) ≤ c`.

Localizing at `𝔭` commutes with forming `Ext` into `K`, and `K_𝔭` shifted by `-δ(𝔭)` is a
normalized dualizing complex over `A_𝔭` — that is what `δ` is. So the statement is
`exists_nontrivial_ext_ge_iff_depth_le` over `A_𝔭`, reindexed by `δ(𝔭)`. -/
private theorem exists_nontrivial_localized_ext_iff_depth_add_dualizingDimension_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (hKge : ∃ b : ℤ, K.IsGE b) (p : PrimeSpectrum A) (c : ℤ) :
    (∃ j : ℤ, -c ≤ j ∧ Nontrivial (LocalizedModule p.asIdeal.primeCompl
        (DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A M)) K j))) ↔
      ∃ n : ℕ, Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) = (n : ℕ∞) ∧
        (n : ℤ) + Dualizing.dualizingDimension K p ≤ c := by
  set T := p.asIdeal.primeCompl with hT
  set B := Localization.AtPrime p.asIdeal with hB
  set d := Dualizing.dualizingDimension K p with hd
  let G := ModuleCat.localizedModuleFunctor.{u} T
  let Mloc := G.obj (ModuleCat.of A M)
  let Xloc := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj Mloc
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K
  have hKpN : Dualizing.IsNormalizedDualizingComplex (Kp⟦-d⟧) :=
    Dualizing.dualizingDimension_spec K hK p
  have eK : Kp ≅ G.mapDerivedCategory.obj K :=
    Dualizing.pseudoCoherenceLocalizationDerivedIso p.asIdeal K
  have hbridge : ∀ j : ℤ, Nontrivial (LocalizedModule T
      (DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A M)) K j)) ↔ Nontrivial (DerivedCategory.Ext Xloc Kp j) := by
    intro j
    refine (Dualizing.localized_ext_nontrivial_iff K hKge j).trans ?_
    exact ((Iso.refl Xloc).homCongr ((shiftFunctor _ j).mapIso eK)).nontrivial_congr.symm
  have hshift : ∀ j : ℤ, Nontrivial (DerivedCategory.Ext Xloc Kp j) ↔
      Nontrivial (DerivedCategory.Ext Xloc (Kp⟦-d⟧) (j + d)) := fun j =>
    ((Iso.refl Xloc).homCongr
      ((shiftFunctorAdd' _ (-d) (j + d) j (by omega)).app Kp)).nontrivial_congr
  have hlocdepth : Module.depth B (maximalIdeal B) (Mloc : Type u) =
      Module.depth B (maximalIdeal B) (LocalizedModule T M) :=
    Module.depth_eq_depth_of_linearEquiv (maximalIdeal B) (Shrink.linearEquiv.{u} B _)
  let : Module.Finite B (Mloc : Type u) :=
    Module.Finite.equiv (Shrink.linearEquiv.{u} B (LocalizedModule T M)).symm
  have hnormal := exists_nontrivial_ext_ge_iff_depth_le (B := B) (N := (Mloc : Type u))
    (Kp⟦-d⟧) hKpN (c - d)
  constructor
  · rintro ⟨j, hj, hjN⟩
    obtain ⟨n, hn, hnc⟩ := hnormal.mp ⟨j + d, by omega, (hshift j).mp ((hbridge j).mp hjN)⟩
    exact ⟨n, hlocdepth ▸ hn, by omega⟩
  · rintro ⟨n, hn, hnc⟩
    obtain ⟨j, hj, hjN⟩ := hnormal.mpr ⟨n, hlocdepth.trans hn, by omega⟩
    refine ⟨j - d, by omega, (hbridge (j - d)).mpr ((hshift (j - d)).mpr ?_)⟩
    simpa only [sub_add_cancel] using hjN

/-- **Semicontinuity of `depth + δ`, Stacks 0ECM.** The locus of primes at which the depth of `M`
is finite and `depth(M_𝔭) + δ(𝔭) ≤ c` is closed.

By `exists_nontrivial_localized_ext_iff_depth_add_dualizingDimension_le` that locus is the union
of the supports of `Ext^j(M, K)` over the degrees `j ∈ [-c, b]`, where `b` bounds the degrees in
which `RHom(M, K)` has cohomology. Each `Ext^j(M, K)` is a finite module, so each support is
closed, and the union is finite. -/
theorem isClosed_depth_add_dualizingDimension_sublevel
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K) (c : ℤ) :
    IsClosed {p : PrimeSpectrum A | ∃ n : ℕ,
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) = (n : ℕ∞) ∧
      (n : ℤ) + Dualizing.dualizingDimension K p ≤ c} := by
  classical
  obtain ⟨a, b, hAmp⟩ := hK.finiteInjectiveDimension
  have hKge : ∃ e : ℤ, K.IsGE e :=
    ⟨a, (Dualizing.isGE_isLE_of_hasInjectiveAmplitude K a b hAmp).1⟩
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  let D := (Dualizing.dualizingDerivedHomFunctor A K).obj (.op X)
  have hX : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) :=
    Dualizing.finite_homology_single (ModuleCat.of A M)
  have hD := Dualizing.dualizingDerivedHom_finiteCohomology A K hK X hX
  obtain ⟨b', hb'⟩ := (Dualizing.dualizingDerivedHom_plus_iff_minus A K hK X hX).mp
    ⟨0, inferInstance⟩
  let E := fun j : ℤ => DerivedCategory.Ext X K j
  have hE : ∀ j : ℤ, Module.Finite A (E j) := by
    intro j
    let := hD j
    exact Module.Finite.equiv
      (Dualizing.extIntoOmegaAtLinearEquiv A K j (ModuleCat.of A M)).symm
  have hzero : ∀ j : ℤ, b' < j → Module.support A (E j) = ∅ := by
    intro j hj
    have hz := DerivedCategory.isZero_of_isLE D b' j hj
    let := ModuleCat.isZero_iff_subsingleton.mp hz
    let : Subsingleton (E j) :=
      (Dualizing.extIntoOmegaAtLinearEquiv A K j (ModuleCat.of A M)).injective.subsingleton
    ext q
    exact iff_of_false (not_nontrivial_iff_subsingleton.mpr inferInstance) (Set.notMem_empty q)
  have hclosed : IsClosed (⋃ j ∈ Set.Icc (-c) b', Module.support A (E j)) :=
    (Set.finite_Icc _ _).isClosed_biUnion fun j _ => by
      let := hE j
      exact Module.isClosed_support (R := A) (M := E j)
  convert hclosed using 1
  ext p
  simp only [Set.mem_ofPred_eq]
  rw [← exists_nontrivial_localized_ext_iff_depth_add_dualizingDimension_le K hK hKge p c]
  constructor
  · rintro ⟨j, hj, hpj⟩
    have hj' : j ≤ b' := by
      by_contra h
      have hmem : p ∈ Module.support A (E j) := hpj
      rw [hzero j (lt_of_not_ge h)] at hmem
      exact hmem
    exact Set.mem_iUnion₂.mpr ⟨j, ⟨hj, hj'⟩, hpj⟩
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨j, hj.1, hpj⟩

/-! ### The closure of a set of bounded depth -/

/-- A point of the closure of a finite set that specializes to every member of the set is itself
a member of it. -/
private theorem mem_of_mem_closure_finite_of_specializes
    {X : Type*} [TopologicalSpace X] [T0Space X]
    {p : X} {S : Set X} (hS : S.Finite) (hp : p ∈ closure S)
    (hgen : ∀ q ∈ S, p ⤳ q) : p ∈ S := by
  have hcl : closure S = ⋃ q ∈ S, closure ({q} : Set X) := by
    simpa only [Set.biUnion_of_singleton] using hS.closure_biUnion (fun q => {q})
  rw [hcl] at hp
  obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hp
  have heq : p = q :=
    ((hgen q hq).antisymm (specializes_iff_mem_closure.mpr hpq)).eq
  exact heq.symm ▸ hq

/-- A prime in the closure of a set on which the depth of `M` is bounded has finite depth: the
bound puts the set inside the support of `M`, which is closed. -/
private theorem depth_lt_top_of_mem_closure_of_bounded_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (B : Set (PrimeSpectrum A)) (s : ℤ)
    (hB : ∀ q ∈ B, enatToEInt
      (Module.depth (Localization.AtPrime q.asIdeal)
        (maximalIdeal (Localization.AtPrime q.asIdeal))
        (LocalizedModule q.asIdeal.primeCompl M)) ≤ (s : EInt))
    (p : PrimeSpectrum A) (hp : p ∈ closure B) :
    Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) < ⊤ := by
  have hsupport : B ⊆ Module.support A M := by
    intro q hq
    rw [Module.mem_support_iff, ← not_subsingleton_iff_nontrivial]
    intro hzero
    let := hzero
    have hsmul : maximalIdeal (Localization.AtPrime q.asIdeal) •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)) = ⊤ := Subsingleton.elim _ _
    have hdepth := hB q hq
    simp only [Module.depth, hsmul, ite_true] at hdepth
    change (⊤ : EInt) ≤ (s : EInt) at hdepth
    simp at hdepth
  have hpSupport : p ∈ Module.support A M := by
    apply closure_minimal hsupport _ hp
    rw [Module.support_eq_zeroLocus]
    exact PrimeSpectrum.isClosed_zeroLocus _
  let := Module.mem_support_iff.mp hpSupport
  apply Module.depth_lt_top
  exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (maximalIdeal_le_jacobson _)).symm

/-- **Stacks 0DWY, in the form used for the closure.** A prime `𝔭` which is a generic point of
the closure, inside `V(𝔭)`, of a set on which the depth of `M` is at most `s`, and which does not
itself lie in that set, has `depth(M_𝔭) < s`.

Stacks 0DWY makes the depth at least `e = depth(M_𝔭)` on an open neighbourhood of `𝔭` in `V(𝔭)`
and strictly greater than `e` off a finite subset of it; were `e ≥ s`, that finite subset would
contain the whole intersection of the neighbourhood with the set, and `𝔭` would be one of its
points. -/
private theorem nat_lt_of_mem_closure_of_bounded_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (e : ℕ)
    (he : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) = (e : ℕ∞))
    (s : ℤ) (B : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)))
    (hB : ∀ q ∈ B, enatToEInt
      (Module.depth (Localization.AtPrime q.1.asIdeal)
        (maximalIdeal (Localization.AtPrime q.1.asIdeal))
        (LocalizedModule q.1.asIdeal.primeCompl M)) ≤ (s : EInt))
    (hp : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus
      (p.asIdeal : Set A))) ∈ closure B)
    (hpB : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus
      (p.asIdeal : Set A))) ∉ B) :
    (e : ℤ) < s := by
  let η : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) := ⟨p, fun _ hx => hx⟩
  have hgen (q : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) : η ⤳ q := by
    rw [specializes_iff_mem_closure,
      Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    simpa only [Set.image_singleton, PrimeSpectrum.closure_singleton,
      Set.mem_preimage, η] using q.2
  obtain ⟨U, hU, hUne, -, hfinite⟩ :=
    Module.exists_open_depth_localization_ge_and_finite_exceptional p e he
  have hηU : η ∈ U := by
    obtain ⟨q, hq⟩ := hUne
    exact (hgen q).mem_open hU hq
  by_contra hn
  have hs : (s : EInt) ≤ ((e : ℤ) : EInt) :=
    WithBotTop.coe_le_coe.mpr (le_of_not_gt hn)
  have hBU : (U ∩ B).Finite := hfinite.subset (by
    rintro q ⟨hqU, hqB⟩
    refine ⟨hqU, ?_⟩
    intro hlt
    exact (not_lt_of_ge ((hB q hqB).trans hs))
      ((intCast_lt_enatToEInt_iff e _).mpr hlt))
  exact hpB (mem_of_mem_closure_finite_of_specializes hBU
    (hU.inter_closure ⟨hηU, hp⟩) (fun q _ => hgen q)).2

/-- The conclusion of `nat_lt_of_mem_closure_of_bounded_depth` with the depth read in `EInt`. -/
theorem depth_lt_of_mem_closure_of_bounded_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (s : ℤ)
    (B : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)))
    (hB : ∀ q ∈ B, enatToEInt
      (Module.depth (Localization.AtPrime q.1.asIdeal)
        (maximalIdeal (Localization.AtPrime q.1.asIdeal))
        (LocalizedModule q.1.asIdeal.primeCompl M)) ≤ (s : EInt))
    (hp : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus
      (p.asIdeal : Set A))) ∈ closure B)
    (hpB : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus
      (p.asIdeal : Set A))) ∉ B) :
    enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M)) < (s : EInt) := by
  have hp' : p ∈ closure (Subtype.val '' B) := by
    rwa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hp
  have hfinite := depth_lt_top_of_mem_closure_of_bounded_depth
    (Subtype.val '' B) s (by rintro _ ⟨q, hq, rfl⟩; exact hB q hq) p hp'
  generalize he : Module.depth (Localization.AtPrime p.asIdeal)
    (maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M) = depthAtP at hfinite ⊢
  cases depthAtP using ENat.recTopCoe with
  | top => exact (lt_irrefl _ hfinite).elim
  | coe e =>
      exact WithBotTop.coe_lt_coe.mpr
        (nat_lt_of_mem_closure_of_bounded_depth p e he s B hB hp hpB)

/-- A set all of whose generic points lie in a specialization-stable set has its closure inside
that set: the closure is covered by the closures of the finitely many minimal primes of its
vanishing ideal, and each of those is the closure of a generic point. -/
theorem closure_subset_of_generic_mem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (B T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hgeneric : ∀ p : PrimeSpectrum A,
      (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) ∈
        closure (Subtype.val ⁻¹' B) → p ∈ T) :
    closure B ⊆ T := by
  let K := PrimeSpectrum.vanishingIdeal B
  have hBK : B ⊆ PrimeSpectrum.zeroLocus (K : Set A) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact subset_closure
  let C (r : Ideal A) := B ∩ PrimeSpectrum.zeroLocus (r : Set A)
  have hcover : B ⊆ ⋃ r ∈ K.minimalPrimes, C r := by
    intro b hb
    obtain ⟨r, hr, hrb⟩ := Ideal.exists_minimalPrimes_le (hBK hb)
    exact Set.mem_iUnion₂.mpr ⟨r, hr, hb, hrb⟩
  intro q hq
  have hKq : K ≤ q.asIdeal := by
    show q ∈ PrimeSpectrum.zeroLocus (K : Set A)
    rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  obtain ⟨p₀, hp₀, hpq⟩ := Ideal.exists_minimalPrimes_le hKq
  let p : PrimeSpectrum A := ⟨p₀, hp₀.1.1⟩
  have hpK : p ∈ PrimeSpectrum.zeroLocus (K : Set A) := hp₀.1.2
  have hpB : p ∈ closure B := by
    rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hpK
  have hpcover := closure_mono hcover hpB
  rw [K.finite_minimalPrimes_of_isNoetherianRing.closure_biUnion] at hpcover
  obtain ⟨r, hr, hpr⟩ := Set.mem_iUnion₂.mp hpcover
  have hrp : r ≤ p₀ := closure_minimal Set.inter_subset_right
    (PrimeSpectrum.isClosed_zeroLocus (r : Set A)) hpr
  have hprEq : p₀ = r := le_antisymm (hp₀.2 hr.1 hrp) hrp
  subst r
  have hpSub : (⟨p, fun _ hx => hx⟩ :
      ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) ∈
      closure (Subtype.val ⁻¹' B) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    have himage : Subtype.val '' (Subtype.val ⁻¹' B :
        Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) = C p₀ := by
      ext b
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨hb, b.2⟩
      · rintro ⟨hb, hbp⟩
        exact ⟨⟨b, hbp⟩, hb, rfl⟩
    show p ∈ closure _
    rwa [himage]
  exact hT ((PrimeSpectrum.le_iff_specializes p q).mp hpq) (hgeneric p hpSub)

end Stacks.Algebraization

end
