module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleSpecialization.StalkLengths
public import
  StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleSpecialization.FiberCycleCoefficients

/-!
# The specialization formula for the cycle of a flat module

Length additivity along a regular parameter (Stacks 02QG), the bijection between the minimal
primes of the support of a stalk on the special fibre and the points of the generic fibre
specializing to it, and the coefficientwise proof that the specialization map sends `[F_K]_r` to
`[F_kappa]_r` (Stacks 0H4I).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.ModuleSpecialization

private lemma maximalIdeal_smul_top_ne_top_of_nontrivial {A N : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] : IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ :=
  .symm <| Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator <| by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _
      (mt Module.annihilator_eq_top_iff.mp (not_subsingleton N))]

private lemma depth_eq_depthSup_of_nontrivial {A N : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] : Module.depth A (IsLocalRing.maximalIdeal A) N =
      Module.depthSup A (IsLocalRing.maximalIdeal A) N := by
  rw [Module.depth, ite_eq_right maximalIdeal_smul_top_ne_top_of_nontrivial]
  exact (Module.depthSup_eq_iSup (IsLocalRing.maximalIdeal A) N).symm

private theorem local_module_cohenMacaulay_of_regular_parameter
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular M a)
    (hquot : Module.supportDim A (QuotSMulTop a M) = 0) :
    Module.IsCohenMacaulayAtMaximalIdeal A M := by
  let Q := QuotSMulTop a M
  let : AddCommGroup Q := inferInstance
  let : Module A Q := inferInstance
  let : Module.Finite A Q := inferInstance
  have : Nontrivial Q := nontrivial_quotSMulTop_of_mem_maximalIdeal M ha
  have hdepth_le : (Module.depthSup A (IsLocalRing.maximalIdeal A) Q : WithBot ℕ∞) ≤ 0 := by
    rw [← depth_eq_depthSup_of_nontrivial]
    exact (Module.depth_le_supportDim A _ Q maximalIdeal_smul_top_ne_top_of_nontrivial).trans
      (by simpa [Q] using hquot.le)
  have hzero_mem : (0 : ℕ∞) ∈
      {n : ℕ∞ | ∃ rs : List A, (rs.length : ℕ∞) = n ∧
        (∀ a ∈ rs, a ∈ IsLocalRing.maximalIdeal A) ∧
          RingTheory.Sequence.IsRegular Q rs} :=
    ⟨[], by simp, by simp, RingTheory.Sequence.IsRegular.nil A Q⟩
  have hzero_le : (0 : WithBot ℕ∞) ≤
      (Module.depthSup A (IsLocalRing.maximalIdeal A) Q : WithBot ℕ∞) := by
    rw [Module.depthSup]
    exact WithBot.coe_le_coe.mpr (le_sSup hzero_mem)
  have hdepth : (Module.depthSup A (IsLocalRing.maximalIdeal A) Q : WithBot ℕ∞) = 0 :=
    le_antisymm hdepth_le hzero_le
  have hQcm : IsCohenMacaulayModule A Q :=
    isCohenMacaulayModule_iff_supportDim_eq_depth.mpr (by rw [hquot, hdepth])
  have hMcm : IsCohenMacaulayModule A M :=
    (isCohenMacaulayModule_iff_isCohenMacaulayModule_quotSMulTop
      (R := A) (M := M) ha hreg).2 hQcm
  simpa [Module.IsCohenMacaulayAtMaximalIdeal, IsCohenMacaulayModule,
    Module.supportDim, depth_eq_depthSup_of_nontrivial (N := M)]
    using hMcm

private theorem local_length_additivity_of_regular_parameter
    {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular M a)
    (hquot : Module.supportDim A (QuotSMulTop a M) = 0) :
    Module.length A (QuotSMulTop a M) =
      ∑ᶠ q ∈ {q : PrimeSpectrum A | Minimal (· ∈ Module.support A M) q},
        Module.length A (A ⧸ (Ideal.span {a} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  have hM : Module.supportDim A M = 1 := by
    calc
      Module.supportDim A M = Module.supportDim A (QuotSMulTop a M) + 1 :=
        (Module.supportDim_quotSMulTop_succ_eq_supportDim hreg ha).symm
      _ = 1 := by rw [hquot]; norm_num
  exact AlgebraicGeometry.length_quotSMulTop_eq_sum_minimal_support a
    (local_module_cohenMacaulay_of_regular_parameter a ha hreg hquot) hM hquot

private noncomputable def stalkPrimeOfSpecialization {Y : Scheme.{u}} (x y : Y)
    (hyx : y ⤳ x) : PrimeSpectrum (Y.presheaf.stalk x) :=
  Classical.choose (Set.mem_range.mp
    (show y ∈ Set.range (Y.fromSpecStalk x) by rwa [Scheme.range_fromSpecStalk (x := x)]))

private theorem fromSpecStalk_stalkPrimeOfSpecialization {Y : Scheme.{u}} (x y : Y)
    (hyx : y ⤳ x) :
    Y.fromSpecStalk x (stalkPrimeOfSpecialization x y hyx) = y :=
  Classical.choose_spec (Set.mem_range.mp
    (show y ∈ Set.range (Y.fromSpecStalk x) by rwa [Scheme.range_fromSpecStalk (x := x)]))

private lemma mem_genericFiber_of_specializes_genericFiber
    {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S)
    (ξ : f.fiber (genericPoint S)) {y : X}
    (h : y ⤳ f.fiberι (genericPoint S) ξ) : f y = genericPoint S := by
  have he : f (f.fiberι (genericPoint S) ξ) = genericPoint S :=
    (f.fiberHomeo (genericPoint S) ξ).2
  have hy : f y ⤳ genericPoint S := he ▸ h.map f.continuous
  exact (hy.antisymm (genericPoint_spec S |>.specializes (Set.mem_univ _))).eq

private lemma minimal_support_stalk_of_genericFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsCoherent) (r : ℕ)
    (hK : fiberSupportDimension f F hF (genericPoint (Spec (.of R))) ≤ ((r : ℤ) : EInt))
    (x : X) (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : ξ ∈ SheafOfModules.supp (fiberModule f F (genericPoint (Spec (.of R)))))
    (hδξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = f.fiberι (genericPoint (Spec (.of R))) ξ) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    Minimal (· ∈ Module.support (X.presheaf.stalk x) (F.presheaf.stalk x)) p := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := hF.isFiniteType
  let η := genericPoint (Spec (.of R))
  let C := fieldChowSituation
    ((Spec (.of R)).residueField η)
  let g := f.fiberToSpecResidueField η
  have : LocallyOfFiniteType g := by
    change LocallyOfFiniteType (pullback.snd f ((Spec (.of R)).fromSpecResidueField η))
    infer_instance
  rw [minimal_support_stalk_iff F x p, hp]
  refine ⟨?_, ?_⟩
  · rwa [Stacks.Modules.supp_pullback] at hξ
  · intro y hy hspec
    have hfy := mem_genericFiber_of_specializes_genericFiber f ξ hspec
    let ζ := (f.fiberHomeo η).symm ⟨y, hfy⟩
    have hζ : f.fiberι η ζ = y := f.fiberι_fiberHomeo_symm η ⟨y, hfy⟩
    have hζsupp : ζ ∈ SheafOfModules.supp (fiberModule f F η) := by
      rw [Stacks.Modules.supp_pullback]
      change f.fiberι η ζ ∈ SheafOfModules.supp F
      rwa [hζ]
    have hζξ : ζ ⤳ ξ := (f.fiberι η).isEmbedding.isInducing.specializes_iff.mp
      (hζ.symm ▸ hspec)
    have he := eq_of_mem_supp_of_specializes_of_relativeDimension_eq C g
      (fiberModule f F η) (fiberModule_isCoherent f F η)
      (r : ℤ) hK hζsupp hδξ hζξ
    exact hζ.symm.trans (congrArg (f.fiberι η) he)

private lemma exists_minimalSupportEquiv_genericFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsCoherent) (r : ℕ)
    (hK : fiberSupportDimension f F hF (genericPoint (Spec (.of R))) ≤ ((r : ℤ) : EInt))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hδx : fiberPointDimension f (IsLocalRing.closedPoint R) x = (r : ℤ))
    (a : X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x))
    (hker : RingHom.ker ((f.fiberι (IsLocalRing.closedPoint R)).stalkMap x).hom =
      Ideal.span {a})
    (hreg :
      letI := Stacks.ModuleStalkSpecialization.stalkModule F
        (f.fiberι (IsLocalRing.closedPoint R) x)
      IsSMulRegular (F.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) x)) a) :
    let η := genericPoint (Spec (.of R))
    let s : Spec (.of R) := IsLocalRing.closedPoint R
    let z := f.fiberι s x
    letI := Stacks.ModuleStalkSpecialization.stalkModule F z
    ∃ e : {p : PrimeSpectrum (X.presheaf.stalk z) //
        Minimal (· ∈ Module.support (X.presheaf.stalk z) (F.presheaf.stalk z)) p} ≃
      {ξ : f.fiber η //
        fiberPointDimension f η ξ = (r : ℤ) ∧
        ξ ∈ SheafOfModules.supp (fiberModule f F η) ∧ f.fiberι η ξ ⤳ z},
      ∀ p, f.fiberι η (e p).1 = X.fromSpecStalk z p.1 := by
  classical
  dsimp only
  let η := genericPoint (Spec (.of R))
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let z := f.fiberι s x
  let C := fieldChowSituation
    ((Spec (.of R)).residueField η)
  let g := f.fiberToSpecResidueField η
  let G := fiberModule f F η
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := hF.isFiniteType
  have : LocallyOfFiniteType g := by
    change LocallyOfFiniteType (pullback.snd f ((Spec (.of R)).fromSpecResidueField η))
    infer_instance
  let := Stacks.ModuleStalkSpecialization.stalkModule F z
  let P := {p : PrimeSpectrum (X.presheaf.stalk z) //
    Minimal (· ∈ Module.support (X.presheaf.stalk z) (F.presheaf.stalk z)) p}
  let T := {ξ : f.fiber η //
    relativeDimension C.dimensionFunction g ξ = (r : ℤ) ∧
    ξ ∈ SheafOfModules.supp G ∧ f.fiberι η ξ ⤳ z}
  have hmap : ∀ p : P, ∃ t : T, f.fiberι η t.1 = X.fromSpecStalk z p.1 := by
    intro p
    have hyη := image_minimal_support_stalk_mem_genericFiber f F x p.1 a hker hreg p.2
    let ξ := (f.fiberHomeo η).symm ⟨X.fromSpecStalk z p.1, hyη⟩
    have hξ : f.fiberι η ξ = X.fromSpecStalk z p.1 :=
      f.fiberι_fiberHomeo_symm η ⟨X.fromSpecStalk z p.1, hyη⟩
    have hξsupp : ξ ∈ SheafOfModules.supp G := by
      rw [Stacks.Modules.supp_pullback]
      change f.fiberι η ξ ∈ SheafOfModules.supp F
      rw [hξ]
      exact (fromSpecStalk_mem_supp_iff F z p.1).mpr p.2.1
    have hξspec : f.fiberι η ξ ⤳ z := hξ.symm ▸ specializes_fromSpecStalk z p.1
    have hδle := relativeDimension_le_of_mem_supp C g G
      (fiberModule_isCoherent f F η) (r : ℤ) hK ξ hξsupp
    have hδge := relativeDimension_generic_ge_special f ξ x hξspec
    rw [hδx] at hδge
    exact ⟨⟨ξ, le_antisymm hδle hδge, hξsupp, hξspec⟩, hξ⟩
  let b : P → T := fun p ↦ (hmap p).choose
  have hb (p : P) : f.fiberι η (b p).1 = X.fromSpecStalk z p.1 := (hmap p).choose_spec
  have hbij : Function.Bijective b := by
    refine ⟨fun p q hpq ↦ Subtype.ext ((X.fromSpecStalk z).isEmbedding.injective ?_), fun t ↦ ?_⟩
    · rw [← hb p, ← hb q, hpq]
    · let p := stalkPrimeOfSpecialization z (f.fiberι η t.1) t.2.2.2
      have hp : X.fromSpecStalk z p = f.fiberι η t.1 :=
        fromSpecStalk_stalkPrimeOfSpecialization z (f.fiberι η t.1) t.2.2.2
      have hpmin := minimal_support_stalk_of_genericFiber f F hF r hK z t.1
        t.2.2.1 t.2.1 p hp
      exact ⟨⟨p, hpmin⟩,
        Subtype.ext ((f.fiberι η).isEmbedding.injective ((hb ⟨p, hpmin⟩).trans hp))⟩
  exact ⟨Equiv.ofBijective b hbij, hb⟩

private theorem fiberCycle_apply {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent) (r : ℕ)
    (s : Spec (.of R))
    (hdim : fiberSupportDimension f F hF s ≤ ((r : ℤ) : EInt))
    (x : f.fiber s)
    (hrel : fiberPointDimension f s x = (r : ℤ)) :
    (fiberCycle f F hF r s hdim : AlgebraicCycle (f.fiber s) ℤ) x =
      (open Classical in
        if x ∈ SheafOfModules.supp (fiberModule f F s) then
          Stacks.Chow.sheafMultiplicity (fiberModule f F s) x else 0) := by
  classical
  have : F.IsFiniteType := hF.isFiniteType
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let C := fieldChowSituation
    ((Spec (.of R)).residueField s)
  let g := f.fiberToSpecResidueField s
  have hcoh : (fiberModule f F s).IsCoherent := fiberModule_isCoherent f F s
  have hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ (fiberModule f F s) hcoh).subschemeι ≫ g) ≤
        ((r : ℤ) : EInt) := by
    simpa [fiberSupportDimension, C, g] using hdim
  have hδ : relativeDimension C.dimensionFunction g x = (r : ℤ) := hrel
  change (@Stacks.Chow.cycleAssociatedToCoherentSheaf _ C g _ (fiberModule f F s)
    hcoh (r : ℤ) hbound : AlgebraicCycle (f.fiber s) ℤ) x = _
  rw [cycleAssociatedToCoherentSheaf_apply]
  by_cases hx : x ∈ SheafOfModules.supp (fiberModule f F s) <;> simp [hx, hδ]

private theorem relativeDimension_eq_of_cycle_coeff_ne_zero
    (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] (r : ℤ)
    (c : Stacks.Chow.CycleGroup C g r) (x : Y) (hx : c.1 x ≠ 0) :
    relativeDimension C.dimensionFunction g x = r := by
  let Z : TopologicalSpace.IrreducibleCloseds Y :=
    ⟨closure ({x} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
  have hgen : Z.isIrreducible.genericPoint = x :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq
      (isGenericPoint_closure (x := x))
  have hdim := (mem_cyclesOfDimension C g r c.1).mp c.2 Z
  have hcoeff : c.1 Z.isIrreducible.genericPoint ≠ 0 := by
    simpa [hgen] using hx
  simpa [Stacks.Chow.deltaDimension, hgen] using hdim hcoeff

private theorem specializationCycleCoeff_ne_zero_dimension {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (h : specializationCoeff f r ξ x ≠ 0) :
    let s : Spec (.of R) := IsLocalRing.closedPoint R
    let C := fieldChowSituation
      ((Spec (.of R)).residueField s)
    relativeDimension C.dimensionFunction (f.fiberToSpecResidueField s) x =
      (r : ℤ) := by
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let C := fieldChowSituation
    ((Spec (.of R)).residueField s)
  let g := f.fiberToSpecResidueField s
  change relativeDimension C.dimensionFunction g x = (r : ℤ)
  unfold specializationCoeff at h
  dsimp only at h
  unfold closedSubschemeCycleCoeff at h
  split_ifs at h with hx
  · obtain ⟨ζ, hζ, hdim⟩ := hx
    exact hdim
  · exact (h rfl).elim

private theorem specializationCycleCoeff_ne_zero_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (r : ℕ) (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (h : specializationCoeff f r ξ x ≠ 0) :
    f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x := by
  by_contra hspec
  apply h
  let η := genericPoint (Spec (.of R))
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let J := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({ξ} : Set (f.fiber η)))
  let j := J.subschemeι ≫ f.fiberι η
  have hqc : QuasiCompact (f.fiberι η) := by
    change QuasiCompact (pullback.fst f ((Spec (.of R)).fromSpecResidueField η))
    infer_instance
  have hsupp : (j.ker.support : Set X) =
      closure ({f.fiberι η ξ} : Set X) := by
    change ((J.map (f.fiberι η)).support : Set X) = _
    rw [Scheme.IdealSheafData.support_map]
    simp only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure]
    rw [← Set.image_singleton]
    exact closure_image_closure (f.fiberι η).continuous
  unfold specializationCoeff closedSubschemeCycleCoeff
  dsimp only
  split_ifs with he
  · obtain ⟨z, hz, _⟩ := he
    exfalso
    apply hspec
    rw [specializes_iff_mem_closure, ← hsupp]
    have hm := (j.ker.comap (f.fiberι s)).range_subschemeι ▸
      Set.mem_range_self z.1
    rw [hz] at hm
    simpa only [Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage, Set.mem_preimage] using hm
  · rfl

private lemma toNat_finsum_mul_eq_tsum {ι : Type*} (s : Set ι) (hs : s.Finite)
    (a b : ι → ℕ∞) (hfin : (∑ᶠ p ∈ s, a p * b p) ≠ ⊤) :
    (((∑ᶠ p ∈ s, a p * b p).toNat : ℕ) : ℤ) =
      ∑' p : s, ((a p).toNat : ℤ) * ((b p).toNat : ℤ) := by
  classical
  let : Fintype s := hs.fintype
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype] at hfin ⊢
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hfin), Nat.cast_sum, tsum_fintype]
  exact Finset.sum_congr rfl fun p _ ↦ by rw [ENat.toNat_mul, Nat.cast_mul]



/-- **Stacks Project, Tag 0H4I**, in the delta-dimension form the associated cycle consumes: if
the support of the generic fibre has delta-dimension at most `r` over `K`, so does the support of
the special fibre over `kappa`. -/
private theorem fiberSupportDimension_le_of_genericFibre {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent)
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : topologicalKrullDim (SheafOfModules.supp
      (fiberModule f F (genericPoint (Spec (.of R))))) ≤ (r : WithBot ℕ∞))
    (s : Spec (.of R)) :
    fiberSupportDimension f F hF s ≤ ((r : ℤ) : EInt) := by
  let : F.IsFiniteType := hF.isFiniteType
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact fiberModule_schemeDeltaDimension_le f F r
    (fun t ↦ Stacks.RelativeAssassin.topologicalKrullDim_supp_fiber_le_of_generic f F hflat
      (genericPoint (Spec (.of R)))
      ((IrreducibleSpace.isIrreducible_univ (Spec (.of R))).isGenericPoint_genericPoint
        isClosed_univ)
      (r : WithBot ℕ∞) hK t)
    s

/-- The `[Z]`-coefficient comparison of Stacks 0H4I at a point `x` of the special fibre of
delta-dimension `r` lying in the support: the sum over the points of the generic fibre of
delta-dimension `r` of the multiplicity of `F_K` there times the coefficient at `x` of the
specialized fundamental cycle is the coefficient of `[F_kappa]_r` at `x`. Writing `A` for the
local ring of `X` at the image of `x`, `M` for the stalk of `F` there and `pi` for a regular
parameter cutting out the fibre, the left side is
`sum_i length_A (A/(pi, q_i)) * length_{A_{q_i}} M_{q_i}` over the minimal primes of the support
of `M`, and the right side is `length_A (M / pi M)`; the identity is Stacks 02QG. -/
private theorem tsum_specializationCoeff_eq_fiberCycle_apply_of_mem_supp {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent)
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : fiberSupportDimension f F hF (genericPoint (Spec (.of R))) ≤ ((r : ℤ) : EInt))
    (hs : fiberSupportDimension f F hF (IsLocalRing.closedPoint R) ≤ ((r : ℤ) : EInt))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hδx : fiberPointDimension f (IsLocalRing.closedPoint R) x = (r : ℤ))
    (hx : x ∈ SheafOfModules.supp (fiberModule f F (IsLocalRing.closedPoint R))) :
    (∑' b : {ξ : f.fiber (genericPoint (Spec (.of R))) //
        fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)},
      (open Classical in
        if b.1 ∈ SheafOfModules.supp (fiberModule f F (genericPoint (Spec (.of R)))) then
          Stacks.Chow.sheafMultiplicity (fiberModule f F (genericPoint (Spec (.of R)))) b.1
        else 0) * specializationCoeff f r b.1 x) =
      (fiberCycle f F hF r (IsLocalRing.closedPoint R) hs :
        AlgebraicCycle (f.fiber (IsLocalRing.closedPoint R)) ℤ) x := by
  classical
  let η := genericPoint (Spec (.of R))
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let C := fieldChowSituation ((Spec (.of R)).residueField s)
  let g := f.fiberToSpecResidueField s
  let G := fiberModule f F s
  have : F.IsFiniteType := hF.isFiniteType
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hG : G.IsCoherent := fiberModule_isCoherent f F s
  have : G.IsFiniteType := hG.isFiniteType
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hbound : Stacks.Chow.schemeDeltaDimension C
      ((@reducedSupport _ G hG).subschemeι ≫ g) ≤ ((r : ℤ) : EInt) := by
    simpa [fiberSupportDimension, C, g, s, G] using
      hs
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨Z, hZ⟩ := @Stacks.Chow.isGenericPoint_component_supp_of_relativeDimension_eq
    _ C g _ G hG (r : ℤ) x hbound hx hδx
  have hfinite := @Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp
    _ _ G hG Z x hZ
  let z := f.fiberι s x
  let A := X.presheaf.stalk z
  let M := F.presheaf.stalk z
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val z
  have : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F z
  obtain ⟨a, ha, hreg, hker⟩ := exists_regular_fiber_parameter f F hflat x
  rw [fiberCycle_apply f F hF r s hs x hδx,
    ite_eq_left (show x ∈ SheafOfModules.supp (fiberModule f F s) from hx),
    length_pullback_stalk (f.fiberι s) F x]
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : Module ((f.fiber s).presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (f.fiber s).presheaf) G.val x
  have hlen := length_pullback_stalk_eq_length_quotient (f.fiberι s) F x
  dsimp only at hlen
  rw [hker, Submodule.ideal_span_singleton_smul a (⊤ : Submodule A M)] at hlen ⊢
  have hfinQ : IsFiniteLength A (QuotSMulTop a M) := by
    apply Module.length_ne_top_iff.mp
    rw [← hlen]
    exact Module.length_ne_top_iff.mpr hfinite
  have : Nontrivial M := by
    have hz : z ∈ SheafOfModules.supp F := by
      rwa [Stacks.Modules.supp_pullback] at hx
    exact not_subsingleton_iff_nontrivial.mp fun h ↦ by
      obtain ⟨m, hm⟩ := hz
      exact hm (h.elim _ _)
  have : Nontrivial (QuotSMulTop a M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M ha
  have hdimQ : Module.supportDim A (QuotSMulTop a M) = 0 :=
    supportDim_eq_zero_of_isFiniteLength hfinQ
  have hadd := local_length_additivity_of_regular_parameter a ha hreg hdimQ
  rw [hadd]
  let P := {p : PrimeSpectrum A // Minimal (· ∈ Module.support A M) p}
  let B := {ξ : f.fiber η // fiberPointDimension f η ξ = (r : ℤ)}
  let t : B → ℤ := fun b ↦
    (if b.1 ∈ SheafOfModules.supp (fiberModule f F η) then
      Stacks.Chow.sheafMultiplicity (fiberModule f F η) b.1 else 0) *
        specializationCoeff f r b.1 x
  obtain ⟨e, he⟩ := exists_minimalSupportEquiv_genericFiber f F hF r hK x hδx a hker hreg
  let b : P → B := fun p ↦ ⟨(e p).1, (e p).2.1⟩
  have hb : Function.Injective b := fun p q hpq ↦
    e.injective (Subtype.ext (congrArg (fun v : B ↦ v.1) hpq))
  have ht : Function.support t ⊆ Set.range b := by
    intro ξ hξ
    have hn : t ξ ≠ 0 := hξ
    have hξsupp : ξ.1 ∈ SheafOfModules.supp (fiberModule f F η) := by
      by_contra h
      simp [t, h] at hn
    have hξspec : f.fiberι η ξ.1 ⤳ z :=
      specializationCycleCoeff_ne_zero_specializes f r ξ.1 x
        (right_ne_zero_of_mul hn)
    exact ⟨e.symm ⟨ξ.1, ξ.2, hξsupp, hξspec⟩,
      Subtype.ext (congrArg (fun v ↦ v.1) (e.apply_symm_apply ⟨ξ.1, ξ.2, hξsupp, hξspec⟩))⟩
  have hsumfin : (∑ᶠ p ∈ {p : PrimeSpectrum A | Minimal (· ∈ Module.support A M) p},
      Module.length A (A ⧸ (Ideal.span {a} ⊔ p.asIdeal)) *
        Module.length (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) ≠ ⊤ := by
    rw [← hadd]
    exact Module.length_ne_top_iff.mpr hfinQ
  change (∑' ξ : B, t ξ) = _
  calc
    _ = ∑' p : P, t (b p) := (hb.tsum_eq ht).symm
    _ = ∑' p : P,
        ((Module.length A (A ⧸ (Ideal.span {a} ⊔ p.1.asIdeal))).toNat : ℤ) *
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule p.1.asIdeal.primeCompl M)).toNat : ℤ) := by
      apply tsum_congr
      intro p
      change (if (e p).1 ∈ SheafOfModules.supp (fiberModule f F η) then
        Stacks.Chow.sheafMultiplicity (fiberModule f F η) (e p).1 else 0) *
          specializationCoeff f r (e p).1 x = _
      rw [ite_eq_left (e p).2.2.1,
        sheafMultiplicity_genericFiber_eq_localized_length f F z (e p).1 p.1 (he p).symm,
        specializationCycleCoeff_eq_length_quotient f F hF r
          hs
          (e p).1 (e p).2.2.1 x hδx p.1 (he p).symm a hker]
      exact mul_comm _ _
    _ = _ := (toNat_finsum_mul_eq_tsum _ (finite_minimal_support (R := A) (M := M))
      (fun p ↦ Module.length A (A ⧸ (Ideal.span {a} ⊔ p.asIdeal)))
      (fun p ↦ Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) hsumfin).symm

private theorem specializationCycle_fiberCycle {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (F : X.Modules) (hF : F.IsCoherent)
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : fiberSupportDimension f F hF (genericPoint (Spec (.of R))) ≤ ((r : ℤ) : EInt))
    (hs : fiberSupportDimension f F hF (IsLocalRing.closedPoint R) ≤ ((r : ℤ) : EInt)) :
    specializationCycle f r (fiberCycle f F hF r (genericPoint (Spec (.of R))) hK) =
      fiberCycle f F hF r (IsLocalRing.closedPoint R) hs := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  have hloc := hasSum_specializationCycle f r
    (fiberCycle f F hF r (genericPoint (Spec (.of R))) hK) x
  rw [← hloc.tsum_eq]
  let η := genericPoint (Spec (.of R))
  have hterm : ∀ b : {ξ : f.fiber η //
      fiberPointDimension f η ξ = (r : ℤ)},
      (fiberCycle f F hF r η hK : AlgebraicCycle (f.fiber η) ℤ) b.1 *
        (specializationCycle f r (integralGenericCycle f r b.1) :
            AlgebraicCycle (f.fiber (IsLocalRing.closedPoint R)) ℤ) x =
      (if b.1 ∈ SheafOfModules.supp (fiberModule f F η) then
        Stacks.Chow.sheafMultiplicity (fiberModule f F η) b.1 else 0) *
          specializationCoeff f r b.1 x := by
    intro b
    have hb := b.2
    calc
      _ = (if b.1 ∈ SheafOfModules.supp (fiberModule f F η) then
          Stacks.Chow.sheafMultiplicity (fiberModule f F η) b.1 else 0) *
            (specializationCycle f r (integralGenericCycle f r b.1) :
                AlgebraicCycle (f.fiber (IsLocalRing.closedPoint R)) ℤ) x := by
        rw [fiberCycle_apply f F hF r η hK b.1 hb]
      _ = _ := by
        rw [specializationCycle_integralGenericCycle_coeff f r b.1 hb x]
  rw [tsum_congr hterm]
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let C := fieldChowSituation
    ((Spec (.of R)).residueField s)
  let g := f.fiberToSpecResidueField s
  have : F.IsFiniteType := hF.isFiniteType
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hsum : (∀ b : {ξ : f.fiber η // fiberPointDimension f η ξ = (r : ℤ)},
      b.1 ∈ SheafOfModules.supp (fiberModule f F η) → specializationCoeff f r b.1 x = 0) →
      (∑' b : {ξ : f.fiber η // fiberPointDimension f η ξ = (r : ℤ)},
        (if b.1 ∈ SheafOfModules.supp (fiberModule f F η) then
            Stacks.Chow.sheafMultiplicity (fiberModule f F η) b.1 else 0) *
          specializationCoeff f r b.1 x) = 0 := fun h ↦ by
    refine (tsum_congr fun b ↦ ?_).trans tsum_zero
    by_cases hb : b.1 ∈ SheafOfModules.supp (fiberModule f F η)
    · simp [hb, h b hb]
    · simp [hb]
  by_cases hδx : relativeDimension C.dimensionFunction g x = (r : ℤ)
  · by_cases hx : x ∈ SheafOfModules.supp (fiberModule f F s)
    · exact tsum_specializationCoeff_eq_fiberCycle_apply_of_mem_supp f F hF hflat r hK hs x
        hδx hx
    · rw [hsum fun b hb ↦ by_contra fun hn ↦ hx <| by
          have hspec := specializationCycleCoeff_ne_zero_specializes f r b.1 x hn
          have hbtotal : f.fiberι η b.1 ∈ SheafOfModules.supp F := by
            rwa [Stacks.Modules.supp_pullback] at hb
          have hxtotal : f.fiberι s x ∈ SheafOfModules.supp F :=
            closure_minimal (Set.singleton_subset_iff.mpr hbtotal)
              (SheafOfModules.isClosed_supp F) (specializes_iff_mem_closure.mp hspec)
          rwa [Stacks.Modules.supp_pullback],
        fiberCycle_apply f F hF r s hs x hδx]
      exact (ite_eq_right hx).symm
  · rw [hsum fun b _ ↦ by_contra fun hn ↦
      hδx (specializationCycleCoeff_ne_zero_dimension f r b.1 x hn)]
    by_contra hn
    exact hδx (relativeDimension_eq_of_cycle_coeff_ne_zero C g (r : ℤ)
      (fiberCycle f F hF r s hs) x (Ne.symm hn))

end Stacks.Chow.ModuleSpecialization

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType]
  [F.IsQuasicoherent]

omit [IsDiscreteValuationRing R] in
/-- **Stacks Project, Tag 0H3X** over a discrete valuation ring: for a module flat over `R` the
bound on the dimension of the support of the generic fibre holds on every fibre, which is what
the family of cycles of Stacks 0H4Q consumes. -/
theorem topologicalKrullDim_supp_fiberModule_le_of_genericFibre
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (genericPoint (Spec (.of R))))).obj F)) ≤
        (r : WithBot ℕ∞)) (s : Spec (.of R)) :
    topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
      (r : WithBot ℕ∞) :=
  Stacks.RelativeAssassin.topologicalKrullDim_supp_fiber_le_of_generic f F hflat
    (genericPoint (Spec (.of R)))
    ((IrreducibleSpace.isIrreducible_univ (Spec (.of R))).isGenericPoint_genericPoint
      isClosed_univ)
    (r : WithBot ℕ∞) hK s

/-- **Stacks Project, Tag 0H4I.** Let `R` be a discrete valuation ring with fraction field `K`
and residue field `kappa`, let `X` be a scheme locally of finite type over `R`, let `r >= 0` and
let `F` be a coherent `O_X`-module flat over `R`. If `dim(Supp(F_K)) <= r`, then
`dim(Supp(F_kappa)) <= r`. -/
@[stacks 0H4I "the dimension bound on the special fibre"]
theorem topologicalKrullDim_supp_fiberModule_closedPoint_le
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (genericPoint (Spec (.of R))))).obj F)) ≤
        (r : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (IsLocalRing.closedPoint R))).obj F)) ≤
      (r : WithBot ℕ∞) :=
  topologicalKrullDim_supp_fiberModule_le_of_genericFibre f F hflat r hK
    (IsLocalRing.closedPoint R)

/-- **Stacks Project, Tag 0H4I.** Let `R` be a discrete valuation ring with fraction field `K`
and residue field `kappa`, let `X` be a scheme locally of finite type over `R`, let `r >= 0` and
let `F` be a coherent `O_X`-module flat over `R` with `dim(Supp(F_K)) <= r`. Then the
specialization map `sp_{X/R} : Z_r(X_K) -> Z_r(X_kappa)` carries `[F_K]_r` to `[F_kappa]_r`:
the member over the generic point of the family of cycles `[F/X/Spec R]_r` specializes to its
member over the closed point. -/
@[stacks 0H4I "the specialization formula"]
theorem specializationCycle_familyAssociatedToModule
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) (r : ℕ)
    (hK : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (genericPoint (Spec (.of R))))).obj F)) ≤
        (r : WithBot ℕ∞)) :
    specializationCycle f r
        (familyAssociatedToModule f F r
          (topologicalKrullDim_supp_fiberModule_le_of_genericFibre f F hflat r hK)
          (genericPoint (Spec (.of R)))) =
      familyAssociatedToModule f F r
        (topologicalKrullDim_supp_fiberModule_le_of_genericFibre f F hflat r hK)
        (IsLocalRing.closedPoint R) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let hF : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType F
  exact ModuleSpecialization.specializationCycle_fiberCycle f F hF hflat r
    (ModuleSpecialization.fiberSupportDimension_le_of_genericFibre f F hF hflat r hK
      (genericPoint (Spec (.of R))))
    (ModuleSpecialization.fiberSupportDimension_le_of_genericFibre f F hF hflat r hK
      (IsLocalRing.closedPoint R))

end Stacks.Chow

end
