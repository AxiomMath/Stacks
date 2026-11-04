module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibrationTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibrationGeometry
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaOfCore
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension

/-!
# The trace formula for `D_ctf` in every dimension

Let `X` be a scheme separated of finite type over a finite field `k`, `Λ` a finite ring
(possibly noncommutative) with `#Λ` invertible in `k`, and `K` a bounded below complex on
`X_étale` whose class lies in `D_ctf(X, Λ)`. Then `RΓ_c(X_k̄, K)` is perfect and

`∑_{x ∈ X(k)} Tr(π_x | K_x̄) = Tr(π_X^* | RΓ_c(X_k̄, K))`

in `Λ^♮`. That `R π_*` preserves `D_ctf` along proper morphisms, the proposition
`Stacks.EtaleCohomology.ProperDirectImageCtfInput`, is a hypothesis.

## Main results

* `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_openClosed_step`: the
  trace formula on a compactification of `X` from the trace formula for an open `U ⊆ X` and on
  the closed subschemes of `X` disjoint from `U`.
* `cohomologicalTraceFormula_extensionByZero_of_isCtf_of_isSeparated_of_properDirectImageCtfInput`:
  `T''(X̄, j_! K) = T'(X̄, j_! K)` for every compactification.
* `perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated_of_`
  `properDirectImageCtfInput`:
  the trace formula of [Stacks, Tag 03V3].

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  (B : BigEtaleSite.{u})

omit [Finite Λ] [Algebra.IsAlgebraic k kbar] in
/-- **The open and closed step.** Let `X` be separated of finite type over `k` with a
compactification `j : X ⟶ X̄`, and `u : U ⟶ X` an open immersion. If the trace formula holds on
`X̄` for every complex in `D_ctf(U, Λ)` extended by zero along `U ⟶ X̄`, and on every
compactification of every closed subscheme of `X` disjoint from `U` for every complex in `D_ctf`
extended by zero, then it holds on `X̄` for `j_! K`, for every `K` in `D_ctf(X, Λ)`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_openClosed_step
    (hk : B.Contains (Spec (.of k))) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] (hX : B.Contains X)
    (J : CompactificationOf (Over.mk f)) {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (hU : B.Contains U)
    (hUpart : ∀ (Ku : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
      (_ : IsCtf B (B.obj U hU) Λ (DerivedCategory.Q.obj Ku.obj)) (hKus : HasPerfectStalks Λ Ku),
      CohomologicalTraceFormula Λ kbar p q hcard (Over.mk (J.restrictOpen u).toBase)
        ((etaleModuleExtensionByZero.{u, 0} Λ
          (J.restrictOpen u).immersion).mapCochainComplexPlus.obj Ku)
        (hasPerfectStalks_extensionByZero Λ (J.restrictOpen u).immersion Ku hKus))
    (hrest : ∀ {X' : Scheme.{u}} (e : X' ⟶ X) [IsClosedImmersion e],
      (∀ x', e.base x' ∉ Set.range u.base) → ∀ (hX' : B.Contains X')
      (Jz : CompactificationOf (Over.mk (e ≫ f)))
      (K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X'))
      (_ : IsCtf B (B.obj X' hX') Λ (DerivedCategory.Q.obj K'.obj)) (hK's : HasPerfectStalks Λ K'),
      CohomologicalTraceFormula Λ kbar p q hcard (Over.mk Jz.toBase)
        ((etaleModuleExtensionByZero.{u, 0} Λ Jz.immersion).mapCochainComplexPlus.obj K')
        (hasPerfectStalks_extensionByZero Λ Jz.immersion K' hK's))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) (hKs : HasPerfectStalks Λ K) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace (Over.mk f).left := inferInstanceAs (CompactSpace X)
  have : CompactSpace J.space := QuasiCompact.compactSpace_of_compactSpace J.toBase
  have : QuasiSeparatedSpace J.space := quasiSeparatedSpace_of_quasiSeparated J.toBase
  have hXb : B.Contains J.space :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact J.toBase).trans_lt hk
  let j := u ≫ J.immersion
  let Zc : J.space.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hij : Set.range j.base = (Set.range Zc.subschemeι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  let Z : Over (Spec (.of k)) := Over.mk (Zc.subschemeι ≫ J.toBase)
  let i : Z ⟶ Over.mk J.toBase := Over.homMk Zc.subschemeι rfl
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion Zc.subschemeι)
  let N := (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K
  have hN : HasPerfectStalks Λ N := hasPerfectStalks_extensionByZero Λ J.immersion K hKs
  have hNc : IsCtf B (B.obj J.space hXb) Λ (DerivedCategory.Q.obj N.obj) :=
    isCtf_extensionByZero_of_isOpenImmersion B Λ J.immersion hX hXb K hK
  refine cohomologicalTraceFormula_of_openClosed Λ kbar p q hcard i j hij N hN ?_ ?_
  · let Ku := (etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj N
    have hKu : IsCtf B (B.obj U hU) Λ (DerivedCategory.Q.obj Ku.obj) :=
      (isCtf_inverseImage B Λ j hU hXb N hNc).of_iso B _ Λ (DerivedCategory.Q.mapIso
        ((NatIso.mapHomologicalComplex (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j) _).app
          N.obj))
    exact hUpart Ku hKu (hasPerfectStalks_restriction Λ j N hN)
  · let e := pullback.fst J.immersion Zc.subschemeι
    let s := pullback.snd J.immersion Zc.subschemeι
    have hrange (x' : ↥(pullback J.immersion Zc.subschemeι)) :
        e.base x' ∉ Set.range u.base := by
      rintro ⟨y, hy⟩
      have h₁ : j.base y ∈ Set.range j.base := ⟨y, rfl⟩
      rw [hij] at h₁
      refine h₁ ⟨s.base x', ?_⟩
      change (s ≫ Zc.subschemeι).base x' = (u ≫ J.immersion).base y
      rw [← pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hy]
    have hX' : B.Contains (pullback J.immersion Zc.subschemeι) :=
      (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (e ≫ f)).trans_lt hk
    have hs : s ≫ Zc.subschemeι ≫ J.toBase = e ≫ f := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, J.immersion_toBase]
    let Jz : CompactificationOf (Over.mk (e ≫ f)) :=
      ⟨StructuredArrow.mk (Y := Over.mk (Zc.subschemeι ≫ J.toBase))
        (Over.homMk (U := Over.mk (e ≫ f)) s hs),
        ⟨inferInstanceAs (IsOpenImmersion s),
          inferInstanceAs (IsProper (Zc.subschemeι ≫ J.toBase))⟩⟩
    let K' := (etaleModuleInverseImage.{u, 0} Λ e).mapCochainComplexPlus.obj K
    let e₂ : (etaleModuleInverseImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj N ≅
        (etaleModuleExtensionByZero.{u, 0} Λ s).mapCochainComplexPlus.obj K' :=
      ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
        (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ
          (IsPullback.of_hasPullback J.immersion Zc.subschemeι)) _).app K.obj).symm
    exact cohomologicalTraceFormula_of_iso Λ kbar p q hcard e₂.symm _ _
      (hrest e hrange hX' Jz K' (isCtf_inverseImage B Λ e hX' hX K hK)
        (isPerfect_stalk_inverseImage Λ e K hKs))

/-- `X` is covered by the images of `n` open immersions of affine schemes. -/
def HasAffineCoverOfCard (X : Scheme.{u}) (n : ℕ) : Prop :=
  ∃ (Y : Fin n → Scheme.{u}) (ι : ∀ i, Y i ⟶ X), (∀ i, IsOpenImmersion (ι i)) ∧
    (∀ i, IsAffine (Y i)) ∧ ∀ x, ∃ i, x ∈ Set.range (ι i).base

/-- A quasi-compact scheme is covered by finitely many affine schemes. -/
theorem exists_hasAffineCoverOfCard (X : Scheme.{u}) [CompactSpace X] :
    ∃ n, HasAffineCoverOfCard X n := by
  classical
  have hcov : (Set.univ : Set X) ⊆ ⋃ x, ((X.affineCover.f x).opensRange : Set X) := by
    intro x _
    have hx : x ∈ (⨆ i, (X.affineCover.f i).opensRange) := by
      rw [Scheme.OpenCover.iSup_opensRange]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    exact Set.mem_iUnion.2 hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((X.affineCover.f x).opensRange : Set X)) (fun x => (X.affineCover.f x).opensRange.2)
    hcov
  refine ⟨t.card, fun i => X.affineCover.X (t.equivFin.symm i).1,
    fun i => X.affineCover.f (t.equivFin.symm i).1, fun i => inferInstance,
    fun i => inferInstance, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, (congrArg (fun w : t => x ∈ Set.range (X.affineCover.f w.1).base)
    (t.equivFin.symm_apply_apply ⟨y, hy⟩)).mpr hxy⟩

/-- A closed subscheme of `X` missing the image of the first of `n + 1` affine opens covering `X`
is covered by `n` affine opens. -/
theorem hasAffineCoverOfCard_of_isClosedImmersion {X X' : Scheme.{u}} {n : ℕ}
    (Y : Fin (n + 1) → Scheme.{u}) (ι : ∀ i, Y i ⟶ X) (hι : ∀ i, IsOpenImmersion (ι i))
    (hY : ∀ i, IsAffine (Y i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (ι i).base) (e : X' ⟶ X)
    [IsClosedImmersion e] (hrange : ∀ x', e.base x' ∉ Set.range (ι 0).base) :
    HasAffineCoverOfCard X' n := by
  refine ⟨fun i => pullback (ι i.succ) e, fun i => pullback.snd (ι i.succ) e,
    fun i => have := hι i.succ; inferInstance,
    fun i => have := hY i.succ; isAffine_of_isAffineHom (pullback.fst (ι i.succ) e),
    fun x' => ?_⟩
  obtain ⟨i, hi⟩ := hcov (e.base x')
  induction i using Fin.cases with
  | zero => exact absurd hi (hrange x')
  | succ i =>
    exact ⟨i, by rwa [Scheme.Pullback.range_snd]⟩

variable {Λ kbar p q hcard B} in
/-- **The trace formula for `D_ctf` on a compactification.** For `X` of dimension at most `d`
covered by `n` affine opens, `T''(X̄, j_! K) = T'(X̄, j_! K)`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_isCtf_of_hasAffineCoverOfCard
    (hΛ : (Nat.card Λ : k) ≠ 0) (hctf : ProperDirectImageCtfInput B Λ)
    (hk : B.Contains (Spec (.of k))) (d : ℕ) :
    ∀ (n : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f]
      [QuasiCompact f] (hX : B.Contains X), topologicalKrullDim X ≤ d → HasAffineCoverOfCard X n →
      ∀ (J : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
        (_ : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) (hKs : HasPerfectStalks Λ K),
        CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
          ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
          (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
  intro n
  induction n with
  | zero =>
    intro X f _ _ _ hX _ hcov J K hK hKs
    obtain ⟨Y, ι, -, -, hcov⟩ := hcov
    have : IsEmpty X := ⟨fun x => (hcov x).choose.elim0⟩
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨fun s => isEmptyElim s.isIrreducible.nonempty.some⟩
    have hdim : topologicalKrullDim X ≤ 1 := by
      change Order.krullDim (TopologicalSpace.IrreducibleCloseds X) ≤ 1
      rw [Order.krullDim_eq_bot]
      exact bot_le
    exact cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf Λ kbar p q hcard
      (hΛ := hΛ) (curveTraceCore Λ k hΛ kbar p q hcard) B f hdim J K hX hK hKs
  | succ n IHn =>
    intro X f _ _ _ hX hdim hcov J K hK hKs
    by_cases hd : d ≤ 1
    · exact cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_isCtf Λ kbar p q hcard
        (hΛ := hΛ) (curveTraceCore Λ k hΛ kbar p q hcard) B f
        (hdim.trans (by exact_mod_cast hd)) J K hX hK hKs
    obtain ⟨Y, ι, hι, hY, hcov⟩ := hcov
    have := hι 0
    have := hY 0
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    let R := Γ(Y 0, ⊤)
    let u : Spec R ⟶ X := (Y 0).isoSpec.inv ≫ ι 0
    have : IsSeparated (u ≫ f) := by
      rw [← Spec.map_preimage (u ≫ f)]
      infer_instance
    have : QuasiCompact (u ≫ f) := by
      rw [← Spec.map_preimage (u ≫ f)]
      infer_instance
    have hU : B.Contains (Spec R) :=
      (Scheme.size_le_of_locallyOfFiniteType (u ≫ f)).trans_lt hk
    refine cohomologicalTraceFormula_extensionByZero_of_openClosed_step Λ kbar p q hcard B hk f hX
      J u hU ?_ ?_ K hK hKs
    · intro Ku hKu hKus
      let ψ : CommRingCat.of k ⟶ R := Spec.preimage (u ≫ f)
      have : LocallyOfFiniteType (Spec.map ψ) := by
        rw [Spec.map_preimage]
        infer_instance
      have hdimU : topologicalKrullDim (Spec R) ≤ (m : WithBot ℕ∞) + 1 :=
        u.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans (by exact_mod_cast hdim)
      obtain ⟨g, hg, hfib⟩ := exists_mvPolynomial_fibration R ψ m hdimU
      let fA := Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k)))
      have : LocallyOfFiniteType fA := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 inferInstance)
      let JA := (hasCompactification_of_compactSpace_quasiSeparatedSpace fA).choose
      have hA : B.Contains (Spec (.of (MvPolynomial (Fin m) k))) :=
        (Scheme.size_le_of_locallyOfFiniteType fA).trans_lt hk
      have hdimA : topologicalKrullDim (Spec (.of (MvPolynomial (Fin m) k))) ≤ (m : ℕ) := by
        change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin m) k)) ≤ _
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp
      have hcovA : HasAffineCoverOfCard (Spec (.of (MvPolynomial (Fin m) k))) 1 :=
        ⟨fun _ => _, fun _ => 𝟙 _, fun _ => inferInstance, fun _ => inferInstance,
          fun x => ⟨0, x, rfl⟩⟩
      exact cohomologicalTraceFormula_extensionByZero_of_fibration Λ kbar p q hcard B hΛ hctf
        (u ≫ f) fA (J.restrictOpen u) JA g (hg.trans (Spec.map_preimage _))
        (fun y hy _ a c h =>
          topologicalKrullDim_le_of_isPullback_of_isOpenImmersion g JA.immersion JA.toBase y hy
            hfib a c h)
        hU hA hk (fun KA hKA hKAs => IHd m (by omega) 1 fA hA hdimA hcovA JA KA hKA hKAs)
        Ku hKu hKus
    · intro X' e _ hrange hX' Jz K' hK' hK's
      refine IHn (e ≫ f) hX' (e.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
        (hasAffineCoverOfCard_of_isClosedImmersion Y ι hι hY hcov e (fun x' hx' => hrange x' ?_))
        Jz K' hK' hK's
      obtain ⟨z, hz⟩ := hx'
      refine ⟨(Y 0).isoSpec.hom.base z, ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable {Λ kbar p q hcard B} in
/-- **The trace formula `T''(X̄, j_! K) = T'(X̄, j_! K)` for `D_ctf` in every dimension.** For `X`
separated of finite type over `k`, lying in the big étale site, a compactification `j : X ⟶ X̄`
and a bounded below complex `K` whose class lies in `D_ctf(X, Λ)`, `RΓ(X̄_k̄, j_! K)` is perfect
and the trace of the geometric Frobenius on it is the sum of the local terms of `K` at the rational
points. -/
theorem cohomologicalTraceFormula_extensionByZero_of_isCtf_of_isSeparated_of_properDirectImageCtfInput
    (hΛ : (Nat.card Λ : k) ≠ 0) (hctf : ProperDirectImageCtfInput B Λ) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (J : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hX : B.Contains X) (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj))
    (hKs : HasPerfectStalks Λ K) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hKs) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hk : B.Contains (Spec (.of k)) := B.contains_spec_of_mk_lt _
    (lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) B.aleph0_lt_cutoff.le)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim X ≤ d := by
    have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
    generalize topologicalKrullDim X = t at hne ⊢
    induction t using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe t =>
      induction t using ENat.recTopCoe with
      | top => exact absurd rfl hne
      | coe n => exact ⟨n, le_rfl⟩
  obtain ⟨n, hn⟩ := exists_hasAffineCoverOfCard X
  exact cohomologicalTraceFormula_extensionByZero_of_isCtf_of_hasAffineCoverOfCard hΛ hctf hk d n f
    hX hd hn J K hK hKs

variable {Λ kbar p q hcard B} in
/-- **The trace formula for `D_ctf`.** Let `X` be a separated scheme of finite type over the finite
field `k`, lying in the big étale site `B`, with a compactification `j : X ⟶ X̄`; let `Λ` be a
finite ring (possibly noncommutative) with `#Λ` invertible in `k`, and `K` a bounded below complex
of sheaves of `Λ`-modules on `X_étale` whose class lies in `D_ctf(X, Λ)`. Then the stalks of `K`
and `RΓ_c(X_k̄, K)` are perfect and `Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)` in
`Λ^♮`.

That `R π_*` preserves `D_ctf` along proper morphisms is the hypothesis `hctf`
(`Stacks.EtaleCohomology.ProperDirectImageCtfInput`). -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated_of_properDirectImageCtfInput
    (hΛ : (Nat.card Λ : k) ≠ 0) (hctf : ProperDirectImageCtfInput B Λ) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [Fintype (rationalPoints f)] (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hX : B.Contains X)
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Q.obj K.obj)) :
    ∃ (hKs : HasPerfectStalks Λ K) (hperf : StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K))),
      perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard K)) =
        ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hKs (rationalGeometricPoint kbar x.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) := by
  have hKs := hasPerfectStalks_of_isCtf B hX Λ K hK
  exact ⟨hKs,
    perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_cohomologicalTraceFormula
      Λ kbar p q hcard f J K hKs
    (cohomologicalTraceFormula_extensionByZero_of_isCtf_of_isSeparated_of_properDirectImageCtfInput
      hΛ hctf f J K hX hK hKs)⟩

end Stacks.EtaleCohomology

end
