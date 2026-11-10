module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseStratumCharSeries
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExcisionCharSeries

/-!
# The trace formula for the regular descent sheaves from the trace formula

`Stacks.EtaleCohomology.RegularDescentTraceFormula` is the instance of the trace formula of
[Stacks, Tag 03V3] consumed by the lisse case of [Stacks, Tag 03UZ]: over every finite extension
`k'` of `k`, the trace of Frobenius on `RΓ_c` of the inverse image to `Z ×_k k'` of the regular
descent sheaf of a Galois covering is the sum of the local terms at the rational points. This file
derives it from the conclusion of the trace formula in the form in which it is stated, a finite
sum over the rational points with the perfectness of the stalks at all geometric points; the
set of rational points of `Z ×_k k'` is finite.

## Main results

* `Stacks.EtaleCohomology.finite_fieldValuedPoints`,
  `Stacks.EtaleCohomology.finite_rationalPoints_baseChange`.
* `Stacks.EtaleCohomology.regularDescentTraceFormula_of_traceFormula`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Finite

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [Finite K] [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- A scheme of finite type over a finite field has finitely many points with values in a finite
extension. -/
theorem finite_fieldValuedPoints : Finite (fieldValuedPoints f K) := by
  classical
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  set S := (closedPointsDegreeLE f (Module.finrank k K)).filter
    (fun x => residueDegree f x.1 ∣ Module.finrank k K)
  have hmem : ∀ (x : X) (σ : residueEmbeddings f K x),
      ∃ h : IsClosed ({x} : Set X), (⟨x, h⟩ : closedPoints X) ∈ S := by
    intro x σ
    obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f K x σ
    refine ⟨hc, Finset.mem_filter.2 ⟨?_, hd⟩⟩
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_of_dvd hpos hd
  let e : (Σ x : X, residueEmbeddings f K x) ≃ Σ y : S, residueEmbeddings f K y.1.1 :=
    { toFun := fun c => ⟨⟨⟨c.1, (hmem c.1 c.2).1⟩, (hmem c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : ∀ y : S, Finite (residueEmbeddings f K y.1.1) := by
    intro y
    refine Nat.finite_of_card_ne_zero ?_
    have hd := (Finset.mem_filter.1 y.2).2
    rw [natCard_residueEmbeddings, ite_eq_left hd]
    intro h0
    rw [h0, zero_dvd_iff] at hd
    omega
  exact Finite.of_equiv _ ((fieldValuedPointsEquiv f K).trans e).symm

/-- The base change of a scheme of finite type over a finite field to a finite extension has
finitely many rational points. -/
theorem finite_rationalPoints_baseChange :
    Finite (rationalPoints (pullback.snd f (specAlgebraMap k K))) := by
  have := finite_fieldValuedPoints f K
  exact Finite.of_equiv _ (rationalPointsBaseChangeEquiv f K).symm

/-- The order of the group ring `ℤ/ℓ^M[H]` is invertible in `k` when `ℓ` is. -/
theorem natCast_card_monoidAlgebra_zmod_ne_zero {k : Type*} [Field k] (ℓ M : ℕ) (H : Type)
    [Group H] [Finite H] (hℓ : ((ℓ : ℕ) : k) ≠ 0) :
    ((Nat.card (MonoidAlgebra (ZMod (ℓ ^ M)) H) : ℕ) : k) ≠ 0 := by
  have hl : ℓ ≠ 0 := fun h => hℓ (by rw [h, Nat.cast_zero])
  have : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ hl⟩
  have : Nat.card (MonoidAlgebra (ZMod (ℓ ^ M)) H) = (ℓ ^ M) ^ Nat.card H := by
    rw [Nat.card_congr (MonoidAlgebra.coeffEquiv.trans
        (Finsupp.equivFunOnFinite : (H →₀ ZMod (ℓ ^ M)) ≃ (H → ZMod (ℓ ^ M)))),
      Nat.card_fun, Nat.card_zmod]
  rw [this, Nat.cast_pow, Nat.cast_pow]
  exact pow_ne_zero _ (pow_ne_zero _ hℓ)

/-- **The base change of a contained scheme to a finite field extension is contained** in the
big étale site: `Spec k'` is countable, and the cutoff is closed under fibre products. -/
theorem contains_pullback_specAlgebraMap (B : BigEtaleSite.{u}) {k : Type u} [Field k]
    {Z : Scheme.{u}} (hZ : B.Contains Z) (fZ : Z ⟶ Spec (.of k)) (k' : Type u) [Field k']
    [Finite k'] [Algebra k k'] : B.Contains (pullback fZ (specAlgebraMap k k')) := by
  have hk' : (Spec (.of k')).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff)
  exact Scheme.size_pullback_lt _ _ hZ hk'

end Finite

/-- **The conclusion of the trace formula of [Stacks, Tag 03V3] for the regular descent sheaves**,
in the form in which Tag 03V3 states it: over every finite extension `k'` of `k` inside `k̄`, the
stalks of the inverse image to `Z ×_k k'` of the regular descent sheaf of `C` with coefficients
`ℤ/ℓ^M[H]` are perfect, `RΓ_c` of it is perfect, and the trace of Frobenius is the finite sum of
the local terms at the rational points. -/
def RegularDescentTraceFormulaConclusion {k : Type u} [Field k] [Fintype k]
    {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of k)) (J : CompactificationOf (Over.mk fZ)) (kbar : Type u)
    [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP kbar p]
    {H : Type} [Group H] [Fintype H] (C : EtaleGaloisCovering Z H) (ℓ M : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Algebra k' kbar]
  [IsScalarTower k k' kbar] [CharP k' p] (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * m))
  [Fintype (rationalPoints (pullback.snd fZ (specAlgebraMap k k')))],
  ∃ (hKs : ∀ s : GeometricPoint (pullback fZ (specAlgebraMap k k')),
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
    (((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj
        (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
          (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
            (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))
            (groupRingRightAction ℓ M H))).obj)))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
    (pullback.snd fZ (specAlgebraMap k k')) (compactificationFieldBaseChange fZ J k') kbar
    (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
      (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H)))))),
    perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H) ⟨_, hperf⟩
    (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
        (pullback.snd fZ (specAlgebraMap k k')) (compactificationFieldBaseChange fZ J k')
        kbar p (q * m) hcard'
        (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
          (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
            (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))
            (groupRingRightAction ℓ M H))))) =
      ∑ s : rationalPoints (pullback.snd fZ (specAlgebraMap k k')),
    perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H)
      ⟨_, hKs (rationalGeometricPoint kbar s.1)⟩ (DerivedCategory.Q.map
        (rationalPointStalkFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) kbar p
          (q * m) hcard' s.1
          (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
            (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
              (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))
              (groupRingRightAction ℓ M H)))))

/-- **The trace formula for the regular descent sheaves from the trace formula.** The hypothesis is
the conclusion of [Stacks, Tag 03V3] for the inverse image to `Z ×_k k'` of the regular descent
sheaf, over every finite extension `k'` of `k` inside `k̄`. -/
theorem regularDescentTraceFormula_of_traceFormula {k : Type u} [Field k] [Fintype k]
    {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType fZ] [QuasiCompact fZ]
    (J : CompactificationOf (Over.mk fZ)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP kbar p] {H : Type} [Group H] [Fintype H]
    (C : EtaleGaloisCovering Z H) (ℓ M : ℕ) [Fact ℓ.Prime]
    (h : RegularDescentTraceFormulaConclusion fZ J kbar p q C ℓ M) :
    RegularDescentTraceFormula fZ J kbar p q C ℓ M := by
  intro k' _ _ _ _ _ _ m hcard'
  have := finite_rationalPoints_baseChange fZ k'
  let := Fintype.ofFinite (rationalPoints (pullback.snd fZ (specAlgebraMap k k')))
  obtain ⟨hKs, hperf, htr⟩ := h k' m hcard'
  exact ⟨fun s => hKs _, hperf, htr.trans (finsum_eq_sum_of_fintype _).symm⟩

/-- **The trace formula of [Stacks, Tag 03V3] with coefficients `ℤ/ℓ^M[H]`, as stated**: over
every finite field `k' ⊆ k̄` in which the order of `ℤ/ℓ^M[H]` is invertible, for a bounded below
complex in `D_ctf` on a separated scheme of finite type contained in `B`, the stalks and `RΓ_c` are
perfect and the trace of Frobenius is the sum of the local terms at the rational points. -/
def GroupRingCtfTraceFormula (B : BigEtaleSite.{u}) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    (p : ℕ) [Fact p.Prime] [CharP kbar p] (ℓ M : ℕ) (H : Type) [Group H] [Fintype H] : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k' kbar] [Algebra.IsAlgebraic k' kbar]
    [CharP k' p] (q' : ℕ) (hcard : Fintype.card k' = p ^ q'),
  ((Nat.card (MonoidAlgebra (ZMod (ℓ ^ M)) H) : ℕ) : k') ≠ 0 →
  ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k')) [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact f] [Fintype (rationalPoints f)] (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) X))
    (hX : B.Contains X),
    IsCtf B (B.obj X hX) (MonoidAlgebra (ZMod (ℓ ^ M)) H) (DerivedCategory.Q.obj K.obj) →
    ∃ (hKs : ∀ s : GeometricPoint X,
        StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
          (((Scheme.pointSmallEtale s.hom).sheafFiber
            (A := ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))).mapHomologicalComplex
              (ComplexShape.up ℤ) |>.obj K.obj)))
      (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) f J kbar
          K))),
      perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H) ⟨_, hperf⟩
          (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) f J kbar
              p q' hcard K)) =
        ∑ s : rationalPoints f, perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H)
          ⟨_, hKs (rationalGeometricPoint kbar s.1)⟩ (DerivedCategory.Q.map
            (rationalPointStalkFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) kbar p q'
              hcard s.1 K))

/-- **The trace formula for the regular descent sheaves from the trace formula for complexes in
`D_ctf`.** The hypothesis `hTF` is the trace formula of [Stacks, Tag 03V3] with coefficients
`ℤ/ℓ^M[H]`, over every finite field `k' ⊆ k̄`, for a bounded below complex in `D_ctf` on a
separated scheme of finite type contained in the big étale site `B`. The inverse image of the
regular descent sheaf to `Z ×_k k'` is such a complex
(`Stacks.EtaleCohomology.isCtf_single_inverseImage_descentSheaf`), `Z ×_k k'` is contained in `B`,
and the order of `ℤ/ℓ^M[H]` is invertible in `k'` when `ℓ` is invertible in `k`. -/
theorem regularDescentTraceFormulaConclusion_of_isCtf (B : BigEtaleSite.{u}) {k : Type u}
    [Field k] [Fintype k] {Z : Scheme.{u}} (hZ : B.Contains Z) (fZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType fZ] [QuasiCompact fZ] [IsSeparated fZ]
    (J : CompactificationOf (Over.mk fZ)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
    [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (p q : ℕ) [Fact p.Prime] [CharP kbar p]
    {H : Type} [Group H] [Fintype H]
    (C : EtaleGaloisCovering Z H) (ℓ M : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : k) ≠ 0)
    (hTF : GroupRingCtfTraceFormula B kbar p ℓ M H) :
    RegularDescentTraceFormulaConclusion fZ J kbar p q C ℓ M := by
  intro k' _ _ _ _ _ _ m hcard' _
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  have hR : ((Nat.card (MonoidAlgebra (ZMod (ℓ ^ M)) H) : ℕ) : k') ≠ 0 := by
    rw [← map_natCast (algebraMap k k')]
    exact (map_ne_zero (algebraMap k k')).2 (natCast_card_monoidAlgebra_zmod_ne_zero ℓ M H hℓ)
  have hX := contains_pullback_specAlgebraMap B hZ fZ k'
  refine hTF k' (q * m) hcard' hR (pullback.snd fZ (specAlgebraMap k k'))
    (compactificationFieldBaseChange fZ J k')
    (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
      (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H))) hX ?_
  refine IsCtf.of_iso B _ _ (DerivedCategory.Q.mapIso (CochainComplex.Plus.ι _ |>.mapIso
    (singlePlusObjMapIso (etaleModuleInverseImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
      (pullback.fst fZ (specAlgebraMap k k')))
      (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H))))) ?_
  exact isCtf_single_inverseImage_descentSheaf B (MonoidAlgebra (ZMod (ℓ ^ M)) H)
    (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H) hX C
    (pullback.fst fZ (specAlgebraMap k k'))

end Stacks.EtaleCohomology
