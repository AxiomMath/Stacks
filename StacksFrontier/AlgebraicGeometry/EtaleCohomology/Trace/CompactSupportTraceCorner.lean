module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat

/-!
# The vanishing of the trace of `π_X^*` from the primary factors of the coefficients

The last bullet of Step 3 of the proof of [Stacks, Tag 03UG] reduces the trace formula for a
finite ring `Λ` with `#Λ ∈ k^*` to rings `Λ` killed by a power of a prime `ℓ ∈ k^*`. Indeed `Λ`
is a finite product of such rings: for a central idempotent `e` of `Λ`, every sheaf `F` of
`Λ`-modules is the direct sum `eF ⊕ (1 - e)F`, the trace is additive (Step 1), and the trace over
`Λ` of the restriction of scalars of a sheaf of `eΛ`-modules is the image of its trace over `eΛ`.

## Main results

* `Stacks.EtaleCohomology.compactSupportTraceVanishes_cornerRestrict`:
  the vanishing over a corner `eΛ` gives the vanishing over `Λ` for the restriction of scalars.
* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_corners`:
  the vanishing for `eF` and `(1 - e)F` gives the vanishing for `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

section Corner

variable {Λ : Type} [Ring Λ] {e : Λ} (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a)

/-- **The vanishing over a corner gives the vanishing over `Λ`.** For a central idempotent `e`
of `Λ` and a sheaf `G` of `eΛ`-modules, if `RΓ_c(X_k̄, G)` is perfect over `eΛ` with
`Tr(π_X^*) = 0`, then `RΓ_c(X_k̄, G)` is perfect over `Λ` with `Tr(π_X^*) = 0`, `G` being viewed
as a sheaf of `Λ`-modules by restriction of scalars. -/
theorem compactSupportTraceVanishes_cornerRestrict
    (G : EtaleModules.{u, 0} he.Corner X)
    (h : CompactSupportTraceVanishes he.Corner kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G)) :
    CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((etaleModuleRestrictScalars (cornerRingHom he hc) X).obj G)) := by
  obtain ⟨hG, hGt⟩ := h
  obtain ⟨hR, hRt⟩ := perfectDerivedTrace_canonicalCompactSupportFrobenius_restrictScalars
    (cornerRingHom he hc) f j kbar p q hcard (preservesFiniteProjective_cornerRestrict he hc) _ hG
  let E := (singlePlusFunctorCompMapCochainComplexPlusIso
    (etaleModuleRestrictScalars (cornerRingHom he hc) X)).app G
  have hP := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ f j kbar E hR
  unfold CompactSupportTraceVanishes
  exact ⟨hP, (perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso Λ f j kbar p q hcard E
    hR hP).symm.trans (hRt.trans (by rw [hGt, map_zero]))⟩

include he hc in
/-- **The splitting `F = eF ⊕ (1 - e)F`**, as a split short complex
`0 → eF → F → (1 - e)F → 0` of sheaves of `Λ`-modules. -/
def cornerShortComplex (F : EtaleModules.{u, 0} Λ X) : ShortComplex (EtaleModules.{u, 0} Λ X) :=
  ShortComplex.mk ((sheafCornerι.{u + 1} he hc X.smallEtaleTopology).app F)
    ((sheafCornerπ.{u + 1} he.one_sub (fun a => ((Commute.one_right a).sub_right (hc a)).eq)
      X.smallEtaleTopology).app F) (by
      ext U m
      apply Subtype.ext
      change (1 - e) • (m : cornerSubmodule hc _).1 = 0
      rw [sub_smul, one_smul, show e • (m : cornerSubmodule hc _).1 = m.1 from m.2, sub_self])

include he hc in
/-- The short complex `0 → eF → F → (1 - e)F → 0` is split. -/
def cornerShortComplexSplitting (F : EtaleModules.{u, 0} Λ X) :
    (cornerShortComplex he hc F).Splitting where
  r := (sheafCornerπ.{u + 1} he hc X.smallEtaleTopology).app F
  s := (sheafCornerι.{u + 1} he.one_sub (fun a => ((Commute.one_right a).sub_right (hc a)).eq)
    X.smallEtaleTopology).app F
  f_r := congrArg (fun t => NatTrans.app t F) (sheafCornerι_π.{u + 1} he hc X.smallEtaleTopology)
  s_g := congrArg (fun t => NatTrans.app t F)
    (sheafCornerι_π.{u + 1} he.one_sub (fun a => ((Commute.one_right a).sub_right (hc a)).eq)
      X.smallEtaleTopology)
  id := by
    ext U m
    change e • m + (1 - e) • m = m
    rw [← add_smul, add_sub_cancel, one_smul]

/-- **The vanishing for `eF` and `(1 - e)F` gives the vanishing for `F`** (Step 1 of the proof of
[Stacks, Tag 03UG] along the split sequence `0 → eF → F → (1 - e)F → 0`). -/
theorem compactSupportTraceVanishes_of_corners [Finite Λ]
    (F : EtaleModules.{u, 0} Λ X)
    (h₁ : CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (cornerShortComplex he hc F).X₁))
    (h₃ : CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (cornerShortComplex he hc F).X₃)) :
    CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) := by
  obtain ⟨hp₁, ht₁⟩ := h₁
  obtain ⟨hp₃, ht₃⟩ := h₃
  let S := (cornerShortComplex he hc F).map (CochainComplex.singleFunctor _ 0)
  have hS : S.ShortExact := ((cornerShortComplexSplitting he hc F).map _).shortExact
  have hp₂ := isPerfect_compactSupportFrobeniusCohomology_X₂ Λ f j kbar hS
    (CochainComplex.plus_singleFunctor_obj _) (CochainComplex.plus_singleFunctor_obj _)
    (CochainComplex.plus_singleFunctor_obj _) hp₁ hp₃
  unfold CompactSupportTraceVanishes
  exact ⟨hp₂, (canonicalCompactSupportLefschetzNumber_X₂_eq_add Λ f j kbar p q hcard hS
    (CochainComplex.plus_singleFunctor_obj _) (CochainComplex.plus_singleFunctor_obj _)
    (CochainComplex.plus_singleFunctor_obj _) hp₁ hp₂ hp₃).trans
      ((congrArg₂ (· + ·) ht₁ ht₃).trans (add_zero 0))⟩

end Corner

end Stacks.EtaleCohomology

end
