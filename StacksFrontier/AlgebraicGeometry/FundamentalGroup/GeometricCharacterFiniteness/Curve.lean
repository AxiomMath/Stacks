module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportCoeffaceable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricCharacterFiniteness.CoinducedCharacters
public import StacksFrontier.NumberTheory.TraceFormula.GeometricMonodromyFiniteness

/-!
# Finitely many `𝔽_ℓ`-characters on open subgroups of `π₁(X_k̄)` for a curve

Let `X` be a smooth, proper, geometrically irreducible curve over a field `k`, `K` an algebraic
closure of `k` and `ℓ` a prime invertible in `k`. For every open subgroup `V` of the geometric
fundamental group `π₁(X_K, x)` there are only finitely many continuous homomorphisms
`V → ℤ/ℓ`.

Geometrically, `V` is the fundamental group of a finite étale cover `Y` of `X_K`, a smooth proper
curve over `K`, and the homomorphisms are `H¹(Y, ℤ/ℓ)`, which is finite (Tag 03RQ). The proof
here stays on `X`: since `π₁(X_K) → π₁(X)` is a topological embedding (Tag 0BTX), `V` contains
`N = φ⁻¹(H)` for an open normal subgroup `H` of `π₁(X)`, and the characters of `V` are finite in
number as soon as those of `N` are
(`Stacks.GroupCohomology.finite_continuous_monoidHom_of_le`). Characters of `N` inject into
`H¹(π₁(X_K), Coind_H 𝔽_ℓ)` through their Shapiro cocycles
(`Stacks.GroupCohomology.finite_continuous_monoidHom_comap_of_finite`). That group is
`H¹(X_K, ℱ_{Coind_H 𝔽_ℓ})` (`AlgebraicGeometry.bijective_geometricComparison_app_one`), which is
finite (`AlgebraicGeometry.finite_and_natCard_compactSupportRepresentationHomology_one_le`).

## Main results

* `AlgebraicGeometry.finite_continuous_monoidHom_multiplicative_zmod_of_isOpen` — the finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
  Stacks.Frobenius

universe u

/-- Sheafification for sheaves of `Λ`-modules at the module universe `u + 1`, pinned. -/
local instance (priority := 3000) etaleModulesHasSheafifyCharacterFiniteness (Λ : Type) [Ring Λ]
    (Y : AlgebraicGeometry.Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Stacks.EtaleCohomology.etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules at coefficient universe `0`, pinned. -/
local instance (priority := 3000) etaleModulesEnoughInjectivesCharacterFiniteness (Λ : Type)
    [Ring Λ] (Y : AlgebraicGeometry.Scheme.{u}) :
    EnoughInjectives (Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ Y) :=
  Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, 0} Λ Y

namespace AlgebraicGeometry

open Stacks.TraceFormula in
/-- The geometric curve of a geometrically irreducible scheme is connected; pinned, since the
general search for this instance runs out of heartbeats here. -/
local instance (priority := 3000) connectedSpace_geometricBaseChange_of_geometricallyIrreducible
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIrreducible f] : ConnectedSpace (geometricBaseChange k K f) :=
  have := geometricallyConnected_of_geometricallyIrreducible f
  connectedSpace_fieldBaseChange f K

open Stacks.TraceFormula in
/-- **Finitely many `𝔽_ℓ`-characters on an open subgroup of `π₁(X_K)`.** For a smooth, proper,
geometrically irreducible curve `X` over a field `k`, an algebraic closure `K` of `k`, a prime `ℓ`
invertible in `k`, a geometric point `x` of `X_K` and an open subgroup `V` of `π₁(X_K, x)`, there
are only finitely many continuous homomorphisms `V → ℤ/ℓ`. -/
theorem finite_continuous_monoidHom_multiplicative_zmod_of_isOpen
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f]
    [Smooth f] [IsProper f]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (x : GeometricPoint (geometricBaseChange k K f))
    (V : Subgroup (EtaleFundamentalGroup (geometricBaseChange k K f) x))
    (hV : IsOpen (V : Set (EtaleFundamentalGroup (geometricBaseChange k K f) x))) :
    Finite {χ : V →* Multiplicative (ZMod ℓ) // Continuous χ} := by
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have := geometricallyConnected_of_geometricallyIrreducible f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let B := BigEtaleSite.containing X
  let X' : B.Scheme := ⟨X, BigEtaleSite.contains_containing X⟩
  have : ConnectedSpace X'.1 := connectedSpace_of_isCurve B X' f
  have : CompactSpace X'.1 := ‹CompactSpace X›
  have : QuasiSeparatedSpace X'.1 := ‹QuasiSeparatedSpace X›
  have : ConnectedSpace (fieldBaseChange (Over.mk f) K) := connectedSpace_fieldBaseChange f K
  have hK := contains_fieldBaseChange_of_isCurve B X' f K
  let y : GeometricPoint (fieldBaseChange (Over.mk f) K) := x
  have := compactSpace_etaleFundamentalGroup _ y
  have := totallyDisconnectedSpace_etaleFundamentalGroup _ y
  have := compactSpace_etaleFundamentalGroup _ (y.map (fieldBaseChangeObjProj B X' f K hK).hom)
  have := totallyDisconnectedSpace_etaleFundamentalGroup _
    (y.map (fieldBaseChangeObjProj B X' f K hK).hom)
  let φ := geometricFundamentalGroupMap B X' f K hK y
  have hφ : Topology.IsInducing φ := isInducing_geometricFundamentalGroupMap B X' f K hK y
  -- an open normal subgroup `H` of `π₁(X)` with `φ⁻¹(H) ≤ V`
  obtain ⟨U, hU, hUV⟩ := hφ.isOpen_iff.1 hV
  have h1U : (1 : EtaleFundamentalGroup X'.1
      (y.map (fieldBaseChangeObjProj B X' f K hK).hom)) ∈ U := by
    have : (1 : EtaleFundamentalGroup _ y) ∈ φ ⁻¹' U := by rw [hUV]; exact V.one_mem
    simpa using this
  obtain ⟨H, hHU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U
  let H' : OpenSubgroup (EtaleFundamentalGroup X'.1
    (y.map (fieldBaseChangeObjProj B X' f K hK).hom)) := H.toOpenSubgroup
  have : H'.toSubgroup.Normal := H.isNormal'
  have hNV : (H' : Subgroup _).comap φ.toMonoidHom ≤ V := by
    intro g hg
    have : g ∈ φ ⁻¹' U := hHU hg
    rwa [hUV] at this
  -- `H¹(π₁(X_K), Coind_H 𝔽_ℓ)` is finite
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓK : (ℓ : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k K)]
    exact (map_ne_zero _).2 hℓ
  have hΛ : IsUnit ((Nat.card (ZMod ℓ) : ℕ) : K) := by
    rw [Nat.card_zmod]
    exact hℓK.isUnit
  obtain ⟨-, hfin, -⟩ := finite_and_natCard_compactSupportRepresentationHomology_one_le B X' f K
    (ZMod ℓ) y (CompactificationOf.ofProper f) hΛ H' (zmodCoefficient.{u + 1} ℓ)
  let P := (finiteTypeContinuousModuleCoind (ZMod ℓ) H').obj
    ((finiteTypeContinuousModuleTrivial (ZMod ℓ) _).obj (zmodCoefficient.{u + 1} ℓ))
  have hbij := bijective_geometricComparison_app_one B X' (ZMod ℓ) f K hK y P
  have hgrp : Finite (((invariantsDelta.{0, u + 1, u + 1} (ZMod ℓ)
      (G := EtaleFundamentalGroup _ y)).functor 1).obj (coinducedZModRes ℓ φ H')) :=
    Finite.of_injective _ hbij.1
  exact finite_continuous_monoidHom_of_le hNV (H'.isOpen.preimage φ.continuous)
    (finite_continuous_monoidHom_comap_of_finite ℓ φ H' hgrp)

end AlgebraicGeometry

end
