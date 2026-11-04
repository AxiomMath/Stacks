module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmoothIrreducibleStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportEmpty
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExcisionCharSeries

/-!
# Dévissage of `det(1 - π^* T | RΓ_c)` along a closed filtration

Let `X` be a scheme over a finite field `k`, `s` a stratification of `X` whose strata are the
successive differences of a closed filtration `X = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y n = ∅`, and `G` a sheaf of
`Λ`-modules on `X_étale`. Suppose given power series `L i` such that, for every stratum, every
compactification of the open stratum `Y i \ Y (i + 1)` of `Y i`, `RΓ_c` of the restriction of `G`
to it is perfect and its characteristic series `c` satisfies `c · L i = 1`. Then for every
compactification of `X`, `RΓ_c(X_k̄, G)` is perfect and
`det(1 - π_X^* T | RΓ_c(X_k̄, G)) · ∏ᵢ L i = 1`.

The proof removes the strata one at a time by the excision of
`Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_excision`,
applied to the open stratum of `Y j` and its closed complement `Y (j + 1)`, with the
compactifications induced from one of `Y j`; the induction starts at the empty `Y n`
(`Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_of_isEmpty`),
and `X` itself is reached by excision of its closed subscheme `Y 0`, whose open complement is
empty. This is the dévissage of [Stacks, Tag 03UZ] to the strata.

## Main definitions

* `Stacks.EtaleCohomology.CompactSupportCharSeriesInverts`: `RΓ_c(X_k̄, G)` is perfect and
  `det(1 - π_X^* T | RΓ_c(X_k̄, G)) · L = 1`.

## Main results

* `Stacks.EtaleCohomology.compactSupportCharSeriesInverts_of_closedFiltration`: if every open
  stratum satisfies `CompactSupportCharSeriesInverts` with `L i`, then so does `X` with `∏ᵢ L i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Inverts

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`RΓ_c(X_k̄, G)` is perfect and its characteristic series is inverse to `L`**, for one
compactification `j` of `X`. -/
def CompactSupportCharSeriesInverts {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (j : CompactificationOf (Over.mk f)) (G : EtaleModules.{u, 0} Λ X) (L : PowerSeries Λ) :
    Prop :=
  ∃ hp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj G))),
    (CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj G))) :
        PowerSeries Λ) * L = 1

variable {Λ kbar p q hcard}

/-- The property is invariant under isomorphisms of sheaves. -/
theorem CompactSupportCharSeriesInverts.of_iso {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
    {j : CompactificationOf (Over.mk f)} {G G' : EtaleModules.{u, 0} Λ X} (e : G ≅ G')
    {L : PowerSeries Λ} (h : CompactSupportCharSeriesInverts Λ kbar p q hcard f j G L) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f j G' L := by
  obtain ⟨hp, hL⟩ := h
  let e' := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).mapIso e
  refine ⟨isPerfect_compactSupportFrobeniusCohomology_of_iso Λ f j kbar e' hp, ?_⟩
  rwa [← perfectDerivedCharSeries_canonicalCompactSupportFrobenius_congr Λ f j kbar p q hcard e'
    hp]

/-- The property for every compactification transports along an equality of structure
morphisms. -/
theorem compactSupportCharSeriesInverts_of_eq {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (.of k)}
    (h : f₁ = f₂) {G : EtaleModules.{u, 0} Λ X} {L : PowerSeries Λ}
    (H : ∀ j : CompactificationOf (Over.mk f₂), CompactSupportCharSeriesInverts Λ kbar p q hcard
      f₂ j G L) (j : CompactificationOf (Over.mk f₁)) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f₁ j G L := by
  subst h
  exact H j

/-- On an empty scheme the property holds with `L = 1`. -/
theorem compactSupportCharSeriesInverts_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (G : EtaleModules.{u, 0} Λ X) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f j G 1 := by
  refine ⟨isPerfect_compactSupportFrobeniusCohomology_of_isEmpty Λ f j kbar _, ?_⟩
  rw [perfectDerivedCharSeries_canonicalCompactSupportFrobenius_of_isEmpty, mul_one,
    Units.val_one]

/-- **Excision.** If the property holds on an open subscheme with `L₁` and on its closed
complement with `L₂`, for the induced compactifications, it holds on `X` with `L₁ · L₂`. -/
theorem CompactSupportCharSeriesInverts.excision {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [QuasiCompact f] (j : CompactificationOf (Over.mk f)) {Z U : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (jU : U ⟶ X) [IsOpenImmersion jU]
    (hij : Set.range jU.base = (Set.range i.base)ᶜ) (G : EtaleModules.{u, 0} Λ X)
    {L₁ L₂ : PowerSeries Λ}
    (hU : CompactSupportCharSeriesInverts Λ kbar p q hcard (jU ≫ f) (j.restrictOpen jU)
      ((etaleModuleRestriction.{u, 0} Λ jU).obj G) L₁)
    (hZ : CompactSupportCharSeriesInverts Λ kbar p q hcard (i ≫ f) (j.restrictClosed i)
      ((etaleModuleInverseImage.{u, 0} Λ i).obj G) L₂) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f j G (L₁ * L₂) := by
  obtain ⟨hpU, hLU⟩ := hU
  obtain ⟨hpZ, hLZ⟩ := hZ
  obtain ⟨hX, hc⟩ := perfectDerivedCharSeries_canonicalCompactSupportFrobenius_excision Λ f j i jU
    hij kbar p q hcard G hpU hpZ
  refine ⟨hX, ?_⟩
  rw [hc, Units.val_mul]
  linear_combination (↑(CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hpZ _) * L₂) *
    hLU + hLZ

end Inverts

/-! ### The induction along the filtration -/

section Filtration

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  {B : BigEtaleSite.{u}} {X : B.Scheme} (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f]
  {s : ConstructibleStratification B X ⊤} (Φ : s.ClosedFiltration)

/-- The structure morphism of the `j`-th member of the filtration. -/
abbrev filtrationStageMap (j : ℕ) : B.inclusion.obj (Φ.stage j) ⟶ Spec (.of k) :=
  B.inclusion.map (Φ.stageInclusion j) ≫ f

/-- The restriction of a sheaf to the `j`-th member of the filtration. -/
abbrev filtrationStageSheaf (G : EtaleModules.{u, 0} Λ X.obj) (j : ℕ) :
    EtaleModules.{u, 0} Λ (B.inclusion.obj (Φ.stage j)) :=
  (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (Φ.stageInclusion j))).obj G

/-- The structure morphism of the open stratum of the `j`-th member of the filtration. -/
abbrev filtrationPieceMap (j : ℕ) : (Φ.stageOpen j).toScheme ⟶ Spec (.of k) :=
  (Φ.stageOpen j).ι ≫ filtrationStageMap f Φ j

/-- The restriction of a sheaf to the open stratum of the `j`-th member of the filtration. -/
abbrev filtrationPieceSheaf (G : EtaleModules.{u, 0} Λ X.obj) (j : ℕ) :
    EtaleModules.{u, 0} Λ (Φ.stageOpen j).toScheme :=
  (etaleModuleRestriction.{u, 0} Λ (Φ.stageOpen j).ι).obj (filtrationStageSheaf Λ Φ G j)

omit [Fintype k] [QuasiCompact f] in
/-- The structure morphism of the `j`-th member of the filtration, precomposed with the inclusion
of the `(j + 1)`-th member, is the structure morphism of the `(j + 1)`-th member. -/
theorem stageSucc_comp_filtrationStageMap (j : ℕ) :
    B.inclusion.map (Φ.stageSucc j) ≫ filtrationStageMap f Φ j =
      filtrationStageMap f Φ (j + 1) := by
  rw [filtrationStageMap, filtrationStageMap, ← Category.assoc, ← Functor.map_comp,
    Φ.stageSucc_stageInclusion]

/-- The restriction to the `(j + 1)`-th member through the `j`-th. -/
def filtrationStageSheafSuccIso (G : EtaleModules.{u, 0} Λ X.obj) (j : ℕ) :
    (etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (Φ.stageSucc j))).obj
        (filtrationStageSheaf Λ Φ G j) ≅ filtrationStageSheaf Λ Φ G (j + 1) :=
  ((etaleModuleInverseImageCompIso.{u, 0} Λ (B.inclusion.map (Φ.stageSucc j))
      (B.inclusion.map (Φ.stageInclusion j))).app G).symm ≪≫
    eqToIso (by rw [← Functor.map_comp, Φ.stageSucc_stageInclusion])

omit [QuasiCompact f] in
/-- The `j`-th member of the filtration is empty for `j ≥ n`. -/
theorem isEmpty_filtrationStage {j : ℕ} (hj : s.n ≤ j) :
    IsEmpty (B.inclusion.obj (Φ.stage j)) := by
  refine ⟨fun x => ?_⟩
  have h : (B.inclusion.map (Φ.stageInclusion j)).base x ∈ Φ.Y j := by
    rw [← Φ.range_stageInclusion j]
    exact ⟨x, rfl⟩
  rwa [Φ.eq_empty j hj] at h

/-- **Dévissage along the members of the filtration.** -/
theorem compactSupportCharSeriesInverts_stage (G : EtaleModules.{u, 0} Λ X.obj)
    (L : ℕ → PowerSeries Λ)
    (hpiece : ∀ i < s.n, ∀ J : CompactificationOf (Over.mk (filtrationPieceMap f Φ i)),
      CompactSupportCharSeriesInverts Λ kbar p q hcard (filtrationPieceMap f Φ i) J
        (filtrationPieceSheaf Λ Φ G i) (L i)) :
    ∀ d j, j + d = s.n → ∀ J : CompactificationOf (Over.mk (filtrationStageMap f Φ j)),
      CompactSupportCharSeriesInverts Λ kbar p q hcard (filtrationStageMap f Φ j) J
        (filtrationStageSheaf Λ Φ G j) (∏ i ∈ Finset.Ico j s.n, L i) := by
  intro d
  induction d with
  | zero =>
    intro j hj J
    have := isEmpty_filtrationStage Φ (j := j) (by omega)
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
    exact compactSupportCharSeriesInverts_of_isEmpty _ J _
  | succ d ih =>
    intro j hj J
    have hjn : j < s.n := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hjn]
    refine CompactSupportCharSeriesInverts.excision (filtrationStageMap f Φ j) J
      (B.inclusion.map (Φ.stageSucc j)) (Φ.stageOpen j).ι (Φ.range_stageOpen_ι j)
      (filtrationStageSheaf Λ Φ G j) (hpiece j hjn _) ?_
    exact (compactSupportCharSeriesInverts_of_eq (stageSucc_comp_filtrationStageMap f Φ j)
      (fun J' => ih (j + 1) (by omega) J') _).of_iso (filtrationStageSheafSuccIso Λ Φ G j).symm

/-- **Dévissage of `det(1 - π^* T | RΓ_c)` along a closed filtration.** If on every open stratum
`RΓ_c` of the restriction of `G` is perfect with characteristic series inverse to `L i`, for every
compactification, then for every compactification of `X`, `RΓ_c(X_k̄, G)` is perfect with
characteristic series inverse to `∏ᵢ L i`. -/
theorem compactSupportCharSeriesInverts_of_closedFiltration (G : EtaleModules.{u, 0} Λ X.obj)
    (L : ℕ → PowerSeries Λ)
    (hpiece : ∀ i < s.n, ∀ J : CompactificationOf (Over.mk (filtrationPieceMap f Φ i)),
      CompactSupportCharSeriesInverts Λ kbar p q hcard (filtrationPieceMap f Φ i) J
        (filtrationPieceSheaf Λ Φ G i) (L i))
    (J : CompactificationOf (Over.mk f)) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f J G (∏ i ∈ Finset.range s.n, L i) := by
  have hrange : Set.range (⊥ : X.obj.Opens).ι.base =
      (Set.range (B.inclusion.map (Φ.stageInclusion 0)).base)ᶜ := by
    rw [Φ.range_stageInclusion 0, Φ.zero, Set.compl_univ, Scheme.Opens.range_ι]
    rfl
  have : IsEmpty (⊥ : X.obj.Opens).toScheme := ⟨fun x => by simpa using x.2⟩
  have h := CompactSupportCharSeriesInverts.excision f J (B.inclusion.map (Φ.stageInclusion 0))
    (⊥ : X.obj.Opens).ι hrange G (L₁ := 1)
    (compactSupportCharSeriesInverts_of_isEmpty _ _ _)
    (compactSupportCharSeriesInverts_stage Λ kbar p q hcard f Φ G L hpiece s.n 0 (by omega)
      (J.restrictClosed _))
  rwa [one_mul, ← Finset.range_eq_Ico] at h

end Filtration

end Stacks.EtaleCohomology
