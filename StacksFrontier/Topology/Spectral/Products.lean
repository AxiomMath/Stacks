module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Products of spectral spaces

The product of two spectral spaces is spectral, together with the corresponding statements for
prespectral, quasi-separated and quasi-sober spaces.

## Main results

* `prespectralSpace_prod`: a product of prespectral spaces is prespectral.
* `exists_finite_cover_qc_rect`: a quasi-compact open of a product is a finite union of
  quasi-compact open rectangles contained in it.
* `quasiSeparatedSpace_prod`: a product of quasi-separated prespectral spaces is quasi-separated.
* `eq_prod_closure_image_of_irreducible_isClosed`: an irreducible closed subset of a product is
  the product of the closures of its projections.
* `quasiSober_prod`: a product of quasi-sober spaces is quasi-sober.
* `prod_spectralSpace`: a product of spectral spaces is spectral.
-/

@[expose] public section

open TopologicalSpace Set

/-- The product of two prespectral spaces is prespectral. -/
lemma prespectralSpace_prod
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace (X × Y) := by
  refine PrespectralSpace.mk (isTopologicalBasis_of_isOpen_of_nhds (fun _ hu => hu.1) ?_)
  intro p u hpu hu
  obtain ⟨a, b, ha, hb, hpa, hpb, hab⟩ := isOpen_prod_iff.mp hu p.1 p.2 hpu
  obtain ⟨U, ⟨hUO, hUC⟩, hpU, hUa⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hpa ha
  obtain ⟨V, ⟨hVO, hVC⟩, hpV, hVb⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open hpb hb
  exact ⟨U ×ˢ V, ⟨hUO.prod hVO, hUC.prod hVC⟩, ⟨hpU, hpV⟩,
    (Set.prod_mono hUa hVb).trans hab⟩

/-- A quasi-compact open `W ⊆ X × Y` is a finite union of rectangles `A ×ˢ B ⊆ W` with `A`
quasi-compact open in `X` and `B` quasi-compact open in `Y`. -/
lemma exists_finite_cover_qc_rect
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y]
    (W : Set (X × Y)) (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ (s : Finset (Set X × Set Y)),
      (∀ p ∈ s, IsOpen p.1 ∧ IsCompact p.1 ∧ IsOpen p.2 ∧ IsCompact p.2 ∧
        p.1 ×ˢ p.2 ⊆ W) ∧
      W = ⋃ p ∈ s, p.1 ×ˢ p.2 := by
  set 𝒰 : Set (Set X × Set Y) :=
    {p | IsOpen p.1 ∧ IsCompact p.1 ∧ IsOpen p.2 ∧ IsCompact p.2 ∧ p.1 ×ˢ p.2 ⊆ W}
  have hbasis : IsTopologicalBasis
      (Set.image2 (· ×ˢ ·) {U : Set X | IsOpen U ∧ IsCompact U}
        {V : Set Y | IsOpen V ∧ IsCompact V}) :=
    PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis
  have hcover : W ⊆ ⋃ p ∈ 𝒰, p.1 ×ˢ p.2 := by
    intro q hq
    obtain ⟨T, ⟨U, ⟨hUo, hUc⟩, V, ⟨hVo, hVc⟩, rfl⟩, hqT, hTW⟩ :=
      hbasis.exists_subset_of_mem_open hq hWo
    exact Set.mem_iUnion₂.mpr ⟨(U, V), ⟨hUo, hUc, hVo, hVc, hTW⟩, hqT⟩
  have hopen : ∀ p ∈ 𝒰, IsOpen (p.1 ×ˢ p.2) := fun _ ⟨ho1, _, ho2, _, _⟩ => ho1.prod ho2
  obtain ⟨s', hs'sub, hs'fin, hs'cover⟩ := hWc.elim_finite_subcover_image hopen hcover
  refine ⟨hs'fin.toFinset, fun p hp => hs'sub (hs'fin.mem_toFinset.mp hp),
    Set.Subset.antisymm (fun q hq => ?_) (fun q hq => ?_)⟩
  · obtain ⟨p, hps', hqp⟩ := Set.mem_iUnion₂.mp (hs'cover hq)
    exact Set.mem_iUnion₂.mpr ⟨p, hs'fin.mem_toFinset.mpr hps', hqp⟩
  · obtain ⟨p, hps, hqp⟩ := Set.mem_iUnion₂.mp hq
    obtain ⟨-, -, -, -, hpW⟩ := hs'sub (hs'fin.mem_toFinset.mp hps)
    exact hpW hqp

/-- The product of two quasi-separated prespectral spaces is quasi-separated. -/
lemma quasiSeparatedSpace_prod
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace (X × Y) := by
  refine QuasiSeparatedSpace.mk fun U V hUo hUc hVo hVc => ?_
  obtain ⟨sU, hsU, hUeq⟩ := exists_finite_cover_qc_rect U hUo hUc
  obtain ⟨sV, hsV, hVeq⟩ := exists_finite_cover_qc_rect V hVo hVc
  have hUV : U ∩ V = ⋃ p ∈ sU, ⋃ q ∈ sV, (p.1 ∩ q.1) ×ˢ (p.2 ∩ q.2) := by
    rw [hUeq, hVeq, Set.iUnion₂_inter]
    refine Set.iUnion₂_congr fun p _ => ?_
    rw [Set.inter_iUnion₂]
    exact Set.iUnion₂_congr fun _ _ => Set.prod_inter_prod
  rw [hUV]
  refine Set.Finite.isCompact_biUnion (Finset.finite_toSet sU) fun p hp => ?_
  refine Set.Finite.isCompact_biUnion (Finset.finite_toSet sV) fun q hq => ?_
  obtain ⟨hpo1, hpc1, hpo2, hpc2, _⟩ := hsU p hp
  obtain ⟨hqo1, hqc1, hqo2, hqc2, _⟩ := hsV q hq
  exact (QuasiSeparatedSpace.inter_isCompact p.1 q.1 hpo1 hpc1 hqo1 hqc1).prod
    (QuasiSeparatedSpace.inter_isCompact p.2 q.2 hpo2 hpc2 hqo2 hqc2)

/-- An irreducible closed subset of a product equals the product of the closures of its two
projections. -/
lemma eq_prod_closure_image_of_irreducible_isClosed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Z : Set (X × Y)} (hZirr : IsIrreducible Z) (hZcl : IsClosed Z) :
    Z = closure (Prod.fst '' Z) ×ˢ closure (Prod.snd '' Z) := by
  refine Set.Subset.antisymm
    (fun _ hp => ⟨subset_closure (mem_image_of_mem _ hp),
      subset_closure (mem_image_of_mem _ hp)⟩) ?_
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  rw [← hZcl.closure_eq, mem_closure_iff]
  intro W hWopen hxyW
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hWopen x y hxyW
  obtain ⟨x₁, hx₁U, ⟨a₁, b₁⟩, haZ, rfl⟩ := mem_closure_iff.mp hx U hU hxU
  obtain ⟨y₂, hy₂V, ⟨a₂, b₂⟩, hbZ, rfl⟩ := mem_closure_iff.mp hy V hV hyV
  have hIntNE : (Z ∩ ((U ×ˢ (univ : Set Y)) ∩ ((univ : Set X) ×ˢ V))).Nonempty :=
    hZirr.2 _ _ (hU.prod isOpen_univ) (isOpen_univ.prod hV)
      ⟨(a₁, b₁), haZ, hx₁U, mem_univ _⟩ ⟨(a₂, b₂), hbZ, mem_univ _, hy₂V⟩
  rw [Set.prod_inter_prod, inter_univ, univ_inter] at hIntNE
  obtain ⟨p, hpZ, hpUV⟩ := hIntNE
  exact ⟨p, hUV hpUV, hpZ⟩

/-- The product of two quasi-sober spaces is quasi-sober. -/
lemma quasiSober_prod
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] :
    QuasiSober (X × Y) := by
  refine ⟨fun {Z} hZirr hZcl => ?_⟩
  obtain ⟨x₀, hx₀⟩ :=
    QuasiSober.sober (hZirr.image Prod.fst continuous_fst.continuousOn).closure isClosed_closure
  obtain ⟨y₀, hy₀⟩ :=
    QuasiSober.sober (hZirr.image Prod.snd continuous_snd.continuousOn).closure isClosed_closure
  refine ⟨(x₀, y₀), ?_⟩
  rw [isGenericPoint_def]
  rw [← Set.singleton_prod_singleton, closure_prod_eq, hx₀, hy₀,
    ← eq_prod_closure_image_of_irreducible_isClosed hZirr hZcl]

/-- The product of two spectral spaces is a spectral space. -/
@[stacks 0907]
theorem prod_spectralSpace (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] :
    SpectralSpace (X × Y) :=
  have := prespectralSpace_prod X Y
  have := quasiSeparatedSpace_prod X Y
  have := quasiSober_prod X Y
  SpectralSpace.mk
