module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DeJongConjectureFiniteness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldTopologicalGenerator
public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.Flatness

/-!
# Flatness of the universal deformation ring of a residual representation of `π₁` of a curve

Let `X` be a smooth, geometrically irreducible, projective curve over a finite field `k`, `k̄` an
algebraic closure, and `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous, `ℓ` a prime different from the
characteristic and not dividing `n`, with `ρ₀|_{π₁(X_k̄)}` absolutely irreducible. Assume de Jong's
conjecture for `X` in every rank. If `H ²(π₁(X_k̄), ad⁰ ρ₀) = 0` (locally constant cochains),
then the universal deformation ring of `ρ₀` with determinant fixed to `δ` is flat over `ℤ_[ℓ]`.

The proof assembles: finiteness of `R`
(`moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal`, with the normality of
`π₁(X_k̄)` from Stacks 0BTX), the exact sequence
`1 → π₁(X_k̄) → π₁(X) → π₁(Spec k) → 1` (Stacks 0BTX: `π₁(X_k̄)` is a closed subgroup), a
topological generator of `π₁(X)` modulo `π₁(X_k̄)`
(`exists_forall_openSubgroup_eq_top_of_finite`), and the deformation-theoretic flatness criterion
`Deformation.IsUniversalFixedDeterminantDeformation.flat_of_vanishesTwo`.

## Main results

* `AlgebraicGeometry.vanishesTwo_range_of_isClosedEmbedding`: `H ²` vanishing transported to the
  image of a closed embedding of profinite groups.
* `AlgebraicGeometry.flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology groupCohomology
open scoped PowerSeries.WithPiTopology

universe u v

namespace AlgebraicGeometry

/-- **Transport of `H ² = 0` to the image of a closed embedding.** If `ι : G → π` is an injective
continuous homomorphism which is a closed embedding and every locally constant `2`-cocycle of `G`
with values in `M` (through `ι`) is a coboundary, the same holds for the image of `ι`. -/
theorem vanishesTwo_range_of_isClosedEmbedding {G π : Type*} [Group G] [TopologicalSpace G]
    [Group π] [TopologicalSpace π] {M : Type*} [AddCommGroup M] [DistribMulAction π M]
    (ι : G →* π) (hι : Function.Injective ι) (hemb : Topology.IsClosedEmbedding ι)
    [DistribMulAction G M] (hact : ∀ (g : G) (m : M), g • m = ι g • m)
    (hvan : VanishesTwo G M) : VanishesTwo ι.range M := by
  classical
  let e : G ≃* ι.range := MonoidHom.ofInjective hι
  have he : ∀ g, ((e g : ι.range) : π) = ι g := fun g => rfl
  have hesym : ∀ y : ι.range, ι (e.symm y) = y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hec : Continuous e := Continuous.subtype_mk hemb.continuous _
  have hesc : Continuous e.symm := by
    refine hemb.isEmbedding.continuous_iff.mpr ?_
    rw [show (ι : G → π) ∘ e.symm = Subtype.val from funext hesym]
    exact continuous_subtype_val
  intro c hcl hc
  let c' : G × G → M := fun p => c (e p.1, e p.2)
  have hc'l : IsLocallyConstant c' :=
    hcl.comp_continuous ((hec.comp continuous_fst).prodMk (hec.comp continuous_snd))
  have hc' : IsCocycle₂ c' := by
    intro g h j
    have := hc (e g) (e h) (e j)
    simp only [c', hact, Subgroup.smul_def, he] at this ⊢
    rwa [map_mul, map_mul]
  obtain ⟨x', hx'l, hx'⟩ := hvan c' hc'l hc'
  refine ⟨fun y => x' (e.symm y), hx'l.comp_continuous hesc, funext fun ⟨y₁, y₂⟩ => ?_⟩
  have := congrFun hx' (e.symm y₁, e.symm y₂)
  simp only [c', MulEquiv.apply_symm_apply, dOne_apply, hact] at this
  simp only [dOne_apply, Subgroup.smul_def]
  rw [map_mul, ← this, hesym]

/-- **Lifting a topological generator along a surjection of profinite groups.** If `φ : π → Γ` is a
continuous surjective homomorphism from a compact group to a Hausdorff group and `γ ∈ Γ` lies in
no proper open subgroup, then a preimage `σ` of `γ` satisfies: every open subgroup of `π`
containing `ker φ` and `σ` is all of `π`. -/
theorem forall_openSubgroup_eq_top_of_surjective {π Γ : Type*} [Group π] [TopologicalSpace π]
    [CompactSpace π] [Group Γ] [TopologicalSpace Γ] [T2Space Γ] (φ : π →* Γ)
    (hφc : Continuous φ) (hφ : Function.Surjective φ) {γ : Γ}
    (hγ : ∀ U : OpenSubgroup Γ, γ ∈ U → U = ⊤) {σ : π} (hσ : φ σ = γ) :
    ∀ H : OpenSubgroup π, φ.ker ≤ H → σ ∈ H → H = ⊤ := by
  intro H hNH hσH
  have hpre : φ ⁻¹' (H.toSubgroup.map φ : Set Γ) = (H : Set π) :=
    congrArg SetLike.coe (Subgroup.comap_map_eq_self hNH)
  have hquot : Topology.IsQuotientMap φ :=
    (hφc.isClosedMap).isQuotientMap hφc hφ
  have hopen : IsOpen ((H.toSubgroup.map φ : Subgroup Γ) : Set Γ) := by
    rw [← hquot.isOpen_preimage, hpre]; exact H.isOpen
  have htop := hγ ⟨H.toSubgroup.map φ, hopen⟩ ⟨σ, hσH, hσ⟩
  ext g
  simp only [OpenSubgroup.mem_top, iff_true]
  have : φ g ∈ (⟨H.toSubgroup.map φ, hopen⟩ : OpenSubgroup Γ) := by
    rw [htop]; trivial
  rw [← SetLike.mem_coe, ← hpre]
  exact this

/-- **Flatness half of Stacks 03W1, given `H ²(π₁(X_k̄), ad⁰) = 0`.** Let `X` be a smooth,
geometrically irreducible, projective curve over a finite field `k` of characteristic `p`, `k̄` an
algebraic closure of `k` with `X_k̄` connected, and `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous with
`ℓ ≠ p`, `ℓ ∤ n` and `ρ₀|_{π₁(X_k̄)}` absolutely irreducible. Assume de Jong's conjecture for `X`
in every rank. If every locally constant `2`-cocycle of `π₁(X_k̄)` with values in `ad⁰ ρ₀` is a
coboundary, then the universal deformation ring of `ρ₀` with determinant fixed to `δ` is flat over
`ℤ_[ℓ]`. -/
theorem flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo
    (k kbar : Type u) [Field k] [Finite k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
    (ρ₀ : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ* ℤ_[ℓ]ˣ)
    (hconj : ∀ (m : ℕ) (ρ : EtaleFundamentalGroup X (x.map (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (Set.range fun g : EtaleFundamentalGroup _ x => ρ (etaleFundamentalGroupMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g)).Finite)
    (hirred : Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ x =>
      ρ₀ (etaleFundamentalGroupMap (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g))
    (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) R)
    (hR : Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv)
    (hvan : VanishesTwo (EtaleFundamentalGroup _ x)
      (Deformation.AdZero ((ρ₀.comp (etaleFundamentalGroupMap (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x)).toMonoidHom))) :
    Module.Flat ℤ_[ℓ] R := by
  classical
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let g₀ := Spec.map (CommRingCat.ofHom (algebraMap k kbar))
  let q := pullback.fst f g₀
  let ι := etaleFundamentalGroupMap q x
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  have := forall_finite_finiteEtaleFiberFunctor_obj (x.map q)
  have hbc : IsPullback q (pullback.snd f g₀) f g₀ := IsPullback.of_hasPullback f g₀
  -- 0BTX
  obtain ⟨hinj, hemb, -, -, -⟩ :=
    topologicalShortExact_etaleFundamentalGroupMap_isAlgClosure k kbar f x
  let N := ι.toMonoidHom.range
  have hNn : N.Normal := normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed k kbar f
    q (pullback.snd f g₀) hbc x
  have hNc : IsClosed (N : Set (EtaleFundamentalGroup X (x.map q))) := by
    rw [MonoidHom.coe_range]; exact hemb.isClosed_range
  -- finiteness and the special fibre
  have := moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal k kbar p ℓ n hℓp hn X f
    (pullback f g₀) q (pullback.snd f g₀) hbc x ρ₀ δ hconj hirred hNn R reduce ρuniv hR
  have hrange : ∀ {β : Type} (φ : EtaleFundamentalGroup X (x.map q) → β),
      Set.range (fun g : N => φ g) = Set.range fun g : EtaleFundamentalGroup _ x => φ (ι g) := by
    intro β φ
    ext y
    constructor
    · rintro ⟨⟨_, g, rfl⟩, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨⟨_, g, rfl⟩, rfl⟩
  have hirrN : Deformation.IsAbsolutelyIrreducible fun g : N => ρ₀ g := by
    unfold Deformation.IsAbsolutelyIrreducible at hirred ⊢
    have := hrange fun g => (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))
    simp only at this ⊢
    rw [this]
    exact hirred
  have hconjN : ∀ (m : ℕ) (ρ : EtaleFundamentalGroup X (x.map q) →ₜ*
      Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (ρ '' (N : Set (EtaleFundamentalGroup X (x.map q)))).Finite := by
    intro m ρ
    rw [MonoidHom.coe_range, ← Set.range_comp]
    exact hconj m ρ
  have hfin := hR.finite_quotient_span_of_finite_image N hirrN hn hconjN
  -- the generator
  obtain ⟨σ, hσ⟩ := exists_forall_openSubgroup_eq_top_of_finite k kbar f x
  -- the vanishing of `H ²` on `N`
  have hvanN : VanishesTwo N (Deformation.AdZero ρ₀.toMonoidHom) :=
    @vanishesTwo_range_of_isClosedEmbedding _ _ _ _ _ _ _ _ _ ι.toMonoidHom hinj hemb
      (inferInstance : DistribMulAction (EtaleFundamentalGroup _ x)
        (Deformation.AdZero ((ρ₀.comp ι).toMonoidHom))) (fun _ _ => rfl) hvan
  exact hR.flat_of_vanishesTwo hfin N hNc hirrN hn hvanN σ hσ

end AlgebraicGeometry
