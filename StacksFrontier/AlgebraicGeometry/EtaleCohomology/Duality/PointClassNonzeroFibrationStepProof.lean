module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTrace

/-!
# The step of the class of a point through an elementary fibration

Let `k` be algebraically closed and `ℓ` a prime invertible in `k`. Let `W` be smooth irreducible of
relative dimension `e + 1` over `k`, and `g : U → S` an elementary fibration on an open `U ⊆ W`
over `S` affine, irreducible and smooth of relative dimension `e`. If every point class of `S` is
nonzero in `H^{2e}_c(S)`, then the class of every `k`-point of `W` lying in `U` is nonzero in
`H^{2e+2}_c(W)` (`Stacks.EtaleCohomology.pointClassNonzeroFibrationStep`).

The point is the spectrum of `k` (`k` is separably closed), hence a section `x` of `W → Spec k`,
and it lifts to a section `p` of `U`, over the `k`-point `i' = g ∘ p` of `S`. By excision
(`Stacks.EtaleCohomology.pointClassNonzeroAt_of_restrictOpen`; the complement of the dense open
`U` has dimension at most `e`) it suffices to treat `p` in `U`. The fibre `C = U ×_S Spec k` is an
open of the fibre of the compactification `X̄ → S` of the fibration, a geometrically irreducible
smooth projective curve, and contains the point `p`, so `C` is irreducible. The class of `p` on
the curve `C` gives `δ ∈ Ext²_U(p_* Λ, g⁻¹ i'_* Λ)` with `H⁰(Rg_!(δ)) ≠ 0`
(`Stacks.EtaleCohomology.exists_ext_homology_map_ne_zero_of_fibre`), which splits the top trace
(`Stacks.EtaleCohomology.exists_section_of_homology_map_ne_zero`, through the relative trace
`R²g_! g⁻¹ ≅ 𝟭`, `Stacks.EtaleCohomology.relativeTraceOfElementaryFibration`); then the class of
`p` is nonzero (`Stacks.EtaleCohomology.pointClassNonzeroAt_of_fibration_of_section`).

This is the induction step for the class of a point in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.pointClassNonzeroFibrationStep`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`.
attribute [-instance] ZMod.instField

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe, on which instance
-- problems below get stuck.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **The step of the class of a point through an elementary fibration**
(`Stacks.EtaleCohomology.PointClassNonzeroFibrationStep`), over an algebraically closed field `k`
in which `ℓ` is invertible. -/
theorem pointClassNonzeroFibrationStep (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [IsAlgClosed k] (hℓ : IsUnit (ℓ : k)) : PointClassNonzeroFibrationStep ℓ k := by
  intro e W f _ _ _ jc U S q g _ _ _ hg hgq hS N P n _ i _ _ _ hU
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  -- the scheme-level instances
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsSeparated f := by
    rw [← CompactificationOf.immersion_toBase jc]; infer_instance
  have : CompactSpace W := inferInstance
  have : QuasiCompact f := inferInstance
  have : QuasiCompact q := inferInstance
  have : IsSeparated q := inferInstance
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace U.toScheme := inferInstance
  have : QuasiSeparatedSpace U.toScheme := NoetherianSpace.to_quasiSeparatedSpace
  have : CompactSpace S := inferInstance
  have : QuasiSeparatedSpace S := inferInstance
  have : CompactSpace jc.space := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := jc.toBase) Set.univ isOpen_univ
      isCompact_univ⟩
  have : IsLocallyNoetherian jc.space := LocallyOfFiniteType.isLocallyNoetherian jc.toBase
  have : IsNoetherian jc.space := ⟨⟩
  -- the point is the spectrum of `k`, a section `x` of `W`, lifting to a section `p` of `U`
  obtain ⟨s₀, hs₀, _⟩ := exists_isIso_section_of_smoothOfRelativeDimension_zero (i ≫ n ≫ f)
  refine pointClassNonzeroAt_of_comp_isIso ℓ (e + 1) f jc n i s₀ ?_
  let x : Spec (.of k) ⟶ W := s₀ ≫ i ≫ n
  have hxf : x ≫ f = 𝟙 _ := by simpa only [x, Category.assoc] using hs₀
  have : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id f x hxf
  have hxU : Set.range x.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU ⟨s₀.base y, rfl⟩
  let p : Spec (.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι x hxU
  have hp : p ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  have hpf : p ≫ g ≫ q = 𝟙 _ := by rw [hgq, ← Category.assoc, hp, hxf]
  have : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id (g ≫ q) p hpf
  let i' : Spec (.of k) ⟶ S := p ≫ g
  have hi'q : i' ≫ q = 𝟙 _ := by simpa only [i', Category.assoc] using hpf
  have : IsClosedImmersion i' := isClosedImmersion_of_comp_eq_id q i' hi'q
  -- the class of `i'` on `S` is nonzero
  obtain ⟨jS⟩ : Nonempty (CompactificationOf (Over.mk q)) := IsCofiltered.nonempty
  have : SmoothOfRelativeDimension 0 (i' ≫ 𝟙 S ≫ q) := by
    rw [Category.id_comp, hi'q]; infer_instance
  have hS' : PointClassNonzeroAt ℓ e q jS (𝟙 S) i' := hS jS S (Spec (.of k)) (𝟙 S) i'
  -- the compactification of `g` given by the elementary fibration
  obtain ⟨Xbar, Z, j, fbar, iZ, hj, hjf, hsm, hproj, hgi, -, -, -, -, -, -⟩ :=
    hg.exists_compactification
  have := hsm
  have := hgi
  have : IsOpenImmersion j := hj
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  let jg : CompactificationOf (Over.mk g) :=
    ⟨StructuredArrow.mk (Y := Over.mk fbar) (Over.homMk (U := Over.mk g) j hjf),
      ⟨hj, inferInstanceAs (IsProper fbar)⟩⟩
  have : IsSeparated g := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType g := by rw [← hjf]; infer_instance
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have : SmoothOfRelativeDimension 1 g := by
    rw [← hjf, show (1 : ℕ) = 0 + 1 from rfl]; infer_instance
  have hfib : ∀ y : S, topologicalKrullDim (jg.toBase.fiber y) ≤ (1 : WithBot ℕ∞) := fun y =>
    topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 fbar y
  let ν := (relativeTraceOfElementaryFibration k ℓ hℓ U.toScheme S q g e hg jg).some
  -- the fibre `C` of `g` over `i'`: an open of the irreducible fibre of `fbar`, containing `p`
  let b := pullback.fst fbar i'
  have hsq₀ : IsPullback (pullback.fst j b) (pullback.snd j b ≫ pullback.snd fbar i')
      (j ≫ fbar) i' :=
    (IsPullback.of_hasPullback j b).paste_vert (IsPullback.of_hasPullback fbar i')
  have hsq : IsPullback (pullback.fst j b) (pullback.snd j b ≫ pullback.snd fbar i') g i' := by
    rw [← hjf]; exact hsq₀
  have : IrreducibleSpace ↥(pullback fbar i') :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  obtain ⟨y₀⟩ : Nonempty (Spec (.of k)) := inferInstance
  have : Nonempty ↥(pullback j b) :=
    ⟨(hsq.lift p (𝟙 _) (by rw [Category.id_comp])).base y₀⟩
  have : IrreducibleSpace ↥(pullback j b) :=
    (pullback.snd j b).isOpenEmbedding.irreducibleSpace
  -- the class on the fibre curve splits the top trace
  obtain ⟨δ, hδ⟩ := exists_ext_homology_map_ne_zero_of_fibre ℓ hℓ g jg i' p rfl hsq
  obtain ⟨σ, hσ⟩ := exists_section_of_homology_map_ne_zero ℓ g jg hfib ν i' p rfl δ hδ
  -- the class of `p` in `U`, for every compactification of `U → Spec k`
  have hUp : ∀ (φ : U.toScheme ⟶ Spec (.of k)) (_ : g ≫ q = φ)
      (jφ : CompactificationOf (Over.mk φ)),
        PointClassNonzeroAt ℓ (e + 1) φ jφ (𝟙 U.toScheme) p := by
    rintro φ rfl jφ
    exact pointClassNonzeroAt_of_fibration_of_section ℓ g q jg jS jφ hfib ν e p i' hS' δ σ hσ
  -- excision: the complement of `U` has dimension at most `e`
  obtain ⟨Zc, iC, hiC, hrange⟩ := exists_isClosedImmersion_range_eq ((U : Set W)ᶜ)
    U.isOpen.isClosed_compl
  have := hiC
  have : Nonempty W := ⟨x.base y₀⟩
  have hUne : (U : Set W).Nonempty := by
    have h := hxU ⟨y₀, rfl⟩
    rw [Scheme.Opens.range_ι] at h
    exact ⟨_, h⟩
  have hint : interior ((U : Set W)ᶜ) = ∅ := by
    rw [interior_compl, (U.isOpen.dense hUne).closure_eq, Set.compl_univ]
  have hdimW : topologicalKrullDim W ≤ (e + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (e + 1) f).le
  have hlt := topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty U.isOpen.isClosed_compl
    hint hdimW iC.isEmbedding.isInducing hrange.le
  have hdimZ : topologicalKrullDim Zc ≤ (e : WithBot ℕ∞) := by
    rcases hZ : topologicalKrullDim Zc with _ | y
    · exact bot_le
    · rw [hZ] at hlt
      have h0 : (y : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞) := hlt
      have h1 : y < (e : ℕ∞) + 1 := by
        have := WithBot.coe_lt_coe.1 h0
        exact_mod_cast this
      exact WithBot.coe_le_coe.2 (Order.le_of_lt_add_one h1)
  have hiU : Set.range U.ι.base = (Set.range iC.base)ᶜ := by
    rw [hrange, compl_compl, Scheme.Opens.range_ι]
  exact pointClassNonzeroAt_of_restrictOpen ℓ f jc U iC hiU e hdimZ n (s₀ ≫ i) p x
    (Category.assoc _ _ _) hp (hUp _ hgq (jc.restrictOpen U.ι))

end Stacks.EtaleCohomology

end
