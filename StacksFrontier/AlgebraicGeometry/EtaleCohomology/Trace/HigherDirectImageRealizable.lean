module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopRealizableInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCurveTraceFormulaInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseBiprod
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SmoothAffineCurveCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage

/-!
# Realizability of the higher direct images of a family of smooth affine curves

In the induction step of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 1.5 and 3.3; Kedlaya,
*Fourier transforms and p-adic Weil II*, §6) the base `W` is fibred by smooth affine curves
`g : U ⟶ W`, and the higher direct images `Rʳ g_! G` of a lisse `ι`-realizable `G` have to be
`ι`-realizable over a nonempty open of `W`. Here `R` is a family in the role of `Rʳ g_!`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageFamily`), and the statement
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageRealizableInput R` is deduced from

* the stalks of the `Rʳ g_!` at closed points, `Hʳ_c` of the fibres with the Frobenius of `κ(w)`
  (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageStalkInput`, proper base change);
* the lisse locus of the `Rʳ g_!`
  (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageLisseLocusInput`);
* the trace formula for lisse sheaves on smooth curves
  (`Stacks.EtaleCohomology.LisseCurveTraceFormulaInput`, Tag 03V2);
* the realizability of `R² g_!`, the family of geometric coinvariants twisted by `(-1)`
  (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopRealizableInput`).

At a closed point `w`, `H⁰_c` of the fibre, a smooth affine curve over `κ(w)`, vanishes
(`subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension`
in the namespace `Stacks.EtaleCohomology.LAdicSheaf`),
so does `Hʳ_c` for `r ≥ 3`, and the trace formula on the fibre, for `G` and its witness `G'`,
makes `-(Tr R¹ G + Tr R¹ G') + (Tr R² G + Tr R² G')` real: the point sums are sums of traces
of `G ⊕ G'` at closed points of `U`. Hence `R¹ g_! G` is realizable with witness
`R¹ g_! G' ⊞ (E ⊞ E')`, `E` and `E'` witnesses of the realizability of `R² g_! G` and
`R² g_! G'`.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed compactly supported cohomology and Frobenius objects are defined there.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImage_traces`: the Frobenius traces on the
  stalks of the `Rʳ g_!` at a closed point.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageRealizableInput`: the realizability of the
  `Rʳ g_! G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- A complex number is real exactly when its imaginary part vanishes. -/
theorem mem_range_ofReal_iff_im_eq_zero (z : ℂ) : z ∈ Set.range ((↑) : ℝ → ℂ) ↔ z.im = 0 :=
  ⟨fun ⟨r, hr⟩ => hr ▸ Complex.ofReal_im r,
    fun h => ⟨z.re, Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, h])⟩⟩

/-- Read along `ι`, the trace of a power of an endomorphism only depends on its characteristic
polynomial. -/
theorem map_trace_pow_eq_of_charpoly_eq {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (ι : K →+* ℂ) {f : Module.End K V} {f' : Module.End K V'} (h : f.charpoly = f'.charpoly)
    (N : ℕ) : ι (LinearMap.trace K V (f ^ N)) = ι (LinearMap.trace K V' (f' ^ N)) := by
  rw [map_trace_pow_eq_sum_roots_map_pow, map_trace_pow_eq_sum_roots_map_pow, h]

/-- The trace of any endomorphism of a subsingleton module vanishes. -/
theorem trace_eq_zero_of_subsingleton {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Subsingleton V] (f : Module.End K V) : LinearMap.trace K V f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

/-! ### Fibres of a morphism at closed points -/

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- The fibre of a quasi-compact morphism is quasi-compact over the residue field. -/
theorem quasiCompact_fiberToSpecResidueField [QuasiCompact f] :
    QuasiCompact (f.fiberToSpecResidueField y) :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

/-- The fibre of a separated morphism is separated over the residue field. -/
theorem isSeparated_fiberToSpecResidueField [IsSeparated f] :
    IsSeparated (f.fiberToSpecResidueField y) :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The fibre of a quasi-compact morphism locally of finite type is noetherian. -/
theorem isNoetherian_fiber [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (f.fiber y) := by
  have : IsLocallyNoetherian (f.fiber y) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (f.fiberToSpecResidueField y)
      (Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f y) inferInstance
  exact ⟨⟩

/-- The fibre at a closed point of a morphism of a big étale site lies in the site. -/
theorem contains_fiber {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) (y : Y.1)
    (hy : IsClosed ({y} : Set Y.1)) : B.Contains ((B.inclusion.map f).fiber y) := by
  have := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι (B.inclusion.map f) hy
  exact Scheme.size_lt_of_isClosedImmersion ((B.inclusion.map f).fiberι y) X.2

end Fibre

/-! ### Frobenius traces at points of a fibre -/

/-- At a point `y` with finite residue field, the residue field of its image under a morphism is
finite, and `#κ(y)` is a power `#κ(g y) ^ (e + 1)` of it. -/
theorem finite_residueField_and_exists_natCard_eq_pow {X' X : Scheme.{u}} (g : X' ⟶ X) (y : X')
    [Finite (X'.residueField y)] :
    Finite (X.residueField (g.base y)) ∧
      ∃ e : ℕ, Nat.card (X'.residueField y) = Nat.card (X.residueField (g.base y)) ^ (e + 1) := by
  have : Finite (X.residueField (g.base y)) :=
    Finite.of_injective _ (g.residueFieldMap y).hom.injective
  refine ⟨inferInstance, ?_⟩
  let : Algebra (X.residueField (g.base y)) (X'.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : Module.Finite (X.residueField (g.base y)) (X'.residueField y) := Module.Finite.of_finite
  have hm : Module.finrank (X.residueField (g.base y)) (X'.residueField y) ≠ 0 :=
    Module.finrank_pos.ne'
  refine ⟨Module.finrank (X.residueField (g.base y)) (X'.residueField y) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]
  exact Module.natCard_eq_pow_finrank

section Traces

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **Realness of the Frobenius traces of a realizable pair at a point mapping to the base.**
Let `G`, `G'` be ℓ-adic sheaves on `U`, of finite type over a finite field `k`, such that
`ι(Tr(π_u ^ m | G) + Tr(π_u ^ m | G'))` is real at every closed point `u` and every `m ≥ 1`.
Then for morphisms `a : U' ⟶ U`, `b : X ⟶ U'` and a point `y` of `X` with finite residue field,
the same holds for `b⁻¹ a⁻¹ G` and `b⁻¹ a⁻¹ G'` at `y`: the traces at `y` are traces at the image
of `y` in `U`, which is a closed point. -/
theorem LAdicSheaf.mem_range_ofReal_trace_inverseImage_inverseImage {U U' X : B.Scheme}
    [IsNoetherian U.1] [IsNoetherian U'.1] [IsNoetherian X.1] {k : Type u} [Field k] [Finite k]
    (fU : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fU] {ι : ℚ_[ℓ] →+* ℂ}
    (G G' : LAdicSheaf.{u, u + 1} B U ℓ)
    (hreal : ∀ (u : closedPoints U.1) (m : ℕ), 1 ≤ m →
      ι (LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B U ℓ G u.1 (finite_residueField fU u.1 u.2) ^ m) +
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B U ℓ G' u.1 (finite_residueField fU u.1 u.2) ^ m)) ∈
        Set.range ((↑) : ℝ → ℂ))
    (a : U' ⟶ U) (b : X ⟶ U') [LocallyOfFiniteType (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map b)] (y : X.1) (hy : Finite (X.1.residueField y)) (M : ℕ)
    (hM : 1 ≤ M) :
    ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ
          (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a G)) y hy ^ M) +
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ
          (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a G')) y hy ^ M)) ∈
      Set.range ((↑) : ℝ → ℂ) := by
  have := hy
  have : Finite ((B.inclusion.obj X).residueField y) := hy
  obtain ⟨hx, e, he⟩ := finite_residueField_and_exists_natCard_eq_pow (B.inclusion.map b) y
  have := hx
  have : Finite (U'.1.residueField ((B.inclusion.map b).base y)) := hx
  obtain ⟨hu, e', he'⟩ :=
    finite_residueField_and_exists_natCard_eq_pow (B.inclusion.map a) ((B.inclusion.map b).base y)
  have := hu
  have : Finite (U.1.residueField ((B.inclusion.map a).base ((B.inclusion.map b).base y))) := hu
  have hcl : IsClosed ({(B.inclusion.map a).base ((B.inclusion.map b).base y)} : Set U.1) :=
    isClosed_singleton_of_module_finite_residueField fU _ (by
      let := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fU.appTop ≫
        U.1.Γevaluation ((B.inclusion.map a).base ((B.inclusion.map b).base y))).hom.toAlgebra
      exact Module.Finite.of_finite)
  have hM' : 1 ≤ (e + 1) * M := Nat.mul_pos e.succ_pos hM
  have hM'' : 1 ≤ (e' + 1) * ((e + 1) * M) := Nat.mul_pos e'.succ_pos hM'
  rw [LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U' ℓ b _ y hy hx e he hM,
    LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U' ℓ b _ y hy hx e he hM,
    LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U ℓ a _ _ hx hu e' he' hM',
    LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U ℓ a _ _ hx hu e' he' hM']
  exact hreal ⟨_, hcl⟩ _ hM''

/-- **Realness of a finite sum of realizable pairs of traces.** -/
theorem im_finsum_add_eq_zero {α : Type*} {K : Type*} [CommRing K] (ι : K →+* ℂ) (P : α → Prop)
    (hP : {y | P y}.Finite) (d : α → ℕ) (t t' : α → K) (h : ∀ y, P y → (ι (t y + t' y)).im = 0) :
    (ι ((∑ᶠ (y) (_ : P y), (d y : K) * t y) + ∑ᶠ (y) (_ : P y), (d y : K) * t' y)).im = 0 := by
  classical
  change (ι ((∑ᶠ y ∈ {y | P y}, (d y : K) * t y) + ∑ᶠ y ∈ {y | P y}, (d y : K) * t' y)).im = 0
  rw [finsum_mem_eq_finite_toFinset_sum _ hP, finsum_mem_eq_finite_toFinset_sum _ hP,
    ← Finset.sum_add_distrib, map_sum, Complex.im_sum]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [← mul_add, map_mul, map_natCast, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    h y ((Set.Finite.mem_toFinset hP).1 hy), mul_zero, zero_mul, add_zero]

end Traces

/-! ### The traces of Frobenius on the stalks of the `Rʳ g_!` at a closed point -/

section Stalks

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Frobenius traces on the stalks of the `Rʳ g_!` at a closed point**, for a family
`g : U' ⟶ V'` of smooth affine curves with nonempty fibre at a closed point `w`, and a realizable
pair `G`, `G'` of lisse sheaves on `U` restricted along `a : U' ⟶ U`: read along `ι`, the traces
of `π_w ^ N` on `(Rʳ g_! a⁻¹G)_w̄` and `(Rʳ g_! a⁻¹G')_w̄` vanish for `r = 0` and `r ≥ 3`, and
`-(Tr R¹ + Tr R¹') + (Tr R² + Tr R²')` is real. By the stalk input these are the traces of the
Frobenius of `κ(w)` on `Hʳ_c` of the fibre, a smooth affine curve over `κ(w)`, where `H⁰_c` and
`Hʳ_c`, `r ≥ 3`, vanish; and the trace formula on the fibre turns the alternating sum into a sum
over the closed points of the fibre of traces at the image points in `U`, which are real. -/
theorem LAdicSheaf.higherDirectImage_traces (R : LAdicSheaf.HigherDirectImageFamily B ℓ)
    (hS : LAdicSheaf.HigherDirectImageStalkInput R) (hT : LisseCurveTraceFormulaInput.{u})
    {k : Type u} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] (hℓ : ℓ ≠ p)
    (ι : ℚ_[ℓ] →+* ℂ) {U : B.Scheme} [IsNoetherian U.1] (fU : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType fU] (G G' : LAdicSheaf.{u, u + 1} B U ℓ) (hG : G.IsLisse)
    (hG' : G'.IsLisse)
    (hreal : ∀ (u : closedPoints U.1) (m : ℕ), 1 ≤ m →
      ι (LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B U ℓ G u.1 (finite_residueField fU u.1 u.2) ^ m) +
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B U ℓ G' u.1 (finite_residueField fU u.1 u.2) ^ m)) ∈
        Set.range ((↑) : ℝ → ℂ))
    {V' U' : B.Scheme} [IsNoetherian V'.1] [IsNoetherian U'.1] (a : U' ⟶ U)
    [LocallyOfFiniteType (B.inclusion.map a)] (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] [SmoothOfRelativeDimension 1 (B.inclusion.map g')]
    [IsAffineHom (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (fV' : V'.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV'] (w : closedPoints V'.1)
    (hne : Nonempty ((B.inclusion.map g').fiber w.1)) (N : ℕ) (hN : 0 < N) :
    (ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G) 0) w.1 (finite_residueField fV' w.1 w.2) ^ N)) = 0 ∧
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G') 0) w.1 (finite_residueField fV' w.1 w.2) ^ N)) =
          0) ∧
    (∀ r, 3 ≤ r →
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G) r) w.1 (finite_residueField fV' w.1 w.2) ^ N)) = 0 ∧
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G') r) w.1 (finite_residueField fV' w.1 w.2) ^ N)) =
          0) ∧
    (-(ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G) 1) w.1 (finite_residueField fV' w.1 w.2) ^ N)) +
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G') 1) w.1 (finite_residueField fV' w.1 w.2) ^ N))) +
      (ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G) 2) w.1 (finite_residueField fV' w.1 w.2) ^ N)) +
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a G') 2) w.1 (finite_residueField fV' w.1 w.2) ^
          N)))).im =
      0 := by
  classical
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨w, hw⟩ := w
  dsimp only at hne ⊢
  -- the fibre over `w`, as an object of the site, smooth affine over `κ(w)`
  have hB : B.Contains ((B.inclusion.map g').fiber w) := contains_fiber g' w hw
  let XB : B.Scheme := B.obj ((B.inclusion.map g').fiber w) hB
  have : IsNoetherian ((B.inclusion.map g').fiber w) := isNoetherian_fiber _ _
  have : IsNoetherian XB.1 := ‹IsNoetherian ((B.inclusion.map g').fiber w)›
  have := quasiCompact_fiberToSpecResidueField (B.inclusion.map g') w
  have := isSeparated_fiberToSpecResidueField (B.inclusion.map g') w
  have :=
    AlgebraicGeometry.smoothOfRelativeDimension_fiberToSpecResidueField (B.inclusion.map g') 1 w
  have : @LocallyOfFiniteType _ (Spec (.of (V'.1.residueField w)))
      ((B.inclusion.map g').fiberToSpecResidueField w) :=
    Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField (B.inclusion.map g') w
  have : @QuasiCompact _ (Spec (.of (V'.1.residueField w)))
      ((B.inclusion.map g').fiberToSpecResidueField w) :=
    quasiCompact_fiberToSpecResidueField (B.inclusion.map g') w
  have : @IsSeparated _ (Spec (.of (V'.1.residueField w)))
      ((B.inclusion.map g').fiberToSpecResidueField w) :=
    isSeparated_fiberToSpecResidueField (B.inclusion.map g') w
  have : @SmoothOfRelativeDimension 1 _ (Spec (.of (V'.1.residueField w)))
      ((B.inclusion.map g').fiberToSpecResidueField w) :=
    AlgebraicGeometry.smoothOfRelativeDimension_fiberToSpecResidueField (B.inclusion.map g') 1 w
  have : IsAffine XB.1 := inferInstanceAs (IsAffine ((B.inclusion.map g').fiber w))
  have : Nonempty XB.1 := hne
  -- the residue field `κ(w)` and an algebraic closure, in both spellings of `κ(w)`
  have : Finite (V'.1.residueField w) := finite_residueField fV' w hw
  have : Finite ((B.inclusion.obj V').residueField w) := finite_residueField fV' w hw
  let : Fintype ((B.inclusion.obj V').residueField w) := Fintype.ofFinite _
  let : Fintype (V'.1.residueField w) := Fintype.ofFinite _
  let : Fintype (IsLocalRing.ResidueField ((B.inclusion.obj V').presheaf.stalk w)) :=
    ‹Fintype (V'.1.residueField w)›
  let : Algebra k ((B.inclusion.obj V').residueField w) := (fieldToResidue fV' w).hom.toAlgebra
  have : CharP ((B.inclusion.obj V').residueField w) p :=
    charP_of_injective_algebraMap (algebraMap k ((B.inclusion.obj V').residueField w)).injective p
  have : CharP (V'.1.residueField w) p := ‹CharP ((B.inclusion.obj V').residueField w) p›
  obtain ⟨m, -, hm⟩ := FiniteField.card ((B.inclusion.obj V').residueField w) p
  have hm' : Fintype.card (V'.1.residueField w) = p ^ (m : ℕ) := hm
  let kbar := AlgebraicClosure ((B.inclusion.obj V').residueField w)
  have hdim : topologicalKrullDim XB.1 ≤ 1 :=
    (@topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field _ _ _ _ 1
      ((B.inclusion.map g').fiberToSpecResidueField w)
      (smoothOfRelativeDimension_fiberToSpecResidueField (B.inclusion.map g') 1 w)).le
  have hfin := LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one
    (k := (B.inclusion.obj V').residueField w) B ℓ kbar p m
    hm XB ((B.inclusion.map g').fiberToSpecResidueField w) hdim
  obtain ⟨jw, hjw⟩ := @hS k _ _ U' V' _ _ g' _ _ _ jg' fV' _ ⟨w, hw⟩ hB _ _ _ _ _ kbar _
    (inferInstance : Algebra ((B.inclusion.obj V').residueField w) kbar)
    (inferInstance : IsAlgClosure ((B.inclusion.obj V').residueField w) kbar) p m _ _ hm'
  let b : XB ⟶ U' := ObjectProperty.homMk ((B.inclusion.map g').fiberι w)
  have : IsClosedImmersion ((B.inclusion.map g').fiberι w) :=
    Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι _ hw
  have : LocallyOfFiniteType (B.inclusion.map b) :=
    inferInstanceAs (LocallyOfFiniteType ((B.inclusion.map g').fiberι w))
  -- each stalk trace is a trace on the compactly supported cohomology of the fibre
  have hstalk : ∀ (H : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ),
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a H) r) w (finite_residueField fV' w hw) ^ N)) =
      ι (LinearMap.trace ℚ_[ℓ] _ ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
        (k := (B.inclusion.obj V').residueField w)
        B XB ℓ ((B.inclusion.map g').fiberToSpecResidueField w) jw kbar p m hm
          (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H))
          r).hom ^ N)) := by
    intro H r
    exact @map_trace_pow_eq_of_charpoly_eq _ _ _ _ _ _ _ _ _
      (hfin jw (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H)) r).1 ι _ _
      (@hjw (LAdicSheaf.inverseImage a H) r
        (hfin jw (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H)) r).1) N
  have hlisse : ∀ H : LAdicSheaf.{u, u + 1} B U ℓ, H.IsLisse →
      (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H)).IsLisse :=
    fun H hH => (hH.inverseImage a).inverseImage b
  -- `H⁰_c` and `Hʳ_c`, `r ≥ 3`, of the fibre vanish
  have hvan : ∀ H : LAdicSheaf.{u, u + 1} B U ℓ, H.IsLisse → ∀ r : ℕ, (r = 0 ∨ 3 ≤ r) →
      ι (LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
        (R g' jg' (LAdicSheaf.inverseImage a H) r) w (finite_residueField fV' w hw) ^ N)) = 0 := by
    intro H hH r hr
    rw [hstalk H r]
    have h0 :=
      subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension
        (k := (B.inclusion.obj V').residueField w) B XB ℓ
        ((B.inclusion.map g').fiberToSpecResidueField w) jw kbar _ (hlisse H hH)
    have : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
        (k := (B.inclusion.obj V').residueField w) B XB ℓ
        ((B.inclusion.map g').fiberToSpecResidueField w) jw kbar
        (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H)) r) := by
      rcases hr with rfl | hr
      · exact h0
      · exact LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt
          (k := (B.inclusion.obj V').residueField w) B XB ℓ
          ((B.inclusion.map g').fiberToSpecResidueField w) jw kbar _ r (by omega)
    rw [trace_eq_zero_of_subsingleton, map_zero]
  have h0 := hvan G hG 0 (Or.inl rfl)
  have h0' := hvan G' hG' 0 (Or.inl rfl)
  refine ⟨⟨h0, h0'⟩,
    fun r hr => ⟨hvan G hG r (Or.inr hr), hvan G' hG' r (Or.inr hr)⟩, ?_⟩
  -- the trace formula on the fibre, for `G` and for `G'`
  have htf := fun (H : LAdicSheaf.{u, u + 1} B U ℓ) (hH : H.IsLisse) =>
    hT B XB ℓ ((B.inclusion.obj V').residueField w)
      ((B.inclusion.map g').fiberToSpecResidueField w) jw kbar p m hm hℓ
      (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a H)) (hlisse H hH) N hN
  have hfinpts : {y : closedPoints XB.1 |
      residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1 ∣ N}.Finite :=
    (finite_setOf_closedPoints_residueDegree_le (k := (B.inclusion.obj V').residueField w)
      ((B.inclusion.map g').fiberToSpecResidueField w) N).subset fun y hy =>
        Nat.le_of_dvd hN hy
  have hsum := im_finsum_add_eq_zero ι
    (fun y : closedPoints XB.1 =>
      residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1 ∣ N) hfinpts
    (fun y => residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1)
    (fun y => LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B XB ℓ
      (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a G)) y.1
      (finite_residueField (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1 y.2) ^
        (N / residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1)))
    (fun y => LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B XB ℓ
      (LAdicSheaf.inverseImage b (LAdicSheaf.inverseImage a G')) y.1
      (finite_residueField (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1 y.2) ^
        (N / residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1)))
    (fun y hy => by
      have hd : 0 < residueDegree (k := (B.inclusion.obj V').residueField w)
        ((B.inclusion.map g').fiberToSpecResidueField w) y.1 :=
        Nat.pos_of_dvd_of_pos hy hN
      exact (mem_range_ofReal_iff_im_eq_zero _).1
        (LAdicSheaf.mem_range_ofReal_trace_inverseImage_inverseImage fU G G' hreal a b y.1 _ _
          (Nat.div_pos (Nat.le_of_dvd hN hy) hd)))
  rw [htf G hG, htf G' hG'] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul, pow_one,
    map_add, map_mul, map_pow, map_neg, map_one, Nat.cast_ofNat] at hsum
  rw [hstalk G 1, hstalk G' 1, hstalk G 2, hstalk G' 2]
  rw [hstalk G 0] at h0
  rw [hstalk G' 0] at h0'
  have e0 := congrArg Complex.im h0
  have e0' := congrArg Complex.im h0'
  simp only [Complex.zero_im] at e0 e0'
  simp only [Nat.cast_ofNat, Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.neg_re,
    Complex.one_re, Complex.one_im, neg_one_sq, neg_zero, zero_mul, add_zero,
    one_mul] at hsum e0 e0' ⊢
  linarith

/-- The fibre of a base change `g'` of `g` at a point of its base mapping into the image of `g` is
nonempty. -/
theorem nonempty_fiber_of_isPullback {U U' V' W : Scheme.{u}} {jU : U' ⟶ U} {g' : U' ⟶ V'}
    {g : U ⟶ W} {jV : V' ⟶ W} (h : IsPullback jU g' g jV) (v : V')
    (hv : jV.base v ∈ Set.range g.base) : Nonempty (g'.fiber v) := by
  obtain ⟨z, hz⟩ : v ∈ Set.range (pullback.snd g jV).base := by
    rw [Scheme.Pullback.range_snd]
    exact hv
  have hz' : g'.base (h.isoPullback.inv.base z) = v := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz]
  have hmem : h.isoPullback.inv.base z ∈ Set.range (g'.fiberι v).base := by
    rw [Scheme.Hom.range_fiberι]
    exact hz'
  obtain ⟨x, -⟩ := hmem
  exact ⟨x⟩

/-- **Realizability of the higher direct images of a family of smooth affine curves** (Weil II
1.5, Kedlaya §6), the input `LAdicSheaf.HigherDirectImageRealizableInput` of the induction step
of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), from the
stalks of the `Rʳ g_!` (proper base change), their lisse locus, the trace formula on smooth
curves, and the realizability of `R² g_!`. Let `G` be lisse and realizable with witness `G'`.
Over a nonempty open `V` of the irreducible base, inside the image of `g`, where the `Rʳ g_! G'`
are lisse and `R² g_! G`, `R² g_! G'` are realizable: at a closed point `w`, `H⁰_c` and `Hʳ_c`,
`r ≥ 3`, of the fibre vanish, so `R⁰ g_! G` and `Rʳ g_! G` are realizable with witness `Rʳ g_! G'`;
`R² g_! G` is realizable by assumption; and the trace formula on the fibre makes
`-(Tr R¹ G + Tr R¹ G') + (Tr R² G + Tr R² G')` real, so `R¹ g_! G` is realizable with witness
`R¹ g_! G' ⊞ (B ⊞ B')`, `B`, `B'` witnesses for `R² g_! G` and `R² g_! G'`. -/
theorem LAdicSheaf.higherDirectImageRealizableInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ)
    (hS : LAdicSheaf.HigherDirectImageStalkInput R)
    (hL : LAdicSheaf.HigherDirectImageLisseLocusInput R) (hT : LisseCurveTraceFormulaInput.{u})
    (hTop : LAdicSheaf.HigherDirectImageTopRealizableInput R) :
    LAdicSheaf.HigherDirectImageRealizableInput R := by
  intro k _ _ p n _ _ hcard hℓ q ι U W _ _ _ g _ _ _ _ _ fW _ _ _ G w hGl _ hGr hW hU
  obtain ⟨G', hG'l, hreal⟩ := hGr
  have hG'r : LAdicSheaf.IsIotaRealizable B U ℓ (B.inclusion.map g ≫ fW) G' ι :=
    ⟨G, hGl, fun y m hm => by rw [add_comm]; exact hreal y m hm⟩
  have : Nonempty W.1 := ⟨(B.inclusion.map g).base hU.some⟩
  obtain ⟨V₁, j₁, hj₁, hV₁ne, hV₁⟩ := hL U W g G' hG'l inferInstance
  obtain ⟨V₂, j₂, hj₂, hV₂ne, hV₂⟩ := hTop k p n hcard hℓ ι U W g fW G hGl ⟨G', hG'l, hreal⟩ hW hU
  obtain ⟨V₃, j₃, hj₃, hV₃ne, hV₃⟩ := hTop k p n hcard hℓ ι U W g fW G' hG'l hG'r hW hU
  -- the good open: the intersection of the three opens and of the image of `g`
  have hopen : ∀ (V : B.Scheme) (j : V ⟶ W), IsOpenImmersion (B.inclusion.map j) →
      IsOpen (Set.range (B.inclusion.map j).base) := fun V j hj =>
    (B.inclusion.map j).isOpenEmbedding.isOpen_range
  have : Smooth (B.inclusion.map g) := SmoothOfRelativeDimension.smooth 1 _
  have : Flat (B.inclusion.map g) := inferInstance
  have : LocallyOfFinitePresentation (B.inclusion.map g) := inferInstance
  have : UniversallyOpen (B.inclusion.map g) := UniversallyOpen.of_flat (f := B.inclusion.map g)
  have : IrreducibleSpace (B.inclusion.obj W) := hW
  have himg : IsOpen (Set.range (B.inclusion.map g).base) :=
    (B.inclusion.map g).isOpenMap.isOpen_range
  have hne : ∀ (V : B.Scheme) (j : V ⟶ W), Nonempty V.1 →
      (Set.range (B.inclusion.map j).base).Nonempty := fun V j hV =>
    ⟨_, hV.some, rfl⟩
  obtain ⟨x, hx⟩ : (Set.range (B.inclusion.map j₁).base ∩ Set.range (B.inclusion.map j₂).base ∩
      Set.range (B.inclusion.map j₃).base ∩ Set.range (B.inclusion.map g).base).Nonempty :=
    nonempty_preirreducible_inter (((hopen _ _ hj₁).inter (hopen _ _ hj₂)).inter (hopen _ _ hj₃))
      himg (nonempty_preirreducible_inter ((hopen _ _ hj₁).inter (hopen _ _ hj₂)) (hopen _ _ hj₃)
        (nonempty_preirreducible_inter (hopen _ _ hj₁) (hopen _ _ hj₂) (hne _ _ hV₁ne)
          (hne _ _ hV₂ne)) (hne _ _ hV₃ne)) ⟨_, hU.some, rfl⟩
  let O : W.1.Opens :=
    ⟨_, (((hopen _ _ hj₁).inter (hopen _ _ hj₂)).inter (hopen _ _ hj₃)).inter himg⟩
  let V : B.Scheme := B.obj O (AlgebraicGeometry.BigEtaleOver.contains_opens B W.2 O)
  let jV : V ⟶ W := ObjectProperty.homMk O.ι
  have : IsOpenImmersion (B.inclusion.map jV) := inferInstanceAs (IsOpenImmersion O.ι)
  have hO : Set.range (B.inclusion.map jV).base = (O : Set W.1) := Scheme.Opens.range_ι O
  have hlift : ∀ (Vi : B.Scheme) (ji : Vi ⟶ W) (_ : IsOpenImmersion (B.inclusion.map ji)),
      (O : Set W.1) ⊆ Set.range (B.inclusion.map ji).base →
      ∃ l : V ⟶ Vi, l ≫ ji = jV := by
    intro Vi ji hji hsub
    refine ⟨ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map ji) O.ι ?_), ?_⟩
    · rw [Scheme.Opens.range_ι]; exact hsub
    · exact (ObjectProperty.ι _).map_injective (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨l₁, hl₁⟩ := hlift V₁ j₁ hj₁ fun y hy => hy.1.1.1
  obtain ⟨l₂, hl₂⟩ := hlift V₂ j₂ hj₂ fun y hy => hy.1.1.2
  obtain ⟨l₃, hl₃⟩ := hlift V₃ j₃ hj₃ fun y hy => hy.1.2
  refine ⟨V, jV, inferInstance, ⟨⟨x, hx⟩⟩, ?_⟩
  intro V' U' _ _ jV' jU g' _ _ _ jg' hjV' hpb fV' _ r
  have := hjV'
  -- the base change `g'` is again smooth of relative dimension one and affine
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (B.inclusion.map g') :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hpb ‹_›
  have : IsAffineHom (B.inclusion.map g') := MorphismProperty.of_isPullback hpb ‹_›
  have : IsOpenImmersion (B.inclusion.map (jV' ≫ jV)) := by
    rw [Functor.map_comp]; infer_instance
  have : IsOpenImmersion (B.inclusion.map jU) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have hpbi : ∀ (Vi : B.Scheme) (ji : Vi ⟶ W) (li : V ⟶ Vi), li ≫ ji = jV →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
        (B.inclusion.map ((jV' ≫ li) ≫ ji)) := by
    intro Vi ji li hli
    rwa [Category.assoc, hli]
  have hopi : ∀ (Vi : B.Scheme) (li : V ⟶ Vi) (ji : Vi ⟶ W), li ≫ ji = jV →
      IsOpenImmersion (B.inclusion.map ji) → IsOpenImmersion (B.inclusion.map (jV' ≫ li)) := by
    intro Vi li ji hli hji
    have := hji
    have : IsOpenImmersion (B.inclusion.map li ≫ B.inclusion.map ji) := by
      rw [← Functor.map_comp, hli]; infer_instance
    have : IsOpenImmersion (B.inclusion.map li) :=
      IsOpenImmersion.of_comp (B.inclusion.map li) (B.inclusion.map ji)
    rw [Functor.map_comp]; infer_instance
  have hlisse := hV₁ V' U' (jV' ≫ l₁) jU g' jg' (hopi _ _ _ hl₁ hj₁) (hpbi _ _ _ hl₁)
  -- the fibres over the closed points of `V'` are nonempty
  have hfib : ∀ y : V'.1, Nonempty ((B.inclusion.map g').fiber y) := by
    intro y
    refine nonempty_fiber_of_isPullback hpb y ?_
    have hy : (B.inclusion.map (jV' ≫ jV)).base y ∈ (O : Set W.1) := by
      rw [← hO, Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp]
      exact ⟨_, rfl⟩
    exact hy.2
  have key := fun (y : closedPoints V'.1) (N : ℕ) (hN : 1 ≤ N) =>
    LAdicSheaf.higherDirectImage_traces R hS hT hℓ ι (B.inclusion.map g ≫ fW) G G' hGl hG'l hreal
      jU g' jg' fV' y (hfib y.1) N hN
  obtain ⟨E, hEl, hE⟩ :=
    hV₂ V' U' (jV' ≫ l₂) jU g' jg' (hopi _ _ _ hl₂ hj₂) (hpbi _ _ _ hl₂) fV'
  obtain ⟨E', hE'l, hE'⟩ :=
    hV₃ V' U' (jV' ≫ l₃) jU g' jg' (hopi _ _ _ hl₃ hj₃) (hpbi _ _ _ hl₃) fV'
  rcases Nat.lt_or_ge r 3 with hr | hr
  · interval_cases r
    · -- `R⁰`: the traces vanish
      refine ⟨_, hlisse 0, fun y N hN => ?_⟩
      rw [mem_range_ofReal_iff_im_eq_zero, map_add, (key y N hN).1.1, (key y N hN).1.2,
        add_zero, Complex.zero_im]
    · -- `R¹`: the trace formula on the fibres
      refine ⟨_ ⊞ (E ⊞ E'), (hlisse 1).biprod (hEl.biprod hE'l), fun y N hN => ?_⟩
      rw [LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow,
        LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow, mem_range_ofReal_iff_im_eq_zero]
      have h1 := (key y N hN).2.2
      have h2 := (mem_range_ofReal_iff_im_eq_zero _).1 (hE y N hN)
      have h3 := (mem_range_ofReal_iff_im_eq_zero _).1 (hE' y N hN)
      simp only [map_add, Complex.add_im, Complex.neg_im] at h1 h2 h3 ⊢
      linarith
    · -- `R²`: by assumption
      exact ⟨E, hEl, hE⟩
  · -- `Rʳ`, `r ≥ 3`: the traces vanish
    refine ⟨_, hlisse r, fun y N hN => ?_⟩
    rw [mem_range_ofReal_iff_im_eq_zero, map_add, ((key y N hN).2.1 r hr).1,
      ((key y N hN).2.1 r hr).2, add_zero, Complex.zero_im]

end Stalks

end Stacks.EtaleCohomology

end
