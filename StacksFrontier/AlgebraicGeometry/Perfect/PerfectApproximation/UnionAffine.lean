module

public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Perfect.LiftingComplexes.General
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Transport
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximation by perfect complexes across an affine open

Let `X` be a scheme covered by two opens `U` and `V` with `U` quasi-compact, `V` affine and
`U ∩ V` quasi-compact. If approximation by perfect complexes holds on `U`, then it holds on `X`.
This is [Stacks, Tag 08ER], the inductive step of the proof that approximation holds on every
quasi-compact quasi-separated scheme.

## Main results

* `AlgebraicGeometry.PerfectApproximation.exists_nonneg_of_approximationByPerfectComplexes`: the
  integer of [Stacks, Tag 08EN] may be taken nonnegative.
* `AlgebraicGeometry.PerfectApproximation.approximationByPerfectComplexes_sup_affine` and
  `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_sup_affine`:
  **[Stacks, Tag 08ER]**, in the two encodings of the property of [Stacks, Tag 08EN].

## Implementation notes

**The integer.** Write `a` for the integer of [Stacks, Tag 08EN] attached to `T ∩ U` on `U` and
`b` for the one attached to `T ∖ U` on `V`; the integer the proof produces for `(X, T)` is
`a + b`, and both `a` and `b` are taken nonnegative, which is possible because enlarging the
integer strengthens the hypotheses of [Stacks, Tag 08EN]. The source instead takes the maximum
of the two, with `b` computed as the number of affine opens covering `V ∖ (T ∖ U)`; the sum is
what makes the two cases of the induction below meet, and the maximum does not.

**The induction.** It is on the largest degree `t` in which the cohomology of `E` survives on
`U` — not on the largest degree in which it survives on `X`, which is the induction of
[Stacks, Tag 08EQ] carried out in
`AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep`. That is why the
induction is written out here rather than taken from there: the vanishing that decreases is
vanishing after restriction to `U`, and the surjectivity the step produces is surjectivity after
restriction to `U`. Everything else is reused: the class the induction runs on is
`AlgebraicGeometry.PerfectApproximation.ApproximationClass`, stable under the cones that appear
by `AlgebraicGeometry.PerfectApproximation.approximationClass_obj₃_of_distinguished`, and the
passage from an approximation of the cone to an approximation of `E` is
`DerivedCategory.exists_approximatesFrom_of_triangle`.

* The base case is `t < m - b`: there the cohomology of `E` is supported on `T ∖ U` in every
  degree `≥ m - b`, so [Stacks, Tag 08EQ] on the affine open `V` approximates `E|_V` and
  [Stacks, Tag 08EP] extends that approximation across `V`. Support on `T ∖ U` rather than on
  `T` is what [Stacks, Tag 08EP] needs, since it asks the closed subset to be contained in the
  open subscheme.
* The step is `m - b ≤ t`: there [Stacks, Tag 08EN] on `U`, applied in degree `t`, gives a
  perfect `P` on `U` surjective on `H^t`, and the glueing step of [Stacks, Tag 09IM],
  `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_cover_spec`, produces from it a
  perfect `R` on `X` supported on `T` with a map to `E` whose restriction to `U` is still
  surjective on `H^t`. That lemma does over `V` exactly what the source does with
  [Stacks, Tag 08EK], [Stacks, Tag 08EH] and [Stacks, Tag 08DG], and it presents the affine open
  as `Spec Γ(X, V)` through `AlgebraicGeometry.IsAffineOpen.fromSpec`, which is what keeps the
  affine lifting results applicable without transporting them off a spectrum. Its record of
  `R|_U` as `P ⊞ P[1]` is what bounds the cohomology of `R` on `U`, and hence lets
  `DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top`, applied in `D(𝒪_U)` to the
  restricted triangle, lower the degree by one.

**Quasi-separatedness is not assumed**, and `(T ∖ U)ᶜ` need not be retrocompact in `X`: what is
needed is its retrocompactness inside `V`, where it is the union of the inverse image of `Tᶜ`
and the inverse image of `U`, and the second is a quasi-compact open of the affine — hence
quasi-separated — scheme `V`.

## References

* [Stacks Project, Tag 08ER](https://stacks.math.columbia.edu/tag/08ER)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
* [Stacks Project, Tag 08EP](https://stacks.math.columbia.edu/tag/08EP)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe u

namespace AlgebraicGeometry.PerfectApproximation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The integer of [Stacks, Tag 08EN] may be taken nonnegative.** Enlarging it makes both
hypotheses on the derived object stronger: `m`-pseudo-coherence is monotone in `m`, and the
support condition is asked in fewer degrees. -/
theorem exists_nonneg_of_approximationByPerfectComplexes {Y : Scheme.{u}}
    (h : ApproximationByPerfectComplexes Y) (T : Set Y) (hT : IsClosed T)
    (hTc : IsRetrocompact (Tᶜ : Set Y)) :
    ∃ r : ℤ, 0 ≤ r ∧ ∀ (E : DerivedCategory.{u + 1} Y.Modules) (m : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj E).IsQuasicoherent) →
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E (m - r) →
      (∀ (i : ℤ) (x : Y), m - r ≤ i → x ∉ T →
        IsZero (TopCat.Presheaf.stalk (X := Y)
          (((DerivedCategory.homologyFunctor Y.Modules i).obj E).val.presheaf) x)) →
      ApproximationHolds Y T E m := by
  obtain ⟨r, hr⟩ := h T hT hTc
  have hle : r ≤ max r 0 := le_max_left _ _
  exact ⟨max r 0, le_max_right _ _, fun E m hqc hpc hsupp =>
    hr E m hqc (hpc.mono (by omega)) fun i x hi hx => hsupp i x (by omega) hx⟩

/-- **[Stacks, Tag 08ER].** Let `X` be a scheme, let `X = U ∪ V` be an open covering with `U`
quasi-compact, `V` affine and `U ∩ V` quasi-compact. If approximation by perfect complexes holds
on `U`, then it holds on `X`.

The integer attached to a closed subset `T` with retrocompact complement is `a + b`, where `a`
is the integer attached on `U` to `T ∩ U` and `b` the integer attached on `V` to `T ∖ U`, both
taken nonnegative. Given a triple `(T, E, m)` satisfying the hypotheses for that integer, the
approximation is built by induction on the largest degree in which the cohomology of `E`
survives on `U`: below `m - b` the cohomology of `E` is supported on `T ∖ U ⊆ V` in all relevant
degrees and [Stacks, Tag 08EQ] on `V` together with [Stacks, Tag 08EP] finishes, while above it
the glueing step of [Stacks, Tag 09IM] turns an approximation on `U` in that degree into a
perfect object on `X` surjective there, and the cone of the resulting map survives on `U` in one
degree fewer. -/
@[stacks 08ER "approximation by perfect complexes passes from a quasi-compact open to its union \
with an affine open meeting it in a quasi-compact open; nothing is carried, and the statement is \
at the standard derived category of the sheaves of modules of the scheme, the model the whole \
chapter is written at"]
theorem approximationByPerfectComplexes_sup_affine (X : Scheme.{u}) (U V : X.Opens)
    (hVaff : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (hUc : IsCompact (U : Set X)) (hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hUapp : ApproximationByPerfectComplexes (U : Scheme.{u})) :
    ApproximationByPerfectComplexes X := by
  classical
  let : IsAffine (V : Scheme.{u}) := hVaff
  let : CompactSpace (U : Scheme.{u}) := isCompact_iff_compactSpace.mp hUc
  intro T hT hTc
  -- every point of `X` lies in one of the two opens
  have hmem : ∀ x : X, x ∈ (U : Set X) ∨ x ∈ (V : Set X) := fun x => by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rwa [← hcover] at hx
  -- the part of `T` outside `U` is a closed subset of `V`
  have hT'closed : IsClosed (T \ (U : Set X)) := hT.sdiff U.2
  have hT'V : T \ (U : Set X) ⊆ (V : Set X) := fun x hx => (hmem x).resolve_left hx.2
  -- the two integers of Tag 08EN
  obtain ⟨a, ha0, ha⟩ := exists_nonneg_of_approximationByPerfectComplexes hUapp
    (⇑U.ι.base ⁻¹' T) (hT.preimage U.ι.base.hom.continuous)
    (by rw [← Set.preimage_compl]; exact hTc.preimage_of_isOpenEmbedding U.ι.isOpenEmbedding)
  obtain ⟨b, hb0, hb⟩ := exists_nonneg_of_approximationByPerfectComplexes
    (approximationByPerfectComplexes_of_isAffine (V : Scheme.{u}))
    (⇑V.ι.base ⁻¹' (T \ (U : Set X)))
    (hT'closed.preimage V.ι.base.hom.continuous)
    (by
      have hVU : IsCompact (⇑V.ι.base ⁻¹' (U : Set X)) := by
        refine Stacks.Perfect.LiftingComplexes.isCompact_preimage V.ι (U : Set X) ?_
        rw [Scheme.Opens.range_ι]
        simpa using hUVc
      have hVUopen : IsOpen (⇑V.ι.base ⁻¹' (U : Set X)) :=
        U.2.preimage V.ι.base.hom.continuous
      have hsets : ((⇑V.ι.base ⁻¹' (T \ (U : Set X)))ᶜ : Set (V : Scheme.{u})) =
          (⇑V.ι.base ⁻¹' (Tᶜ)) ∪ (⇑V.ι.base ⁻¹' (U : Set X)) := by
        ext y
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_union, not_and,
          not_not]
        tauto
      rw [hsets]
      exact (hTc.preimage_of_isOpenEmbedding V.ι.isOpenEmbedding).union
        fun W hWc hWo => QuasiSeparatedSpace.inter_isCompact _ _ hVUopen hVU hWo hWc)
  refine ⟨a + b, fun E m hqc hpc hsupp => ?_⟩
  -- the data the glueing step of Tag 09IM asks for
  have hcover' : ∀ x : X,
      x ∈ Set.range ⇑U.ι.base ∨ x ∈ Set.range ⇑hVaff.fromSpec.base := fun x =>
    (hmem x).imp (fun h => ⟨⟨x, h⟩, rfl⟩) (fun h => hVaff.range_fromSpec ▸ h)
  have hTf : IsCompact ((⇑hVaff.fromSpec.base ⁻¹' T)ᶜ : Set (Spec Γ(X, V))) := by
    rw [← Set.preimage_compl]
    refine Stacks.Perfect.LiftingComplexes.isCompact_preimage hVaff.fromSpec (Tᶜ) ?_
    rw [hVaff.range_fromSpec]
    exact hTc hVaff.isCompact V.2
  have hW : IsCompact ((hVaff.fromSpec ⁻¹ᵁ U.ι.opensRange : (Spec Γ(X, V)).Opens) :
      Set (Spec Γ(X, V))) := by
    change IsCompact (⇑hVaff.fromSpec.base ⁻¹' ((U.ι.opensRange : X.Opens) : Set X))
    refine Stacks.Perfect.LiftingComplexes.isCompact_preimage hVaff.fromSpec _ ?_
    rw [hVaff.range_fromSpec, Scheme.Opens.opensRange_ι]
    simpa using hUVc
  -- the induction on the top degree in which the cohomology of `F` survives on `U`
  suffices H : ∀ n : ℕ, ∀ s : ℤ, s < (m - b) + n →
      ∀ F : DerivedCategory.{u + 1} X.Modules,
      ApproximationClass X T (m - (a + b)) (m - (a + b)) F →
      (∀ i : ℤ, s < i → IsZero ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules i).obj
        ((derivedRestrict U.ι).obj F))) →
      ApproximationHolds X T F m by
    obtain ⟨t₀, ht₀⟩ := RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom
      (X := (U : Scheme.{u}).toRingedSpace) ((derivedRestrict U.ι).obj E) (m - (a + b))
      (isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion U.ι E (m - (a + b)) hpc)
    exact H (t₀ - (m - b)).toNat (t₀ - 1) (by omega) E
      ⟨hqc, hpc, fun i hi x hx => hsupp i x hi hx⟩ fun i hi => ht₀ i (by omega)
  intro n
  induction n with
  | zero =>
    intro s hs F hF hvan
    obtain ⟨hqcF, hpcF, hsuppF⟩ := hF
    have hs' : s < m - b := by simpa using hs
    -- the cohomology of `F` vanishes at the points of `U` in every degree `> s`
    have hstalkU : ∀ (i : ℤ) (x : X), x ∈ (U : Set X) → s < i →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x) :=
      fun i x hx hi => (isZero_stalk_of_isZero (hvan i hi) ⟨x, hx⟩).of_iso
        (stalkHomologyDerivedRestrictIso U.ι F i ⟨x, hx⟩).symm
    -- hence it is supported on `T ∖ U` in every degree `≥ m - b`
    have hsuppT' : ∀ (i : ℤ) (x : X), m - b ≤ i → x ∉ T \ (U : Set X) →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj F).val.presheaf) x) := by
      intro i x hi hx
      by_cases hxT : x ∈ T
      · exact hstalkU i x (by by_contra hxU; exact hx ⟨hxT, hxU⟩) (by omega)
      · exact hsuppF i (by omega) x hxT
    -- Tag 08EQ on the affine open, extended across it by Tag 08EP
    have happrox := hb ((derivedRestrict V.ι).obj F) m
      (Stacks.DerivedQCoh.isDQCoh_derivedRestrict V.ι F hqcF)
      (isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion V.ι F (m - b) (hpcF.mono (by omega)))
      (fun i y hi hy => (hsuppT' i (V.ι.base y) hi hy).of_iso
        (stalkHomologyDerivedRestrictIso V.ι F i y))
    have happrox' := (approximationHolds_iff_hasPerfectApproximation (V : Scheme.{u})
      (⇑V.ι.base ⁻¹' (T \ (U : Set X))) _ m).1
      (approximationHolds_of_iso (V : Scheme.{u}) (⇑V.ι.base ⁻¹' (T \ (U : Set X)))
        ((Stacks.DerivedQCoh.derivedRestrictionIso V).app F).symm m happrox)
    obtain ⟨P, hPperf, hPT, α, hαiso, hαepi⟩ :=
      hasPerfectApproximation_of_open X V (T \ (U : Set X)) hT'closed hT'V F m happrox'
        fun i hi x hx => hsuppT' i x (by omega) hx
    exact ⟨P, hPperf, fun i x hx => hPT i x fun hx' => hx hx'.1, α, hαiso, hαepi⟩
  | succ n ih =>
    intro s hs F hF hvan
    rcases lt_or_ge s ((m - b) + n) with hlt | hge
    · exact ih s (by exact_mod_cast hlt) F hF hvan
    obtain ⟨hqcF, hpcF, hsuppF⟩ := hF
    have hsb : m - b ≤ s := by omega
    -- the approximation on `U` in degree `s`
    obtain ⟨P, hPperf, hPT, α, hα⟩ := ha ((derivedRestrict U.ι).obj F) s
      (Stacks.DerivedQCoh.isDQCoh_derivedRestrict U.ι F hqcF)
      (isPseudoCoherentFrom_derivedRestrict_of_isOpenImmersion U.ι F (s - a) (hpcF.mono (by omega)))
      (fun i y hi hy => (hsuppF i (by omega) (U.ι.base y) hy).of_iso
        (stalkHomologyDerivedRestrictIso U.ι F i y))
    have hPvan : ∀ i : ℤ, s < i →
        IsZero ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules i).obj P) := by
      intro i hi
      have := hα.1 i hi
      exact (hvan i hi).of_iso (asIso ((DerivedCategory.homologyFunctor _ i).map α))
    -- the glueing step of Tag 09IM
    obtain ⟨R, β, hRperf, hRT, ⟨eR⟩, i₀, p₀, -, hiβ⟩ :=
      Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_cover_spec U.ι hVaff.fromSpec
        hcover' T hT hTf hW F hqcF P hPperf hPT α
    have hRvan : ∀ i : ℤ, s < i →
        IsZero ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules i).obj
          ((derivedRestrict U.ι).obj R)) := by
      intro i hi
      refine IsZero.of_iso ?_
        ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules i).mapIso eR)
      exact DerivedCategory.isZero_homology_obj₂_of_distinguished
        (binaryBiproductTriangle P (P⟦(1 : ℤ)⟧))
        (binaryBiproductTriangle_distinguished P (P⟦(1 : ℤ)⟧)) i (hPvan i hi)
        ((DerivedCategory.isZero_homology_shift_iff P i).2 (hPvan (i + 1) (by omega)))
    have hepi : Epi ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules s).map
        ((derivedRestrict U.ι).map β)) := by
      have := hα.2
      exact epi_of_epi_fac
        (f := (DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules s).map i₀)
        (by rw [← Functor.map_comp, hiβ])
    -- the cone of the glued map, and the induction hypothesis on it
    obtain ⟨F', g', h', hTri⟩ := Pretriangulated.distinguished_cocone_triangle β
    have hF' : ApproximationClass X T (m - (a + b)) (m - (a + b)) F' :=
      approximationClass_obj₃_of_distinguished X T (m - (a + b)) (m - (a + b))
        (Pretriangulated.Triangle.mk β g' h') hTri ⟨hRperf, hRT⟩ ⟨hqcF, hpcF, hsuppF⟩
    have hvan' : ∀ i : ℤ, s - 1 < i →
        IsZero ((DerivedCategory.homologyFunctor (U : Scheme.{u}).Modules i).obj
          ((derivedRestrict U.ι).obj F')) := by
      let := Stacks.DerivedQCoh.OpenLift.isTriangulated_derivedRestrict U.ι
      intro i hi
      exact DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top
        ((derivedRestrict U.ι).mapTriangle.obj (Pretriangulated.Triangle.mk β g' h'))
        ((derivedRestrict U.ι).map_distinguished _ hTri) s hRvan hvan hepi i (by omega)
    obtain ⟨R', hR'perf, hR'T, α', hα'⟩ := ih (s - 1) (by push_cast at hs ⊢; omega) F' hF' hvan'
    obtain ⟨P'', u, v, hTri'', φ, hφ⟩ := DerivedCategory.exists_approximatesFrom_of_triangle
      (Pretriangulated.Triangle.mk β g' h') hTri m α' hα'
    obtain ⟨hP''perf, hP''T⟩ := isAdmissible_obj₂_of_distinguished X T
      (Pretriangulated.Triangle.mk u v (α' ≫ h')) hTri'' ⟨hRperf, hRT⟩ ⟨hR'perf, hR'T⟩
    exact ⟨P'', hP''perf, hP''T, φ, hφ⟩

/-- **[Stacks, Tag 08ER]**, in the encoding of
`AlgebraicGeometry.HasApproximationByPerfectComplexes`. -/
@[stacks 08ER "the same statement in the second encoding of the property of Tag 08EN; nothing \
is carried, and the derived category is the standard model, as in the first encoding"]
theorem hasApproximationByPerfectComplexes_sup_affine (X : Scheme.{u}) (U V : X.Opens)
    (hVaff : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (hUc : IsCompact (U : Set X)) (hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hUapp : HasApproximationByPerfectComplexes (U : Scheme.{u})) :
    HasApproximationByPerfectComplexes X :=
  (approximationByPerfectComplexes_iff X).1
    (approximationByPerfectComplexes_sup_affine X U V hVaff hcover hUc hUVc
      ((approximationByPerfectComplexes_iff (U : Scheme.{u})).2 hUapp))

end AlgebraicGeometry.PerfectApproximation

end
