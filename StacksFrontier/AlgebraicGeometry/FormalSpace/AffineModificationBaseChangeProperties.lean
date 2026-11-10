module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfAdicCompletion

/-!
# Properties of modifications are unchanged by an isomorphism on completions

Let `φ : A →+* R` be a homomorphism of rings, `A` Noetherian, inducing an isomorphism
`A^∧ ≅ R^∧` of the `I`-adic and `I R`-adic completions. Stacks 0AE5
(`AlgebraicGeometry.FormalSpace.isEquivalence_affineModificationBaseChange`) says that base
change along `Spec R ⟶ Spec A` is an equivalence between the categories of Stacks 0AS2 for
`(A, I)` and `(R, I R)`. **Stacks 0BH5** says that if `f : X' ⟶ Spec A` corresponds to
`g : Y' ⟶ Spec R` under it, then `f` is quasi-compact, quasi-separated, separated, proper,
respectively finite, exactly when `g` is.

## Main results

* `AlgebraicGeometry.FormalSpace.fpqcLocalProperties_iff_of_affineModificationBaseChange_obj_iso`:
  `f` is quasi-compact, quasi-separated, separated, proper, respectively finite, exactly when its
  corresponding object `g` is.
* `AlgebraicGeometry.FormalSpace.prop_iff_of_affineModificationBaseChange_obj_iso`: the same for
  any property of morphisms which is stable under base change, local on the base for the fpqc
  topology and true for isomorphisms.
* `AlgebraicGeometry.FormalSpace.isFpqcCovering_completionAwayCover`: `Spec A^∧` and the
  `Spec A_{tⱼ}` form an fpqc covering of `Spec A`.
* `exists_comap_algebraMap_adicCompletion_eq`: every prime of `A` containing `I` lies under a
  prime of `A^∧`.
* `AlgebraicGeometry.Space.isFpqcCovering_yoneda_map_of_mem_fpqcPrecoverage`: a finite family
  of morphisms of affine objects of the site which is an fpqc covering of schemes is an fpqc
  covering of algebraic spaces.

## Implementation notes

"`f` corresponds to `g` via the equivalence" is an isomorphism `e` from the image of `f` under
the base change functor of Stacks 0AE5 to `g`. Since that functor is an equivalence, every `g`
corresponds to some `f`. The five properties are those of morphisms of algebraic spaces over `S`
in this library: `AlgebraicGeometry.Space.IsQuasiCompact` (Stacks 03HE),
`AlgebraicGeometry.Space.IsQuasiSeparated` and `AlgebraicGeometry.Space.IsSeparated`
(Stacks 03HL), `AlgebraicGeometry.Space.IsProper` (Stacks 03ZM) and
`AlgebraicGeometry.Space.IsFinite` (Stacks 03ZP).

## References

* [Stacks Project, Tag 0BH5](https://stacks.math.columbia.edu/tag/0BH5)
* [Stacks Project, Tag 0AE5](https://stacks.math.columbia.edu/tag/0AE5)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041N](https://stacks.math.columbia.edu/tag/041N)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### The primes of the completion and of the localizations -/

section Algebra

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- Every prime of a Noetherian ring `A` containing `I` is the contraction of a prime of the
`I`-adic completion of `A`. -/
theorem exists_comap_algebraMap_adicCompletion_eq (p : PrimeSpectrum A)
    (hp : I ≤ p.asIdeal) :
    ∃ q : PrimeSpectrum (AdicCompletion I A),
      PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q = p := by
  have hne : p.asIdeal.map (algebraMap A (AdicCompletion I A)) ≠ ⊤ := by
    intro htop
    have h := congrArg (Ideal.map (AdicCompletion.evalₐ I 1).toRingHom) htop
    rw [Ideal.map_map, Ideal.map_top] at h
    have hcomp : (AdicCompletion.evalₐ I 1).toRingHom.comp
        (algebraMap A (AdicCompletion I A)) = Ideal.Quotient.mk (I ^ 1) := by
      ext a
      simp
    rw [hcomp] at h
    have h' := congrArg (Ideal.comap (Ideal.Quotient.mk (I ^ 1))) h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, pow_one, sup_eq_left.mpr hp] at h'
    exact p.isPrime.ne_top h'
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  let q := Q.comap (algebraMap A (AdicCompletion I A))
  have hpq : p.asIdeal ≤ q := Ideal.map_le_iff_le_comap.mp hle
  have : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨P, -, hP, hPover⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p.asIdeal) (q := q) Q hpq
  exact ⟨⟨P, hP⟩, PrimeSpectrum.ext hPover.over.symm⟩

end Algebra

/-! ### An fpqc covering of the big fppf site by affine objects -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A finite family of morphisms of affine objects of the big fppf site of `S`, whose
underlying family of morphisms of schemes is an fpqc covering, is an fpqc covering of
algebraic spaces over `S` after Yoneda. -/
theorem isFpqcCovering_yoneda_map_of_mem_fpqcPrecoverage {ι : Type (u + 1)} [Finite ι]
    {V : BigFppfOver B S hS} (U : ι → BigFppfOver B S hS) (b : ∀ i, U i ⟶ V)
    (hU : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (U i)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hmem : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i ↦ (BigFppfOver.toScheme B S hS).map (b i)) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj V)) :
    IsFpqcCovering B S hS (fun i ↦ yoneda.map (b i)) := by
  let G := BigFppfOver.toScheme B S hS
  let Af := BigAffineFppf.inclusion B S hS
  have hflat : ∀ i, Flat (G.map (b i)) := ((Scheme.ofArrows_mem_precoverage_iff _).mp hmem.2).2
  refine ⟨fun i ↦ isFlat_yoneda_map B S hS (b i) (hflat i), fun T g ↦ ?_⟩
  let h : Af.obj T ⟶ V := yoneda.preimage g
  have hg : yoneda.map h = g := yoneda.map_preimage _
  have sq (i : ι) := (IsPullback.of_hasPullback h (b i)).map G
  have : IsAffine (G.obj V) := hV
  have : IsAffine (G.obj (Af.obj T)) := T.property
  have hW (i : ι) : IsAffine (G.obj (pullback h (b i))) :=
    have := hU i
    .of_isIso (sq i).isoPullback.hom
  let W (i : ι) : BigAffineFppf B S hS := ⟨pullback h (b i), hW i⟩
  let E : PreZeroHypercover.{u + 1} T :=
    ⟨ι, W, fun i ↦ ObjectProperty.homMk (pullback.fst h (b i))⟩
  refine ⟨E, inferInstanceAs (Finite ι), ?_, fun i ↦ ⟨i, yoneda.map (pullback.snd h (b i)), ?_⟩⟩
  · rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
    exact Precoverage.mem_coverings_of_isPullback (fun i ↦ G.map (b i)) hmem (G.map h)
      (fun i ↦ G.map (pullback.fst h (b i))) (fun i ↦ G.map (pullback.snd h (b i))) sq
  · change yoneda.map (pullback.snd h (b i)) ≫ yoneda.map (b i) =
      yoneda.map (pullback.fst h (b i)) ≫ g
    rw [← hg, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

end AlgebraicGeometry.Space

/-! ### The covering of `Spec A` by `Spec A^∧` and the `Spec A_t`, `t ∈ I` -/

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] (I : Ideal A) (hA : B.Contains (Spec (.of A)))
  (s : Spec (.of A) ⟶ S) {k : ℕ} (t : Fin k → A)

/-- The spectrum of a localization `A_a` of a ring `A` whose spectrum is in the site is in the
site. -/
theorem contains_spec_away {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A))) (a : A) :
    B.Contains (Spec (.of (Localization.Away a))) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))) hA

/-- The members of the covering of `Spec A` by `Spec A^∧` (index `none`) and the `Spec A_{t j}`
(index `some j`), as objects of the big fppf site of `S`. -/
def completionAwayCoverObj (I : Ideal A) (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    {k : ℕ} (t : Fin k → A) : Option (Fin k) → BigFppfOver B S hS
  | none => affineOver B S hS (B.contains_spec_adicCompletion hA I)
      (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ s)
  | some j => affineOver B S hS (contains_spec_away hA (t j))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (t j)))) ≫ s)

/-- The morphisms of the covering of `Spec A` by `Spec A^∧` and the `Spec A_{t j}`. -/
def completionAwayCoverHom (I : Ideal A) (hA : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
    {k : ℕ} (t : Fin k → A) : ∀ j, completionAwayCoverObj I hA s t j ⟶ affineOver B S hS hA s
  | none => affineOverMap (algebraMap A (AdicCompletion I A)) hA _ s
  | some j => affineOverMap (algebraMap A (Localization.Away (t j))) hA _ s

/-- The members of the covering of `Spec A` by `Spec A^∧` and the `Spec A_{t j}` are affine. -/
theorem isAffine_completionAwayCoverObj (j : Option (Fin k)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (completionAwayCoverObj (hS := hS) I hA s t j)) := by
  rcases j with _ | j <;> exact inferInstanceAs (IsAffine (Spec _))

variable [IsNoetherianRing A]

/-- If `I` is generated by `t 0, …, t (k - 1)`, then `Spec A^∧` and the `Spec A_{t j}` form an
fpqc covering of `Spec A`. -/
theorem mem_fpqcPrecoverage_completionAwayCover (ht : Ideal.span (Set.range t) = I) :
    Presieve.ofArrows (fun j : ULift.{u + 1} (Option (Fin k)) ↦
        (BigFppfOver.toScheme B S hS).obj (completionAwayCoverObj I hA s t j.down))
      (fun j ↦ (BigFppfOver.toScheme B S hS).map (completionAwayCoverHom I hA s t j.down)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA s)) := by
  have hsurj : ∀ x, ∃ j : ULift.{u + 1} (Option (Fin k)),
      x ∈ Set.range
        ((BigFppfOver.toScheme B S hS).map (completionAwayCoverHom I hA s t j.down)) := by
    intro x
    let p : PrimeSpectrum A := x
    by_cases hx : I ≤ p.asIdeal
    · obtain ⟨q, hq⟩ := exists_comap_algebraMap_adicCompletion_eq I p hx
      exact ⟨⟨none⟩, q, hq⟩
    · obtain ⟨j, hj⟩ : ∃ j, t j ∉ p.asIdeal := by
        by_contra! hc
        exact hx (ht ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr hc))
      have hmem : p ∈ (PrimeSpectrum.basicOpen (t j) : Set (PrimeSpectrum A)) := hj
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (t j)) (t j)] at hmem
      exact ⟨⟨some j⟩, hmem⟩
  refine ⟨?_, (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, ?_⟩⟩
  · let E : PreZeroHypercover.{u + 1}
        ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA s)) :=
      ⟨ULift.{u + 1} (Option (Fin k)),
        fun j ↦ (BigFppfOver.toScheme B S hS).obj (completionAwayCoverObj I hA s t j.down),
        fun j ↦ (BigFppfOver.toScheme B S hS).map (completionAwayCoverHom I hA s t j.down)⟩
    change E.presieve₀ ∈ _
    rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
    refine ⟨fun {U} hU ↦ .of_finite_of_isSpectralMap (fun j ↦ ?_) (fun x _ ↦ hsurj x) U.2
      hU.isCompact⟩
    rcases j with ⟨_ | j⟩
    · exact (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))).isSpectralMap
    · exact (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (t j))))).isSpectralMap
  · rintro ⟨_ | j⟩
    · exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
    · exact Flat.SpecMap_iff.mpr
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers (t j))))

/-- The covering of `Spec A` by `Spec A^∧` and the `Spec A_{t j}` is an fpqc covering of
algebraic spaces over `S`. -/
theorem isFpqcCovering_completionAwayCover (ht : Ideal.span (Set.range t) = I) :
    Space.IsFpqcCovering B S hS (fun j : ULift.{u + 1} (Option (Fin k)) ↦
      yoneda.map (completionAwayCoverHom (hS := hS) I hA s t j.down)) :=
  Space.isFpqcCovering_yoneda_map_of_mem_fpqcPrecoverage
    (fun j : ULift.{u + 1} (Option (Fin k)) ↦ completionAwayCoverObj I hA s t j.down)
    (fun j ↦ completionAwayCoverHom I hA s t j.down)
    (fun j ↦ isAffine_completionAwayCoverObj I hA s t j.down)
    (inferInstanceAs (IsAffine (Spec _)))
    (mem_fpqcPrecoverage_completionAwayCover I hA s t ht)

end AlgebraicGeometry.FormalSpace

/-! ### Properties of morphisms which are local on the base for the fpqc topology -/

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A property of morphisms of algebraic spaces over `S` which is local on the base for the fpqc
topology holds for `f : X' ⟶ X` as soon as, for some fpqc covering `{Y i ⟶ X}`, it holds for
every base change of `f` to a `Y i`, presented by any cartesian square of presheaves. -/
theorem prop_of_forall_isPullback (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS)]
    {X' X : AlgebraicSpaces B S hS} (f : X' ⟶ X) {ι : Type (u + 1)}
    (Y : ι → AlgebraicSpaces B S hS) (g : ∀ i, Y i ⟶ X)
    (hg : Space.IsFpqcCovering B S hS (fun i ↦ (g i).hom))
    (h : ∀ i (Z : AlgebraicSpaces B S hS) (t : Z ⟶ X') (v : Z ⟶ Y i),
      IsPullback t.hom v.hom f.hom (g i).hom → P v) :
    P f :=
  MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Space.Topology.precoverage.{u, u + 1} .fpqc B S hS) (R := Presieve.ofArrows Y g)
    ⟨ι, Y, g, rfl, X.property, fun i ↦ (Y i).property, hg⟩ fun {_ _} _ hg' ↦ by
      rcases hg' with ⟨i⟩
      exact h i _ _ _ (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f (g i)))

variable {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)
  (hA : B.Contains (Spec (.of A))) (hR : B.Contains (Spec (.of R))) (s : Spec (.of A) ⟶ S)

/-- The ring map `R → A^∧` through which `A → A^∧` factors, when `φ : A →+* R` induces an
isomorphism `A^∧ ≅ R^∧` of completions. -/
def completionLift (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    R →+* AdicCompletion I A :=
  (RingEquiv.ofBijective _ h).symm.toRingHom.comp (algebraMap R (AdicCompletion (I.map φ) R))

/-- `completionLift` is a factorization of `A → A^∧` through `φ`. -/
theorem completionLift_comp (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    (completionLift φ I h).comp φ = algebraMap A (AdicCompletion I A) := by
  refine RingHom.ext fun a ↦ (RingEquiv.ofBijective _ h).injective ?_
  change (RingEquiv.ofBijective _ h) ((RingEquiv.ofBijective _ h).symm
    (algebraMap R (AdicCompletion (I.map φ) R) (φ a))) = _
  rw [RingEquiv.apply_symm_apply, RingEquiv.ofBijective_apply]
  exact (RingHom.congr_fun (adicCompletionMap_comp_algebraMap φ I (I.map φ) le_rfl) a).symm

/-- The morphism `Spec A^∧ ⟶ Spec R` of the site through which `Spec A^∧ ⟶ Spec A` factors. -/
def completionAwayCoverLift {k : ℕ} (t : Fin k → A)
    (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    completionAwayCoverObj (hS := hS) I hA s t none ⟶
      affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (completionLift φ I h)))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (completionLift φ I h)) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ s) =
      Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ s
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, completionLift_comp])

/-- `completionAwayCoverLift` is a factorization of `Spec A^∧ ⟶ Spec A` through
`Spec R ⟶ Spec A`. -/
theorem completionAwayCoverLift_comp {k : ℕ} (t : Fin k → A)
    (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    completionAwayCoverLift (hS := hS) φ I hA hR s t h ≫ affineOverMap φ hA hR s =
      completionAwayCoverHom I hA s t none := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (completionLift φ I h)) ≫ Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, completionLift_comp]

/-- The open subspace `Spec A ∖ V(I)` of `Spec A`. -/
abbrev zeroLocusComplement : Subfunctor (yoneda.obj (affineOver B S hS hA s)) :=
  Space.openSubspaceOfPoints B S hS _ (zeroLocusPoints B S hS hA s I)ᶜ

/-- `Spec A_t ⟶ Spec A` factors through `Spec A ∖ V(I)` when `t ∈ I`. -/
theorem range_yoneda_map_completionAwayCoverHom_le {k : ℕ} (t : Fin k → A)
    (ht : Ideal.span (Set.range t) = I) (j : Fin k) :
    Subfunctor.range (yoneda.map (completionAwayCoverHom (hS := hS) I hA s t (some j))) ≤
      zeroLocusComplement I hA s := by
  rintro V _ ⟨x, rfl⟩
  rw [Space.mem_openSubspaceOfPoints_iff]
  have hx : yonedaEquiv.symm ((yoneda.map (completionAwayCoverHom (hS := hS) I hA s t (some j))).app
      V x) = yoneda.map (x ≫ completionAwayCoverHom I hA s t (some j)) := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    rfl
  rw [hx]
  rintro _ ⟨y, rfl⟩ hy
  have hy' : (Space.pointsToScheme B S hS (affineOver B S hS hA s)
      (Space.pointsMap B S hS (yoneda.obj V.unop)
        (yoneda.map (x ≫ completionAwayCoverHom (hS := hS) I hA s t (some j))) y) :
        PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (I : Set A) :=
    (Set.ext_iff.mp (zeroLocusPoints_eq_preimage_pointsToScheme B S hS hA s I) _).mp hy
  rw [Space.pointsToScheme_pointsMap_yoneda, Functor.map_comp] at hy'
  have htj : t j ∈ I := ht ▸ Ideal.subset_span ⟨j, rfl⟩
  have hmem := hy' htj
  change algebraMap A (Localization.Away (t j)) (t j) ∈
    (((BigFppfOver.toScheme B S hS).map x
      (Space.pointsToScheme B S hS V.unop y)) : PrimeSpectrum (Localization.Away (t j))).asIdeal
    at hmem
  let z : PrimeSpectrum (Localization.Away (t j)) :=
    (BigFppfOver.toScheme B S hS).map x (Space.pointsToScheme B S hS V.unop y)
  exact z.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit (t j)))

/-- A property of morphisms of algebraic spaces over `S` which is stable under base change, local
on the base for the fpqc topology and true for isomorphisms holds for an object `f` of the
category of Stacks 0AS2 for `(A, I)` exactly when it holds for an object of the category for
`(R, I R)` corresponding to `f` under base change, when `A` is Noetherian and `A^∧ ≅ R^∧`. -/
theorem prop_iff_of_affineModificationBaseChange_obj_iso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS)]
    (hiso : ∀ {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z), IsIso f → P f)
    [IsNoetherianRing A] (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl))
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hA s)) (zeroLocusPoints B S hS hA s I)ᶜ))
    (N : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s)))
      (zeroLocusPoints B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) (I.map φ))ᶜ))
    (e : (affineModificationBaseChange B S hS φ I hA hR s).obj M ≅ N) :
    P (ObjectProperty.homMk M.obj.hom :
        (⟨M.obj.left, M.property.1.1⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (affineOver B S hS hA s)) ↔
      P (ObjectProperty.homMk N.obj.hom :
        (⟨N.obj.left, N.property.1.1⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace (affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s))) := by
  let G := yoneda.map (affineOverMap (hS := hS) φ hA hR s)
  let e' : N.obj ≅ (Over.pullback G).obj M.obj :=
    (ObjectProperty.ι _).mapIso e.symm ≪≫
      (affineModificationBaseChangeCompιIso B S hS φ I hA hR s).app M
  have hsqN : IsPullback (e'.hom.left ≫ pullback.fst M.obj.hom G) N.obj.hom M.obj.hom G :=
    IsPullback.of_iso_pullback ⟨by
      rw [Category.assoc, pullback.condition, ← Over.w e'.hom]
      simp only [Category.assoc]
      rfl⟩ ((Over.forget _).mapIso e') rfl (Over.w e'.hom)
  have lift_sq : ∀ {W₁ W₂ W₃ W₄ : AlgebraicSpaces B S hS} {a : W₁.obj ⟶ W₂.obj}
      {b : W₁.obj ⟶ W₃.obj} {c : W₂.obj ⟶ W₄.obj} {d : W₃.obj ⟶ W₄.obj}, IsPullback a b c d →
      IsPullback (ObjectProperty.homMk a : W₁ ⟶ W₂) (ObjectProperty.homMk b : W₁ ⟶ W₃)
        (ObjectProperty.homMk c) (ObjectProperty.homMk d) :=
    fun hp ↦ IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hp.w) hp
  constructor
  · intro hM
    exact MorphismProperty.of_isPullback (lift_sq hsqN) hM
  · intro hN
    obtain ⟨k, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
    refine prop_of_forall_isPullback P _
      (fun j : ULift.{u + 1} (Option (Fin k)) ↦
        ⟨yoneda.obj (completionAwayCoverObj I hA s t j.down), isAlgebraicSpace_yoneda B S hS _⟩)
      (fun j ↦ ObjectProperty.homMk (yoneda.map (completionAwayCoverHom I hA s t j.down)))
      (isFpqcCovering_completionAwayCover I hA s t ht) ?_
    rintro ⟨_ | j⟩ Z tt v hpb
    · have hfac : yoneda.map (completionAwayCoverHom (hS := hS) I hA s t none) =
          yoneda.map (completionAwayCoverLift φ I hA hR s t h) ≫ G := by
        rw [← Functor.map_comp, completionAwayCoverLift_comp]
      change IsPullback tt.hom v.hom M.obj.hom
        (yoneda.map (completionAwayCoverHom (hS := hS) I hA s t none)) at hpb
      rw [hfac] at hpb
      have hl := IsPullback.of_right' hpb hsqN
      exact MorphismProperty.of_isPullback (lift_sq (W₁ := Z) hl) hN
    · let w := Subfunctor.lift _
        (range_yoneda_map_completionAwayCoverHom_le (hS := hS) I hA s t ht j)
      have hfac : yoneda.map (completionAwayCoverHom (hS := hS) I hA s t (some j)) =
          w ≫ (zeroLocusComplement I hA s).ι := (Subfunctor.lift_ι _ _).symm
      change IsPullback tt.hom v.hom M.obj.hom
        (yoneda.map (completionAwayCoverHom (hS := hS) I hA s t (some j))) at hpb
      rw [hfac] at hpb
      have hl := IsPullback.of_right' hpb
        (IsPullback.of_hasPullback M.obj.hom (zeroLocusComplement I hA s).ι)
      have : IsIso (pullback.snd M.obj.hom (zeroLocusComplement I hA s).ι) :=
        M.property.isIso_pullback_snd
      have : IsIso ((ObjectProperty.ι _).map v) := hl.isIso_snd_of_isIso
      exact hiso v (isIso_of_fully_faithful (ObjectProperty.ι _) v)

/-! ### Quasi-compact, quasi-separated, separated, proper and finite morphisms -/

/-- Let `φ : A →+* R` be a homomorphism of rings, `A` Noetherian, inducing an isomorphism from
the `I`-adic completion of `A` to the `I R`-adic completion of `R`, as in Stacks 0AE5. Let
`f : X' ⟶ Spec A`, an object of the category of Stacks 0AS2 for `(A, I)`, correspond to
`g : Y' ⟶ Spec R`, an object of the category for `(R, I R)`, under the base change functor of
Stacks 0AE5, that is `g ≅ f ×_{Spec A} Spec R`. Then `f` is quasi-compact, quasi-separated,
separated, proper, respectively finite, if and only if `g` is. -/
@[stacks 0BH5]
theorem fpqcLocalProperties_iff_of_affineModificationBaseChange_obj_iso
    [IsNoetherianRing A] (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl))
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hA s)) (zeroLocusPoints B S hS hA s I)ᶜ))
    (N : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s)))
      (zeroLocusPoints B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) (I.map φ))ᶜ))
    (e : (affineModificationBaseChange B S hS φ I hA hR s).obj M ≅ N) :
    (Space.IsQuasiCompact B S hS M.obj.hom ↔ Space.IsQuasiCompact B S hS N.obj.hom) ∧
      (Space.IsQuasiSeparated B S hS M.obj.hom ↔ Space.IsQuasiSeparated B S hS N.obj.hom) ∧
      (Space.IsSeparated B S hS M.obj.hom ↔ Space.IsSeparated B S hS N.obj.hom) ∧
      (Space.IsProper B S hS M.obj.hom ↔ Space.IsProper B S hS N.obj.hom) ∧
      (Space.IsFinite B S hS M.obj.hom ↔ Space.IsFinite B S hS N.obj.hom) :=
  ⟨prop_iff_of_affineModificationBaseChange_obj_iso φ I hA hR s
      (Space.quasiCompactProperty B S hS)
      (fun f _ ↦ (Space.isProper_of_isIso B S hS f.hom).2.1.2) h M N e,
    prop_iff_of_affineModificationBaseChange_obj_iso φ I hA hR s
      (Space.quasiSeparatedProperty B S hS)
      (fun f _ ↦ Space.isQuasiSeparated_of_isSeparated B S hS
        (Space.isSeparated_of_isIso B S hS f.hom)) h M N e,
    prop_iff_of_affineModificationBaseChange_obj_iso φ I hA hR s
      (Space.separatedProperty B S hS)
      (fun f _ ↦ Space.isSeparated_of_isIso B S hS f.hom) h M N e,
    prop_iff_of_affineModificationBaseChange_obj_iso φ I hA hR s
      (Space.properProperty B S hS)
      (fun f _ ↦ Space.isProper_of_isIso B S hS f.hom) h M N e,
    prop_iff_of_affineModificationBaseChange_obj_iso φ I hA hR s
      (Space.finiteMorphismProperty B S hS)
      (fun f _ ↦ Space.isFinite_of_isIso B S hS f.hom) h M N e⟩

end AlgebraicGeometry.FormalSpace
