module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedRegularBoundary
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.AffineFieldFactors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Covers of a principal open of a strictly henselian regular local ring

Let `A` be a strictly henselian regular local ring and `0 ≠ x ∈ A`. A finite étale cover
`Spec B ⟶ D(x)` which is unramified over `Spec A` in codimension one extends, by purity
([Stacks, Tag 0H2W]), to a finite étale cover of `Spec A`, which is split since `A` is strictly
henselian. Hence `B` has a section: there is an `A_x`-algebra map `B ⟶ A_x`. This is the step of
the proof of Abhyankar's lemma for a regular divisor ([Stacks, Tag 0EYG]) at which the Kummer
cover has made the cover unramified.

## Main results

* `AlgebraicGeometry.Abhyankar.nonempty_algHom_of_isUnramifiedInCodimensionOne`: the section,
  granted purity for regular local rings.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Abhyankar

/-- The cover `Spec B ⟶ D(g)` is finite when `B` is a finite `R_g`-algebra. -/
private theorem isFinite_coverMap {R : CommRingCat.{u}} (g : R) (B : Type u) [CommRing B]
    [Algebra (Localization.Away g) B] [Module.Finite (Localization.Away g) B] :
    IsFinite (AffineFieldFactors.coverMap g B) := by
  unfold AffineFieldFactors.coverMap
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) B))) :=
    (IsFinite.SpecMap_iff (f := CommRingCat.ofHom (algebraMap (Localization.Away g) B))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  infer_instance

/-- The cover `Spec B ⟶ D(g)` is étale when `B` is an étale `R_g`-algebra. -/
private theorem etale_coverMap {R : CommRingCat.{u}} (g : R) (B : Type u) [CommRing B]
    [Algebra (Localization.Away g) B] [Algebra.Etale (Localization.Away g) B] :
    Etale (AffineFieldFactors.coverMap g B) := by
  unfold AffineFieldFactors.coverMap
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  infer_instance

/-- The stalks of the spectrum of a regular ring are regular local rings. -/
private theorem isRegularLocalRing_stalk_of_isRegularRing (A : Type u) [CommRing A]
    [IsRegularRing A] (q : Spec (.of A)) :
    IsRegularLocalRing ((Spec (.of A)).presheaf.stalk q) := by
  have := q.isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk q) := StructureSheaf.stalkAlgebra A q
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
      ((Spec (.of A)).presheaf.stalk q)).toRingEquiv

/-- A section over `Spec A` of an extension of the cover `Spec B ⟶ D(x)` gives an
`A_x`-algebra map `B ⟶ A_x`. -/
private theorem nonempty_algHom_of_section {A : Type u} [CommRing A] {x : A} {B : Type u}
    [CommRing B] [Algebra (Localization.Away x) B] {Y' : Scheme.{u}} {p : Y' ⟶ Spec (.of A)}
    (e : pullback p (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen x)) ≅
      Spec (.of B))
    (he : e.hom ≫ AffineFieldFactors.coverMap (R := .of A) x B = pullback.snd _ _)
    (s : Spec (.of A) ⟶ Y') (hs : s ≫ p = 𝟙 _) :
    Nonempty (B →ₐ[Localization.Away x] Localization.Away x) := by
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen x
  let σ : U.toScheme ⟶ Limits.pullback p U.ι :=
    pullback.lift (U.ι ≫ s) (𝟙 _) (by simp [hs])
  let τ : Spec (.of (Localization.Away x)) ⟶ Spec (.of B) :=
    (basicOpenIsoSpecAway (R := .of A) x).inv ≫ σ ≫ e.hom
  have hτ : τ ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away x) B)) = 𝟙 _ := by
    have h1 : τ ≫ AffineFieldFactors.coverMap (R := .of A) x B =
        (basicOpenIsoSpecAway (R := .of A) x).inv := by
      show ((basicOpenIsoSpecAway (R := .of A) x).inv ≫ σ ≫ e.hom) ≫ _ = _
      rw [Category.assoc, Category.assoc, he, pullback.lift_snd, Category.comp_id]
    rwa [AffineFieldFactors.coverMap, ← Category.assoc, Iso.comp_inv_eq, Iso.inv_hom_id] at h1
  let φ : B →+* Localization.Away x := (Spec.preimage τ).hom
  have hφτ : Spec.map (CommRingCat.ofHom φ) = τ := Spec.map_preimage τ
  have hφ : φ.comp (algebraMap (Localization.Away x) B) = RingHom.id _ := by
    rw [← hφτ, ← Spec.map_comp, ← Spec.map_id] at hτ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hτ)
  exact ⟨{ φ with commutes' := fun r ↦ congrArg (fun ψ ↦ ψ r) hφ }⟩

/-- **A cover of `D(x)` unramified in codimension one over a strictly henselian regular local ring
has a section.** The argument `h0BMA` is purity for regular local rings ([Stacks, Tag 0BMA] (1)).
-/
theorem nonempty_algHom_of_isUnramifiedInCodimensionOne (h0BMA : PurityAtRegularLocalRings.{u})
    (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] [IsRegularLocalRing A]
    (x : A) (hx : x ≠ 0)
    (B : Type u) [CommRing B] [Nontrivial B] [Algebra (Localization.Away x) B]
    [Module.Finite (Localization.Away x) B] [Algebra.Etale (Localization.Away x) B]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen x))
      (AffineFieldFactors.coverMap (R := .of A) x B)) :
    Nonempty (B →ₐ[Localization.Away x] Localization.Away x) := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).1 (inferInstance : IsRegularLocalRing A)
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen x
  have hdense : DenseRange U.ι.base := by
    rw [DenseRange, Scheme.Opens.range_ι]
    refine U.isOpen.dense ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    show x ∉ (⊥ : Ideal A)
    simpa using hx
  have := isFinite_coverMap (R := .of A) x B
  have := etale_coverMap (R := .of A) x B
  obtain ⟨Y', p, hp₁, hp₂, e, he⟩ :=
    exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne U hdense
      (AffineFieldFactors.coverMap (R := .of A) x B) hunr
      fun q _ ↦ isRegularLocalRing_stalk_of_isRegularRing A q
  let F : FiniteEtaleOver (Spec (.of A)) :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) p ⟨hp₁, hp₂⟩
  obtain ⟨n, ι, hι⟩ := exists_iso_pi_of_henselian_of_isSepClosed A F
  -- The cover is nonempty, so the split cover has a component.
  have hn : 0 < n := by
    by_contra h0
    obtain rfl : n = 0 := by omega
    obtain ⟨P, hP⟩ := Ideal.exists_maximal B
    let z : Spec (.of B) := ⟨P, hP.isPrime⟩
    let y : Spec (.of (ULift.{u} (Fin 0) → A)) :=
      ι.hom (pullback.fst p U.ι (e.inv z))
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Submodule.zero_mem _)
      (isUnit_of_subsingleton _))
  -- A section of the split cover, through the first component.
  let ev : (ULift.{u} (Fin n) → A) →+* A := Pi.evalRingHom _ ⟨⟨0, hn⟩⟩
  let sec : Spec (.of A) ⟶ F.left := Spec.map (CommRingCat.ofHom ev) ≫ ι.inv
  have hsec : sec ≫ F.hom = 𝟙 _ := by
    have : ι.inv ≫ F.hom = Spec.map (CommRingCat.ofHom
        (algebraMap A (ULift.{u} (Fin n) → A))) := by
      rw [Iso.inv_comp_eq, hι]
    rw [Category.assoc, this, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  exact nonempty_algHom_of_section e he sec hsec

end AlgebraicGeometry.Abhyankar
