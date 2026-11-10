module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.TorsionFixingExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Making the `n`-torsion of the Picard group visible over a bounded extension

Let `X` be a quasi-compact, quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and
let `n` be prime to the characteristic of `k`. If `Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕m}` over an
algebraic closure `k̄`, and `X` has a point with values in a finite separable extension `L/k`,
then there is a finite separable extension `k'/k` with `[k' : k] ≤ [L : k] · (n^m)!` such that
`X_{k'}` has a `k'`-rational point and `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕m}`. This is the proof of
[Stacks, Tag 0CDU] once the input on the algebraic closure ([Stacks, Tag 0C1Z]) and the point
([Stacks, Tag 0CD4], resp. [Stacks, Tag 056U]) are supplied.

The file also records that the base change of a smooth proper curve with `H⁰(X, 𝒪_X) = k` to
any field extension is a smooth projective curve of the same genus, which is what Tag 0C1Z
needs of `X_{k̄}`.

## Main results

* `Stacks.Picard.bijOn_schemePullbackClass_stageProjection_separableClosure`: pullback is a
  bijection `Pic(X_{k^{sep}})[n] → Pic(X_{k̄})[n]` (Tag 0CD5 in characteristic `p > 0`; in
  characteristic zero `k^{sep} = k̄`).
* `Stacks.Picard.exists_finite_separable_torsion_of_torsion_algebraicClosure`: the bounded
  finite separable extension described above.
* `AlgebraicGeometry.isCurve_isProjectiveVariety_genus_pullback`: the base change of a smooth
  proper curve with `H⁰(X, 𝒪_X) = k` is a projective curve of the same genus.
* `Stacks.Picard.exists_finite_separable_torsion_of_residueField`: the same, with the point given
  by a point of `X` whose residue field is finite separable over `k`.

## Implementation notes

The separable closure is Mathlib's `SeparableClosure k`, the separable closure of `k` inside
`AlgebraicClosure k`; `Gal(k^{sep}/k)` acts on `Pic(X_{k^{sep}})[n]` and
`Stacks.Picard.exists_intermediateField_bijOn_zsmulTorsion` gives the extension inside
`k^{sep}`, so it is automatically separable. The comparison of `Pic(X_{k^{sep}})[n]` with
`Pic(X_{k̄})[n]` is the source's appeal to Tag 0CD5.

## References

* [Stacks Project, Tag 0CDU](https://stacks.math.columbia.edu/tag/0CDU)
* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Stacks.HQuasiProjectiveDimensionOne in
/-- **The base change of a smooth proper curve with `H⁰(X, 𝒪_X) = k` is a smooth projective
curve of the same genus.** Let `X` be a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k` and
let `K/k` be any field extension. Then `X_K` is a curve over `K` (it is integral: `X` is
geometrically irreducible by Tag 0FD3, being geometrically normal by Tag 056T), it is projective
over `K` (Tag 0A26), and it has the genus of `X` (Tag 0BY9). -/
theorem isCurve_isProjectiveVariety_genus_pullback {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (K : Type u) [Field K] [Algebra k K] :
    IsCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsProjectiveVariety K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = genus f := by
  have hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := inferInstance
  have hirr : GeometricallyIrreducible f :=
    ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
      (isGeometricallyNormal_of_smooth f)).out 1 3).1 hΓ
  have hcurve : IsCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    isCurve_pullback_snd k K f
  refine ⟨hcurve, ?_, genus_baseChange k K _ _ f (IsPullback.of_hasPullback _ _)⟩
  exact (isProjectiveVariety_iff_isProjectiveMorphism K _).2
    (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one _
      (IsCurve.topologicalKrullDim_eq_one (k := K)
        (f := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).le)

end AlgebraicGeometry

namespace Stacks.Picard

/-- A bijective homomorphism of abelian groups is a bijection of the `n`-torsion sets. -/
theorem bijOn_zsmulTorsion_of_bijective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (hφ : Function.Bijective φ) (n : ℤ) :
    Set.BijOn φ (zsmulTorsion A n) (zsmulTorsion B n) := by
  refine ⟨mapsTo_zsmulTorsion φ n, hφ.1.injOn, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hφ.2 y
  refine ⟨x, ?_, rfl⟩
  rw [mem_zsmulTorsion] at hy ⊢
  apply hφ.1
  rw [map_zsmul, hy, map_zero]

/-- Pullback along an isomorphism of schemes is a bijection of the `n`-torsion of the Picard
groups. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (n : ℤ) :
    Set.BijOn (schemePullbackClass f) (zsmulTorsion (ofScheme Y) n)
      (zsmulTorsion (ofScheme X) n) :=
  bijOn_zsmulTorsion_of_bijective (A := ofScheme Y) (B := ofScheme X) (schemePullbackClassHom f)
    (bijective_schemePullbackClass_of_isIso f) n

variable {k : Type u} [Field k]

/-- **`Pic(X_{k^{sep}})[n] = Pic(X_{k̄})[n]`.** Let `X` be a quasi-compact, quasi-separated scheme
over `k` with `H⁰(X, 𝒪_X) = k` and let `n` be invertible in `k`. Pullback along
`X_{k̄} ⟶ X_{k^{sep}}` is a bijection on `n`-torsion of Picard groups.

`X_{k̄}` is the base change of `X_{k^{sep}}` along the purely inseparable extension `k̄/k^{sep}`,
whose global sections are `k^{sep}`; in characteristic `p > 0` this is Tag 0CD5, and in
characteristic zero the extension `k̄/k^{sep}` is trivial. -/
theorem bijOn_schemePullbackClass_stageProjection_separableClosure (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)) {n : ℤ} (hn : (n : k) ≠ 0) :
    Set.BijOn (schemePullbackClass (stageProjection X (separableClosure k (AlgebraicClosure k))))
      (zsmulTorsion (ofScheme
        (pullback X.hom (spectrumMap k (separableClosure k (AlgebraicClosure k))))) n)
      (zsmulTorsion (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) X)) n) := by
  let Ks := separableClosure k (AlgebraicClosure k)
  have : CompactSpace (stageOver X Ks).left := compactSpace_stage X Ks
  have : QuasiSeparatedSpace (stageOver X Ks).left := quasiSeparatedSpace_stage X Ks
  have hΓs := isIso_appTop_stage X hΓ Ks
  have hsplit : schemePullbackClass (stageProjection X Ks) =
      schemePullbackClass (stageBaseChangeIso X Ks).hom ∘
        schemePullbackClass (pullback.fst (stageOver X Ks).hom
          (Spec.map (CommRingCat.ofHom (algebraMap Ks (AlgebraicClosure k))))) := by
    funext x
    rw [Function.comp_apply, schemePullbackClass_comp, stageBaseChangeIso_hom_fst]
  have hiso : Set.BijOn (schemePullbackClass (stageBaseChangeIso X Ks).hom)
      (zsmulTorsion (ofScheme (SchemeOver.baseChange Ks (AlgebraicClosure k) (stageOver X Ks))) n)
      (zsmulTorsion (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) X)) n) :=
    bijOn_schemePullbackClass_zsmulTorsion_of_isIso _ n
  have hfst : Set.BijOn (schemePullbackClass (pullback.fst (stageOver X Ks).hom
        (Spec.map (CommRingCat.ofHom (algebraMap Ks (AlgebraicClosure k))))))
      (zsmulTorsion (ofScheme (stageOver X Ks).left) n)
      (zsmulTorsion (ofScheme (SchemeOver.baseChange Ks (AlgebraicClosure k) (stageOver X Ks)))
        n) := by
    obtain ⟨p, hchar⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hp | rfl
    · have : CharP Ks p := charP_of_injective_algebraMap (algebraMap k Ks).injective p
      have hcop : n.natAbs.Coprime p := by
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hn ?_)
        exact (CharP.intCast_eq_zero_iff k p n).2 (Int.natCast_dvd.2 hdvd)
      exact bijOn_schemePullbackClass_zsmulTorsion_of_isPurelyInseparable p hp.pos hcop
        (stageOver X Ks).hom hΓs
    · have : CharZero k := CharP.charP_to_charZero k
      have : CharZero Ks := charZero_of_injective_algebraMap (algebraMap k Ks).injective
      have hbij : Function.Bijective (algebraMap Ks (AlgebraicClosure k)) :=
        ⟨(algebraMap Ks (AlgebraicClosure k)).injective,
          IsPurelyInseparable.surjective_algebraMap_of_isSeparable Ks (AlgebraicClosure k)⟩
      let eR : Ks ≃+* AlgebraicClosure k := RingEquiv.ofBijective _ hbij
      have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap Ks (AlgebraicClosure k)))) := by
        have : IsIso (CommRingCat.ofHom (algebraMap Ks (AlgebraicClosure k))) :=
          (RingEquiv.toCommRingCatIso eR).isIso_hom
        infer_instance
      exact bijOn_schemePullbackClass_zsmulTorsion_of_isIso _ n
  rw [hsplit]
  exact hiso.comp hfst

/-- **The bounded extension of Tag 0CDU.** Let `X` be a quasi-compact, quasi-separated scheme
over a field `k` with `H⁰(X, 𝒪_X) = k`, let `n ≥ 1` be invertible in `k`, and suppose
`Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕m}` for an algebraic closure `k̄`. Let `L/k` be a finite separable
extension and `Spec L ⟶ X` a morphism over `k`. Then there is a finite separable extension
`k'/k` with `[k' : k] ≤ [L : k] · (n^m)!` such that `X_{k'}` has a `k'`-rational point and
`Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕m}`.

The proof is the source's. `Pic(X_{k^{sep}})[n] ≅ Pic(X_{k̄})[n]` by Tag 0CD5
(`Stacks.Picard.bijOn_schemePullbackClass_stageProjection_separableClosure`); it is a finite set
of `n^m` elements on which `Gal(k^{sep}/k)` acts continuously, and the fixed field of the
intersection of the kernel with `Gal(k^{sep}/L)` (for an embedding `L ⊆ k^{sep}`) is the
required `k'` (`Stacks.Picard.exists_intermediateField_bijOn_zsmulTorsion`). -/
theorem exists_finite_separable_torsion_of_torsion_algebraicClosure (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)) {n : ℕ} (hn : (n : k) ≠ 0)
    {m : ℕ}
    (e : Submodule.torsionBy ℤ (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) X))
      (n : ℤ) ≃+ (Fin m → ZMod n))
    (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (s : Spec (.of L) ⟶ X.left) (hs : s ≫ X.hom = spectrumMap k L) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Module.finrank k k' ≤ Module.finrank k L * (n ^ m).factorial ∧
      (∃ t : Spec (.of k') ⟶ pullback X.hom (spectrumMap k k'),
        t ≫ pullback.snd X.hom (spectrumMap k k') = 𝟙 _) ∧
      Nonempty (Submodule.torsionBy ℤ (ofScheme (pullback X.hom (spectrumMap k k'))) (n : ℤ) ≃+
        (Fin m → ZMod n)) := by
  have : NeZero n := ⟨fun h => hn (by rw [h, Nat.cast_zero])⟩
  have hnZ : ((n : ℤ) : k) ≠ 0 := by rwa [Int.cast_natCast]
  let K := SeparableClosure k
  -- `Pic(X_{k^{sep}})[n] ≅ Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^m`.
  have hsep : Set.BijOn (schemePullbackClassHom
      (stageProjection X (separableClosure k (AlgebraicClosure k))))
      (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ))
      (zsmulTorsion (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) X)) (n : ℤ)) :=
    bijOn_schemePullbackClass_stageProjection_separableClosure X hΓ hnZ
  let eK : Submodule.torsionBy ℤ (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ) ≃+
      (Fin m → ZMod n) :=
    (torsionByAddEquivOfBijOn _ (n : ℤ) hsep).trans e
  let eT : zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ) ≃ (Fin m → ZMod n) :=
    (Equiv.subtypeEquivRight fun x => (Submodule.mem_torsionBy_iff (n : ℤ) x).symm).trans
      eK.toEquiv
  have hcard : Nat.card (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ)) =
      n ^ m := by
    rw [Nat.card_congr eT, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hfin : (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ)).Finite :=
    Set.finite_coe_iff.1 (Finite.of_equiv _ eT.symm)
  -- Embed `L` into `k^{sep}`.
  let ι : L →ₐ[k] K := IsSepClosed.lift
  let L' : IntermediateField k K := ι.fieldRange
  let eL : L ≃ₐ[k] L' := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional k L' := LinearEquiv.finiteDimensional eL.toLinearEquiv
  have hL' : Module.finrank k L' = Module.finrank k L := eL.toLinearEquiv.finrank_eq.symm
  let s' : Spec (.of L') ⟶ X.left := Spec.map (CommRingCat.ofHom eL.toRingEquiv.toRingHom) ≫ s
  have hs' : s' ≫ X.hom = spectrumMap k L' := by
    rw [Category.assoc, hs, spectrumMap, spectrumMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => eL.commutes a)
  obtain ⟨E, hLE, hEfin, hEdeg, hbij⟩ :=
    exists_intermediateField_bijOn_zsmulTorsion X hΓ (n : ℤ) hfin L' s' hs'
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E K
  refine ⟨E, inferInstance, inferInstance, hEfin, inferInstance, ?_, ?_, ?_⟩
  · rwa [hcard, hL'] at hEdeg
  · refine ⟨pullback.lift
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hLE).toRingHom) ≫ s')
      (𝟙 _) ?_, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, hs', specMap_inclusion_comp_spectrumMap, Category.id_comp]
  · have hbij' : Set.BijOn (schemePullbackClassHom (stageProjection X E))
        (zsmulTorsion (ofScheme (pullback X.hom (spectrumMap k E))) (n : ℤ))
        (zsmulTorsion (ofScheme (SchemeOver.baseChange k K X)) (n : ℤ)) := hbij
    exact ⟨(torsionByAddEquivOfBijOn _ (n : ℤ) hbij').trans eK⟩

/-- **The bounded extension of Tag 0CDU, from a closed point.** Let `X` be a quasi-compact,
quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, let `n ≥ 1` be invertible in
`k`, and suppose `Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕m}`. If `x ∈ X` is a point whose residue field
`κ(x)` is a finite separable extension of `k`, then there is a finite separable extension
`k'/k` with `[k' : k] ≤ d · (n^m)!`, for any bound `[κ(x) : k] ≤ d`, such that `X_{k'}` has a
`k'`-rational point and
`Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕m}`.

The residue field is a `k`-algebra through the structure morphism on global sections followed by
evaluation at `x`, the convention of [Stacks, Tag 056U]
(`AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`); the
point `Spec κ(x) ⟶ X` lies over `Spec k` for this structure
(it is `Spec` of evaluation), and
`Stacks.Picard.exists_finite_separable_torsion_of_torsion_algebraicClosure` applies. -/
theorem exists_finite_separable_torsion_of_residueField {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) {n : ℕ} (hn : (n : k) ≠ 0)
    {m : ℕ}
    (e : Submodule.torsionBy ℤ
      (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
      (n : ℤ) ≃+ (Fin m → ZMod n))
    (x : X)
    (hfin : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x))
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) {d : ℕ}
    (hd : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.finrank k (X.residueField x) ≤ d) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧
      Module.finrank k k' ≤ d * (n ^ m).factorial ∧
      (∃ t : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
        t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) = 𝟙 _) ∧
      Nonempty (Submodule.torsionBy ℤ
        (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
        (Fin m → ZMod n)) := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : CompactSpace (Over.mk f).left := ‹CompactSpace X›
  have : QuasiSeparatedSpace (Over.mk f).left := ‹QuasiSeparatedSpace X›
  have hs : X.fromSpecResidueField x ≫ (Over.mk f).hom = spectrumMap k (X.residueField x) := by
    change X.fromSpecResidueField x ≫ f =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x)
    apply (cancel_mono (Spec (.of k)).toSpecΓ).mp
    rw [Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Scheme.fromSpecResidueField, Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ_assoc]
    rw [← SpecMap_ΓSpecIso_hom]
    simp only [← Spec.map_comp, Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨k', _, _, h1, h2, h3, h4, h5⟩ :=
    exists_finite_separable_torsion_of_torsion_algebraicClosure (Over.mk f) hΓ hn e
      (X.residueField x) (X.fromSpecResidueField x) hs
  exact ⟨k', _, _, h1, h2, h3.trans (Nat.mul_le_mul_right _ hd), h4, h5⟩

end Stacks.Picard

end
