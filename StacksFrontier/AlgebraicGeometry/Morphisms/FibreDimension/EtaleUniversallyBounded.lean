module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.TotallySplit
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.RingTheory.TotallySplit.PrimeSpectrum

/-!
# Bounds on the fibres of an étale morphism

For an étale morphism of schemes, a bound on the degrees of its fibres is equivalent to a bound
on the number of points of every field-valued base change, and it is enough to test the number
of points after extending each residue field of the target to a separable closure.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_etale_of_finite`: an étale morphism with
  finitely many points to the spectrum of a field is finite locally free, of rank the dimension
  of its algebra of global sections.
* `AlgebraicGeometry.cardinalMk_eq_finrank_globalSections_of_etale`: an étale affine scheme
  over a separably closed field has as many points as its algebra of global sections has
  dimensions.
* `AlgebraicGeometry.cardinalMk_eq_of_etale_over_sepClosed`: over a separably closed field the
  rank of an étale finite locally free scheme is exactly its number of points.
* `AlgebraicGeometry.exists_rank_le_of_cardinalMk_baseChange_le`: an étale morphism to the
  spectrum of a field whose base change to a separable closure has at most `n` points is finite
  locally free of some rank at most `n`.
* `AlgebraicGeometry.etale_boundsFiberDegrees_tfae` gives the three equivalent forms of a
  uniform bound for the fibres of an étale morphism.

## Implementation notes

The natural number `n` incorporates the nonnegativity assumption in the source; in the first
condition it is coerced to the integer bound used by `AlgebraicGeometry.BoundsFiberDegrees`. The
three entries of the `List.TFAE` are respectively conditions (1), (2) and (3) of the source. A
separable algebraic closure is represented abstractly by an `IsSepClosure` instance.

The implication (3) ⇒ (1) is the substantial one, and it is proved here *without* descent along
the covering `Spec κ(y)^{sep} ⟶ Spec κ(y)`. The usual argument transports the rank computed over
the separable closure back down by fpqc descent for the rank-indexed finite local freeness of a
morphism (Tag 02VO), which in this development still rests on the effectivity of quasi-coherent
fpqc descent data (Tag 023T). That appeal is unnecessary: hypothesis (3) bounds the number of
points of the base change, and the base change is surjective, so the fibre `X_y` itself has
finitely many points. An étale morphism is locally quasi-finite, so `X_y` is locally Artinian,
hence discrete; being finite and discrete it is affine, by Mathlib's instance for finite
discrete schemes. The fibre is therefore the spectrum of a finite étale `κ(y)`-algebra `A`, and
a basis of `A` produces the rank directly through
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis`. Only the *bound* on that rank needs the
separable closure, and it is obtained from the base change in the easy direction — the rank is
stable under base change (`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback`) — together
with the fact that over a separably closed field the rank counts the points, which is Mathlib's
`Algebra.IsFiniteSplit` for a finite étale algebra over a separably closed field.

Reading the rank of a finite locally free morphism over a field off the dimension of its global
sections needs that a finite locally free module of rank `r` over a field has dimension `r`; that
is `Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq`, and its scheme-level form
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank`, both taken from
`StacksDraft.AlgebraicGeometry.F3b.FiniteLocallyFreeRank.AffineTarget`.

## References

* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An étale morphism with finitely many points to the spectrum of a field is finite: it is
locally quasi-finite because it is étale, and quasi-compact because its source is finite. -/
theorem isFinite_of_etale_of_finite (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [Etale p] [Finite Z] : IsFinite p := by
  have : LocallyQuasiFinite p := (locallyQuasiFinite_of_etale p).2
  exact IsFinite.of_locallyQuasiFinite p

/-- The global sections of an étale affine scheme over a field form an étale algebra. -/
private theorem algebra_etale_sections_of_etale (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [Etale p] [IsAffine Z] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Algebra.Etale k Γ(Z, ⊤) := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  rw [← RingHom.etale_algebraMap]
  change RingHom.Etale ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv))
    (HasRingHomProperty.appTop (P := @Etale) p ‹Etale p›)

/-- **Stacks Project, Tag 02GL.** The global sections of a finite étale scheme over a field form
a finite étale algebra over that field. -/
theorem algebra_etale_and_module_finite_sections (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [Etale p] [IsFinite p] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Algebra.Etale k Γ(Z, ⊤) ∧ Module.Finite k Γ(Z, ⊤) := by
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  refine ⟨algebra_etale_sections_of_etale k p, ?_⟩
  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ p := by
    simpa only [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv] using Scheme.isoSpec_inv_naturality p
  have hFi : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  exact RingHom.finite_algebraMap.mp (show (algebraMap k Γ(Z, ⊤)).Finite from
    (IsFinite.SpecMap_iff φ).mp hFi)

/-- An étale morphism with finitely many points to the spectrum of a field is finite locally
free, of rank the dimension of its algebra of global sections.

The source is locally Artinian because an étale morphism is locally quasi-finite, hence
discrete; being also finite it is affine, and a basis of its global sections exhibits the rank.
No descent along a covering of the base is involved. -/
theorem isFiniteLocallyFreeOfRank_of_etale_of_finite (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [Etale p] [Finite Z] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (Module.finrank k Γ(Z, ⊤)) := by
  have : IsFinite p := isFinite_of_etale_of_finite k p
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  have : Module.Finite k Γ(Z, ⊤) := (algebra_etale_and_module_finite_sections k p).2
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis p _
    ⟨Module.finBasis k Γ(Z, ⊤)⟩

/-- An étale affine scheme over a separably closed field has exactly as many points as its ring
of global sections has dimensions over that field. -/
public theorem cardinalMk_eq_finrank_globalSections_of_etale {K : Type u} [Field K]
    [IsSepClosed K] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [Etale p] [IsAffine Z] :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    Cardinal.mk (Z : Type u) = Module.finrank K ↑Γ(Z, ⊤) := by
  let _ := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom.toAlgebra
  have : Algebra.Etale K ↑Γ(Z, ⊤) := algebra_etale_sections_of_etale K p
  rw [← Algebra.IsFiniteSplit.cardinalMk_primeSpectrum_eq_finrank (K := K) (A := ↑Γ(Z, ⊤))]
  exact Cardinal.mk_congr Z.isoSpec.hom.homeomorph.toEquiv

/-- Over a separably closed field, an étale scheme that is finite locally free of rank `r` has
exactly `r` points: its algebra of global sections is finite étale, hence totally split, so it
is a product of `r` copies of the field. -/
theorem cardinalMk_eq_of_etale_over_sepClosed (K : Type u) [Field K] [IsSepClosed K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [Etale p] (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] :
    Cardinal.mk Z = r := by
  have : IsFinite p := ((Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget p).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r)).1
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨-, hrank⟩ := finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r
  rw [cardinalMk_eq_finrank_globalSections_of_etale p, hrank]

/-- An étale morphism to the spectrum of a field whose base change to a separable closure has at
most `n` points is finite locally free of some rank at most `n`.

The base change is surjective, so the source itself has at most `n` points and is therefore
finite locally free of the rank of its global sections. That rank is stable under base change,
and over the separably closed field it counts the points of the base change, which is what
bounds it by `n`. -/
theorem exists_rank_le_of_cardinalMk_baseChange_le (K : Type u) [Field K]
    (ksep : Type u) [Field ksep] [Algebra K ksep] [IsSepClosure K ksep]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [Etale p] (n : ℕ)
    (hpts : Cardinal.mk
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p : Scheme.{u}) ≤ n) :
    ∃ r ≤ n, Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r := by
  classical
  have : IsSepClosed ksep := IsSepClosure.sep_closed (k := K)
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) := inferInstance
  have hsnd : Surjective
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p) := inferInstance
  have hle : Cardinal.mk Z ≤ n := le_trans (Cardinal.mk_le_of_surjective hsnd.surj) hpts
  have : Finite Z :=
    Cardinal.lt_aleph0_iff_finite.mp (lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0)
  let : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p (Module.finrank K Γ(Z, ⊤)) :=
    isFiniteLocallyFreeOfRank_of_etale_of_finite K p
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p)
      (Module.finrank K Γ(Z, ⊤)) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p).flip
  have hcount : Cardinal.mk
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p : Scheme.{u}) =
      Module.finrank K Γ(Z, ⊤) :=
    cardinalMk_eq_of_etale_over_sepClosed ksep
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K ksep))) p) _
  refine ⟨Module.finrank K Γ(Z, ⊤), ?_, hrank⟩
  have hcard : (Module.finrank K Γ(Z, ⊤) : Cardinal.{u}) ≤ (n : Cardinal.{u}) := by
    rwa [← hcount]
  exact_mod_cast hcard

/-- For an étale morphism, bounding fibre degrees, bounding the points of every field-valued base
change, and bounding the points after passage to separable closures of residue fields are
equivalent. -/
@[stacks 03WU]
theorem etale_boundsFiberDegrees_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    List.TFAE [
      BoundsFiberDegrees f (n : ℤ),
      ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
        Cardinal.mk (pullback g f : Scheme.{u}) ≤ n,
      ∀ (y : Y) (ksep : Type u) [Field ksep] [Algebra (Y.residueField y) ksep]
        [IsSepClosure (Y.residueField y) ksep],
        Cardinal.mk
          (pullback
            (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) ksep)))
            (f.fiberToSpecResidueField y) : Scheme.{u}) ≤ n] := by
  classical
  tfae_have 1 → 2 := by
    intro h
    refine cardinalMk_pullback_le_of_degree_le f n fun k _ g ↦ ?_
    obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange f (n : ℤ)).mp h k g
    exact ⟨r, by exact_mod_cast hr, hrank⟩
  tfae_have 2 → 3 := by
    intro h y ksep _ _ _
    let q : Spec (.of ksep) ⟶ Spec (.of (Y.residueField y)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) ksep))
    let g : Spec (.of ksep) ⟶ Y := q ≫ Y.fromSpecResidueField y
    let e : pullback q (f.fiberToSpecResidueField y) ≅ pullback g f :=
      pullbackSymmetry q (f.fiberToSpecResidueField y) ≪≫
        pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) q ≪≫
          pullbackSymmetry f (q ≫ Y.fromSpecResidueField y)
    calc
      Cardinal.mk (pullback q (f.fiberToSpecResidueField y) : Scheme.{u}) =
          Cardinal.mk (pullback g f : Scheme.{u}) :=
        Cardinal.mk_congr e.hom.homeomorph.toEquiv
      _ ≤ n := h ksep g
  tfae_have 3 → 1 := by
    intro h y
    have : Etale (f.fiberToSpecResidueField y) :=
      inferInstanceAs (Etale (pullback.snd f (Y.fromSpecResidueField y)))
    obtain ⟨r, hr, hrank⟩ := exists_rank_le_of_cardinalMk_baseChange_le (Y.residueField y)
      (SeparableClosure (Y.residueField y)) (f.fiberToSpecResidueField y) n
      (h y (SeparableClosure (Y.residueField y)))
    exact ⟨r, by exact_mod_cast hr, hrank⟩
  tfae_finish

end AlgebraicGeometry

end
