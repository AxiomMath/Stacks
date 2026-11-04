module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteEtaleCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecompositionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.Theorem
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Transporting vanishing bounds with coefficients killed by `n`

Three ways of moving the bound `IsTorsionVanishingBound X n d` (the étale cohomology of `X` with
coefficients killed by `n` vanishes above `d`) from one scheme to another:

* along an isomorphism of schemes;
* from the factors of a finite product of rings to the spectrum of the product: the spectrum of
  `∏ᵢ Kᵢ` is the disjoint union of the open subschemes `Spec Kᵢ`, and the cohomology of a finite
  disjoint union is the product of the cohomologies;
* from the residue field of a henselian local ring `A` to `Spec A`: by Gabber's theorem
  (Stacks 09ZI) restriction to the closed point is bijective on the cohomology of torsion
  sheaves.

## Main results

* `AlgebraicGeometry.Scheme.IsTorsionVanishingBound.of_iso`
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_pi`
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_henselianLocalRing`

## References

* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **The inverse image of a sheaf killed by `n` is killed by `n`.** -/
theorem forall_nsmul_eq_zero_etaleAbelianInverseImage {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) :
    ∀ (T : Y.Etale) (x : ((etaleAbelianInverseImage.{u, 0} f).obj G).obj.obj (op T)),
      n • x = 0 :=
  (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero _).2
    (nsmul_id_obj_eq_zero _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero G).1 hG))

/-- A vanishing bound for `Y` kills the cohomology of the inverse image of a torsion sheaf. -/
private theorem subsingleton_H_inverseImage_of_isTorsionVanishingBound {X Y : Scheme.{u}}
    (f : Y ⟶ X) {n : ℕ} {d : WithBot ℕ∞} (h : IsTorsionVanishingBound Y n d)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) {p : ℕ} (hp : d < p) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} f).obj G) p) :=
  h _ (forall_nsmul_eq_zero_etaleAbelianInverseImage f hG) p hp

/-- **A vanishing bound is invariant under isomorphism of schemes.** -/
theorem IsTorsionVanishingBound.of_iso {X Y : Scheme.{u}} (e : X ≅ Y) {n : ℕ}
    {d : WithBot ℕ∞} (h : IsTorsionVanishingBound Y n d) : IsTorsionVanishingBound X n d := by
  intro G hG p hp
  have h₁ := (subsingleton_H_inverseImage_iff_of_isIso G p (𝟙 X) e.inv e.hom
    e.hom_inv_id.symm).2 (subsingleton_H_inverseImage_of_isTorsionVanishingBound e.inv h hG hp)
  exact (subsingleton_H_iff_of_iso ((etaleAbelianInverseImageIdIso X).app G) p).1 h₁

/-- **The cohomology of a finite disjoint union.** Let `jₖ : Uₖ ⟶ Y` (`k` in a finite type) be
open immersions with pairwise disjoint images covering `Y`. If `d` bounds the cohomology of every
`Uₖ` with coefficients killed by `n`, then it bounds that of `Y`. -/
theorem isTorsionVanishingBound_of_disjoint_cover {Y : Scheme.{u}} {ι : Type} [Finite ι]
    {U : ι → Scheme.{u}} (j : ∀ k, U k ⟶ Y) [∀ k, IsOpenImmersion (j k)]
    (hdisj : Pairwise fun k m => Disjoint (Set.range (j k).base) (Set.range (j m).base))
    (hcov : ⋃ k, Set.range (j k).base = Set.univ) {n : ℕ} {d : WithBot ℕ∞}
    (h : ∀ k, IsTorsionVanishingBound (U k) n d) : IsTorsionVanishingBound Y n d := by
  classical
  cases nonempty_fintype ι
  intro G hG p hp
  have : Subsingleton (∀ k, Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (j k)).obj G) p) :=
    have := fun k => subsingleton_H_inverseImage_of_isTorsionVanishingBound (j k) (h k) hG hp
    inferInstance
  exact (bijective_etaleCohomologyRestrictionMap_pi.{u + 1, u, 0} j hdisj hcov G p).1.subsingleton

/-- **The spectrum of a finite product of rings.** If `d` bounds the cohomology of each
`Spec Kᵢ` with coefficients killed by `n`, then it bounds that of `Spec (∏ᵢ Kᵢ)`. -/
theorem isTorsionVanishingBound_spec_pi {ι : Type u} [Finite ι] (K : ι → Type u)
    [∀ i, CommRing (K i)] {n : ℕ} {d : WithBot ℕ∞}
    (h : ∀ i, IsTorsionVanishingBound (Spec (.of (K i))) n d) :
    IsTorsionVanishingBound (Spec (.of (∀ i, K i))) n d := by
  classical
  have := Fintype.ofFinite ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let R : ι → CommRingCat.{u} := fun i => .of (K i)
  let j : ∀ k : Fin (Fintype.card ι), Spec (.of (K (σ k))) ⟶ Spec (.of (∀ i, K i)) :=
    fun k => Spec.map (CommRingCat.ofHom (Pi.evalRingHom K (σ k)))
  have hj : ∀ k, j k = Sigma.ι (fun i => Spec (R i)) (σ k) ≫ sigmaSpec R := fun k =>
    (ι_sigmaSpec R (σ k)).symm
  have : ∀ k, IsOpenImmersion (j k) := fun k => by
    rw [hj]
    infer_instance
  refine isTorsionVanishingBound_of_disjoint_cover j ?_ ?_ (fun k => h (σ k))
  · intro k m hkm
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ e
    rw [hj, hj, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    exact hkm (σ.injective (congrArg Sigma.fst
      ((sigmaι_eq_iff (fun i => Spec (R i)) (σ k) (σ m) x y).1
        ((sigmaSpec R).isOpenEmbedding.injective e))))
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨z, rfl⟩ : ∃ z, (sigmaSpec R) z = y :=
      ⟨(inv (sigmaSpec R)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk (fun i => Spec (R i))).surjective z
    obtain ⟨k, rfl⟩ := σ.surjective i
    refine Set.mem_iUnion.2 ⟨k, x, ?_⟩
    rw [hj, Scheme.Hom.comp_apply, sigmaMk_mk]

/-- **A henselian local ring has the vanishing bound of its residue field** (Stacks 09ZI). If
`d` bounds the cohomology of `Spec κ` with coefficients killed by `n > 0`, `κ` the residue field
of a henselian local ring `A`, then `d` bounds that of `Spec A`: restriction to the closed point
is bijective on the cohomology of torsion sheaves. -/
theorem isTorsionVanishingBound_spec_of_henselianLocalRing (A : Type u) [CommRing A]
    [HenselianLocalRing A] {n : ℕ} (hn : 0 < n) {d : WithBot ℕ∞}
    (hk : IsTorsionVanishingBound (Spec (.of (IsLocalRing.ResidueField A))) n d) :
    IsTorsionVanishingBound (Spec (.of A)) n d := by
  intro G hG p hp
  have := subsingleton_H_inverseImage_of_isTorsionVanishingBound
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) hk hG hp
  exact (etaleCohomologyRestrictionMap_bijective_of_henselianPair A
    (IsLocalRing.maximalIdeal A) (henselianPair_maximalIdeal A) G
    (torsionSheafProperty_of_forall_nsmul_eq_zero hn hG) p).1.subsingleton

end AlgebraicGeometry.Scheme

end
